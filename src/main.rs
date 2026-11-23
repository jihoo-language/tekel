use std::io::Read;
use std::process::ExitCode;
use tekel::eval::{self, Family, Machine, RunError};
use tekel::rat::Rat;
use tekel::syntax::Metric;
use tekel::{Analysis, BudgetResult, Options};

const USAGE: &str = "\
usage:
  tekel bound FILE                 infer a cost bound for every function, check budgets
  tekel run FILE FUNCTION ARGS...  run a call, audit every call against its bound
  tekel weigh FILE FUNCTION        compare the bound with the worst cost seen on inputs

options:
  --metric steps|alloc|ticks       what a run costs (default: the file's `metric`, else steps)
  --degree D                       highest polynomial degree to try (default 4)
  --max N                          largest input size for `weigh` (default 64)

FILE may be `-` for standard input.";

struct Args {
    cmd: String,
    rest: Vec<String>,
    opts: Options,
    max: usize,
}

fn parse_args() -> Result<Args, String> {
    let mut it = std::env::args().skip(1);
    let mut opts = Options::default();
    let mut max = 64;
    let mut pos = Vec::new();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--metric" => {
                let m = it.next().ok_or("--metric needs a value")?;
                opts.metric = Some(Metric::parse(&m).ok_or(format!("unknown metric `{m}`"))?);
            }
            "--degree" => {
                let d = it.next().ok_or("--degree needs a value")?;
                opts.max_degree = d.parse().ok().filter(|d| *d <= 8).ok_or("--degree takes 0 to 8")?;
            }
            "--max" => {
                let n = it.next().ok_or("--max needs a value")?;
                max = n.parse().map_err(|_| "--max takes a number")?;
            }
            "-h" | "--help" => return Err(String::new()),
            _ => pos.push(a),
        }
    }
    if pos.is_empty() {
        return Err(String::new());
    }
    let cmd = pos.remove(0);
    Ok(Args { cmd, rest: pos, opts, max })
}

fn read(path: &str) -> Result<String, String> {
    if path == "-" {
        let mut s = String::new();
        std::io::stdin().read_to_string(&mut s).map_err(|e| e.to_string())?;
        Ok(s)
    } else {
        std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))
    }
}

fn load(path: &str, opts: &Options) -> Result<Analysis, String> {
    let src = read(path)?;
    tekel::analyze(&src, opts).map_err(|e| format!("{}: {e}", if path == "-" { "<stdin>" } else { path }))
}

fn cmd_bound(a: &Args) -> Result<bool, String> {
    let [path] = &a.rest[..] else { return Err("usage: tekel bound FILE".into()) };
    let an = load(path, &a.opts)?;
    println!("metric: {}", an.metric.name());
    let width = an
        .module
        .fns
        .iter()
        .map(|f| f.name.chars().count() + 2 + f.params.iter().map(|(x, _)| x.chars().count() + 2).sum::<usize>())
        .max()
        .unwrap_or(0);
    for (f, r) in an.module.fns.iter().zip(&an.fns) {
        let call = format!("{}({})", f.name, f.params.iter().map(|(x, _)| x.as_str()).collect::<Vec<_>>().join(", "));
        let pad = width.saturating_sub(call.chars().count());
        match &r.bound {
            Some(_) => println!("  {call}{} ≤ {}    {}", " ".repeat(pad), r.text, r.order),
            None => println!("  {call}{}   {}", " ".repeat(pad), r.text),
        }
        match &r.budget {
            BudgetResult::None => {}
            BudgetResult::Within(b) => println!("  {}   within its budget {b}", " ".repeat(width)),
            BudgetResult::Exceeds(b) => {
                println!("  {}   EXCEEDS its budget {b}: weighed and found wanting", " ".repeat(width))
            }
        }
    }
    Ok(an.ok())
}

fn cmd_run(a: &Args) -> Result<bool, String> {
    if a.rest.len() < 2 {
        return Err("usage: tekel run FILE FUNCTION ARGS...".into());
    }
    let an = load(&a.rest[0], &a.opts)?;
    let name = &a.rest[1];
    let fi = an.module.index(name).ok_or(format!("no function `{name}`"))?;
    let f = &an.module.fns[fi];
    let raw = &a.rest[2..];
    if raw.len() != f.params.len() {
        return Err(format!("`{name}` takes {} argument(s), but {} were given", f.params.len(), raw.len()));
    }
    let args = raw
        .iter()
        .zip(&f.params)
        .map(|(s, (x, t))| eval::parse_value(s, t).map_err(|e| format!("argument `{x}`: {e}")))
        .collect::<Result<Vec<_>, _>>()?;
    let bounds = an.bounds();
    let mut m = Machine::new(&an.module, an.metric, Some(&bounds));
    let result = m.call(fi, args.clone());
    let v = result.map_err(|e| match e {
        RunError::Unsound { .. } => format!("{e}"),
        _ => format!("runtime error after cost {}: {e}", m.cost),
    })?;
    println!("{v}");
    let bound = an.fns[fi].bound.as_ref().map(|b| eval::bound_at(b, &args));
    eprintln!(
        "cost {} {}{}, {} call(s) audited",
        m.cost,
        an.metric.name(),
        match bound {
            Some(b) => format!(" (bound {b})"),
            None => " (no bound)".into(),
        },
        m.calls_audited
    );
    Ok(true)
}

fn cmd_weigh(a: &Args) -> Result<bool, String> {
    let [path, name] = &a.rest[..] else { return Err("usage: tekel weigh FILE FUNCTION".into()) };
    let an = load(path, &a.opts)?;
    let fi = an.module.index(name).ok_or(format!("no function `{name}`"))?;
    let f = &an.module.fns[fi];
    let report = &an.fns[fi];
    let call = format!("{}({})", f.name, f.params.iter().map(|(x, _)| x.as_str()).collect::<Vec<_>>().join(", "));
    println!("{call} ≤ {}    [{}]", report.text, an.metric.name());
    let Some(bound) = &report.bound else { return Ok(false) };
    let bounds = an.bounds();
    let mut sizes = vec![0usize, 1, 2, 3, 4];
    let mut n = 8;
    while n <= a.max {
        sizes.push(n);
        n *= 2;
    }
    sizes.retain(|s| *s <= a.max);
    println!();
    println!("  {:>5}  {:>14}  {:>14}", "n", "worst seen", "bound");
    let mut all_tight = true;
    let mut audited = 0u64;
    for n in sizes {
        let mut worst: Option<Rat> = None;
        let mut at_worst = Rat::ZERO;
        let mut failure = None;
        for fam in Family::all() {
            let args: Vec<_> = f.params.iter().map(|(_, t)| eval::generate(t, n, fam)).collect();
            let mut m = Machine::new(&an.module, an.metric, Some(&bounds));
            match m.call(fi, args.clone()) {
                Ok(_) => {
                    audited += m.calls_audited;
                    if worst.is_none_or(|w| m.cost > w) {
                        worst = Some(m.cost);
                        at_worst = eval::bound_at(bound, &args);
                    }
                }
                Err(e @ RunError::Unsound { .. }) => return Err(e.to_string()),
                Err(e) => failure = Some(e.to_string()),
            }
        }
        match worst {
            Some(w) => {
                let tight = w == at_worst;
                all_tight &= tight;
                println!(
                    "  {n:>5}  {:>14}  {:>14}{}",
                    w.to_string(),
                    at_worst.to_string(),
                    if tight { "  tight" } else { "" }
                );
            }
            None => println!("  {n:>5}  {:>14}", failure.unwrap_or_default()),
        }
    }
    println!();
    println!(
        "{audited} call(s) audited; {}",
        if all_tight { "the bound is reached at every size" } else { "no call exceeded its bound" }
    );
    Ok(true)
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            if !e.is_empty() {
                eprintln!("tekel: {e}");
            }
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    // Overflow in exact arithmetic is reported as an error, not a crash.
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if info.payload().downcast_ref::<&str>() != Some(&tekel::rat::OVERFLOW) {
            default(info);
        }
    }));
    // Deep recursion over long lists needs a deep stack.
    let child = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || match args.cmd.as_str() {
            "bound" => cmd_bound(&args),
            "run" => cmd_run(&args),
            "weigh" => cmd_weigh(&args),
            other => Err(format!("unknown command `{other}`\n{USAGE}")),
        })
        .expect("spawn");
    match child.join() {
        Ok(Ok(true)) => ExitCode::SUCCESS,
        Ok(Ok(false)) => ExitCode::FAILURE,
        Ok(Err(e)) => {
            eprintln!("tekel: {e}");
            ExitCode::FAILURE
        }
        Err(_) => ExitCode::FAILURE,
    }
}

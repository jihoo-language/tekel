use tekel::eval::{self, Family, Machine, RunError};
use tekel::syntax::Metric;
use tekel::{Analysis, BudgetResult, Options};

fn analyze(src: &str) -> Analysis {
    tekel::analyze(src, &Options::default()).unwrap_or_else(|e| panic!("{e}"))
}

fn analyze_with(src: &str, metric: Metric) -> Analysis {
    tekel::analyze(src, &Options { metric: Some(metric), ..Options::default() }).unwrap_or_else(|e| panic!("{e}"))
}

fn bound(a: &Analysis, f: &str) -> String {
    let r = a.get(f).unwrap_or_else(|| panic!("no function {f}"));
    assert!(r.bound.is_some(), "{f}: {}", r.text);
    r.text.clone()
}

fn example(name: &str) -> String {
    std::fs::read_to_string(format!("{}/examples/{name}", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

/// Runs every function on generated inputs and audits every call.
/// Returns the number of calls audited.
fn audit_all(src: &str, metric: Metric, max_n: usize) -> u64 {
    let a = analyze_with(src, metric);
    let bounds = a.bounds();
    let mut audited = 0;
    for (i, f) in a.module.fns.iter().enumerate() {
        if a.fns[i].bound.is_none() {
            continue;
        }
        for n in 0..=max_n {
            for fam in Family::all() {
                let args: Vec<_> = f.params.iter().map(|(_, t)| eval::generate(t, n, fam)).collect();
                let mut m = Machine::new(&a.module, a.metric, Some(&bounds));
                match m.call(i, args) {
                    Ok(_) | Err(RunError::Fail(_)) | Err(RunError::Arith(_)) => audited += m.calls_audited,
                    Err(e) => panic!("{} at n = {n} under {}: {e}", f.name, metric.name()),
                }
            }
        }
    }
    audited
}

// ---------------------------------------------------------------- bounds

#[test]
fn sorting_bounds() {
    let a = analyze(&example("sort.tk"));
    assert_eq!(bound(&a, "insert"), "|l| + 1");
    assert_eq!(bound(&a, "isort"), "1/2·|l|² + 3/2·|l| + 1");
    assert_eq!(bound(&a, "append"), "|xs| + 1");
    assert_eq!(bound(&a, "partition"), "|l| + 1");
    assert_eq!(bound(&a, "quicksort"), "|l|² + 3·|l| + 1");
    assert!(a.ok());
}

#[test]
fn amortized_queue() {
    let a = analyze(&example("queue.tk"));
    assert_eq!(bound(&a, "dequeue"), "|back| + 2");
    assert_eq!(bound(&a, "simulate"), "3·|ops| + 2");
}

#[test]
fn reverse_two_ways() {
    let a = analyze(&example("reverse.tk"));
    assert_eq!(bound(&a, "slow_reverse"), "1/2·|l|² + 3/2·|l| + 1");
    assert_eq!(bound(&a, "reverse"), "|l| + 2");
    assert!(a.ok());
}

#[test]
fn nested_lists() {
    let a = analyze(&example("nested.tk"));
    assert_eq!(bound(&a, "concat"), "Σ_{x∈ls} |x| + 2·|ls| + 1");
    assert_eq!(bound(&a, "pairs"), "|l|² + 2·|l| + 1");
    let alloc = analyze_with(&example("nested.tk"), Metric::Alloc);
    assert_eq!(bound(&alloc, "pairs"), "|l|² - |l|");
    assert_eq!(bound(&alloc, "sum"), "0");
}

#[test]
fn products_of_sizes() {
    let a = analyze(&example("product.tk"));
    assert_eq!(bound(&a, "product"), "2·|xs|·|ys| + 3·|xs| + 1");
    assert_eq!(bound(&a, "sort_onto"), "|xs|·|ys| + 1/2·|xs|² + 1/2·|ys|² + 5/2·|xs| + 3/2·|ys| + 3");
    assert!(a.ok());
}

#[test]
fn composition_of_quadratics() {
    let a = analyze(&example("compose.tk"));
    assert_eq!(bound(&a, "sorted_pair_sums"), "1/8·|l|⁴ - 1/4·|l|³ + 15/8·|l|² + 5/4·|l| + 3");
}

#[test]
fn comparisons() {
    let a = analyze(&example("comparisons.tk"));
    assert_eq!(a.metric, Metric::Ticks);
    assert_eq!(bound(&a, "isort"), "1/2·|l|² - 1/2·|l|");
    assert_eq!(bound(&a, "merge"), "|xs| + |ys|");
}

#[test]
fn exponential_has_no_bound() {
    let a = analyze(&example("rejected/subsets.tk"));
    assert!(a.get("subsets").unwrap().bound.is_none());
    assert!(a.get("cons_all").unwrap().bound.is_some());
}

#[test]
fn budget_exceeded() {
    let a = analyze(&example("rejected/budget.tk"));
    assert!(!a.ok());
    assert!(matches!(a.get("reverse").unwrap().budget, BudgetResult::Exceeds(_)));
}

#[test]
fn budget_checked_exactly() {
    // n² + 2 − (1/2 n² + 3/2 n + 1) = (n − 1)(n − 2)/2 ≥ 0 on the naturals,
    // though not coefficient by coefficient in the binomial basis.
    let src = example("sort.tk").replace("costs 1 + |l| + |l|^2", "costs |l|^2 + 2");
    assert!(analyze(&src).ok());
    // At n = 1 insertion sort makes 3 calls.
    let src = example("sort.tk").replace("costs 1 + |l| + |l|^2", "costs |l|^2 + 1");
    assert!(!analyze(&src).ok());
    let src = example("sort.tk").replace("costs 1 + |l| + |l|^2", "costs |l|^2");
    assert!(!analyze(&src).ok());
}

#[test]
fn product_budget() {
    let src =
        example("product.tk").replace("costs 2 * |xs| * |ys| + 3 * |xs| + 1", "costs 2 * |xs| * |ys| + 2 * |xs| + 1");
    assert!(!analyze(&src).ok());
}

#[test]
fn sharing_a_list() {
    let a = analyze(
        "fn len(l: List<Int>) -> Int = match l { [] => 0  _ :: t => 1 + len(t) }
         fn both(l: List<Int>) -> Int = len(l) + len(l)
         fn pair_up(l: List<Int>) -> (List<Int>, List<Int>) = (l, l)
         fn twice_len(l: List<Int>) -> Int = { let (a, b) = pair_up(l); len(a) + len(b) }
         fn same(a: List<Int>, b: List<Int>) -> Int = len(a) + len(b)
         fn diag(l: List<Int>) -> Int = same(l, l)",
    );
    assert_eq!(bound(&a, "both"), "2·|l| + 3");
    assert_eq!(bound(&a, "twice_len"), "2·|l| + 4");
    assert_eq!(bound(&a, "diag"), "2·|l| + 4");
}

#[test]
fn generic_functions_drop_element_potential() {
    // `id` cannot carry the potential inside the elements of a `List<a>`,
    // so the inner lists must be paid for before the call.
    let a = analyze(
        "fn len(l: List<Int>) -> Int = match l { [] => 0  _ :: t => 1 + len(t) }
         fn id(l: List<a>) -> List<a> = l
         fn total(m: List<List<Int>>) -> Int = match m { [] => 0  r :: rs => len(r) + total(rs) }
         fn total_id(m: List<List<Int>>) -> Int = total(id(m))",
    );
    assert_eq!(bound(&a, "total"), "Σ_{x∈m} |x| + 2·|m| + 1");
    assert!(a.get("total_id").unwrap().bound.is_none());
}

#[test]
fn constant_and_branching() {
    let a = analyze(
        "fn head(l: List<Int>) -> Int = match l { [] => fail(\"empty\")  x :: _ => x }
         fn pick(b: Bool, l: List<Int>) -> Int = if b then head(l) else 0",
    );
    assert_eq!(bound(&a, "head"), "1");
    assert_eq!(bound(&a, "pick"), "2");
}

// ---------------------------------------------------------------- soundness

#[test]
fn every_call_within_its_bound() {
    let files = ["sort.tk", "queue.tk", "reverse.tk", "nested.tk", "product.tk", "compose.tk", "comparisons.tk"];
    let mut total = 0;
    for f in files {
        let src = example(f);
        for metric in [Metric::Steps, Metric::Alloc, Metric::Ticks] {
            total += audit_all(&src, metric, 7);
        }
    }
    assert!(total > 100_000, "only {total} calls audited");
}

#[test]
fn adversarial_programs_within_bounds() {
    let src = "
        fn len(l: List<Int>) -> Int = match l { [] => 0  _ :: t => 1 + len(t) }
        fn append(xs: List<a>, ys: List<a>) -> List<a> = match xs { [] => ys  x :: r => x :: append(r, ys) }
        fn dup(l: List<Int>) -> List<Int> = append(l, l)
        fn square(l: List<Int>) -> List<Int> = match l { [] => []  _ :: t => append(l, square(t)) }
        fn self_pair(l: List<Int>) -> Int = { let p = (l, l); let (a, b) = p; len(append(a, b)) }
        fn tails(l: List<Int>) -> List<List<Int>> = match l { [] => [[]]  _ :: t => l :: tails(t) }
        fn flat(ls: List<List<Int>>) -> List<Int> = match ls { [] => []  l :: r => append(l, flat(r)) }
        fn tails_len(l: List<Int>) -> Int = len(flat(tails(l)))
        fn zip(xs: List<Int>, ys: List<Int>) -> List<(Int, Int)> =
          match xs { [] => []  x :: xr => match ys { [] => []  y :: yr => (x, y) :: zip(xr, yr) } }
        fn zip_self(l: List<Int>) -> Int = { let z = zip(l, l); match z { [] => 0  _ :: _ => len(l) } }
        fn nested_match(l: List<Int>) -> Int =
          match l { [] => 0  x :: t => match l { [] => 1  _ :: u => x + len(u) + len(t) } }
    ";
    let a = analyze(src);
    for f in ["dup", "square", "self_pair", "tails_len", "zip_self", "nested_match"] {
        assert!(a.get(f).unwrap().bound.is_some(), "{f} has no bound");
    }
    // tails, flatten and count: (n + 1)² + 2n + 5 calls, exactly.
    assert_eq!(bound(&a, "tails_len"), "|l|² + 4·|l| + 6");
    for metric in [Metric::Steps, Metric::Alloc] {
        audit_all(src, metric, 8);
    }
}

// ---------------------------------------------------------------- running

#[test]
fn run_and_audit() {
    let a = analyze(&example("sort.tk"));
    let bounds = a.bounds();
    let f = a.module.index("quicksort").unwrap();
    let arg = eval::parse_value("[3, 1, 4, 1, 5, 9, 2, 6]", &a.module.fns[f].params[0].1).unwrap();
    let mut m = Machine::new(&a.module, a.metric, Some(&bounds));
    let v = m.call(f, vec![arg.clone()]).unwrap();
    assert_eq!(v.to_string(), "[1, 1, 2, 3, 4, 5, 6, 9]");
    assert!(m.cost <= eval::bound_at(a.fns[f].bound.as_ref().unwrap(), &[arg]));
    assert_eq!(m.calls_audited, 53);
}

#[test]
fn arithmetic_errors() {
    let a = analyze("fn f(x: Int) -> Int = 10 / x");
    let arg = eval::parse_value("0", &tekel::syntax::Type::Int).unwrap();
    let mut m = Machine::new(&a.module, a.metric, None);
    assert!(matches!(m.call(0, vec![arg]), Err(RunError::Arith(_))));
}

// ---------------------------------------------------------------- errors

fn error(src: &str) -> String {
    match tekel::analyze(src, &Options::default()) {
        Ok(_) => panic!("expected an error"),
        Err(e) => e.to_string(),
    }
}

#[test]
fn type_errors() {
    assert!(error("fn f(x: Int) -> Bool = x").contains("expected Bool, found Int"));
    assert!(error("fn f(l: List<Int>) -> Int = match l { [] => 0 }").contains("does not handle `x :: xs`"));
    assert!(error("fn f(x: Int) -> Int = g(x)").contains("unknown function `g`"));
    assert!(error("fn f(x: Int) -> Int = y").contains("unknown variable `y`"));
    assert!(error("fn f(l: List<Int>) -> Bool = l == l").contains("compares Int, Bool or Unit"));
    assert!(error("fn f(x: Int) -> a = fail(\"no\")").contains("type parameter `a`"));
}

#[test]
fn budget_errors() {
    assert!(error("fn f(x: Int) -> Int costs |x| = x").contains("is not a list"));
    assert!(error("fn f(l: List<Int>) -> Int costs |m| = 0").contains("not a parameter"));
}

#[test]
fn parse_errors() {
    assert!(error("fn f( -> Int = 0").starts_with("1:"));
    assert!(error("fn f(l: List<Int>) -> Int = match l { [] => 0  x :: y :: z => 1 }").contains("one cell at a time"));
    assert!(error("fn f(x: Int) -> Bool = 1 < x < 2").contains("do not chain"));
}

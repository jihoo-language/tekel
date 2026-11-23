//! Tekel: a language whose functions are weighed.
//!
//! The analysis infers, for every function, a polynomial bound on its cost
//! in terms of the sizes of its arguments. A declared budget that cannot be
//! proved is a compile-time error. The interpreter audits every call of a
//! run against its bound.

pub mod aara;
pub mod core;
pub mod error;
pub mod eval;
pub mod lp;
pub mod poly;
pub mod rat;
pub mod report;
pub mod syntax;
pub mod types;

use aara::{Analyzer, Bound};
use error::{Error, Result};
use syntax::Metric;

pub const DEFAULT_DEGREE: usize = 4;

#[derive(Clone, Debug)]
pub struct Options {
    /// Overrides the metric the program declares.
    pub metric: Option<Metric>,
    pub max_degree: usize,
}

impl Default for Options {
    fn default() -> Options {
        Options { metric: None, max_degree: DEFAULT_DEGREE }
    }
}

pub enum BudgetResult {
    None,
    Within(String),
    Exceeds(String),
}

pub struct FnReport {
    pub name: String,
    pub bound: Option<Bound>,
    /// The bound, written out, or why there is none.
    pub text: String,
    pub order: String,
    pub budget: BudgetResult,
}

pub struct Analysis {
    pub module: core::Module,
    pub metric: Metric,
    pub fns: Vec<FnReport>,
}

impl Analysis {
    pub fn bounds(&self) -> Vec<Option<Bound>> {
        self.fns.iter().map(|f| f.bound.clone()).collect()
    }

    pub fn get(&self, name: &str) -> Option<&FnReport> {
        self.fns.iter().find(|f| f.name == name)
    }

    /// Whether every declared budget was proved.
    pub fn ok(&self) -> bool {
        self.fns.iter().all(|f| !matches!(f.budget, BudgetResult::Exceeds(_)))
    }
}

pub fn parse_and_check(src: &str) -> Result<(syntax::Program, core::Module)> {
    let prog = syntax::parse(src)?;
    let module = types::check(&prog)?;
    Ok((prog, module))
}

/// Parses, type-checks and weighs a program.
pub fn analyze(src: &str, opts: &Options) -> Result<Analysis> {
    let (prog, module) = parse_and_check(src)?;
    let metric = opts.metric.or(prog.metric).unwrap_or(Metric::Steps);
    let mut an = Analyzer::new(&module, metric);
    let mut fns = Vec::new();
    for (i, f) in module.fns.iter().enumerate() {
        let def = &prog.fns[i];
        let split = def.budget.as_ref().map(|b| report::split_budget(f, b)).transpose()?;
        if let (Some(s), Some(b)) = (&split, &def.budget)
            && s.degree > 8
        {
            return Err(Error::at(b.pos, "a budget's degree is at most 8"));
        }
        let bound = an.bound(i, opts.max_degree)?;
        let (text, order) = match &bound {
            Some(b) => (report::show_bound(b, &f.params), report::show_order(b, &f.params)),
            None => (format!("no polynomial bound of degree ≤ {}", opts.max_degree), "unbounded?".to_string()),
        };
        let budget = match &split {
            None => BudgetResult::None,
            Some(s) => {
                let shown = report::show_budget(f, s);
                match report::check_budget(&mut an, i, s, bound.as_ref(), opts.max_degree)? {
                    report::Verdict::Within => BudgetResult::Within(shown),
                    report::Verdict::Exceeds => BudgetResult::Exceeds(shown),
                }
            }
        };
        fns.push(FnReport { name: f.name.clone(), bound, text, order, budget });
    }
    Ok(Analysis { module, metric, fns })
}

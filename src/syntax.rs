//! Lexer, abstract syntax and parser.

use crate::error::{Error, Pos, Result};
use crate::rat::Rat;

// ---------------------------------------------------------------- syntax

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    List(Box<Type>),
    Pair(Box<Type>, Box<Type>),
    /// A type parameter such as `a`. Values of a parameter type carry no potential.
    Param(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Metric {
    /// Every call of a function costs one step.
    Steps,
    /// Every list cell that is built costs one.
    Alloc,
    /// Only `tick(q)` costs, and it costs `q`.
    Ticks,
}

impl Metric {
    pub fn name(self) -> &'static str {
        match self {
            Metric::Steps => "steps",
            Metric::Alloc => "alloc",
            Metric::Ticks => "ticks",
        }
    }

    pub fn parse(s: &str) -> Option<Metric> {
        match s {
            "steps" => Some(Metric::Steps),
            "alloc" => Some(Metric::Alloc),
            "ticks" => Some(Metric::Ticks),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "&&",
            BinOp::Or => "||",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: usize,
    pub pos: Pos,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Var(String),
    Int(i64),
    Bool(bool),
    Unit,
    Nil,
    List(Vec<Expr>),
    Cons(Box<Expr>, Box<Expr>),
    Pair(Box<Expr>, Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Arm>),
    Let(Pat, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Tick(Rat),
    Fail(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Var(String),
    Wild,
    Pair(Box<Pat>, Box<Pat>),
}

#[derive(Clone, Debug)]
pub enum ArmPat {
    Nil,
    Cons(Option<String>, Option<String>),
    Other(Pat),
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pos: Pos,
    pub pat: ArmPat,
    pub body: Expr,
}

/// A monomial `c · |x₁|^k₁ · |x₂|^k₂ …` of a declared budget.
#[derive(Clone, Debug)]
pub struct Monomial {
    pub coeff: Rat,
    pub sizes: Vec<(String, usize)>,
}

#[derive(Clone, Debug)]
pub struct Budget {
    pub pos: Pos,
    pub terms: Vec<Monomial>,
}

#[derive(Clone, Debug)]
pub struct FnDef {
    pub pos: Pos,
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub budget: Option<Budget>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub metric: Option<Metric>,
    pub fns: Vec<FnDef>,
    /// Number of expression ids handed out.
    pub exprs: usize,
}

impl Program {
    pub fn get(&self, name: &str) -> Option<&FnDef> {
        self.fns.iter().find(|f| f.name == name)
    }
}

// ---------------------------------------------------------------- lexer

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Int(i64),
    Str(String),
    Sym(&'static str),
    Eof,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    pos: Pos,
}

const SYMS: &[&str] = &[
    "::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "(", ")", "[", "]", "{", "}", ",", ";", ":", "=", "<", ">",
    "+", "-", "*", "/", "%", "!", "|", "^", ".",
];

fn lex(src: &str) -> Result<Vec<Token>> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let (mut i, mut line, mut col) = (0usize, 1usize, 1usize);
    while i < chars.len() {
        let c = chars[i];
        let pos = Pos { line, col };
        if c == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            col += 1;
            continue;
        }
        if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
            }
            let text: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            let n = text.parse::<i64>().map_err(|_| Error::at(pos, format!("integer literal {text} is too large")))?;
            col += i - start;
            out.push(Token { tok: Tok::Int(n), pos });
            continue;
        }
        if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '\'') {
                i += 1;
            }
            col += i - start;
            out.push(Token { tok: Tok::Ident(chars[start..i].iter().collect()), pos });
            continue;
        }
        if c == '"' {
            let start = i;
            i += 1;
            let mut s = String::new();
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\n' {
                    return Err(Error::at(pos, "unterminated string"));
                }
                s.push(chars[i]);
                i += 1;
            }
            if i == chars.len() {
                return Err(Error::at(pos, "unterminated string"));
            }
            i += 1;
            col += i - start;
            out.push(Token { tok: Tok::Str(s), pos });
            continue;
        }
        let rest: String = chars[i..chars.len().min(i + 2)].iter().collect();
        match SYMS.iter().find(|s| rest.starts_with(**s)) {
            Some(s) => {
                i += s.len();
                col += s.len();
                out.push(Token { tok: Tok::Sym(s), pos });
            }
            None => return Err(Error::at(pos, format!("unexpected character `{c}`"))),
        }
    }
    out.push(Token { tok: Tok::Eof, pos: Pos { line: line + 1, col: 1 } });
    Ok(out)
}

// ---------------------------------------------------------------- parser

const KEYWORDS: &[&str] =
    &["fn", "let", "if", "then", "else", "match", "true", "false", "tick", "fail", "costs", "metric"];

struct Parser {
    toks: Vec<Token>,
    i: usize,
    next_id: usize,
}

pub fn parse(src: &str) -> Result<Program> {
    let mut p = Parser { toks: lex(src)?, i: 0, next_id: 0 };
    let mut metric = None;
    let mut fns: Vec<FnDef> = Vec::new();
    while !p.at_eof() {
        if p.eat_kw("metric") {
            let pos = p.pos();
            let name = p.ident()?;
            let m = Metric::parse(&name)
                .ok_or_else(|| Error::at(pos, format!("unknown metric `{name}` (use steps, alloc or ticks)")))?;
            if metric.replace(m).is_some() {
                return Err(Error::at(pos, "the metric is declared twice"));
            }
        } else if p.peek_kw("fn") {
            let f = p.fn_def()?;
            if fns.iter().any(|g| g.name == f.name) {
                return Err(Error::at(f.pos, format!("function `{}` is defined twice", f.name)));
            }
            fns.push(f);
        } else {
            return Err(p.unexpected("`fn` or `metric`"));
        }
    }
    Ok(Program { metric, fns, exprs: p.next_id })
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.i].tok
    }

    fn pos(&self) -> Pos {
        self.toks[self.i].pos
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek(), Tok::Eof)
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.i].clone();
        if !matches!(t.tok, Tok::Eof) {
            self.i += 1;
        }
        t
    }

    fn describe(t: &Tok) -> String {
        match t {
            Tok::Ident(s) => format!("`{s}`"),
            Tok::Int(n) => format!("`{n}`"),
            Tok::Str(s) => format!("\"{s}\""),
            Tok::Sym(s) => format!("`{s}`"),
            Tok::Eof => "end of file".into(),
        }
    }

    fn unexpected(&self, want: &str) -> Error {
        Error::at(self.pos(), format!("expected {want}, found {}", Self::describe(self.peek())))
    }

    fn peek_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(t) if *t == s)
    }

    fn eat_sym(&mut self, s: &str) -> bool {
        if self.peek_sym(s) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect_sym(&mut self, s: &str) -> Result<()> {
        if self.eat_sym(s) {
            return Ok(());
        }
        // `List<Int>=` lexes as `>=`; split it when a `>` is wanted.
        if s == ">" && self.peek_sym(">=") {
            self.toks[self.i].tok = Tok::Sym("=");
            return Ok(());
        }
        Err(self.unexpected(&format!("`{s}`")))
    }

    fn peek_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Ident(t) if t == k)
    }

    fn eat_kw(&mut self, k: &str) -> bool {
        if self.peek_kw(k) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect_kw(&mut self, k: &str) -> Result<()> {
        if self.eat_kw(k) { Ok(()) } else { Err(self.unexpected(&format!("`{k}`"))) }
    }

    fn ident(&mut self) -> Result<String> {
        match self.peek().clone() {
            Tok::Ident(s) if !KEYWORDS.contains(&s.as_str()) => {
                self.bump();
                Ok(s)
            }
            _ => Err(self.unexpected("a name")),
        }
    }

    fn mk(&mut self, pos: Pos, kind: ExprKind) -> Expr {
        let id = self.next_id;
        self.next_id += 1;
        Expr { id, pos, kind }
    }

    fn fn_def(&mut self) -> Result<FnDef> {
        self.expect_kw("fn")?;
        let pos = self.pos();
        let name = self.ident()?;
        self.expect_sym("(")?;
        let mut params: Vec<(String, Type)> = Vec::new();
        while !self.peek_sym(")") {
            let ppos = self.pos();
            let x = self.ident()?;
            if params.iter().any(|(y, _)| *y == x) {
                return Err(Error::at(ppos, format!("parameter `{x}` is declared twice")));
            }
            self.expect_sym(":")?;
            let t = self.ty()?;
            params.push((x, t));
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym(")")?;
        self.expect_sym("->")?;
        let ret = self.ty()?;
        let budget = if self.peek_kw("costs") {
            let bpos = self.pos();
            self.bump();
            Some(Budget { pos: bpos, terms: self.budget()? })
        } else {
            None
        };
        self.expect_sym("=")?;
        let body = self.expr()?;
        Ok(FnDef { pos, name, params, ret, budget, body })
    }

    fn ty(&mut self) -> Result<Type> {
        let pos = self.pos();
        if self.eat_sym("(") {
            if self.eat_sym(")") {
                return Ok(Type::Unit);
            }
            let a = self.ty()?;
            if self.eat_sym(")") {
                return Ok(a);
            }
            self.expect_sym(",")?;
            let b = self.ty()?;
            self.expect_sym(")")?;
            return Ok(Type::Pair(Box::new(a), Box::new(b)));
        }
        let name = self.ident()?;
        match name.as_str() {
            "Int" => Ok(Type::Int),
            "Bool" => Ok(Type::Bool),
            "Unit" => Ok(Type::Unit),
            "List" => {
                self.expect_sym("<")?;
                let t = self.ty()?;
                self.expect_sym(">")?;
                Ok(Type::List(Box::new(t)))
            }
            s if s.starts_with(|c: char| c.is_lowercase()) => Ok(Type::Param(name)),
            _ => Err(Error::at(pos, format!("unknown type `{name}`"))),
        }
    }

    fn rat_lit(&mut self) -> Result<Rat> {
        let n = match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                n
            }
            _ => return Err(self.unexpected("a number")),
        };
        if self.eat_sym("/") {
            let pos = self.pos();
            match self.peek().clone() {
                Tok::Int(0) => Err(Error::at(pos, "division by zero in a constant")),
                Tok::Int(d) => {
                    self.bump();
                    Ok(Rat::new(n as i128, d as i128))
                }
                _ => Err(self.unexpected("a denominator")),
            }
        } else {
            Ok(Rat::int(n as i128))
        }
    }

    /// `budget ::= term ('+' term)*`, `term ::= factor ('*' factor)*`,
    /// `factor ::= n | n/m | '|' x '|' ('^' k)?`.
    fn budget(&mut self) -> Result<Vec<Monomial>> {
        let mut terms = Vec::new();
        loop {
            let mut m = Monomial { coeff: Rat::ONE, sizes: Vec::new() };
            loop {
                if self.eat_sym("|") {
                    let x = self.ident()?;
                    self.expect_sym("|")?;
                    let mut k = 1usize;
                    if self.eat_sym("^") {
                        match self.peek().clone() {
                            Tok::Int(e) if (1..=8).contains(&e) => {
                                self.bump();
                                k = e as usize;
                            }
                            _ => return Err(self.unexpected("an exponent between 1 and 8")),
                        }
                    }
                    m.sizes.push((x, k));
                } else {
                    m.coeff = m.coeff * self.rat_lit()?;
                }
                if !self.eat_sym("*") {
                    break;
                }
            }
            terms.push(m);
            if !self.eat_sym("+") {
                break;
            }
        }
        Ok(terms)
    }

    fn pat(&mut self) -> Result<Pat> {
        if self.eat_sym("(") {
            let a = self.pat()?;
            if self.eat_sym(")") {
                return Ok(a);
            }
            self.expect_sym(",")?;
            let b = self.pat()?;
            self.expect_sym(")")?;
            return Ok(Pat::Pair(Box::new(a), Box::new(b)));
        }
        let x = self.ident()?;
        Ok(if x == "_" { Pat::Wild } else { Pat::Var(x) })
    }

    fn binder(&mut self) -> Result<Option<String>> {
        let x = self.ident()?;
        Ok(if x == "_" { None } else { Some(x) })
    }

    fn arm_pat(&mut self) -> Result<ArmPat> {
        if self.eat_sym("[") {
            self.expect_sym("]")?;
            return Ok(ArmPat::Nil);
        }
        if matches!(self.peek(), Tok::Ident(_)) && matches!(self.toks[self.i + 1].tok, Tok::Sym("::")) {
            let h = self.binder()?;
            self.expect_sym("::")?;
            let t = self.binder()?;
            if self.peek_sym("::") {
                return Err(Error::at(
                    self.pos(),
                    "patterns match one cell at a time: write a nested `match` on the tail",
                ));
            }
            return Ok(ArmPat::Cons(h, t));
        }
        Ok(ArmPat::Other(self.pat()?))
    }

    pub fn expr(&mut self) -> Result<Expr> {
        self.binary(0)
    }

    fn binary(&mut self, level: usize) -> Result<Expr> {
        // Levels from loosest to tightest.
        const LEVELS: &[&[(&str, BinOp)]] = &[
            &[("||", BinOp::Or)],
            &[("&&", BinOp::And)],
            &[
                ("==", BinOp::Eq),
                ("!=", BinOp::Ne),
                ("<=", BinOp::Le),
                (">=", BinOp::Ge),
                ("<", BinOp::Lt),
                (">", BinOp::Gt),
            ],
            &[], // `::`, right associative
            &[("+", BinOp::Add), ("-", BinOp::Sub)],
            &[("*", BinOp::Mul), ("/", BinOp::Div), ("%", BinOp::Mod)],
        ];
        if level == LEVELS.len() {
            return self.unary();
        }
        if level == 3 {
            let pos = self.pos();
            let head = self.binary(level + 1)?;
            if self.eat_sym("::") {
                let tail = self.binary(level)?;
                return Ok(self.mk(pos, ExprKind::Cons(Box::new(head), Box::new(tail))));
            }
            return Ok(head);
        }
        let pos = self.pos();
        let mut lhs = self.binary(level + 1)?;
        loop {
            let op = LEVELS[level].iter().find(|(s, _)| self.peek_sym(s)).map(|(_, op)| *op);
            let Some(op) = op else { break };
            self.bump();
            let rhs = self.binary(level + 1)?;
            lhs = self.mk(pos, ExprKind::Bin(op, Box::new(lhs), Box::new(rhs)));
            if level == 2 {
                if LEVELS[2].iter().any(|(s, _)| self.peek_sym(s)) {
                    return Err(Error::at(self.pos(), "comparisons do not chain; add parentheses"));
                }
                break;
            }
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> Result<Expr> {
        let pos = self.pos();
        if self.eat_sym("-") {
            let e = self.unary()?;
            return Ok(self.mk(pos, ExprKind::Neg(Box::new(e))));
        }
        if self.eat_sym("!") {
            let e = self.unary()?;
            return Ok(self.mk(pos, ExprKind::Not(Box::new(e))));
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Expr> {
        let pos = self.pos();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(self.mk(pos, ExprKind::Int(n)))
            }
            Tok::Ident(k) if k == "true" || k == "false" => {
                self.bump();
                Ok(self.mk(pos, ExprKind::Bool(k == "true")))
            }
            Tok::Ident(k) if k == "if" => {
                self.bump();
                let c = self.expr()?;
                self.expect_kw("then")?;
                let t = self.expr()?;
                self.expect_kw("else")?;
                let e = self.expr()?;
                Ok(self.mk(pos, ExprKind::If(Box::new(c), Box::new(t), Box::new(e))))
            }
            Tok::Ident(k) if k == "match" => {
                self.bump();
                let scrut = self.expr()?;
                self.expect_sym("{")?;
                let mut arms = Vec::new();
                while !self.peek_sym("}") {
                    let apos = self.pos();
                    let pat = self.arm_pat()?;
                    self.expect_sym("=>")?;
                    let body = self.expr()?;
                    arms.push(Arm { pos: apos, pat, body });
                    while self.eat_sym(",") || self.eat_sym(";") {}
                }
                self.expect_sym("}")?;
                Ok(self.mk(pos, ExprKind::Match(Box::new(scrut), arms)))
            }
            Tok::Ident(k) if k == "tick" => {
                self.bump();
                self.expect_sym("(")?;
                let r = self.rat_lit()?;
                self.expect_sym(")")?;
                Ok(self.mk(pos, ExprKind::Tick(r)))
            }
            Tok::Ident(k) if k == "fail" => {
                self.bump();
                self.expect_sym("(")?;
                let msg = match self.bump().tok {
                    Tok::Str(s) => s,
                    _ => return Err(Error::at(pos, "`fail` takes a string")),
                };
                self.expect_sym(")")?;
                Ok(self.mk(pos, ExprKind::Fail(msg)))
            }
            Tok::Ident(_) => {
                let line = pos.line;
                let x = self.ident()?;
                // A call needs its `(` on the same line, so a match arm that
                // starts with a pair pattern is not read as a call.
                if self.peek_sym("(") && self.pos().line == line {
                    self.bump();
                    let mut args = Vec::new();
                    while !self.peek_sym(")") {
                        args.push(self.expr()?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                    self.expect_sym(")")?;
                    return Ok(self.mk(pos, ExprKind::Call(x, args)));
                }
                Ok(self.mk(pos, ExprKind::Var(x)))
            }
            Tok::Sym("(") => {
                self.bump();
                if self.eat_sym(")") {
                    return Ok(self.mk(pos, ExprKind::Unit));
                }
                let a = self.expr()?;
                if self.eat_sym(")") {
                    return Ok(a);
                }
                self.expect_sym(",")?;
                let b = self.expr()?;
                self.expect_sym(")")?;
                Ok(self.mk(pos, ExprKind::Pair(Box::new(a), Box::new(b))))
            }
            Tok::Sym("[") => {
                self.bump();
                let mut items = Vec::new();
                while !self.peek_sym("]") {
                    items.push(self.expr()?);
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym("]")?;
                if items.is_empty() { Ok(self.mk(pos, ExprKind::Nil)) } else { Ok(self.mk(pos, ExprKind::List(items))) }
            }
            Tok::Sym("{") => {
                self.bump();
                self.block()
            }
            _ => Err(self.unexpected("an expression")),
        }
    }

    /// The rest of a block after `{`. A block is a run of `let p = e` and
    /// expression statements, ending in an expression.
    fn block(&mut self) -> Result<Expr> {
        while self.eat_sym(";") {}
        if self.eat_kw("let") {
            let lpos = self.pos();
            let p = self.pat()?;
            self.expect_sym("=")?;
            let e = self.expr()?;
            while self.eat_sym(";") {}
            if self.peek_sym("}") {
                return Err(Error::at(lpos, "a block cannot end with `let`"));
            }
            let rest = self.block()?;
            return Ok(self.mk(lpos, ExprKind::Let(p, Box::new(e), Box::new(rest))));
        }
        let epos = self.pos();
        let e = self.expr()?;
        while self.eat_sym(";") {}
        if self.eat_sym("}") {
            return Ok(e);
        }
        let rest = self.block()?;
        Ok(self.mk(epos, ExprKind::Let(Pat::Wild, Box::new(e), Box::new(rest))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_function() {
        let p = parse(
            "fn rev(l: List<Int>, acc: List<Int>) -> List<Int> costs 1 + |l| =
               match l {
                 [] => acc
                 x :: xs => rev(xs, x :: acc)
               }",
        )
        .unwrap();
        assert_eq!(p.fns.len(), 1);
        assert_eq!(p.fns[0].params.len(), 2);
        assert_eq!(p.fns[0].budget.as_ref().unwrap().terms.len(), 2);
    }

    #[test]
    fn nested_list_types_close() {
        let p = parse("fn f(l: List<List<Int>>) -> Int = 0").unwrap();
        assert_eq!(p.fns[0].params[0].1, Type::List(Box::new(Type::List(Box::new(Type::Int)))));
    }

    #[test]
    fn reports_position() {
        let e = parse("fn f() -> Int = (1,").unwrap_err();
        assert!(e.pos.is_some());
    }
}

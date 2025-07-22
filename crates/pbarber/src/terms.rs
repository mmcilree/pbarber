use std::ops::{Add, AddAssign, Mul, Not};

type VarID = u32;
type FlagID = u32;
type Int = i64;

#[derive(Clone, Debug)]
pub struct SimpleVar {
    id: VarID,
}

#[derive(Clone, Debug)]
pub struct ViewVar {
    var: SimpleVar,
    first_multiply: Int,
    then_add: Int,
}

#[derive(Clone, Debug)]
pub enum Var {
    Simple(SimpleVar),
    View(ViewVar),
}

#[derive(Clone, Debug)]
pub enum AtomOp {
    GE,
    EQ,
    LT,
    NE,
}

#[derive(Clone, Debug)]
pub struct AtomLit {
    var: Var,
    op: AtomOp,
    val: Int,
}

#[derive(Clone, Debug)]
pub struct Flag {
    id: FlagID,
}

#[derive(Clone, Debug)]
pub enum FlagLit {
    Pos(Flag),
    Neg(Flag),
}

#[derive(Clone, Debug)]
pub enum Lit {
    Atom(AtomLit),
    Flag(FlagLit),
}

#[derive(Clone, Debug)]
pub enum Term {
    Var(Var),
    Lit(Lit),
    Const(i64),
}

#[derive(Clone, Debug)]
pub struct WeightedTerm {
    coeff: Int,
    term: Term,
}

#[derive(Clone, Debug)]
pub struct WeightedSum {
    terms: Vec<WeightedTerm>,
}

#[derive(Clone, Debug)]
pub struct LinearGeq {
    sum: WeightedSum,
    rhs: Int,
}

impl SimpleVar {
    fn with_id(id: VarID) -> SimpleVar {
        return SimpleVar { id };
    }

    fn add(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.clone(),
            first_multiply: 1,
            then_add: value,
        }
    }

    fn times(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.clone(),
            first_multiply: value,
            then_add: 0,
        }
    }
}

impl ViewVar {
    fn add(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.var.clone(),
            first_multiply: self.first_multiply,
            then_add: self.then_add + value,
        }
    }

    fn times(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.var.clone(),
            first_multiply: self.first_multiply * value,
            then_add: self.then_add * value,
        }
    }
}

impl Var {
    fn with_id(id: VarID) -> Var {
        Var::Simple(SimpleVar::with_id(id))
    }

    fn add(&self, value: Int) -> Var {
        match self {
            Var::Simple(sv) => Var::View(sv.add(value)),
            Var::View(vv) => Var::View(vv.add(value)),
        }
    }

    fn times(&self, value: Int) -> Var {
        match self {
            Var::Simple(sv) => Var::View(sv.times(value)),
            Var::View(vv) => Var::View(vv.times(value)),
        }
    }

    fn ge(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::GE,
            val: value,
        };
    }

    fn eq(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::EQ,
            val: value,
        };
    }

    fn ne(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::NE,
            val: value,
        };
    }

    fn lt(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::LT,
            val: value,
        };
    }
}

impl Flag {
    fn with_id(id: FlagID) -> Flag {
        return Flag { id };
    }
}

impl Not for FlagLit {
    type Output = Self;

    fn not(self) -> FlagLit {
        match self {
            FlagLit::Pos(flag) => FlagLit::Neg(flag.clone()),
            FlagLit::Neg(flag) => FlagLit::Pos(flag.clone()),
        }
    }
}

impl Not for AtomLit {
    type Output = Self;
    fn not(self) -> AtomLit {
        let neg_op = match self.op {
            AtomOp::EQ => AtomOp::NE,
            AtomOp::NE => AtomOp::EQ,
            AtomOp::GE => AtomOp::LT,
            AtomOp::LT => AtomOp::GE,
        };
        AtomLit {
            var: self.var.clone(),
            op: neg_op,
            val: self.val,
        }
    }
}

impl Not for Lit {
    type Output = Self;
    fn not(self) -> Lit {
        match self {
            Lit::Atom(atom_lit) => Lit::Atom(atom_lit.not()),
            Lit::Flag(flag_lit) => Lit::Flag(flag_lit.not()),
        }
    }
}

impl From<SimpleVar> for Term {
    fn from(v: SimpleVar) -> Self {
        Term::Var(Var::Simple(v.clone()))
    }
}

impl From<ViewVar> for Term {
    fn from(v: ViewVar) -> Self {
        Term::Var(Var::View(v.clone()))
    }
}

impl From<Var> for Term {
    fn from(v: Var) -> Self {
        match v {
            Var::Simple(sv) => sv.into(),
            Var::View(vv) => vv.into(),
        }
    }
}

impl From<AtomLit> for Term {
    fn from(a: AtomLit) -> Self {
        Term::Lit(Lit::Atom(a.clone()))
    }
}

impl From<FlagLit> for Term {
    fn from(f: FlagLit) -> Self {
        Term::Lit(Lit::Flag(f.clone()))
    }
}

impl From<Lit> for Term {
    fn from(v: Lit) -> Self {
        match v {
            Lit::Flag(f) => f.into(),
            Lit::Atom(a) => a.into(),
        }
    }
}

impl From<Int> for Term {
    fn from(c: Int) -> Self {
        Term::Const(c)
    }
}

impl WeightedSum {
    fn new() -> WeightedSum {
        WeightedSum {
            terms: Vec::<WeightedTerm>::new(),
        }
    }

    fn add_term(&mut self, wt: WeightedTerm) {
        self.terms.push(wt);
    }

    fn times(self, val: i64) -> WeightedSum {
        let new_terms = self
            .terms
            .into_iter()
            .map(|t| WeightedTerm {
                coeff: t.coeff * val,
                term: t.term,
            })
            .collect();
        WeightedSum { terms: new_terms }
    }

    fn ge(self, rhs: i64) -> LinearGeq {
        LinearGeq { sum: self, rhs }
    }

    fn gt(self, rhs: i64) -> LinearGeq {
        LinearGeq {
            sum: self,
            rhs: rhs + 1,
        }
    }

    fn le(self, rhs: i64) -> LinearGeq {
        LinearGeq {
            sum: self.times(-1),
            rhs: -rhs,
        }
    }

    fn lt(self, rhs: i64) -> LinearGeq {
        LinearGeq {
            sum: self.times(-1),
            rhs: -rhs - 1,
        }
    }
}

impl Add<WeightedTerm> for WeightedTerm {
    type Output = WeightedSum;

    fn add(self, wt: WeightedTerm) -> WeightedSum {
        WeightedSum::new() + self + wt
    }
}

impl Add<WeightedTerm> for WeightedSum {
    type Output = Self;

    fn add(mut self, wt: WeightedTerm) -> Self {
        self.add_term(wt);
        self
    }
}

impl Add<WeightedSum> for WeightedSum {
    type Output = Self;

    fn add(mut self, ws: WeightedSum) -> Self {
        for wt in ws.terms.iter() {
            self.add_term(wt.clone());
        }
        self
    }
}

impl AddAssign<WeightedTerm> for WeightedSum {
    fn add_assign(&mut self, wt: WeightedTerm) {
        self.add_term(wt);
    }
}

impl AddAssign<WeightedSum> for WeightedSum {
    fn add_assign(&mut self, ws: WeightedSum) {
        for wt in ws.terms.iter() {
            self.add_term(wt.clone());
        }
    }
}

impl Mul<Var> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: Var) -> Self::Output {
        match rhs {
            Var::Simple(sv) => self * sv,
            Var::View(vv) => self * vv,
        }
    }
}

impl Mul<SimpleVar> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: SimpleVar) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<ViewVar> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: ViewVar) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<Lit> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: Lit) -> Self::Output {
        match rhs {
            Lit::Flag(f) => self * f,
            Lit::Atom(a) => self * a,
        }
    }
}

impl Mul<AtomLit> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: AtomLit) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<FlagLit> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: FlagLit) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<Flag> for Int {
    type Output = WeightedTerm;

    fn mul(self, rhs: Flag) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: FlagLit::Pos(rhs).into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_linear_geq() {
        let x = Var::with_id(0);
        let y = Var::with_id(1);
        let z = x.times(-1).add(3);
        let f = Flag::with_id(0);

        let xge3 = x.ge(3);
        let term = 3 * x.ge(3);
        let mut sum = WeightedSum::new();

        sum += 3 * !x.ge(3);
        sum += 1 * f + 3 * z;
        let con = sum.ge(5);
        println!("{:?}", con)
    }
}

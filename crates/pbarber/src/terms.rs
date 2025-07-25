//! Module for creating terms, sums of terms and constraints on those terms, with
//! lots of syntactic sugar.
//!
//! Best understood by example:
//!
//! ```rust
//!     let x = Var::with_id(0);
//!     let y = Var::with_id(1);
//!     let z = x.times(-1).add(3);
//!     let f = Flag::with_id(0);
//!     let xge3 = x.ge(3);
//!     let term = 3 * x.ge(3);
//!     let mut sum = 2 * x.ge(4) + 1 * !y.eq(2);
//!     sum += 3 * !x.ge(3);
//!     let what = (1 * f + 3 * z);
//!     let con = sum.ge(5);
//!     println!("{:?}", con)
//! ```
use std::ops::{Add, AddAssign, Mul, Not};

use crate::statements::{Direction, Label, PolTerm, PolToken};

pub type VarID = usize;
pub type FlagID = u32;
pub type Int = i64;

/// A finite domain variable that would need to be encoded in the proof with a
/// bit-string.
///
/// NB: there is no distinction between original problemn variables and "proof-only"
/// auxiliary variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SimpleVar {
    id: VarID,
}

/// A view of a finite domain variable:
///
/// (V * first_multiply) + then_add
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ViewVar {
    var: SimpleVar,
    first_multiply: Int,
    then_add: Int,
}

/// A var with a constant value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstVar {
    value: Int,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Var {
    Simple(SimpleVar),
    View(ViewVar),
    Const(ConstVar),
}

/// Allowed variable condition operators: >=, ==, <, !=
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomOp {
    GE,
    EQ,
    LT,
    NE,
}

/// An "atomic constraint"/"CP literal" describing the relationship between a variable
/// and a value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AtomLit {
    var: Var,
    op: AtomOp,
    val: Int,
}

/// An identifier for a Boolean literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Flag {
    id: FlagID,
}

/// A Boolean literal not related to a variable condition.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FlagLit {
    Pos(Flag),
    Neg(Flag),
}

/// Boolean literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Lit {
    Atom(AtomLit),
    Flag(FlagLit),
}

/// Term for linear sums that can be transformed in into PB constraints.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LinearTerm {
    Var(Var),
    Lit(Lit),
    Const(i64),
}

/// Associates an arbitrary term with a coefficient.
#[derive(Clone, Debug)]
pub struct WeightedTerm<T> {
    pub coeff: Int,
    pub term: T,
}

/// Integer linear combination of arbitrary terms.
#[derive(Clone, Debug)]
pub struct WeightedSum<T: Clone> {
    pub terms: Vec<WeightedTerm<T>>,
}

pub type LinearSum = WeightedSum<LinearTerm>;
pub type PBSum = WeightedSum<Lit>;

/// A greater-than-or-equal constraint on a linear sum.
#[derive(Clone, Debug)]
pub struct SumGeq<T: Clone> {
    sum: WeightedSum<T>,
    rhs: Int,
}

pub type LinearGeq = SumGeq<LinearTerm>;
pub type PBConstraint = SumGeq<Lit>;

impl SimpleVar {
    pub fn with_id(id: VarID) -> SimpleVar {
        return SimpleVar { id };
    }

    /// Create a new view by adding a value.
    pub fn add(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.clone(),
            first_multiply: 1,
            then_add: value,
        }
    }

    /// Create a new view by multiplying by a value.
    pub fn times(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.clone(),
            first_multiply: value,
            then_add: 0,
        }
    }
}

impl ViewVar {
    /// Create a new view by adding a value.
    pub fn add(&self, value: i64) -> ViewVar {
        ViewVar {
            var: self.var.clone(),
            first_multiply: self.first_multiply,
            then_add: self.then_add + value,
        }
    }

    /// Create a new view by multiplying through by a value
    ///
    /// NB: (a*x + b).times(c) = a*c*x + b*c
    pub fn times(&self, value: Int) -> ViewVar {
        ViewVar {
            var: self.var.clone(),
            first_multiply: self.first_multiply * value,
            then_add: self.then_add * value,
        }
    }
}

impl ConstVar {
    /// Create a new constant variable by adding a value.
    pub fn add(&self, to_add: Int) -> ConstVar {
        ConstVar {
            value: self.value + to_add,
        }
    }

    /// Create a new constant variable by multiplying through by a value
    ///
    /// NB: (a*x + b).times(c) = a*c*x + b*c
    pub fn times(&self, to_mult: Int) -> ConstVar {
        ConstVar {
            value: self.value * to_mult,
        }
    }
}

/// Methods for constructing `View`s and `AtomLit`s from variables.
impl Var {
    pub fn with_id(id: VarID) -> Var {
        Var::Simple(SimpleVar::with_id(id))
    }

    pub fn add(&self, value: Int) -> Var {
        match self {
            Var::Simple(sv) => Var::View(sv.add(value)),
            Var::View(vv) => Var::View(vv.add(value)),
            Var::Const(cv) => Var::Const(cv.add(value)),
        }
    }

    pub fn times(&self, value: Int) -> Var {
        match self {
            Var::Simple(sv) => Var::View(sv.times(value)),
            Var::View(vv) => Var::View(vv.times(value)),
            Var::Const(cv) => Var::Const(cv.times(value)),
        }
    }

    pub fn ge(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::GE,
            val: value,
        };
    }

    pub fn eq(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::EQ,
            val: value,
        };
    }

    pub fn ne(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::NE,
            val: value,
        };
    }

    pub fn lt(&self, value: Int) -> AtomLit {
        return AtomLit {
            var: self.clone(),
            op: AtomOp::LT,
            val: value,
        };
    }
}

impl Flag {
    pub fn with_id(id: FlagID) -> Flag {
        return Flag { id };
    }
}

/// Logical negation of a `Flag`.
impl Not for FlagLit {
    type Output = Self;

    fn not(self) -> FlagLit {
        match self {
            FlagLit::Pos(flag) => FlagLit::Neg(flag.clone()),
            FlagLit::Neg(flag) => FlagLit::Pos(flag.clone()),
        }
    }
}

impl FlagLit {
    pub fn def_label(&self) -> Label {
        Label::LitDef(Lit::Flag(self.clone()), Direction::IMPLIES)
    }
}

/// Logical negation of an `AtomLit`.
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

impl AtomLit {
    pub fn def_label(&self) -> Label {
        Label::LitDef(Lit::Atom(self.clone()), Direction::IMPLIES)
    }
}

/// Logical negation of a literal.
impl Not for Lit {
    type Output = Self;
    fn not(self) -> Lit {
        match self {
            Lit::Atom(atom_lit) => Lit::Atom(atom_lit.not()),
            Lit::Flag(flag_lit) => Lit::Flag(flag_lit.not()),
        }
    }
}

impl PolTerm for Lit {}
impl Into<PolToken> for Lit {
    fn into(self) -> PolToken {
        PolToken::Lit(self)
    }
}

impl Lit {
    pub fn def_label(&self) -> Label {
        match self {
            Lit::Atom(atom_lit) => atom_lit.def_label(),
            Lit::Flag(flag_lit) => flag_lit.def_label(),
        }
    }
}

impl From<SimpleVar> for LinearTerm {
    fn from(v: SimpleVar) -> Self {
        LinearTerm::Var(Var::Simple(v.clone()))
    }
}

impl From<ViewVar> for LinearTerm {
    fn from(v: ViewVar) -> Self {
        LinearTerm::Var(Var::View(v.clone()))
    }
}

impl From<ConstVar> for LinearTerm {
    fn from(v: ConstVar) -> Self {
        LinearTerm::Var(Var::Const(v.clone()))
    }
}

impl From<Var> for LinearTerm {
    fn from(v: Var) -> Self {
        match v {
            Var::Simple(sv) => sv.into(),
            Var::View(vv) => vv.into(),
            Var::Const(cv) => cv.into(),
        }
    }
}

impl From<AtomLit> for LinearTerm {
    fn from(a: AtomLit) -> Self {
        LinearTerm::Lit(Lit::Atom(a.clone()))
    }
}

impl From<FlagLit> for LinearTerm {
    fn from(f: FlagLit) -> Self {
        LinearTerm::Lit(Lit::Flag(f.clone()))
    }
}

impl From<Lit> for LinearTerm {
    fn from(v: Lit) -> Self {
        match v {
            Lit::Flag(f) => f.into(),
            Lit::Atom(a) => a.into(),
        }
    }
}

impl From<Int> for LinearTerm {
    fn from(c: Int) -> Self {
        LinearTerm::Const(c)
    }
}

impl<T: Clone> WeightedSum<T> {
    pub fn new() -> WeightedSum<T> {
        WeightedSum {
            terms: Vec::<WeightedTerm<T>>::new(),
        }
    }

    /// Append a `WeightedTerm`.
    pub fn add_term(&mut self, wt: WeightedTerm<T>) {
        self.terms.push(wt);
    }

    /// Multiply all coefficients through by a constant.
    pub fn times(self, val: Int) -> WeightedSum<T> {
        let new_terms = self
            .terms
            .into_iter()
            .map(|t| WeightedTerm {
                coeff: t.coeff * val,
                term: t.term.clone(),
            })
            .collect();
        WeightedSum { terms: new_terms }
    }

    /// Construct a greater-equal constraint from the sum.
    pub fn ge(self, rhs: Int) -> SumGeq<T> {
        SumGeq { sum: self, rhs }
    }

    /// Construct a greater-equal constraint from the sum, adjusting for '>'.
    pub fn gt(self, rhs: Int) -> SumGeq<T> {
        SumGeq::<T> {
            sum: self,
            rhs: rhs + 1,
        }
    }

    /// Construct a greater-equal constraint from the sum, adjusting for '<='.
    pub fn le(self, rhs: Int) -> SumGeq<T> {
        SumGeq::<T> {
            sum: self.times(-1),
            rhs: -rhs,
        }
    }

    /// Construct a greater-equal constraint from the sum,, adjusting for '<'.
    pub fn lt(self, rhs: Int) -> SumGeq<T> {
        SumGeq::<T> {
            sum: self.times(-1),
            rhs: -rhs - 1,
        }
    }
}

/// Operator to add weighted term to sum.
///
/// Since `Lit`, `AtomLit` can all be cast to LinearTerm, allow adding to a
/// WeightedSum<LinearTerm> using `+` operator.
impl<T: Clone, L: Into<T>> Add<WeightedTerm<L>> for WeightedSum<T> {
    type Output = Self;

    fn add(mut self, wt: WeightedTerm<L>) -> Self {
        self.add_term(WeightedTerm {
            coeff: wt.coeff,
            term: wt.term.into(),
        });
        self
    }
}

/// Operator to construct a new weighted sum from two weighted terms.
///
/// Note this will always cast to `LinearTerm`s.
impl<L: Into<LinearTerm>, T: Into<LinearTerm>> Add<WeightedTerm<L>> for WeightedTerm<T> {
    type Output = WeightedSum<LinearTerm>;

    fn add(self, other: WeightedTerm<L>) -> WeightedSum<LinearTerm> {
        WeightedSum::<LinearTerm>::new()
            + WeightedTerm::<LinearTerm> {
                coeff: self.coeff,
                term: self.term.into(),
            }
            + WeightedTerm::<LinearTerm> {
                coeff: other.coeff,
                term: other.term.into(),
            }
    }
}

/// Operator to construct a weighted sum from two weighted sums on the same terms.
///
/// No casting will be performed.
impl<T: Clone> Add<WeightedSum<T>> for WeightedSum<T> {
    type Output = Self;

    fn add(mut self, ws: WeightedSum<T>) -> Self {
        for wt in ws.terms.iter() {
            self.add_term(wt.clone());
        }
        self
    }
}

/// Operator to add and assign weighted term to sum.
///
/// Since `Lit`, `AtomLit` can all be cast to LinearTerm, allow adding to a
/// WeightedSum<LinearTerm> using `+=` operator.
impl<T: Clone, L: Into<T>> AddAssign<WeightedTerm<L>> for WeightedSum<T> {
    fn add_assign(&mut self, wt: WeightedTerm<L>) {
        self.add_term(WeightedTerm {
            coeff: wt.coeff,
            term: wt.term.into(),
        });
    }
}

/// Operator to add and two weighted sums and assign to the first.
///
/// No casting will be performed.
impl<T: Clone> AddAssign<WeightedSum<T>> for WeightedSum<T> {
    fn add_assign(&mut self, ws: WeightedSum<T>) {
        for wt in ws.terms.iter() {
            self.add_term(wt.clone());
        }
    }
}

impl Mul<Var> for Int {
    type Output = WeightedTerm<LinearTerm>;

    fn mul(self, rhs: Var) -> Self::Output {
        match rhs {
            Var::Simple(sv) => self * sv,
            Var::View(vv) => self * vv,
            Var::Const(cv) => self * cv,
        }
    }
}

impl Mul<SimpleVar> for Int {
    type Output = WeightedTerm<LinearTerm>;

    fn mul(self, rhs: SimpleVar) -> Self::Output {
        WeightedTerm::<LinearTerm> {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<ViewVar> for Int {
    type Output = WeightedTerm<LinearTerm>;

    fn mul(self, rhs: ViewVar) -> Self::Output {
        WeightedTerm::<LinearTerm> {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<ConstVar> for Int {
    type Output = WeightedTerm<LinearTerm>;

    fn mul(self, rhs: ConstVar) -> Self::Output {
        WeightedTerm::<LinearTerm> {
            coeff: self,
            term: rhs.into(),
        }
    }
}

impl Mul<Lit> for Int {
    type Output = WeightedTerm<Lit>;

    fn mul(self, rhs: Lit) -> Self::Output {
        match rhs {
            Lit::Flag(f) => self * f,
            Lit::Atom(a) => self * a,
        }
    }
}

impl Mul<AtomLit> for Int {
    type Output = WeightedTerm<Lit>;

    fn mul(self, rhs: AtomLit) -> Self::Output {
        WeightedTerm::<Lit> {
            coeff: self,
            term: Lit::Atom(rhs),
        }
    }
}

impl Mul<FlagLit> for Int {
    type Output = WeightedTerm<Lit>;

    fn mul(self, rhs: FlagLit) -> Self::Output {
        WeightedTerm::<Lit> {
            coeff: self,
            term: Lit::Flag(rhs),
        }
    }
}

impl Mul<Flag> for Int {
    type Output = WeightedTerm<Lit>;

    fn mul(self, rhs: Flag) -> Self::Output {
        WeightedTerm {
            coeff: self,
            term: Lit::Flag(FlagLit::Pos(rhs)),
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_create_linear_geq() {
//         let x = Var::with_id(0);
//         let y = Var::with_id(1);
//         let z = x.times(-1).add(3);
//         let f = Flag::with_id(0);

//         let xge3 = x.ge(3);
//         let term = 3 * x.ge(3);
//         let mut sum = 2 * x.ge(4) + 1 * !y.eq(2);

//         sum += 3 * !x.ge(3);
//         let what = (1 * f + 3 * z);

//         let con = sum.ge(5);
//         println!("{:?}", con)
//     }
// }

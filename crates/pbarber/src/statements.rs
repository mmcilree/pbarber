//! Module to encapsulate statements to be written in the proof. This should hopefully
//! make it simpler to write redundance, pbc, ia rules without complicated string
//! formatting.
//!
//! [`ConstraintStatement`] represents a proof step that
//! explicitly derives a constraint using a VeriPB proof rule, and can be constructed
//! via `ConstraintStatement::new(rule, constraint)` or one of
//! the provided macros like [`rup!`] or [`ia!`]; and then added to with builder
//! functions like `with_antecedents()` `with_hints()`.
//!
//! Additionally it defines types and helpers for constructing cutting planes
//! steps [`PolStatement`], and for labeling, substitution,
//! and handling subproofs.
//!
//! # Example
//! ```rust
//! use crate::proof::{ConstraintStatement, ProofRule};
//!
//! let cs = ConstraintStatement::new(ProofRule::RUP, some_constraint)
//!     .with_label("my_label".into())
//!     .with_antecedents();
//! // Equivalent to
//! let cs = rup!("my_label".into(), some_constraint).with_antecedents();
//! ```
//!
//! # Macros
//! - [`rup!`] — for reverse unit propagation steps.
//! - [`ia!`] — for syntactic implication.
//! - [`a!`] — for assertions.
//! - [`pol!`] — for creating empty pol lines.

use std::ops::{Add, AddAssign, Div, DivAssign, Mul};

use crate::terms::{Int, LinearGeq, Lit, WeightedSum, WeightedTerm};

pub type ProofID = u32;

/// Direction of implication in the definition of a Literal
#[derive(Debug, Clone)]
pub enum Direction {
    IMPLIES,
    IMPLIEDBY,
}

/// Different types of labels for proof lines.
#[derive(Debug, Clone)]
pub enum Label {
    RawID(ProofID),
    Orig(String),
    LitDef(Lit, Direction),
    Enc(usize),
}

/// Allowed tokens in a pol statement.
#[derive(Debug, Clone)]
pub enum PolToken {
    Plus,
    Times,
    Divide,
    Saturate,
    Lit(Lit),
    Label(Label),
    Int(Int),
}

/// The subset of pol tokens that can be explicitly added to a pol statement using
/// operators should implement this trait.
pub trait PolTerm {}

/// Pol statement: sequence of operators and operands in reverse polish notation
/// with a label.
#[derive(Debug, Clone)]
pub struct PolStatement {
    label: Option<Label>,
    tokens: Vec<PolToken>,
}

/// The left-hand side of a substitution (for a redundance witness): i.e. a literal
/// or {0, 1}.
#[derive(Debug, Clone)]
pub enum SubstLHS {
    Const(bool),
    Lit(Lit),
}

/// Supported proof rules.
pub enum ProofRule {
    RUP,
    EA,
    IA,
    POL,
    RED,
    A,
    PBC,
}

/// A subproof is just a sequence of proof statements associated with a proof goal
/// string (not unique).
pub type Subproof = (Option<String>, Vec<ProofStatement>);

/// A constraint statement is a proof step that explicitly specifies a constraint
/// rup, red, ia, a, pbc etc.
///
/// NB: not all of the fields are valid for all the rules here: so it's possible
/// to log garbage (or we could implement fussy checking to stop e.g.
/// `rup!(constraint).with_subproofs()`)
pub struct ConstraintStatement {
    label: Option<Label>,
    rule: ProofRule,
    constraint: LinearGeq,
    antecedents: Option<Vec<Label>>,
    name: Option<String>,
    substitution: Option<Vec<(Lit, SubstLHS)>>,
    subproofs: Option<Vec<Subproof>>,
    hints: Option<String>,
}

/// The only non-constraint statement currently is pol. Could implement deletion
/// and order rules etc. here too if ever needed.
pub enum ProofStatement {
    ConstraintStatement,
    PolStatement,
}

impl From<&str> for Label {
    fn from(value: &str) -> Self {
        Label::Orig(value.to_owned())
    }
}

impl Mul<Label> for Int {
    type Output = WeightedTerm<Label>;

    fn mul(self, rhs: Label) -> WeightedTerm<Label> {
        return WeightedTerm::<Label> {
            coeff: self,
            term: rhs.clone(),
        };
    }
}

impl PolTerm for Label {}
impl Into<PolToken> for Label {
    fn into(self) -> PolToken {
        PolToken::Label(self)
    }
}

impl<P: Into<PolToken> + PolTerm> Add<P> for PolStatement {
    type Output = PolStatement;

    fn add(mut self, rhs: P) -> Self::Output {
        self.tokens.push(rhs.into().clone());
        if self.tokens.len() > 1 {
            self.tokens.push(PolToken::Plus);
        }
        self
    }
}

impl<P: Into<PolToken> + PolTerm> AddAssign<P> for PolStatement {
    fn add_assign(&mut self, rhs: P) {
        self.tokens.push(rhs.into().clone());
        if self.tokens.len() > 1 {
            self.tokens.push(PolToken::Plus);
        }
    }
}

impl<P: Into<PolToken> + PolTerm> Add<WeightedTerm<P>> for PolStatement {
    type Output = PolStatement;
    fn add(mut self, rhs: WeightedTerm<P>) -> Self::Output {
        self.tokens.push(rhs.term.into().clone());
        self.tokens.push(PolToken::Int(rhs.coeff.clone()));
        self.tokens.push(PolToken::Times);
        if self.tokens.len() > 3 {
            self.tokens.push(PolToken::Plus);
        }
        self
    }
}

impl<P: Into<PolToken> + PolTerm> AddAssign<WeightedTerm<P>> for PolStatement {
    fn add_assign(&mut self, rhs: WeightedTerm<P>) {
        self.tokens.push(rhs.term.into().clone());
        self.tokens.push(PolToken::Int(rhs.coeff.clone()));
        self.tokens.push(PolToken::Times);
        if self.tokens.len() > 3 {
            self.tokens.push(PolToken::Plus);
        }
    }
}

impl<P: Into<PolToken> + PolTerm + Clone> Add<WeightedSum<P>> for PolStatement {
    type Output = PolStatement;
    fn add(mut self, rhs: WeightedSum<P>) -> Self::Output {
        for t in rhs.terms {
            self = self + t;
        }
        self
    }
}

impl<P: Into<PolToken> + PolTerm + Clone> AddAssign<WeightedSum<P>> for PolStatement {
    fn add_assign(&mut self, rhs: WeightedSum<P>) {
        for t in rhs.terms {
            *self += t;
        }
    }
}

impl Div<Int> for PolStatement {
    type Output = PolStatement;

    fn div(mut self, rhs: Int) -> Self {
        self.tokens.push(PolToken::Int(rhs));
        self.tokens.push(PolToken::Divide);
        self
    }
}

impl DivAssign<Int> for PolStatement {
    fn div_assign(&mut self, rhs: Int) {
        self.tokens.push(PolToken::Int(rhs));
        self.tokens.push(PolToken::Divide);
    }
}

impl PolStatement {
    pub fn new() -> Self {
        PolStatement {
            label: None,
            tokens: vec![],
        }
    }

    pub fn with_label(label: Label) -> Self {
        PolStatement {
            label: Some(label),
            tokens: vec![],
        }
    }
    pub fn saturate(mut self) -> Self {
        self.tokens.push(PolToken::Saturate);
        self
    }
}

/// Builder pattern for `ConstraintStatement`s.
impl ConstraintStatement {
    pub fn new(rule: ProofRule, constraint: LinearGeq) -> Self {
        Self {
            label: None,
            rule,
            constraint,
            antecedents: None,
            name: None,
            substitution: None,
            subproofs: None,
            hints: None,
        }
    }

    pub fn with_label(mut self, label: Label) -> Self {
        self.label = Some(label);
        self
    }

    pub fn with_antecedents(mut self, antecedents: Vec<Label>) -> Self {
        self.antecedents = Some(antecedents);
        self
    }

    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    pub fn with_substitution(mut self, substitution: Vec<(Lit, SubstLHS)>) -> Self {
        self.substitution = Some(substitution);
        self
    }

    pub fn with_subproofs(mut self, subproofs: Vec<Subproof>) -> Self {
        self.subproofs = Some(subproofs);
        self
    }

    pub fn with_hints(mut self, hints: impl Into<String>) -> Self {
        self.hints = Some(hints.into());
        self
    }
}

#[macro_export]
macro_rules! rup {
    ($constraint:expr) => {
        ConstraintStatement::new(ProofRule::RUP, $constraint)
    };
}

#[macro_export]
macro_rules! ia {
    ($constraint:expr) => {
        ConstraintStatement::new(ProofRule::IA, $constraint)
    };
}

#[macro_export]
macro_rules! a {
    ($constraint:expr) => {
        ConstraintStatement::new(ProofRule::IA, $constraint)
    };
}

#[macro_export]
macro_rules! pol {
    () => {
        PolStatement::new()
    };
}

//! Module to keep all the horrible FlatZinc parsing relatively self contained.
//!
//! We're only supporting a subset of FlatZinc: simple variables and constraints (so no
//! set variables, floats, infinite domains etc.).
use std::{collections::BTreeMap, usize};

use crate::{
    PBarberError, Result,
    terms::{ConstVar, Int, Var},
    writer::VarTracker,
};
use flatzinc_serde::{
    Argument, Array as FZNArray, Constraint as FZNConstraint, Domain, FlatZinc,
    Literal as FZNLiteral, Variable,
};
use rangelist::IntervalIterator;
use ustr::Ustr;

pub struct ConstraintStore {
    constraints: Vec<FZNConstraint<Ustr>>,
    arrays: BTreeMap<Ustr, FZNArray<Ustr>>,
}

/// Parser for a single FlatZinc constraint: allows justifiers to require flatzinc
/// constraints to be in certain forms and get [`Var`]s or vectors or [`Var`]s.
pub struct ConstraintArgParser<'a> {
    constraint: &'a FZNConstraint<Ustr>,
    var_tracker: &'a mut VarTracker,
    arrays: &'a BTreeMap<Ustr, FZNArray<Ustr>>,
    current_idx: usize,
}

/// Helper function to get the bounds out of a FlatZinc Variable.
pub fn parse_fzn_bounds(fzn_var: &Variable<Ustr>) -> Result<(Int, Int)> {
    match fzn_var.ty {
        flatzinc_serde::Type::Bool => todo!(),
        flatzinc_serde::Type::Int => {
            let range_list = match &fzn_var.domain {
                Some(Domain::Int(rangelist)) => Ok(rangelist),
                Some(Domain::Float(_)) => Err(PBarberError::Unsupported("Float domains".into())),
                None => Err(PBarberError::Unsupported("Unconstrained domains".into())),
            }?;
            let mut intervals = range_list.intervals();

            let first = intervals
                .next()
                .ok_or_else(|| PBarberError::Unsupported("Unconstrained domains".into()))?;

            let min = *first.start();

            let max = intervals.last().map(|r| *r.end()).unwrap_or(*first.end());
            Ok((min, max))
        }
        flatzinc_serde::Type::Float => Err(PBarberError::Unsupported("Float FlatZinc vars".into())),
        flatzinc_serde::Type::IntSet => {
            Err(PBarberError::Unsupported("IntSet FlatZinc vars".into()))
        }
    }
}

impl<'a> ConstraintStore {
    /// Create temporary parser for the given constraint index, borrowing a
    /// var_tracker so it can turn FlatZinc identifiers into internal Vars.
    pub fn parser_for(
        &'a self,
        index: usize,
        var_tracker: &'a mut VarTracker,
    ) -> Result<ConstraintArgParser<'a>> {
        Ok(ConstraintArgParser {
            constraint: self.constraints.get(index).ok_or(PBarberError::Parse {
                expected: format!("constraint at index {index}"),
                found: format!("None"),
            })?,
            var_tracker: var_tracker,
            arrays: &self.arrays,
            current_idx: 0,
        })
    }

    pub fn from_fzn(fzn: FlatZinc<Ustr>) -> Self {
        Self {
            arrays: fzn.arrays,
            constraints: fzn.constraints,
        }
    }
}
impl<'a> ConstraintArgParser<'a> {
    /// Helper function to coerce a FlatZinc Literal to an internal [Var].
    fn extract_var(&self, fzn_lit: &FZNLiteral<Ustr>) -> Result<Var> {
        match fzn_lit {
            flatzinc_serde::Literal::Int(v) => Ok(Var::Const(ConstVar::from(*v))),
            flatzinc_serde::Literal::Bool(b) => Ok(Var::Const(ConstVar::from(*b))),
            flatzinc_serde::Literal::Identifier(name) => {
                // The var should always be in the var_tracker if it was correctly
                // initialised using from_fzn()
                let var = self
                    .var_tracker
                    .get_by_name(name)
                    .ok_or(PBarberError::Unexpected(format!(
                        "FlatZinc var name {name} not found in var_tracker"
                    )))?;
                Ok(var.clone())
            }
            _else => Err(PBarberError::Unsupported(format!(
                "FlatZinc Literal {fzn_lit:?}"
            ))),
        }
    }

    /// Helper function to coerce a FlatZinc Literal to an int.
    fn extract_int(&self, fzn_lit: &FZNLiteral<Ustr>) -> Result<Int> {
        match fzn_lit {
            FZNLiteral::Bool(b) => Ok(Int::from(*b)),
            FZNLiteral::Int(v) => Ok(Int::from(*v)),
            _ => Err(PBarberError::FlatZinc {
                expected: "Literal::Bool or Literal::Int".to_owned(),
                found: format!("{fzn_lit:?}"),
            }),
        }
    }

    /// Helper function to ensure an argument is an array.
    fn ensure_array(&self, arg: &'a Argument<Ustr>) -> Result<&Vec<FZNLiteral<Ustr>>> {
        match arg {
            Argument::Array(fzn_lit_vec) => Ok(fzn_lit_vec),
            Argument::Literal(FZNLiteral::Identifier(name)) => {
                // Look up in arrays if necessary
                let arr = self.arrays.get(name).ok_or(PBarberError::FlatZinc {
                    expected: "Argument::Array".to_owned(),
                    found: format!("{arg:?}"),
                })?;
                Ok(&arr.contents)
            }
            _ => Err(PBarberError::FlatZinc {
                expected: "Argument::Array".to_owned(),
                found: format!("{arg:?}"),
            }),
        }
    }

    /// Helper function to ensure an argument is an array.
    fn get_current_arg(&self) -> Result<&Argument<Ustr>> {
        self.constraint
            .args
            .get(self.current_idx)
            .ok_or(PBarberError::FlatZinc {
                expected: format!("Argument at index {}", self.current_idx),
                found: "None".to_owned(),
            })
    }

    /// Parse the next argument as a vector of Vars.
    pub fn parse_var_array(&mut self) -> Result<Vec<Var>> {
        let arg = self.get_current_arg()?;

        // Ensure Array
        let fzn_lit_vec = self.ensure_array(arg)?;

        // Extract the vars from the array, converting constants to ConstVar
        let vars = fzn_lit_vec
            .iter()
            .map(|fzn_lit| self.extract_var(fzn_lit))
            .collect::<Result<Vec<Var>>>()?;

        self.current_idx += 1;
        Ok(vars)
    }

    /// Parse the next argument as a single Var.
    pub fn parse_single_var(&mut self) -> Result<Var> {
        let arg = self.get_current_arg()?;

        // Ensure single fzn_lit
        let Argument::Literal(fzn_lit) = arg else {
            Err(PBarberError::FlatZinc {
                expected: "Argument::Literal".to_owned(),
                found: format!("{arg:?}"),
            })?
        };

        let var = self.extract_var(fzn_lit)?;
        self.current_idx += 1;
        Ok(var)
    }

    /// Parse the next argument as a single constant.
    pub fn parse_single_int(&mut self) -> Result<Int> {
        let arg = self.get_current_arg()?;

        // Ensure single fzn_lit
        let Argument::Literal(fzn_lit) = arg else {
            Err(PBarberError::FlatZinc {
                expected: "Array".to_owned(),
                found: format!("{arg:?}"),
            })?
        };

        // Ensure it is a constant value
        let val = self.extract_int(fzn_lit)?;

        self.current_idx += 1;
        Ok(val)
    }

    /// Parse the next argument as a vector of constants.
    pub fn parse_int_array(&mut self) -> Result<Vec<Int>> {
        let arg = self.get_current_arg()?;

        // Ensure Array
        let fzn_lit_vec = self.ensure_array(arg)?;

        // Extract the vars from the array, converting constants to ConstVar
        let vals = fzn_lit_vec
            .iter()
            .map(|fzn_lit| self.extract_int(fzn_lit))
            .collect::<Result<Vec<Int>>>()?;

        self.current_idx += 1;
        Ok(vals)
    }
}

//! Module to keep all the horrible FlatZinc parsing relatively self contained.
//!
//! We're only supporting a subset of FlatZinc: simple variables and constraints (so no
//! set variables, floats, infinite domains etc.).
use std::usize;

use crate::{
    PBarberError, Result,
    terms::{Int, Var},
    writer::VarTracker,
};
use flatzinc_serde::{Constraint as FZNConstraint, Domain, Variable};
use rangelist::IntervalIterator;
use ustr::Ustr;

pub struct ConstraintStore {
    constraints: Vec<FZNConstraint<Ustr>>,
}

pub struct ConstraintArgParser<'a> {
    constraint: FZNConstraint<Ustr>,
    var_names: &'a mut VarTracker,
}

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

impl ConstraintStore {
    pub fn parser_for(&self, index: usize, var_tracker: &mut VarTracker) -> ConstraintArgParser {
        // ConstraintArgParser {
        //     constraint: self.constraints.get(index),
        //     var_names: (),
        // }
        !todo!()
    }
}
impl<'a> ConstraintArgParser<'a> {
    pub fn parse_var_array() -> Vec<Var> {
        !todo!()
    }

    pub fn parse_single_var() -> Var {
        !todo!()
    }

    pub fn parse_int() -> Int {
        !todo!()
    }
}

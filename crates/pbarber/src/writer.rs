use crate::{
    PBarberError, Result,
    flatzinc::parse_fzn_bounds,
    terms::{Int, Lit, SimpleVar, Var, VarID},
};
use bimap::BiMap;
use flatzinc_serde::FlatZinc;
use rustc_hash::FxHashSet as HashSet; // Supposedly fast, might want to experiment.
use ustr::Ustr;

/// Store all the relevant data about variables in one place. Design decision was to
/// do this (as is often done in CP solvers) rather than keep all this info with each
/// Var struct. Hopefully it pays off efficiency-wise.
#[derive(Debug)]
pub struct VarTracker {
    next_var_id: VarID,
    var_names: BiMap<Var, Ustr>,
    bounds_defined: Vec<bool>,
    bounds: Vec<(Int, Int)>,
}

pub struct LitTracker {
    lit_defined: HashSet<Lit>,
}

pub struct ProofWriter {
    var_tracker: VarTracker,
    lit_tracker: LitTracker,
}

impl VarTracker {
    pub fn create_var(&mut self, name: Ustr, lower: Int, upper: Int) -> Result<Var> {
        let new_var = Var::with_id(self.next_var_id);
        self.var_names
            .insert_no_overwrite(new_var, name)
            .map_err(|(new_var, name)| {
                PBarberError::Unexpected(format!(
                    "{new_var:?} or {name} already exists in VarTracker map."
                ))
            })?;
        self.bounds.push((lower, upper));
        self.bounds_defined.push(false);
        self.next_var_id += 1;
        Ok(Var::Simple(SimpleVar::with_id(self.next_var_id - 1)))
    }

    pub fn from_fzn(fzn: &FlatZinc<Ustr>) -> Result<VarTracker> {
        let mut var_tracker = VarTracker {
            next_var_id: 0,
            var_names: BiMap::new(),
            bounds_defined: Vec::new(),
            bounds: Vec::new(),
        };

        // Attempt to create an internal variable for each FlatZinc variable.
        // This will fail on floats, infinite domains, duplicate names.
        fzn.variables
            .iter()
            .try_for_each(|(name, fzn_var)| -> Result<()> {
                let (lower, upper) = parse_fzn_bounds(&fzn_var)?;
                var_tracker.create_var(*name, lower, upper)?;
                Ok(())
            })?;

        Ok(var_tracker)
    }

    pub fn get_by_name(&self, name: &Ustr) -> Option<&Var> {
        self.var_names.get_by_right(name)
    }
}

impl ProofWriter {
    /// Borrow the internal var_tracker belonging to the ProofWriter.
    /// Use with care! (Particularly for those like me still getting used to the
    /// Rust borrow checker...)
    pub fn var_tracker_mut(&mut self) -> &mut VarTracker {
        &mut self.var_tracker
    }
}

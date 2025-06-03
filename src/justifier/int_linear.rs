use std::os::unix::process;

use flatzinc_serde::Argument;
use flatzinc_serde::Literal as FZNLiteral;
use pboxide_formula::prelude::DynPBConstraint;
use ustr::Ustr;

use crate::PBarberError;
use crate::cp_lit_map::CPVarType;
use crate::justifier::PolBuilder;

use super::JustifierActions;
use super::Justify;

#[derive(Debug)]
pub(crate) struct IntLinearJustifier {
    constraint_name: String,
    fzn_id: String,
    coeffs: Vec<i64>,
    vars: Vec<String>,
    rhs: i64,
    _reif: Option<String>,
    reif_implies_le: Option<String>,
    reif_implies_ge: Option<String>,
}

impl Justify for IntLinearJustifier {
    fn justify(
        &self,
        justifier: &mut dyn JustifierActions,
        constraint: Box<dyn pboxide_formula::prelude::DynPBConstraint + 'static>,
        id_str: &str,
    ) -> Result<(), crate::PBarberError> {
        let (_, neg_def_ids) = justifier.ensure_all_lits_defined(&constraint, true)?;

        if self.constraint_name != "int_lin_le" && self.constraint_name != "int_lin_eq" {
            return Err(PBarberError::JustificationError(format!(
                "{} not yet implemented",
                self.constraint_name
            )));
        }

        let enc_id = self.reif_implies_le.as_ref().unwrap();

        self.sub_lits_into_ineq(justifier, &neg_def_ids, &constraint, enc_id, 1)?;
        if self.constraint_name == "int_lin_eq" {
            let enc_id = self.reif_implies_ge.as_ref().unwrap();

            self.sub_lits_into_ineq(justifier, &neg_def_ids, &constraint, enc_id, -1)?;
        }
        justifier.write(
            format!(
                "{} rup {};",
                id_str,
                &constraint.to_pretty_string(&justifier.pb_var_names())
            )
            .as_str(),
        )?;
        Ok(())
    }
}

impl IntLinearJustifier {
    pub fn new(
        justifier: &mut dyn JustifierActions,
        antecedents_str: &str,
    ) -> Result<Self, PBarberError> {
        let mut split_antecedents = antecedents_str.trim().split(" ");

        let fzn_id = split_antecedents
            .next()
            .ok_or(PBarberError::JustificationError(
                "Missing antecedent for IntLinear".to_string(),
            ))?;

        let fzn_constraint = justifier.get_fzn_constraint(fzn_id)?;

        let (coeffs, vars_l, rhs, reif) = match fzn_constraint.id.as_str() {
            "int_lin_le" | "int_lin_eq" => (
                &fzn_constraint.args[0],
                &fzn_constraint.args[1],
                &fzn_constraint.args[2],
                None::<String>,
            ),
            id => {
                return Err(PBarberError::JustificationError(format!(
                    "Don't know how to encode constraint {id}"
                )));
            }
        };

        let coeffs_l = match coeffs {
            Argument::Array(coeffs) => coeffs.clone(),
            Argument::Literal(flatzinc_serde::Literal::Identifier(id)) => {
                let arr = justifier.get_fzn_array(&id)?;
                arr.contents.clone()
            }
            _ => {
                return Err(PBarberError::JustificationError(format!(
                    "IntLinear: coeff should be array, or array identifier but got {:?}",
                    coeffs
                )));
            }
        };

        let mut coeffs = Vec::<i64>::with_capacity(coeffs_l.len());
        for l in coeffs_l {
            if let FZNLiteral::Int(val) = l {
                coeffs.push(val);
            } else {
                return Err(PBarberError::JustificationError(format!(
                    "IntLinear: coeff should be integer but got {:?}",
                    l
                )));
            }
        }

        let Argument::Array(vars_l) = vars_l else {
            return Err(PBarberError::JustificationError(format!(
                "IntLinear: vars should be array but got {:?}",
                vars_l
            )));
        };

        let mut vars = Vec::<String>::with_capacity(vars_l.len());
        for l in vars_l {
            if let FZNLiteral::Identifier(id) = l {
                vars.push(id.to_string());
            } else {
                return Err(PBarberError::JustificationError(format!(
                    "IntLinear: coeff should be integer but got {:?}",
                    l
                )));
            }
        }

        let Argument::Literal(FZNLiteral::Int(rhs)) = rhs else {
            return Err(PBarberError::JustificationError(format!(
                "IntLinear: rhs should be Int but got {:?}",
                vars_l
            )));
        };

        let mut linear_justifier = Self {
            fzn_id: fzn_id.to_string(),
            constraint_name: fzn_constraint.id.to_string(),
            coeffs,
            vars,
            rhs: rhs.clone(),
            _reif: reif,
            reif_implies_le: None,
            reif_implies_ge: None,
        };
        linear_justifier.encode(justifier)?;
        Ok(linear_justifier)
    }

    fn encode(&mut self, justifier: &mut dyn JustifierActions) -> Result<(), PBarberError> {
        match self.constraint_name.as_str() {
            "int_lin_le" => {
                let mut le_id = String::from(&self.fzn_id);
                le_id.push_str("_le");
                self.encode_lin(justifier, "<=", le_id.as_str())?;
                self.reif_implies_le = Some(le_id);
            }
            "int_lin_eq" => {
                let mut le_id = String::from(&self.fzn_id);
                le_id.push_str("_le");
                self.encode_lin(justifier, "<=", le_id.as_str())?;
                self.reif_implies_le = Some(le_id);

                let mut ge_id = String::from(&self.fzn_id);
                ge_id.push_str("_ge");
                self.encode_lin(justifier, ">=", ge_id.as_str())?;
                self.reif_implies_ge = Some(ge_id);
            }
            id => {
                return Err(PBarberError::JustificationError(format!(
                    "Don't know how to encode constraint {id}"
                )));
            }
        }
        Ok(())
    }

    fn encode_lin(
        &mut self,
        justifier: &mut dyn JustifierActions,
        operator: &str,
        id: &str,
    ) -> Result<(), PBarberError> {
        let mut pb_line = String::from(id);
        pb_line.push_str(" a");
        for (coeff, var) in self.coeffs.iter().zip(self.vars.iter()) {
            pb_line.push(' ');
            pb_line.push_str(&justifier.cp_var_bits_str(&Ustr::from(var), *coeff)?);
        }
        pb_line.push(' ');
        pb_line.push_str(operator);
        pb_line.push(' ');
        pb_line.push_str(&self.rhs.to_string());
        pb_line.push_str(" :: ");
        pb_line.push_str(&self.constraint_name);
        pb_line.push(';');

        justifier.write(&pb_line)?;
        Ok(())
    }

    fn sub_lits_into_ineq(
        &self,
        justifier: &mut dyn JustifierActions,
        neg_def_ids: &Vec<String>,
        constraint: &Box<dyn DynPBConstraint>,
        enc_id: &String,
        mult: i64,
    ) -> Result<(), PBarberError> {
        let mut pol = PolBuilder::new();
        pol.add(enc_id);
        let mut reason_vars = Vec::<String>::new();
        for l in constraint.get_constraint_lits() {
            let cp_lit_data = &justifier.get_cp_lit_data(&l)?;
            reason_vars.push(cp_lit_data.get_name());
        }
        // dbg!(&self);
        // dbg!(&constraint.to_pretty_string(&justifier.pb_var_names()));
        // dbg!(&reason_vars);

        for (coeff, var) in self.coeffs.iter().zip(self.vars.iter()) {
            if let Some(i) = reason_vars.iter().position(|v| v == var) {
                if neg_def_ids.get(i).unwrap() != "" {
                    pol.add_weighted(neg_def_ids.get(i).unwrap(), coeff.abs() as u32);
                }
            } else {
                let (lb, ub) = justifier.ensure_bounds_defined(&Ustr::from(var))?;
                if *coeff * mult > 0 {
                    pol.add_weighted(&lb, coeff.abs() as u32);
                } else if *coeff * mult < 0 {
                    pol.add_weighted(&ub, coeff.abs() as u32);
                }
            }
        }
        //std::process::exit(0);
        justifier.write(pol.done())?;
        Ok(())
    }
}

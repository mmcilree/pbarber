use crate::{
    PBarberError,
    justifier::{JustifierActions, Justify, PolBuilder, trim_sc},
};

pub(crate) struct IntVarDefJustifier {}

impl Justify for IntVarDefJustifier {
    fn justify(
        &self,
        justifier: &mut dyn JustifierActions,
        constraint: Box<dyn pboxide_formula::prelude::DynPBConstraint + 'static>,
        id_str: &str,
    ) -> Result<(), crate::PBarberError> {
        let (_, neg_def_ids) = justifier.ensure_all_lits_defined(&constraint, true)?;

        if neg_def_ids.len() > 2 {
            return Err(PBarberError::JustificationError(
                "IntVarDef with more than 2 lits".to_string(),
            ));
        }

        justifier.write(PolBuilder::new().add_all(&neg_def_ids).done())?;

        let mut imp_line = String::new();
        imp_line.push_str(id_str);
        imp_line.push_str(" ia ");
        imp_line.push_str(trim_sc(
            constraint
                .to_pretty_string(justifier.pb_var_names())
                .as_str(),
        ));
        imp_line.push_str(" : -1;");
        justifier.write(imp_line.as_str())?;
        Ok(())
    }
}

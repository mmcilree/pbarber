use crate::{
    ALLOWED_RULES, FORWARD_LIT_DEF_PREFIX, JustifierConfig, PBarberError, ProofFileStats,
    ProofProcessor, REVERSE_LIT_DEF_PREFIX,
    cp_lit_map::{CPLitData, CPLitMap, CPOperator},
};
use flatzinc_serde::{Domain, FlatZinc, RangeList};
use logos::Logos;
use pboxide_formula::{
    lit::Lit,
    prelude::{DynPBConstraint, VarNameManager},
};
use pboxide_parser::{opb_parser::parse_single_constraint, opb_token::OPBToken};
use rangelist::IntervalIterator;
use rev_buf_reader::RevBufReader;
use std::{
    collections::{HashMap, HashSet},
    fs::OpenOptions,
    io::{self, BufRead, BufReader, Read, Seek, Write},
};
use ustr::Ustr;

pub struct Justifier<W> {
    lines: Box<dyn Iterator<Item = io::Result<String>>>,
    out: W,
    config: JustifierConfig,
    input_stats: ProofFileStats,
    output_stats: ProofFileStats,
    lines_to_justify: HashMap<String, String>,
    var_names: VarNameManager,
    defined_lits: HashSet<Lit>,
    fzn: FlatZinc<Ustr>,
    cp_lit_map: CPLitMap,
    cp_var_bits: HashMap<String, String>,
}

impl<W: Write> ProofProcessor<W> for Justifier<W> {
    fn lines_next(&mut self) -> Option<Result<String, io::Error>> {
        self.lines.next()
    }

    fn has_stats(&self) -> bool {
        self.config.justifier_stats
    }

    fn input_stats_mut(&mut self) -> &mut ProofFileStats {
        &mut self.input_stats
    }

    fn output_stats_mut(&mut self) -> &mut ProofFileStats {
        &mut self.output_stats
    }

    fn out_mut(&mut self) -> &mut W {
        &mut self.out
    }
}

impl<W: Write> Justifier<W> {
    pub fn new<R: Read + Seek + 'static>(input: R, out: W) -> Self {
        Self::with_config(input, out, JustifierConfig::default())
    }

    pub fn with_config<R: Read + Seek + 'static>(
        input: R,
        out: W,
        config: JustifierConfig,
    ) -> Self {
        // Read file in reverse by default, but read forwards if the option is enabled
        let lines: Box<dyn Iterator<Item = io::Result<String>>> = if config.read_forwards {
            Box::new(BufReader::new(input).lines())
        } else {
            Box::new(RevBufReader::new(input).lines())
        };

        let fzn_file = OpenOptions::new()
            .read(true)
            .open(&config.fzn_path)
            .expect("Failed to open fzn file for justifier.");

        let lits_file = OpenOptions::new()
            .read(true)
            .open(&config.lits_path)
            .expect("Failed to open lits file for justifier.");

        let fzn: FlatZinc<Ustr> =
            serde_json::from_reader(fzn_file).expect("Unable to parse fzn input.");
        Self {
            lines,
            out,
            config,
            input_stats: ProofFileStats::default(),
            output_stats: ProofFileStats::default(),
            lines_to_justify: HashMap::<String, String>::new(),
            var_names: VarNameManager::default(),
            defined_lits: HashSet::<Lit>::new(),
            cp_lit_map: CPLitMap::from_reader(lits_file),
            cp_var_bits: HashMap::<String, String>::new(),
            fzn,
        }
    }

    pub fn style(&mut self) -> Result<Option<(ProofFileStats, ProofFileStats)>, PBarberError> {
        while let Some(current_line) = self.next_line() {
            let current_line = current_line.unwrap();
            if current_line.starts_with("@") {
                let mut split_line = current_line.split(" ");
                let id = split_line.next().unwrap();
                let rule = split_line.next().unwrap();
                assert!(ALLOWED_RULES.contains(&rule));
                if rule == "pol" || rule == "p" {
                    for term in split_line {
                        if term == "+" || term == "s" || term == ";" {
                            continue;
                        } else {
                            self.assert_starts_with(&term.to_string(), "@")?;
                            // If possible justify an assertion right before the first time
                            // it is used.
                            if let Some(line_to_justify) = self.lines_to_justify.remove(term) {
                                self.justify(&line_to_justify)?;
                                //self.write_line(&line_to_justify)?;
                            }
                        }
                    }
                    self.write_line(&current_line)?;
                } else if rule == "a" {
                    if self.lines_to_justify.len() < self.config.max_line_cache {
                        self.lines_to_justify.insert(id.to_string(), current_line);
                    } else {
                        // Can't cache so have to justify it right now
                        self.justify(&current_line)?;
                        //self.write_line(&current_line)?;
                    }
                }
            } else {
                // Not a labelled line, ignore :-)
                self.write_line(&current_line)?;
            }
        }
        if self.config.justifier_stats {
            Ok(Some((self.input_stats.clone(), self.output_stats.clone())))
        } else {
            Ok(None)
        }
    }

    fn justify(&mut self, current_line: &str) -> Result<(), PBarberError> {
        let mut split_line = current_line.split(":");
        let before_colon = split_line.next().unwrap();
        let mut split_before_colon = before_colon.splitn(2, " a ");
        let id = split_before_colon.next().unwrap();
        let constraint_str = split_before_colon.next().unwrap();
        let constraint = self.parse_constraint(constraint_str, id);
        let antecedents_str = split_line.next().unwrap();
        let opt_name = split_line.next();
        let _opt_hints = split_line.next();

        if let None = opt_name {
            self.write_line(current_line)?;
            return Ok(());
        }
        let name = opt_name.unwrap();
        let name = Self::trim_sc(name.trim());
        let justify_result = match name {
            "IntVarDef" => {
                let mut commented_assertion = "% (original assertion)".to_string();
                commented_assertion.push_str(current_line);
                self.write_line(&commented_assertion)?;
                self.justify_int_var_def(constraint, id, antecedents_str)
            }
            _ => {
                if let Err(PBarberError::JustificationError(msg)) =
                    self.ensure_all_defined(&constraint)
                {
                    self.write_line(format!("% {msg}").as_str())?;
                }
                self.cant_justify(constraint, id, name)
            }
        };
        match justify_result {
            Err(PBarberError::JustificationError(msg)) => {
                self.failed_to_justify(current_line, msg.as_str())
            }
            _ => justify_result,
        }
    }

    fn ensure_all_defined(
        &mut self,
        constraint: &Box<dyn DynPBConstraint + 'static>,
    ) -> Result<(), PBarberError> {
        let lits = constraint.get_constraint_lits();
        for lit in lits {
            self.ensure_defined(lit)?;
            let mut neg_lit = lit.clone();
            neg_lit.negate();
            self.ensure_defined(&neg_lit)?;
        }
        Ok(())
    }

    fn justify_int_var_def(
        &mut self,
        constraint: Box<dyn DynPBConstraint + 'static>,
        id_str: &str,
        _antecdents_str: &str,
    ) -> Result<(), PBarberError> {
        let lits = constraint.get_constraint_lits();
        let mut ids_to_add = Vec::<String>::new();
        let mut count = 1;
        for lit in lits {
            if count > 2 {
                return Err(PBarberError::JustificationError(
                    "IntVarDef with more than 2 lits".to_string(),
                ));
            }
            let mut neg_lit = lit.clone();
            neg_lit.negate();
            let id = self.ensure_defined(&neg_lit)?;
            let id = id.ok_or(PBarberError::JustificationError(format!(
                "Couldn't find definition for literal {}",
                &neg_lit
            )))?;
            ids_to_add.push(id);
            count += 1;
        }

        self.write_line(Self::pol_sum_ids(&ids_to_add).as_str())?;

        let mut imp_line = String::new();
        imp_line.push_str(id_str);
        imp_line.push_str(" ia ");
        imp_line.push_str(Self::trim_sc(
            constraint.to_pretty_string(&self.var_names).as_str(),
        ));
        imp_line.push_str(" : -1;");
        self.write_line(imp_line.as_str())?;
        Ok(())
    }

    fn ensure_defined(&mut self, lit: &Lit) -> Result<Option<String>, PBarberError> {
        let def_id = self.definition_id(lit);
        if self.is_defined(lit) {
            return Ok(Some(def_id));
        }
        let pb_lit_name = self.var_names.get_name(lit.get_var()).to_string().clone();
        let cp_lit_data =
            self.cp_lit_map
                .get(&pb_lit_name)
                .ok_or(PBarberError::JustificationError(format!(
                    "Couldn't find CP definition for literal {}",
                    self.var_names.get_name(lit.get_var())
                )))?;

        let (name, tilde_if_neg, operator, value) = if let CPLitData::Condition {
            name,
            operator,
            value,
            ..
        } = cp_lit_data
        {
            let (operator, tilde_if_neg) = if lit.is_negated() {
                (operator.negated(), "~")
            } else {
                (operator, "")
            };
            (name, tilde_if_neg, operator, value)
        } else {
            return Ok((None));
            // return Err(PBarberError::JustificationError(format!(
            //     "Expected literal {} to be a condition.",
            //     &self.var_names.get_name(lit.get_var())
            // )));
        };

        let bits = self.cp_var_bits(&name, false)?;
        self.write_line(
            format!(
                "{} red {}{} ==> {} {} {} : {} -> {} ;",
                def_id,
                tilde_if_neg,
                pb_lit_name,
                bits,
                match operator {
                    CPOperator::GreaterEqual => ">=",
                    CPOperator::Less => "<=",
                    _ =>
                        return Err(PBarberError::JustificationError(
                            "Can't handle equality literals yet.".to_string()
                        )),
                },
                value.parse::<i32>().unwrap()
                    + match operator {
                        CPOperator::GreaterEqual => 0,
                        CPOperator::Less => -1,
                        _ =>
                            return Err(PBarberError::JustificationError(
                                "Can't handle equality literals yet.".to_string()
                            )),
                    },
                pb_lit_name,
                if lit.is_negated() { 1 } else { 0 }
            )
            .as_str(),
        )?;

        self.set_defined(lit);
        return Ok(Some(def_id));
    }

    fn cant_justify(
        &mut self,
        constraint: Box<dyn DynPBConstraint + 'static>,
        id_str: &str,
        name_str: &str,
    ) -> Result<(), PBarberError> {
        self.write_line("% PBarber Justifier didn't know how to justify the following:")?;
        let mut a_line = String::new();
        a_line.push_str(id_str);
        a_line.push_str(" a ");
        a_line.push_str(Self::trim_sc(
            constraint.to_pretty_string(&self.var_names).as_str(),
        ));
        a_line.push_str(" :: ");
        a_line.push_str(name_str);
        a_line.push_str(";");
        self.write_line(a_line.as_str())?;
        Ok(())
    }

    fn failed_to_justify(&mut self, line_str: &str, msg: &str) -> Result<(), PBarberError> {
        self.write_line(
            format!("% PBarber Justifier failed to justify the following: (error msg: {msg}")
                .as_str(),
        )?;
        self.write_line(line_str)?;
        Ok(())
    }

    fn parse_constraint(
        &mut self,
        constraint_str: &str,
        id_str: &str,
    ) -> Box<dyn DynPBConstraint + 'static> {
        // Annoying hack to parse constraint for now
        // -- TODO: see if we can get better parsing tools from PBOxide
        let mut constraint_str = String::from(constraint_str);
        constraint_str.push(';');
        let constraint_str = constraint_str.as_str();
        let mut lex = OPBToken::lexer(constraint_str);
        let (constraint, _opt_leq) = parse_single_constraint(&mut lex, &mut self.var_names)
            .expect(format!("Constraint with id {id_str} was not parsed correctly.").as_str());
        // ---
        constraint
    }

    fn is_defined(&self, lit: &Lit) -> bool {
        self.defined_lits.contains(lit)
    }

    fn set_defined(&mut self, lit: &Lit) {
        self.defined_lits.insert(lit.clone());
    }

    fn definition_id(&self, lit: &Lit) -> String {
        let mut id = "@".to_string();
        if lit.is_negated() {
            id.push_str(REVERSE_LIT_DEF_PREFIX);
        } else {
            id.push_str(FORWARD_LIT_DEF_PREFIX);
        }
        id.push_str(self.var_names.get_name(lit.get_var()));
        id
    }

    fn cp_var_bits(&mut self, cp_var: &String, minus: bool) -> Result<String, PBarberError> {
        if let Some(bits) = self.cp_var_bits.get(cp_var) {
            Ok(bits.clone())
        } else {
            let var_fzn = self.fzn.variables.get(&Ustr::from(cp_var)).ok_or(
                PBarberError::JustificationError(format!(
                    "Couldn't find {} in the fzn file",
                    cp_var.as_str()
                )),
            )?;

            let domain = var_fzn
                .domain
                .as_ref()
                .ok_or(PBarberError::JustificationError(format!(
                    "No domain found for {} in the fzn file (unsupported).",
                    cp_var.as_str()
                )))?;

            let int_domain = match domain {
                Domain::Int(r) => r,
                _ => {
                    return Err(PBarberError::JustificationError(format!(
                        "Expected Int domain for {} but found Float (unsupported).",
                        cp_var.as_str()
                    )));
                }
            };

            let (min, max) =
                min_max(int_domain).ok_or(PBarberError::JustificationError(format!(
                    "Couldn't get the min and max domain values for {}",
                    cp_var.as_str()
                )))?;

            let num_bits = if min >= 0 {
                let target = (max as u64) + 1;
                (64 - target.leading_zeros()) as u32
            } else {
                let bound = (max.abs().max(min.abs()) + 1) as u64;
                (64 - bound.leading_zeros()) as u32
            };

            let mut bits = String::new();
            if min >= 0 {
                if !minus {
                    bits.push('-');
                }
                bits.push_str(&u32::pow(2, num_bits + 1).to_string());
                bits.push(' ');
                bits.push_str(cp_var);
                bits.push_str("_b");
                bits.push_str(&(num_bits + 1).to_string());
            }

            for i in (0..num_bits).rev() {
                bits.push(' ');
                if minus {
                    bits.push('-');
                }
                bits.push_str(&u32::pow(2, i).to_string());
                bits.push(' ');
                bits.push_str(cp_var);
                bits.push_str("_b");
                bits.push_str(&(i).to_string());
            }

            let bits = bits.trim().to_string();
            self.cp_var_bits.insert(cp_var.clone(), bits.clone());
            Ok(bits.clone())
        }
    }

    fn pol_sum_ids(ids: &Vec<String>) -> String {
        let mut p_line = "pol ".to_string();
        let mut first = true;
        for id in ids {
            p_line.push_str(id.as_str());

            if first {
                p_line.push_str(" ");
                first = false;
            } else {
                p_line.push_str(" + ");
            }
        }
        p_line.push(';');
        p_line
    }
    fn trim_sc(to_trim: &str) -> &str {
        to_trim.trim_end_matches(';')
    }
}

fn min_max<T: Copy + Ord>(range_list: &RangeList<T>) -> Option<(T, T)> {
    let mut intervals = range_list.intervals();

    let first = intervals.next()?;
    let min = *first.start();

    let max = intervals.last().map(|r| *r.end()).unwrap_or(*first.end());

    Some((min, max))
}

use crate::{
    ALLOWED_RULES, FORWARD_LIT_DEF_PREFIX, JustifierConfig, PBarberError, ProofFileStats,
    ProofReader, REVERSE_LIT_DEF_PREFIX,
    cp_lit_map::{CPLitData, CPLitMap, CPOperator},
};
use flatzinc_serde::{Domain, FlatZinc, RangeList};
use int_linear::IntLinearJustifier;
use int_var_def::IntVarDefJustifier;
use logos::Logos;
use pboxide_formula::{
    lit::Lit as PBLiteral,
    prelude::{DynPBConstraint, ToPrettyString, VarNameManager as PBVarNameManager},
};
use pboxide_parser::{opb_parser::parse_single_constraint, opb_token::OPBToken};
use rangelist::IntervalIterator;
use rev_buf_reader::RevBufReader;
use std::{
    collections::{HashMap, HashSet},
    fs::OpenOptions,
    io::{self, BufRead, BufReader, Read, Seek, Write},
    rc::Rc,
};
use ustr::Ustr;

pub(crate) mod int_linear;
pub(crate) mod int_var_def;

pub(crate) trait JustifierActions {
    fn ensure_lit_defined(&mut self, lit: &PBLiteral) -> Result<String, PBarberError>;
    fn ensure_all_lits_defined(
        &mut self,
        constraint: &Box<dyn DynPBConstraint + 'static>,
        strict: bool,
    ) -> Result<(Vec<String>, Vec<String>), PBarberError>;

    fn ensure_bounds_defined(&mut self, cp_var_id: &Ustr)
    -> Result<(String, String), PBarberError>;
    fn get_min_max_for_var(&mut self, cp_var_id: &Ustr) -> Result<(i64, i64), PBarberError>;
    fn cp_var_bits_str(
        &mut self,
        cp_var_id: &Ustr,
        multiplier: i64,
    ) -> Result<String, PBarberError>;
    fn pb_var_names(&self) -> &PBVarNameManager;
    fn write(&mut self, content: &str) -> Result<(), PBarberError>;
    fn get_fzn_constraint(
        &self,
        fzn_id: &str,
    ) -> Result<&flatzinc_serde::Constraint<Ustr>, PBarberError>;
    fn get_fzn_array(&self, fzn_id: &Ustr) -> Result<&flatzinc_serde::Array<Ustr>, PBarberError>;
    fn get_fzn_variable(
        &self,
        fzn_id: &Ustr,
    ) -> Result<&flatzinc_serde::Variable<Ustr>, PBarberError>;
    fn get_cp_lit_data(&self, lit: &PBLiteral) -> Result<CPLitData, PBarberError>;
}

pub(crate) trait Justify {
    fn justify(
        &self,
        var_manager: &mut dyn JustifierActions,
        constraint: Box<dyn DynPBConstraint + 'static>,
        id_str: &str,
    ) -> Result<(), PBarberError>;
}

pub struct Justifier<W> {
    lines: Box<dyn Iterator<Item = io::Result<String>>>,
    out: W,
    config: JustifierConfig,
    input_stats: ProofFileStats,
    output_stats: ProofFileStats,
    lines_to_justify: HashMap<String, String>,
    justifiers: HashMap<String, Rc<dyn Justify>>,

    pb_var_names: PBVarNameManager,
    defined_lits: HashSet<PBLiteral>,
    defined_bounds: HashSet<String>,
    fzn: FlatZinc<Ustr>,
    cp_lit_map: CPLitMap,
}

pub struct PolBuilder {
    pol_line: String,
    empty: bool,
}

impl PolBuilder {}

impl<W: Write> ProofReader<W> for Justifier<W> {
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
            justifiers: HashMap::<String, Rc<dyn Justify>>::new(),
            pb_var_names: PBVarNameManager::default(),
            defined_lits: HashSet::<PBLiteral>::new(),
            defined_bounds: HashSet::<String>::new(),
            cp_lit_map: CPLitMap::from_reader(lits_file),
            fzn,
            // fzn_encoded: HashMap::<String, Vec<String>>::new(),
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
        let (id, constraint_str, constraint, antecedents_str, opt_name) =
            self.parse_assertion_line(current_line);

        let Some(name) = opt_name else {
            self.write_line(current_line)?;
            return Ok(());
        };
        let name = trim_sc(name.trim());
        let install_result = if let Some(justifier) = self.justifiers.get(antecedents_str) {
            Ok(Rc::clone(justifier))
        } else {
            self.install_justifier(name, antecedents_str)
        };

        match install_result {
            Err(PBarberError::JustificationError(msg)) => {
                let constraint = self.parse_constraint(constraint_str, id);
                self.ensure_all_lits_defined(&constraint, false)?;
                self.failed_to_justify(constraint, id, name, msg.as_str())
            }
            Err(e) => Err(e),
            Ok(justifier) => match justifier.justify(self, constraint, id) {
                Err(PBarberError::JustificationError(msg)) => {
                    let constraint = self.parse_constraint(constraint_str, id);
                    self.failed_to_justify(constraint, id, name, msg.as_str())
                }
                res => res,
            },
        }
    }

    fn parse_assertion_line<'a>(
        &mut self,
        current_line: &'a str,
    ) -> (
        &'a str,
        &'a str,
        Box<dyn DynPBConstraint + 'static>,
        &'a str,
        Option<&'a str>,
    ) {
        let mut split_line = current_line.split(":");
        let before_colon = split_line.next().unwrap();
        let mut split_before_colon = before_colon.splitn(2, " a ");
        let id = split_before_colon.next().unwrap();
        let constraint_str = split_before_colon.next().unwrap();
        let constraint = self.parse_constraint(constraint_str, id);
        let antecedents_str = split_line.next().unwrap();
        let opt_name = split_line.next();
        let _opt_hints = split_line.next();
        (id, constraint_str, constraint, antecedents_str, opt_name)
    }

    fn failed_to_justify(
        &mut self,
        constraint: Box<dyn DynPBConstraint + 'static>,
        id_str: &str,
        name_str: &str,
        msg: &str,
    ) -> Result<(), PBarberError> {
        self.write_line(
            format!("% PBarber Justifier failed to justify the following: (error msg: {msg})")
                .as_str(),
        )?;
        self.write_bare_assertion(constraint, id_str, name_str)?;
        Ok(())
    }

    fn write_bare_assertion(
        &mut self,
        constraint: Box<dyn DynPBConstraint + 'static>,
        id_str: &str,
        name_str: &str,
    ) -> Result<(), PBarberError> {
        let mut a_line = String::new();
        a_line.push_str(id_str);
        a_line.push_str(" a ");
        a_line.push_str(trim_sc(
            constraint.to_pretty_string(&self.pb_var_names).as_str(),
        ));
        a_line.push_str(" :: ");
        a_line.push_str(name_str);
        a_line.push_str(";");
        self.write_line(a_line.as_str())?;
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
        let (constraint, _opt_leq) = parse_single_constraint(&mut lex, &mut self.pb_var_names)
            .expect(format!("Constraint with id {id_str} was not parsed correctly.").as_str());
        // ---
        constraint
    }

    fn is_defined(&self, lit: &PBLiteral) -> bool {
        self.defined_lits.contains(lit)
    }

    fn set_defined(&mut self, lit: &PBLiteral) {
        self.defined_lits.insert(lit.clone());
    }

    fn definition_id(&self, lit: &PBLiteral) -> String {
        let mut id = "@".to_string();
        if lit.is_negated() {
            id.push_str(REVERSE_LIT_DEF_PREFIX);
        } else {
            id.push_str(FORWARD_LIT_DEF_PREFIX);
        }
        id.push_str(self.pb_var_names.get_name(lit.get_var()));
        id
    }

    // fn cp_var_bits_eq(&mut self, cp_var: &str, val: i64) -> Result<String, PBarberError> {
    //     let (min, max) = self.get_min_max_for_var(cp_var)?;
    //     if val < min || val > max {
    //         return Err(PBarberError::JustificationError(format!(
    //             "Val {} not in range for {}",
    //             val, cp_var
    //         )));
    //     }
    //     let mut num_bits = num_bits_for_range(min, max);
    //     let mut val = val;
    //     let mut bits = String::new();
    //     let bin_str = if min <= 0 {
    //         format!(
    //             "{:0width$b}",
    //             (val as i128) & ((1_i128 << num_bits) - 1),
    //             width = num_bits as usize
    //         )
    //     } else {
    //         format!("{:0width$b}", (val as u64), width = num_bits as usize)
    //     };

    //     if min >= 0 {
    //         bits.push(' ');
    //         bits.push_str(cp_var);
    //         bits.push_str("_b");
    //         bits.push_str(&(num_bits + 1).to_string());
    //         num_bits -= 1;
    //     };
    //     Ok(bits)
    // }

    fn install_justifier(
        &mut self,
        name: &str,
        antecedents_str: &str,
    ) -> Result<Rc<dyn Justify>, PBarberError> {
        let cache = false;
        let justifier: Rc<dyn Justify> = match name {
            "IntVarDef" => Rc::new(IntVarDefJustifier {}),
            "IntLinear" => Rc::new(IntLinearJustifier::new(self, antecedents_str)?),
            _ => {
                return Err(PBarberError::JustificationError(format!(
                    "{} not yet supported",
                    name
                )));
            }
        };

        if cache {
            Ok(Rc::clone(
                self.justifiers
                    .entry(name.to_string())
                    .or_insert_with(|| justifier),
            ))
        } else {
            Ok(justifier)
        }
    }
}

impl<W: Write> JustifierActions for Justifier<W> {
    fn write(&mut self, content: &str) -> Result<(), PBarberError> {
        self.write_line(content)?;
        Ok(())
    }
    fn get_min_max_for_var(&mut self, fzn_id: &Ustr) -> Result<(i64, i64), PBarberError> {
        let fzn_var = self.get_fzn_variable(&fzn_id)?;
        let domain = fzn_var
            .domain
            .as_ref()
            .ok_or(PBarberError::JustificationError(format!(
                "No domain found for {} in the fzn file (unsupported).",
                fzn_id.as_str()
            )))?;

        let int_domain = match domain {
            Domain::Int(r) => r,
            _ => {
                return Err(PBarberError::JustificationError(format!(
                    "Expected Int domain for {} but found Float (unsupported).",
                    fzn_id.as_str()
                )));
            }
        };

        let (min, max) = min_max(int_domain).ok_or(PBarberError::JustificationError(format!(
            "Couldn't get the min and max domain values for {}",
            fzn_id.as_str()
        )))?;
        Ok((min, max))
    }

    fn cp_var_bits_str(&mut self, cp_var: &Ustr, multiplier: i64) -> Result<String, PBarberError> {
        let (min, max) = self.get_min_max_for_var(cp_var)?;
        let mut num_bits = num_bits_for_range(min, max);
        let mut bits = String::new();
        if min < 0 {
            bits.push_str(&(i64::pow(2, num_bits) * -multiplier).to_string());
            bits.push(' ');
            bits.push_str(cp_var);
            bits.push_str("_b");
            bits.push_str(&(num_bits + 1).to_string());
            num_bits -= 1;
        }

        for i in (0..num_bits + 1).rev() {
            bits.push(' ');
            bits.push_str(&(i64::pow(2, i) * multiplier).to_string());
            bits.push(' ');
            bits.push_str(cp_var);
            bits.push_str("_b");
            bits.push_str(&(i).to_string());
        }

        Ok(bits.trim().to_string())
    }

    fn ensure_all_lits_defined(
        &mut self,
        constraint: &Box<dyn DynPBConstraint + 'static>,
        strict: bool,
    ) -> Result<(Vec<String>, Vec<String>), PBarberError> {
        let lits = constraint.get_constraint_lits();
        let mut pos_def_ids = Vec::<String>::new();
        let mut neg_def_ids = Vec::<String>::new();
        for lit in lits {
            let pos_def_result = self.ensure_lit_defined(lit);
            match pos_def_result {
                Ok(id) => pos_def_ids.push(id),
                Err(PBarberError::LiteralLookupError(m)) => {
                    if strict {
                        return Err(PBarberError::LiteralLookupError(m));
                    }
                }
                Err(e) => return Err(e),
            }

            let mut neg_lit = lit.clone();
            neg_lit.negate();

            let neg_def_result = self.ensure_lit_defined(&neg_lit);
            match neg_def_result {
                Ok(id) => neg_def_ids.push(id),
                Err(PBarberError::LiteralLookupError(m)) => {
                    if strict {
                        return Err(PBarberError::LiteralLookupError(m));
                    }
                }
                Err(e) => return Err(e),
            }
        }
        Ok((pos_def_ids, neg_def_ids))
    }

    fn ensure_lit_defined(&mut self, lit: &PBLiteral) -> Result<String, PBarberError> {
        let def_id = self.definition_id(lit);
        if self.is_defined(lit) {
            return Ok(def_id);
        }
        let pb_lit_name = self
            .pb_var_names
            .get_name(lit.get_var())
            .to_string()
            .clone();
        let cp_lit_data =
            self.cp_lit_map
                .get(&pb_lit_name)
                .ok_or(PBarberError::LiteralLookupError(format!(
                    "Couldn't find CP definition for literal {}",
                    self.pb_var_names.get_name(lit.get_var())
                )))?;

        let tilde_if_neg: &str = if lit.is_negated() { "~" } else { " " };
        match cp_lit_data {
            CPLitData::Condition {
                name,
                operator,
                value,
                ..
            } => {
                let operator = if lit.is_negated() {
                    operator.negated()
                } else {
                    operator
                };
                let (value, operator_str) = match operator {
                    CPOperator::GreaterEqual => (value.parse::<i32>().unwrap(), ">="),
                    CPOperator::Less => (value.parse::<i32>().unwrap() - 1, "<="),
                    _ => {
                        return Err(PBarberError::JustificationError(
                            "Can't handle equality literals yet.".to_string(),
                        ));
                    }
                };

                let bits = self.cp_var_bits_str(&Ustr::from(name.as_str()), 1)?;
                self.write_line(
                    format!(
                        "{} red {}{} ==> {} {} {} : {} -> {} ;",
                        def_id,
                        tilde_if_neg,
                        pb_lit_name,
                        bits,
                        operator_str,
                        value,
                        pb_lit_name,
                        if lit.is_negated() { 1 } else { 0 }
                    )
                    .as_str(),
                )?;

                self.set_defined(lit);
                return Ok(def_id);
            }
            CPLitData::Boolvar {
                _cpvartype: _,
                name,
            } => {
                // TODO: Probably want a better way of dealing with boolvars
                let mut split_var = name.split("=");
                let Some(var) = split_var.next() else {
                    return Ok(lit.to_pretty_string(&self.pb_var_names));
                };

                let val = split_var
                    .next()
                    .ok_or(PBarberError::JustificationError(format!(
                        "Found Boolvar {name} with '=' in name, but couldn't parse value"
                    )))?;
                let mut val = val.parse::<i64>().map_err(|_| {
                    PBarberError::JustificationError(format!(
                        "Found Boolvar {name} with '=' in name, but couldn't parse value"
                    ))
                })?;

                self.ensure_bounds_defined(&Ustr::from(var))?;

                let bits = self.cp_var_bits_str(&Ustr::from(var), 1)?;
                let (min, max) = self.get_min_max_for_var(&Ustr::from(var))?;
                let operator = if val == min {
                    if lit.is_negated() {
                        val += 1;
                        ">="
                    } else {
                        "<="
                    }
                } else if val == max {
                    if lit.is_negated() {
                        val -= 1;
                        "<="
                    } else {
                        ">="
                    }
                } else {
                    return Err(PBarberError::JustificationError(format!(
                        "Found Boolvar {} with more than two values in its domain.",
                        name
                    )));
                };

                self.write_line(
                    format!(
                        "{} red {}{} ==> {} {} {} : {} -> {} ;",
                        def_id,
                        tilde_if_neg,
                        pb_lit_name,
                        bits,
                        operator,
                        val,
                        pb_lit_name,
                        if lit.is_negated() { 1 } else { 0 }
                    )
                    .as_str(),
                )?;

                self.set_defined(lit);
                return Ok("".to_string());
            }
        }
    }

    fn pb_var_names(&self) -> &PBVarNameManager {
        &self.pb_var_names
    }

    fn get_fzn_constraint(
        &self,
        fzn_id: &str,
    ) -> Result<&flatzinc_serde::Constraint<Ustr>, PBarberError> {
        let fzn_line: usize = match fzn_id.trim().trim_start_matches("@f").parse::<usize>() {
            Ok(f) => f,
            Err(_) => {
                return Err(PBarberError::JustificationError(format!(
                    "Failed to get line number from fzn_id `{fzn_id}`"
                )));
            }
        };

        let fzn_constraint =
            self.fzn
                .constraints
                .get(fzn_line)
                .ok_or(PBarberError::JustificationError(format!(
                    "Couldn't find fzn constraint for id {fzn_id}"
                )))?;
        Ok(fzn_constraint)
    }

    fn get_fzn_array(&self, id: &Ustr) -> Result<&flatzinc_serde::Array<Ustr>, PBarberError> {
        self.fzn
            .arrays
            .get(id)
            .ok_or(PBarberError::JustificationError(format!(
                "Expected array, but got {:?}",
                id
            )))
    }

    fn get_fzn_variable(&self, id: &Ustr) -> Result<&flatzinc_serde::Variable<Ustr>, PBarberError> {
        self.fzn
            .variables
            .get(id)
            .ok_or(PBarberError::JustificationError(format!(
                "Expected variable, but got {:?}",
                id
            )))
    }

    fn get_cp_lit_data(&self, lit: &PBLiteral) -> Result<CPLitData, PBarberError> {
        let pb_lit_name = self
            .pb_var_names
            .get_name(lit.get_var())
            .to_string()
            .clone();

        let data = self
            .cp_lit_map
            .get(&pb_lit_name)
            .ok_or(PBarberError::LiteralLookupError(format!(
                "Couldn't find CP definition for literal {}",
                self.pb_var_names.get_name(lit.get_var())
            )))?;
        Ok(data)
    }

    fn ensure_bounds_defined(
        &mut self,
        cp_var_id: &Ustr,
    ) -> Result<(String, String), PBarberError> {
        let mut lb_id = String::from("@lb");
        lb_id.push_str(&cp_var_id.as_str());
        let mut ub_id = String::from("@ub");
        ub_id.push_str(&cp_var_id.as_str());
        if self.defined_bounds.contains(&cp_var_id.to_string()) {
            return Ok((lb_id, ub_id));
        }

        self.defined_bounds.insert(cp_var_id.to_string());
        let (min, max) = self.get_min_max_for_var(cp_var_id)?;
        let mut pb_line = String::from(&lb_id);
        pb_line.push_str(" a ");
        pb_line.push_str(&self.cp_var_bits_str(&cp_var_id, 1)?);
        pb_line.push_str(" >=");
        pb_line.push_str(&min.to_string());
        pb_line.push_str(":: bits_lower_bound ;");
        self.write_line(&pb_line)?;
        let mut pb_line = String::from(&ub_id);
        pb_line.push_str(" a ");
        pb_line.push_str(&self.cp_var_bits_str(&cp_var_id, 1)?);
        pb_line.push_str(" <=");
        pb_line.push_str(&max.to_string());
        pb_line.push_str(":: bits_upper_bound ;");
        self.write_line(&pb_line)?;
        return Ok((lb_id, ub_id));
    }
}

impl PolBuilder {
    fn new() -> Self {
        Self {
            pol_line: String::from("pol "),
            empty: true,
        }
    }
    fn done(&mut self) -> &str {
        self.pol_line.push(';');
        self.pol_line.as_str()
    }

    fn add(&mut self, term: &String) -> &mut Self {
        self.pol_line.push_str(term.as_str());
        if self.empty {
            self.pol_line.push_str(" ");
            self.empty = false;
        } else {
            self.pol_line.push_str(" + ");
        }
        self
    }

    fn add_all(&mut self, terms: &Vec<String>) -> &mut Self {
        for t in terms {
            self.add(t);
        }
        self
    }

    fn add_weighted(&mut self, term: &String, weight: u32) -> &mut Self {
        self.pol_line.push_str(term.as_str());
        self.pol_line.push(' ');
        self.pol_line.push_str(weight.to_string().as_str());
        self.pol_line.push_str(" *");
        if self.empty {
            self.pol_line.push_str(" ");
            self.empty = false;
        } else {
            self.pol_line.push_str(" + ");
        }
        self
    }
}
fn min_max<T: Copy + Ord>(range_list: &RangeList<T>) -> Option<(T, T)> {
    let mut intervals = range_list.intervals();

    let first = intervals.next()?;
    let min = *first.start();

    let max = intervals.last().map(|r| *r.end()).unwrap_or(*first.end());

    Some((min, max))
}

fn num_bits_for_range(min: i64, max: i64) -> u32 {
    if min >= 0 {
        let target = (max as u64) + 1;
        (64 - target.leading_zeros()) as u32
    } else {
        let bound = (max.abs().max(min.abs()) + 1) as u64;
        (64 - bound.leading_zeros()) as u32
    }
}

fn trim_sc(to_trim: &str) -> &str {
    to_trim.trim_end_matches(';')
}

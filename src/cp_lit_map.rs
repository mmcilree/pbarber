use serde::Deserialize;
use std::{
    collections::HashMap,
    fmt,
    io::{BufReader, Read},
};

#[derive(Debug, Deserialize, Clone)]
#[serde(rename_all = "lowercase")]
pub(crate) enum CPVarType {
    IntVar,
    BoolVar,
}

#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub(crate) enum CPOperator {
    #[serde(alias = "<")]
    Less,
    #[serde(alias = ">=")]
    GreaterEqual,
    #[serde(alias = "==")]
    Equal,
    #[serde(alias = "!=")]
    NotEqual,
}

impl CPOperator {
    pub(crate) fn negated(&self) -> Self {
        match self {
            Self::Less => Self::GreaterEqual,
            Self::GreaterEqual => Self::Less,
            Self::Equal => Self::NotEqual,
            Self::NotEqual => Self::Equal,
        }
    }
}

impl fmt::Display for CPOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let symbol = match self {
            CPOperator::Less => "<",
            CPOperator::GreaterEqual => ">=",
            CPOperator::Equal => "==",
            CPOperator::NotEqual => "!=",
        };
        write!(f, "{}", symbol)
    }
}

#[derive(Debug, Deserialize, Clone)]
#[serde(tag = "type", rename_all = "lowercase")]
pub(crate) enum CPLitData {
    #[serde(rename_all = "camelCase")]
    Condition {
        cpvartype: CPVarType,
        name: String,
        operator: CPOperator,
        value: String,
    },
    #[serde(rename_all = "camelCase")]
    Boolvar { cpvartype: CPVarType, name: String },
}

pub(crate) struct CPLitMap {
    raw_map: HashMap<String, CPLitData>,
}

impl CPLitMap {
    pub fn from_reader<R: Read>(reader: R) -> Self {
        let buffered = BufReader::new(reader);
        let raw_map =
            serde_json::from_reader(buffered).expect("Failed to parse literal mapping data.");
        Self { raw_map }
    }

    pub fn get(&self, pb_var: &String) -> Option<CPLitData> {
        self.raw_map.get(pb_var).cloned()
    }
}

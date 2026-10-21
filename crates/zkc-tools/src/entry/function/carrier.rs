//! Exact compiler-owned Host carrier. All strings remain covered by Package.
use super::{FunctionSignature, Schema};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Document {
    pub format: String,
    pub original: String,
    pub entry: String,
    pub functions: Vec<Function>,
    pub calculations: Vec<Calculation>,
    pub deployments: Vec<Deployment>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Interface {
    pub format: String,
    pub capture: String,
    pub original: String,
    pub toolchain: String,
    pub entry: String,
    pub selection: Selection,
    pub functions: Vec<FunctionSignature>,
    pub protocols: Vec<serde::de::IgnoredAny>,
    pub relations: Vec<serde::de::IgnoredAny>,
    pub setups: Vec<serde::de::IgnoredAny>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Selection {
    pub kind: String,
    pub function: String,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Function {
    pub signature: FunctionSignature,
    pub body: Block,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Block {
    pub arguments: Vec<Definition>,
    pub operations: Vec<Operation>,
    pub returns: Vec<u32>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Definition {
    pub id: u32,
    pub schema: Schema,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
#[serde(tag = "op", rename_all = "lowercase")]
pub(super) enum Operation {
    Construct {
        operands: Vec<u32>,
        results: Vec<Definition>,
        alternative: String,
    },
    Unpack {
        operands: Vec<u32>,
        results: Vec<Definition>,
    },
    Stop {
        operands: Vec<u32>,
        results: Vec<Definition>,
        reason: String,
    },
    Project {
        operands: Vec<u32>,
        results: Vec<Definition>,
        path: Vec<u32>,
    },
    Call {
        operands: Vec<u32>,
        results: Vec<Definition>,
        callee: String,
    },
    Numeric {
        operands: Vec<u32>,
        results: Vec<Definition>,
        calculation: String,
    },
    Invoke {
        operands: Vec<u32>,
        results: Vec<Definition>,
        deployment: String,
    },
    If {
        operands: Vec<u32>,
        results: Vec<Definition>,
        regions: Vec<Block>,
    },
    Match {
        operands: Vec<u32>,
        results: Vec<Definition>,
        alternatives: Vec<String>,
        regions: Vec<Block>,
    },
    For {
        operands: Vec<u32>,
        results: Vec<Definition>,
        carried: u32,
        regions: Vec<Block>,
    },
    Require {
        operands: Vec<u32>,
        results: Vec<Definition>,
    },
    Drop {
        operands: Vec<u32>,
        results: Vec<Definition>,
    },
}
impl Operation {
    pub fn operands(&self) -> &[u32] {
        match self {
            Self::Unpack { operands, .. }
            | Self::Stop { operands, .. }
            | Self::Construct { operands, .. }
            | Self::Project { operands, .. }
            | Self::Call { operands, .. }
            | Self::Numeric { operands, .. }
            | Self::Invoke { operands, .. }
            | Self::If { operands, .. }
            | Self::Match { operands, .. }
            | Self::For { operands, .. }
            | Self::Require { operands, .. }
            | Self::Drop { operands, .. } => operands,
        }
    }
    pub fn results(&self) -> &[Definition] {
        match self {
            Self::Unpack { results, .. }
            | Self::Stop { results, .. }
            | Self::Construct { results, .. }
            | Self::Project { results, .. }
            | Self::Call { results, .. }
            | Self::Numeric { results, .. }
            | Self::Invoke { results, .. }
            | Self::If { results, .. }
            | Self::Match { results, .. }
            | Self::For { results, .. }
            | Self::Require { results, .. }
            | Self::Drop { results, .. } => results,
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Calculation {
    pub id: String,
    pub parameters: Vec<Schema>,
    pub results: Vec<Schema>,
    pub function: String,
    pub program: String,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub(super) struct Deployment {
    pub id: String,
    pub operation: String,
    pub parameters: Vec<Schema>,
    pub results: Vec<Schema>,
    pub package: String,
}
crate::entry::decode::objects!(
    Document,
    Interface,
    Selection,
    Function,
    Block,
    Definition,
    Operation,
    Calculation,
    Deployment
);

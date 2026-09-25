//! Source coordinates retained by an installed correspondence checker.
//!
//! These maps carry the checker's semantic claim. Admission also checks their
//! complete coverage and target coordinates against the actual typed program.

use super::model::{AdmissionError, ErrorCode, Instruction, Limits, Program};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortMapping {
    pub instance: String,
    pub role: String,
    pub participant: String,
    /// Original source argument to actual participant argument, in port order.
    pub arguments: Vec<(String, String)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallMapping {
    pub instance: String,
    pub role: String,
    pub site: String,
    pub source_function: String,
    pub function: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SourceMap {
    pub ports: Vec<PortMapping>,
    pub calls: Vec<CallMapping>,
}

fn error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Correspondence, detail)
}

impl SourceMap {
    pub fn port(&self, instance: &str, role: &str, source: &str) -> Option<&str> {
        self.ports
            .iter()
            .find(|p| p.instance == instance && p.role == role)?
            .arguments
            .iter()
            .find(|p| p.0 == source)
            .map(|p| p.1.as_str())
    }

    pub fn call(&self, instance: &str, role: &str, site: &str) -> Option<&CallMapping> {
        self.calls
            .iter()
            .find(|p| p.instance == instance && p.role == role && p.site == site)
    }

    pub(crate) fn validate(&self, program: &Program) -> Result<(), AdmissionError> {
        if self.ports.len() != program.participants.len()
            || self.calls.len() > Limits::STATIC_INSTRUCTIONS
        {
            return Err(error("source-map-coverage"));
        }
        let mut participants = BTreeSet::new();
        let mut identities = BTreeSet::new();
        let mut expected_calls = BTreeSet::new();
        for mapping in &self.ports {
            let p = program
                .participants
                .get(&mapping.participant)
                .ok_or_else(|| error("source-map-participant"))?;
            if !participants.insert(&mapping.participant)
                || !identities.insert((&p.instance, &p.role))
                || p.instance != mapping.instance
                || p.role != mapping.role
                || mapping.arguments.len() != p.inputs.len()
            {
                return Err(error("source-map-participant"));
            }
            let mut names = BTreeSet::new();
            for ((source, target), (actual, _)) in mapping.arguments.iter().zip(&p.inputs) {
                if source.is_empty()
                    || source.len() > 128
                    || !names.insert(source)
                    || target != actual
                {
                    return Err(error("source-map-port"));
                }
            }
            // The admitted program already bounds nesting and instruction count.
            let mut bodies = vec![p.body.as_ref()];
            while let Some(body) = bodies.pop() {
                for instruction in body {
                    match instruction {
                        Instruction::Local { site, function, .. } => {
                            expected_calls.insert((
                                p.instance.as_str(),
                                p.role.as_str(),
                                site.as_str(),
                                function.as_str(),
                            ));
                        }
                        Instruction::Loop { body, .. } => bodies.push(body),
                        _ => {}
                    }
                }
            }
        }
        for mapping in &self.calls {
            if mapping.source_function.is_empty()
                || mapping.source_function.len() > 128
                || !expected_calls.remove(&(
                    mapping.instance.as_str(),
                    mapping.role.as_str(),
                    mapping.site.as_str(),
                    mapping.function.as_str(),
                ))
            {
                return Err(error("source-map-call"));
            }
        }
        if !expected_calls.is_empty() {
            return Err(error("source-map-call-coverage"));
        }
        Ok(())
    }
}

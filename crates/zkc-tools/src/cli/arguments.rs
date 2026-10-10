//! Command syntax shared by help and argument admission. No file I/O occurs here.
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
pub(super) struct OptionSpec {
    pub syntax: &'static str,
    pub repeated: bool,
    value: ValueFormat,
}
#[derive(Clone, Copy)]
enum ValueFormat {
    Text,
    Unsigned,
    Hex(Option<usize>),
}
impl OptionSpec {
    pub const fn new(syntax: &'static str) -> Self {
        Self {
            syntax,
            repeated: false,
            value: ValueFormat::Text,
        }
    }
    pub const fn unsigned(mut self) -> Self {
        self.value = ValueFormat::Unsigned;
        self
    }
    pub const fn hex(mut self, bytes: Option<usize>) -> Self {
        self.value = ValueFormat::Hex(bytes);
        self
    }
    pub const fn repeated(mut self) -> Self {
        self.repeated = true;
        self
    }
    fn name(self) -> &'static str {
        self.syntax
            .split_once('=')
            .map_or(self.syntax, |(name, _)| name)
    }
}

pub(super) struct Command {
    pub name: &'static str,
    pub summary: &'static str,
    pub positional: &'static str,
    pub options: &'static [OptionSpec],
    pub description: &'static str,
}
pub(crate) struct Arguments<'a> {
    pub positional: Vec<&'a str>,
    pub options: Vec<(&'a str, Option<&'a str>)>,
}
impl<'a> Arguments<'a> {
    pub fn value(&self, name: &str) -> Option<&'a str> {
        self.options
            .iter()
            .find(|(key, _)| *key == name)
            .and_then(|(_, value)| *value)
    }
    pub fn has(&self, name: &str) -> bool {
        self.options.iter().any(|(key, _)| *key == name)
    }
}
#[derive(Debug)]
pub(super) struct Error {
    pub code: &'static str,
    pub message: String,
}
impl Command {
    pub fn help(&self) -> String {
        let mut usage = format!("Usage: zkc {}", self.name);
        if !self.positional.is_empty() {
            usage.push(' ');
            usage.push_str(self.positional);
        }
        for option in self.options {
            let syntax = if option.repeated {
                format!("{} ...", option.syntax)
            } else {
                option.syntax.into()
            };
            usage.push_str(&format!(" [{syntax}]"));
        }
        format!("{usage}\n\n{}\n", self.description)
    }
    pub fn parse<'a>(&self, args: &'a [String]) -> Result<Arguments<'a>, Error> {
        let error = |code, message| Error { code, message };
        let mut parsed = Arguments {
            positional: Vec::new(),
            options: Vec::new(),
        };
        let mut seen = BTreeSet::new();
        let mut positional_only = false;
        for arg in args {
            if !positional_only && arg == "--" {
                positional_only = true;
                continue;
            }
            if positional_only || !arg.starts_with('-') {
                parsed.positional.push(arg);
                continue;
            }
            let (name, value) = arg
                .split_once('=')
                .map_or((arg.as_str(), None), |(name, value)| (name, Some(value)));
            let Some(spec) = self.options.iter().find(|spec| spec.name() == name) else {
                return Err(error(
                    "cli-option",
                    format!("{} does not accept {name}", self.name),
                ));
            };
            if !seen.insert(name) && !spec.repeated {
                return Err(error("cli-option", format!("{name} may only appear once")));
            }
            if spec.syntax.contains('=') {
                if value.is_none_or(str::is_empty) {
                    return Err(error("cli-option", format!("expected {}", spec.syntax)));
                }
            } else if value.is_some() {
                return Err(error("cli-option", format!("{name} does not take a value")));
            }
            if let Some(value) = value {
                let fields = spec.syntax.bytes().filter(|b| *b == b'=').count();
                let parts: Vec<_> = value.splitn(fields, '=').collect();
                if parts.len() != fields || parts.iter().any(|p| p.is_empty()) {
                    return Err(error("cli-option", format!("expected {}", spec.syntax)));
                }
                let value = parts.last().unwrap();
                let valid = match spec.value {
                    ValueFormat::Text => true,
                    ValueFormat::Unsigned => {
                        !value.is_empty()
                            && value.bytes().all(|b| b.is_ascii_digit())
                            && value.parse::<u64>().is_ok()
                    }
                    ValueFormat::Hex(bytes) => {
                        value.len() % 2 == 0
                            && bytes.is_none_or(|n| value.len() == n * 2)
                            && value
                                .bytes()
                                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                    }
                };
                if !valid {
                    return Err(error("cli-option", format!("invalid value for {name}")));
                }
            }
            parsed.options.push((name, value));
        }
        let maximum = self.positional.split_whitespace().count();
        let minimum = self
            .positional
            .split_whitespace()
            .filter(|p| !p.starts_with('['))
            .count();
        if !(minimum..=maximum).contains(&parsed.positional.len()) {
            return Err(error(
                "cli-usage",
                format!("expected positional arguments: {}", self.positional),
            ));
        }
        Ok(parsed)
    }
}

//! The staged interpreter: one emit function per canonical row kind,
//! mirroring the reference executor's dispatch
//! (`lib/Interpreter/Interpreter.cpp`) arm for arm. The reference walks
//! rows at run time against supplier objects; this walk happens once,
//! against the binding's concrete types, and writes down the residual
//! program. Anything the reference would refuse at run time — a missing
//! supplier, an inexecutable check, a foreign row — is refused here, at
//! emit time, so the emitted verifier has no "cannot judge" arm.

use crate::binding::{Binding, CheckImpl, ImplKind, SpongeImpl};
use crate::doc::{Document, Entry, Ref, Row};
use std::collections::HashSet;
use std::fmt::Write as _;

/// The value class of an SSA name during the walk.
#[derive(Debug, Clone, PartialEq, Eq)]
enum VClass {
    /// A document payload class, typed by the binding.
    Doc(String),
    /// A toy-algebra result: plain u64 residue.
    Algebra,
}

pub struct EmittedCrate {
    pub crate_name: String,
    pub lib_rs: String,
    pub cargo_toml: String,
    pub readme: String,
    pub conformance: Option<String>,
}

pub struct Vectors {
    pub artifact_id: String,
    pub cases: Vec<VectorCase>,
}

pub struct VectorCase {
    pub name: String,
    pub statement: Vec<(String, String)>,
    pub proof_hex: String,
    pub expect: String,
    pub challenges: Vec<String>,
}

struct Walk<'a> {
    document: &'a Document,
    binding: &'a Binding,
    /// Rust expression and class per value reference.
    values: std::collections::HashMap<Ref, (String, VClass)>,
    /// Which row results anything later refers to.
    referenced: HashSet<(usize, usize)>,
    current_sponge: Option<Ref>,
    current_stream: Option<Ref>,
    body: String,
    uses_group: bool,
    uses_field: bool,
}

/// The BLS12-381 scalar-field order: the only sample space the `fr`
/// challenge derivation is defined over.
const BLS12_381_R_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

fn rust_string(text: &str) -> String {
    format!("{text:?}")
}

fn is_rust_ident(text: &str) -> bool {
    // Statement labels become field names verbatim — the endpoint ABI is
    // the naming authority, so both cases are admitted and the struct
    // carries `allow(non_snake_case)`. Keywords cannot be fields.
    const KEYWORDS: &[&str] = &[
        "as", "async", "await", "box", "break", "const", "continue", "crate", "dyn", "else",
        "enum", "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
        "move", "mut", "pub", "ref", "return", "self", "static", "struct", "super", "trait",
        "true", "type", "unsafe", "use", "where", "while",
    ];
    !text.is_empty()
        && text.chars().next().unwrap().is_ascii_alphabetic()
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !KEYWORDS.contains(&text)
}

/// Decimal text into little-endian 32-bit limbs, refusing overflow.
fn decimal_to_limbs(text: &str, limb_count: usize) -> Result<Vec<u32>, String> {
    if text.is_empty() || !text.chars().all(|c| c.is_ascii_digit()) {
        return Err(format!("'{text}' is not a decimal number"));
    }
    let mut limbs = vec![0u32; limb_count];
    for digit in text.chars() {
        let mut carry = digit.to_digit(10).unwrap() as u64;
        for limb in limbs.iter_mut() {
            let wide = *limb as u64 * 10 + carry;
            *limb = wide as u32;
            carry = wide >> 32;
        }
        if carry != 0 {
            return Err(format!("'{text}' does not fit {limb_count} 32-bit limbs"));
        }
    }
    Ok(limbs)
}

impl<'a> Walk<'a> {
    fn line(&mut self, indent: usize, text: &str) {
        for _ in 0..indent {
            self.body.push_str("    ");
        }
        self.body.push_str(text);
        self.body.push('\n');
    }

    fn class_impl(&self, class: &str) -> Result<ImplKind, String> {
        Ok(self
            .binding
            .class(class)
            .ok_or_else(|| {
                format!(
                    "binding '{}' supplies no implementation for class '{class}'",
                    self.binding.name
                )
            })?
            .implementation)
    }

    fn value(&self, reference: Ref, context: &str) -> Result<(String, VClass), String> {
        self.values
            .get(&reference)
            .cloned()
            .ok_or_else(|| format!("{context}: reference {reference:?} names no value"))
    }

    fn rust_type(&self, class: &VClass) -> Result<&'static str, String> {
        match class {
            VClass::Algebra => Ok("u64"),
            VClass::Doc(name) => Ok(self.class_impl(name)?.rust_type()),
        }
    }

    fn consume_sponge(&mut self, reference: Ref, row: usize, produced: Ref) -> Result<(), String> {
        if self.current_sponge != Some(reference) {
            return Err(format!(
                "row {row}: sponge reference {reference:?} is not the live sponge \
                 ({:?}); the transcript chain must be linear",
                self.current_sponge
            ));
        }
        self.current_sponge = Some(produced);
        Ok(())
    }

    fn consume_stream(
        &mut self,
        reference: Ref,
        row: usize,
        produced: Option<Ref>,
    ) -> Result<(), String> {
        if self.current_stream != Some(reference) {
            return Err(format!(
                "row {row}: stream reference {reference:?} is not the live stream \
                 ({:?}); the proof stream must be linear",
                self.current_stream
            ));
        }
        self.current_stream = produced;
        Ok(())
    }

    /// The reject early-return in statement position, with the
    /// challenge log carried out.
    fn reject(class: &str) -> String {
        format!("return Outcome::reject(RejectClass::{class}, challenges);")
    }

    /// The same early-return as an underrun match arm.
    fn reject_arm(class: &str) -> String {
        format!("None => return Outcome::reject(RejectClass::{class}, challenges),")
    }

    fn emit_absorb_of(&mut self, expr: &str, class: &VClass, row: usize) -> Result<(), String> {
        match class {
            VClass::Algebra => Err(format!(
                "row {row}: absorbing an algebra result has no framing codec; \
                 no admitted artifact does this"
            )),
            VClass::Doc(name) => {
                let statement = match self.class_impl(name)? {
                    ImplKind::ToyBe8 => {
                        format!("sponge.absorb(&zkc_rt::toy::frame_be8({expr}));")
                    }
                    ImplKind::P3Word => format!("sponge.absorb(&[{expr}]);"),
                    ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                        format!("sponge.absorb(&{expr});")
                    }
                    ImplKind::BlsFrBe32 => {
                        format!("sponge.absorb(&zkc_rt::kzg::fr_to_wire(&{expr}));")
                    }
                    ImplKind::BlsG1Be48 => {
                        format!("sponge.absorb(&zkc_rt::kzg::g1_to_wire(&{expr}));")
                    }
                };
                self.line(1, &statement);
                Ok(())
            }
        }
    }

    fn walk(&mut self) -> Result<(), String> {
        // Pre-pass: which results are referenced, so unused locals can be
        // named `_…` and the emitted crate compiles warning-free.
        for row in &self.document.rows {
            for reference in row_references(row) {
                if let Ref::Res(row_index, result) = reference {
                    self.referenced.insert((row_index, result));
                }
            }
        }

        // Entry arguments.
        let statement_count = self.document.statement_labels.len();
        for (index, element) in self.document.entry.iter().enumerate() {
            match element {
                Entry::Val(class) => {
                    if index >= statement_count {
                        return Err(format!(
                            "entry argument {index} is a value but there are only \
                             {statement_count} statement labels"
                        ));
                    }
                    let label = &self.document.statement_labels[index];
                    if !is_rust_ident(label) {
                        return Err(format!(
                            "statement label '{label}' is not a usable identifier"
                        ));
                    }
                    self.values.insert(
                        Ref::Arg(index),
                        (format!("statement.{label}"), VClass::Doc(class.clone())),
                    );
                }
                Entry::Stream => {
                    if self.current_stream.is_some() {
                        return Err("more than one stream entry argument".into());
                    }
                    self.current_stream = Some(Ref::Arg(index));
                }
            }
        }
        if self.current_stream.is_none() {
            return Err("the verifier entry has no proof stream argument".into());
        }

        // Statement binding gates, in label order, before any event —
        // exactly the reference's bindStatement sequencing.
        for (index, label) in self.document.statement_labels.iter().enumerate() {
            let Entry::Val(class) = &self.document.entry[index] else {
                return Err(format!(
                    "statement label '{label}' has no value entry argument"
                ));
            };
            let class_binding = self
                .binding
                .class(class)
                .ok_or_else(|| format!("binding supplies no implementation for class '{class}'"))?;
            if let Some(modulus) = class_binding.modulus {
                self.line(1, &format!("if statement.{label} >= {modulus}u64 {{"));
                self.line(2, &Self::reject("PublicBindingFailure"));
                self.line(1, "}");
            }
        }

        // The rows.
        let rows: Vec<Row> = self.document.rows.to_vec();
        let last = rows.len().checked_sub(1).ok_or("empty program")?;
        for (index, row) in rows.iter().enumerate() {
            self.emit_row(index, row, index == last)?;
        }
        match rows.last() {
            Some(Row::Decide { .. }) => Ok(()),
            _ => Err("the verifier frame must end in decide".into()),
        }
    }

    fn emit_row(&mut self, index: usize, row: &Row, is_last: bool) -> Result<(), String> {
        match row {
            Row::Init { sponge, iv } => {
                if index != 0 || self.current_sponge.is_some() {
                    return Err(format!("row {index}: init must be the single first row"));
                }
                if *sponge != self.binding.sponge_construction || *iv != self.binding.sponge_iv {
                    return Err(format!(
                        "row {index}: sponge '{sponge}' with iv '{iv}' has no supplier in \
                         binding '{}' (it supplies '{}' with iv '{}')",
                        self.binding.name, self.binding.sponge_construction, self.binding.sponge_iv
                    ));
                }
                let constructor = match (self.binding.sponge_impl, iv.as_str()) {
                    (SpongeImpl::ToyDuplex, "artifact-id") => {
                        "zkc_rt::toy::ToyDuplex::new(SOURCE_PIR_ID)".to_owned()
                    }
                    (SpongeImpl::P3LenpadDuplex, "artifact-id") => {
                        "zkc_rt::p3::P3Duplex::new(SOURCE_PIR_ID)".to_owned()
                    }
                    (SpongeImpl::P3LenpadDuplex, "zero") => {
                        "zkc_rt::p3::P3Duplex::new(\"\")".to_owned()
                    }
                    (implementation, policy) => {
                        return Err(format!(
                            "row {index}: iv policy '{policy}' has no constructor for \
                             {implementation:?}"
                        ))
                    }
                };
                self.line(1, &format!("let mut sponge = {constructor};"));
                self.current_sponge = Some(Ref::Res(index, 0));
                Ok(())
            }

            Row::Absorb { sponge, value } => {
                self.consume_sponge(*sponge, index, Ref::Res(index, 0))?;
                let (expr, class) = self.value(*value, &format!("row {index} (absorb)"))?;
                self.emit_absorb_of(&expr, &class, index)?;
                Ok(())
            }

            Row::Read {
                stream,
                label,
                class,
            } => {
                self.consume_stream(*stream, index, Some(Ref::Res(index, 0)))?;
                let implementation = self.class_impl(class)?;
                let width = implementation.wire_width();
                let used = self.referenced.contains(&(index, 1));
                let name = format!("{}r{index}_1", if used { "" } else { "_" });
                let ty = implementation.rust_type();
                let comment = format!("// [\"read\", \"{label}\" : {class}]");
                self.line(1, &comment);
                match implementation {
                    ImplKind::ToyBe8 => {
                        self.line(
                            1,
                            &format!("let {name}: {ty} = match cursor.take({width}) {{"),
                        );
                        self.line(2, "Some(wire) => zkc_rt::toy::decode_be8(wire),");
                        self.line(2, &Self::reject_arm("AbiDecodeFailure"));
                        self.line(1, "};");
                        let modulus = self
                            .binding
                            .class(class)
                            .and_then(|class_binding| class_binding.modulus);
                        if let Some(modulus) = modulus {
                            self.line(1, &format!("if {name} >= {modulus}u64 {{"));
                            self.line(2, &Self::reject("AbiDecodeFailure"));
                            self.line(1, "}");
                        }
                    }
                    ImplKind::P3Word => {
                        self.line(
                            1,
                            &format!("let {name}: {ty} = match cursor.take({width}) {{"),
                        );
                        self.line(2, "Some(wire) => zkc_rt::p3::decode_words::<1>(wire)[0],");
                        self.line(2, &Self::reject_arm("AbiDecodeFailure"));
                        self.line(1, "};");
                        self.line(1, &format!("if {name} >= zkc_rt::p3::BB {{"));
                        self.line(2, &Self::reject("AbiDecodeFailure"));
                        self.line(1, "}");
                    }
                    ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                        let limbs = implementation.limbs();
                        self.line(
                            1,
                            &format!("let {name}: {ty} = match cursor.take({width}) {{"),
                        );
                        self.line(
                            2,
                            &format!("Some(wire) => zkc_rt::p3::decode_words::<{limbs}>(wire),"),
                        );
                        self.line(2, &Self::reject_arm("AbiDecodeFailure"));
                        self.line(1, "};");
                        self.line(1, &format!("if !zkc_rt::p3::words_canonical(&{name}) {{"));
                        self.line(2, &Self::reject("AbiDecodeFailure"));
                        self.line(1, "}");
                    }
                    ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48 => {
                        // The decoder owns canonicality whole: field
                        // range for fr; compressed form, curve, and
                        // subgroup for g1.
                        let decoder = if implementation == ImplKind::BlsFrBe32 {
                            "fr_from_wire"
                        } else {
                            "g1_from_wire"
                        };
                        self.line(
                            1,
                            &format!("let {name}: {ty} = match cursor.take({width}) {{"),
                        );
                        self.line(
                            2,
                            &format!("Some(wire) => match zkc_rt::kzg::{decoder}(wire) {{"),
                        );
                        self.line(3, "Some(value) => value,");
                        self.line(3, &Self::reject_arm("AbiDecodeFailure"));
                        self.line(2, "},");
                        self.line(2, &Self::reject_arm("AbiDecodeFailure"));
                        self.line(1, "};");
                    }
                }
                let bare = format!("r{index}_1");
                self.values
                    .insert(Ref::Res(index, 1), (bare, VClass::Doc(class.clone())));
                Ok(())
            }

            Row::Squeeze {
                sponge,
                label,
                class,
                count,
                domain,
                rule,
                space,
            } => {
                self.consume_sponge(*sponge, index, Ref::Res(index, 0))?;
                let implementation = self.class_impl(class)?;
                // The canonical rule/count pairing (endpoints.md §3):
                // `uniform` exactly for one draw, `uniform_independent`
                // exactly for a counted vector.
                match (rule.as_str(), *count) {
                    ("uniform", 1) => {}
                    ("uniform_independent", 2..=1048576) => {}
                    _ => {
                        return Err(format!(
                            "row {index}: sampling shape at '{label}' (rule '{rule}', count \
                             {count}) is outside the canonical pairing"
                        ))
                    }
                }
                let comment = format!(
                    "// [\"squeeze\", \"{label}\" : {class}, count {count}, domain \"{domain}\"]"
                );
                self.line(1, &comment);
                if *count == 1 {
                    let used = self.referenced.contains(&(index, 1));
                    let name = format!("{}r{index}_1", if used { "" } else { "_" });
                    match implementation {
                        ImplKind::ToyBe8 => {
                            let space: u64 = space.parse().map_err(|_| {
                                format!(
                                    "row {index}: sample space '{space}' does not fit the toy \
                                         derivation's u64 domain"
                                )
                            })?;
                            if space < 2 {
                                return Err(format!("row {index}: sample space {space} below 2"));
                            }
                            self.line(1, &format!("let {name}: u64 = {{"));
                            self.line(
                                2,
                                &format!("let digest = sponge.squeeze({});", rust_string(domain)),
                            );
                            self.line(
                                2,
                                &format!(
                                    "let value = zkc_rt::toy::derive_be8(&digest, {space}u64);"
                                ),
                            );
                            self.line(2, "challenges.push(value.to_string());");
                            self.line(2, "value");
                            self.line(1, "};");
                        }
                        ImplKind::P3Ext4 => {
                            // The tuple bijection ignores the space value, but the
                            // declared string must still be a sane cardinality —
                            // the reference profile validates it too.
                            if space.is_empty()
                                || !space.chars().all(|c| c.is_ascii_digit())
                                || space == "0"
                                || space == "1"
                            {
                                return Err(format!(
                                    "row {index}: sample space '{space}' is not a cardinality"
                                ));
                            }
                            self.line(1, &format!("let {name}: [u32; 4] = {{"));
                            self.line(2, "let coords = zkc_rt::p3::squeeze_ext4(&mut sponge);");
                            self.line(2, "challenges.push(zkc_rt::p3::ext4_decimal(&coords));");
                            self.line(2, "coords");
                            self.line(1, "};");
                        }
                        ImplKind::P3Word => {
                            let space: u64 = space.parse().map_err(|_| {
                                format!("row {index}: sample space '{space}' does not fit u64")
                            })?;
                            if space < 2 {
                                return Err(format!("row {index}: sample space {space} below 2"));
                            }
                            self.line(1, &format!("let {name}: u32 = {{"));
                            self.line(2, &format!("let value = zkc_rt::p3::squeeze_low_bits(&mut sponge, {space}u64);"));
                            self.line(2, "challenges.push(value.to_string());");
                            self.line(2, "value");
                            self.line(1, "};");
                        }
                        ImplKind::BlsFrBe32 => {
                            if self.binding.sponge_impl != SpongeImpl::ToyDuplex {
                                return Err(format!(
                                    "row {index}: the fr challenge derivation is defined over a \
                                     32-byte digest sponge; binding '{}' supplies {:?}",
                                    self.binding.name, self.binding.sponge_impl
                                ));
                            }
                            // The declared space must be exactly the scalar-field
                            // order the derivation reduces into.
                            if space != BLS12_381_R_DECIMAL {
                                return Err(format!(
                                    "row {index}: sample space '{space}' is not the BLS12-381 \
                                     scalar-field order the fr derivation is defined over"
                                ));
                            }
                            self.line(1, &format!("let {name}: zkc_rt::kzg::Fr = {{"));
                            self.line(
                                2,
                                &format!("let digest = sponge.squeeze({});", rust_string(domain)),
                            );
                            self.line(2, "let value = zkc_rt::kzg::fr_from_digest(&digest);");
                            self.line(2, "challenges.push(zkc_rt::kzg::fr_decimal(&value));");
                            self.line(2, "value");
                            self.line(1, "};");
                        }
                        ImplKind::P3Digest8 | ImplKind::BlsG1Be48 => {
                            return Err(format!(
                                "row {index}: class '{class}' has no squeeze derivation; \
                                 nothing squeezes a digest or a group element"
                            ))
                        }
                    }
                    let bare = format!("r{index}_1");
                    self.values
                        .insert(Ref::Res(index, 1), (bare, VClass::Doc(class.clone())));
                } else {
                    // A counted vector is one event producing one log
                    // entry; its SSA value stays deliberately unbound
                    // (the reference does the same), so any reference to
                    // it must have failed the pre-pass.
                    if self.referenced.contains(&(index, 1)) {
                        return Err(format!(
                            "row {index}: a later row references the vector squeeze '{label}', \
                             but a vector event's value is unbindable"
                        ));
                    }
                    if implementation != ImplKind::P3Word {
                        return Err(format!(
                            "row {index}: counted squeezes are implemented for the word \
                             derivation only (class '{class}' has {implementation:?})"
                        ));
                    }
                    let space: u64 = space.parse().map_err(|_| {
                        format!("row {index}: sample space '{space}' does not fit u64")
                    })?;
                    if space < 2 {
                        return Err(format!("row {index}: sample space {space} below 2"));
                    }
                    self.line(1, "{");
                    self.line(2, "let mut entry = String::new();");
                    self.line(2, &format!("for draw in 0..{count} {{"));
                    self.line(
                        3,
                        &format!(
                            "let value = zkc_rt::p3::squeeze_low_bits(&mut sponge, {space}u64);"
                        ),
                    );
                    self.line(3, "if draw > 0 { entry.push('|'); }");
                    self.line(3, "entry.push_str(&value.to_string());");
                    self.line(2, "}");
                    self.line(2, "challenges.push(entry);");
                    self.line(1, "}");
                }
                Ok(())
            }

            Row::Const { value, class } => {
                let implementation = self.class_impl(class)?;
                let used = self.referenced.contains(&(index, 0));
                let name = format!("{}r{index}_0", if used { "" } else { "_" });
                let literal = match implementation {
                    ImplKind::ToyBe8 => {
                        let parsed: u64 = value.parse().map_err(|_| {
                            format!("row {index}: constant '{value}' is not a decimal u64")
                        })?;
                        format!("{parsed}u64")
                    }
                    ImplKind::P3Word => {
                        let parsed: u32 = value.parse().map_err(|_| {
                            format!("row {index}: constant '{value}' is not a decimal u32")
                        })?;
                        format!("{parsed}u32")
                    }
                    other => {
                        return Err(format!(
                            "row {index}: constants of class '{class}' ({other:?}) have no \
                             literal form; no admitted artifact carries one"
                        ))
                    }
                };
                self.line(
                    1,
                    &format!("let {name}: {} = {literal};", implementation.rust_type()),
                );
                self.values.insert(
                    Ref::Res(index, 0),
                    (format!("r{index}_0"), VClass::Doc(class.clone())),
                );
                Ok(())
            }

            Row::FNeg { operand } => self.algebra_unary(index, operand, "f_neg"),
            Row::FAdd { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "f_add"),
            Row::FMul { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "f_mul"),
            Row::GExp { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "g_exp"),
            Row::GMul { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "g_mul"),

            Row::AssertEq { lhs, rhs, label } => {
                let (left, left_class) = self.value(*lhs, &format!("row {index} (assert_eq)"))?;
                let (right, right_class) = self.value(*rhs, &format!("row {index} (assert_eq)"))?;
                let left_type = self.rust_type(&left_class)?;
                let right_type = self.rust_type(&right_class)?;
                if left_type != right_type {
                    return Err(format!(
                        "row {index}: assert_eq '{label}' compares {left_type} with {right_type}"
                    ));
                }
                self.line(1, &format!("// [\"assert_eq\", \"{label}\"]"));
                self.line(1, &format!("if {left} != {right} {{"));
                self.line(2, &Self::reject("CheckFailure"));
                self.line(1, "}");
                Ok(())
            }

            Row::CheckCall {
                inputs,
                label,
                kind,
                digest,
                params,
            } => {
                let Some(check) = self.binding.check(digest).cloned() else {
                    return Err(format!(
                        "row {index}: opaque check '{label}' (kind '{kind}', contract {digest}) \
                         has no executable adapter in binding '{}'; the reference profiles \
                         refuse this at run time (zkc-E403) and the emitter refuses it here",
                        self.binding.name
                    ));
                };
                // The contract's one static parameter is the suite; the
                // adapter must implement exactly the suite the row cites.
                if params.len() != 1 || params[0] != check.suite {
                    return Err(format!(
                        "row {index}: check '{label}' cites parameters {params:?}; the bound \
                         adapter implements suite '{}'",
                        check.suite
                    ));
                }
                let mut arguments = Vec::new();
                for input in inputs {
                    arguments.push(self.value(*input, &format!("row {index} (check_call)"))?);
                }
                let expect_kind = |walk: &Self,
                                   argument: &(String, VClass),
                                   want: ImplKind,
                                   role: &str|
                 -> Result<String, String> {
                    match &argument.1 {
                        VClass::Doc(name) if walk.class_impl(name)? == want => {
                            Ok(argument.0.clone())
                        }
                        other => Err(format!(
                            "row {index}: check '{label}' {role} operand has class {other:?}, \
                             which is not the contract's {want:?}"
                        )),
                    }
                };
                self.line(1, &format!("// [\"check_call\", \"{label}\" : {kind}]"));
                self.line(
                    1,
                    &format!(
                        "let tau_g2_{index} = zkc_rt::kzg::g2_from_hex({})",
                        rust_string(&check.tau_g2_hex)
                    ),
                );
                self.line(
                    1,
                    "    .expect(\"the binding-pinned tau_g2 point parses\");",
                );
                match check.implementation {
                    CheckImpl::KzgOpening => {
                        // Role order: commitment, point, value, proof.
                        if arguments.len() != 4 {
                            return Err(format!(
                                "row {index}: check '{label}' has {} operands; the opening \
                                 contract takes 4",
                                arguments.len()
                            ));
                        }
                        let commitment =
                            expect_kind(self, &arguments[0], ImplKind::BlsG1Be48, "commitment")?;
                        let point = expect_kind(self, &arguments[1], ImplKind::BlsFrBe32, "point")?;
                        let value = expect_kind(self, &arguments[2], ImplKind::BlsFrBe32, "value")?;
                        let proof = expect_kind(self, &arguments[3], ImplKind::BlsG1Be48, "proof")?;
                        self.line(
                            1,
                            &format!(
                                "if !zkc_rt::kzg::kzg_opening_accepts(&tau_g2_{index}, \
                                 &{commitment}, &{point}, &{value}, &{proof}) {{"
                            ),
                        );
                        self.line(2, &Self::reject("CheckFailure"));
                        self.line(1, "}");
                    }
                    CheckImpl::KzgBatchOpening => {
                        // Role order: commitment*n, point, value*n,
                        // batch_challenge, proof — positions paired by
                        // index, exactly the predicate specification.
                        if arguments.len() < 7 || (arguments.len() - 3) % 2 != 0 {
                            return Err(format!(
                                "row {index}: check '{label}' has {} operands; the batch \
                                 contract takes 2n+3 with n >= 2",
                                arguments.len()
                            ));
                        }
                        let n = (arguments.len() - 3) / 2;
                        let mut commitments = Vec::new();
                        for argument in &arguments[..n] {
                            commitments.push(expect_kind(
                                self,
                                argument,
                                ImplKind::BlsG1Be48,
                                "commitment",
                            )?);
                        }
                        let point = expect_kind(self, &arguments[n], ImplKind::BlsFrBe32, "point")?;
                        let mut values = Vec::new();
                        for argument in &arguments[n + 1..2 * n + 1] {
                            values.push(expect_kind(self, argument, ImplKind::BlsFrBe32, "value")?);
                        }
                        let gamma = expect_kind(
                            self,
                            &arguments[2 * n + 1],
                            ImplKind::BlsFrBe32,
                            "batch_challenge",
                        )?;
                        let proof =
                            expect_kind(self, &arguments[2 * n + 2], ImplKind::BlsG1Be48, "proof")?;
                        self.line(
                            1,
                            &format!(
                                "if !zkc_rt::kzg::kzg_batch_opening_accepts(&tau_g2_{index}, \
                                 &[{}], &{point}, &[{}], &{gamma}, &{proof}) {{",
                                commitments.join(", "),
                                values.join(", ")
                            ),
                        );
                        self.line(2, &Self::reject("CheckFailure"));
                        self.line(1, "}");
                    }
                }
                Ok(())
            }

            Row::ExpectEnd { stream } => {
                self.consume_stream(*stream, index, None)?;
                self.line(1, "if !cursor.at_end() {");
                self.line(2, &Self::reject("ProofTrailingData"));
                self.line(1, "}");
                Ok(())
            }

            Row::Decide { sponge } => {
                if !is_last {
                    return Err(format!("row {index}: decide before the end of the program"));
                }
                self.consume_sponge(*sponge, index, Ref::Res(index, 0))?;
                self.line(1, "Outcome::accept(challenges)");
                Ok(())
            }

            Row::ProverOnly { kind } => Err(format!(
                "row {index}: '{kind}' is a prover-frame row; this emitter takes verifier \
                 documents (the endpoint-kind gate, zkc-E409's emit-time form)"
            )),
        }
    }

    fn algebra_operand(&self, reference: &Ref, index: usize, op: &str) -> Result<String, String> {
        let (expr, class) = self.value(*reference, &format!("row {index} ({op})"))?;
        match &class {
            VClass::Algebra => Ok(expr),
            VClass::Doc(name) if self.class_impl(name)? == ImplKind::ToyBe8 => Ok(expr),
            VClass::Doc(name) => Err(format!(
                "row {index}: {op} over class '{name}' has no algebra; the toy moduli cover \
                 u64 residues only"
            )),
        }
    }

    fn require_algebra(&mut self, index: usize, op: &str) -> Result<(), String> {
        if self.binding.algebra.is_none() {
            return Err(format!(
                "row {index}: algebra op '{op}' has no moduli in binding '{}' (zkc-E404's \
                 emit-time form)",
                self.binding.name
            ));
        }
        match op {
            "f_neg" | "f_add" | "f_mul" => self.uses_field = true,
            _ => self.uses_group = true,
        }
        Ok(())
    }

    fn algebra_unary(&mut self, index: usize, operand: &Ref, op: &str) -> Result<(), String> {
        self.require_algebra(index, op)?;
        let value = self.algebra_operand(operand, index, op)?;
        let used = self.referenced.contains(&(index, 0));
        let name = format!("{}r{index}_0", if used { "" } else { "_" });
        self.line(
            1,
            &format!(
                "let {name}: u64 = (FIELD_MODULUS - ({value}) % FIELD_MODULUS) % FIELD_MODULUS;"
            ),
        );
        self.values
            .insert(Ref::Res(index, 0), (format!("r{index}_0"), VClass::Algebra));
        Ok(())
    }

    fn algebra_binary(
        &mut self,
        index: usize,
        lhs: &Ref,
        rhs: &Ref,
        op: &str,
    ) -> Result<(), String> {
        self.require_algebra(index, op)?;
        let left = self.algebra_operand(lhs, index, op)?;
        let right = self.algebra_operand(rhs, index, op)?;
        let used = self.referenced.contains(&(index, 0));
        let name = format!("{}r{index}_0", if used { "" } else { "_" });
        // The exact reference expressions (Interpreter.cpp): f_add
        // reduces operands before the sum; the modular helpers own the
        // rest.
        let expr = match op {
            "f_add" => {
                format!("(({left}) % FIELD_MODULUS + ({right}) % FIELD_MODULUS) % FIELD_MODULUS")
            }
            "f_mul" => format!("zkc_rt::toy::mulmod({left}, {right}, FIELD_MODULUS)"),
            "g_exp" => format!("zkc_rt::toy::powmod({left}, {right}, GROUP_MODULUS)"),
            "g_mul" => format!("zkc_rt::toy::mulmod({left}, {right}, GROUP_MODULUS)"),
            other => return Err(format!("row {index}: unknown algebra op '{other}'")),
        };
        self.line(1, &format!("let {name}: u64 = {expr};"));
        self.values
            .insert(Ref::Res(index, 0), (format!("r{index}_0"), VClass::Algebra));
        Ok(())
    }
}

fn row_references(row: &Row) -> Vec<Ref> {
    match row {
        Row::Init { .. } | Row::Const { .. } | Row::ProverOnly { .. } => Vec::new(),
        Row::CheckCall { inputs, .. } => inputs.clone(),
        Row::Absorb { sponge, value } => vec![*sponge, *value],
        Row::Squeeze { sponge, .. } => vec![*sponge],
        Row::Read { stream, .. } => vec![*stream],
        Row::FNeg { operand } => vec![*operand],
        Row::FAdd { lhs, rhs }
        | Row::FMul { lhs, rhs }
        | Row::GExp { lhs, rhs }
        | Row::GMul { lhs, rhs }
        | Row::AssertEq { lhs, rhs, .. } => vec![*lhs, *rhs],
        Row::ExpectEnd { stream } => vec![*stream],
        Row::Decide { sponge } => vec![*sponge],
    }
}

/// Emit-time supplier gates: every codec route, construction pin, and
/// the sponge must be realized by the binding before any code exists.
fn gate_suppliers(document: &Document, binding: &Binding) -> Result<(), String> {
    if document.endpoint != "verifier" {
        return Err(format!(
            "endpoint '{}' is not emittable by the verifier emitter (zkc-E409's emit-time form)",
            document.endpoint
        ));
    }
    for (class, codec) in &document.codecs {
        let class_binding = binding.class(class).ok_or_else(|| {
            format!(
                "codec class '{class}' has no implementation in binding '{}' (zkc-E400's \
                 emit-time form)",
                binding.name
            )
        })?;
        if class_binding.codec != *codec {
            return Err(format!(
                "class '{class}' routes to codec '{codec}', but binding '{}' implements \
                 '{}' for it",
                binding.name, class_binding.codec
            ));
        }
    }
    for pin in &document.param_digests {
        let (tagged, digest) = pin
            .split_once('=')
            .ok_or_else(|| format!("malformed param digest '{pin}'"))?;
        let supplied = binding.digest_for(tagged).ok_or_else(|| {
            format!(
                "pinned construction '{tagged}' has no supplier digest in binding '{}'",
                binding.name
            )
        })?;
        if supplied != digest {
            return Err(format!(
                "param digest mismatch at '{tagged}': the artifact pins {digest}, binding \
                 '{}' implements {supplied} (zkc-E408's emit-time form)",
                binding.name
            ));
        }
    }
    Ok(())
}

pub fn emit(
    document: &Document,
    binding: &Binding,
    rt_path: &str,
    crate_name: Option<&str>,
    vectors: Option<&Vectors>,
) -> Result<EmittedCrate, String> {
    gate_suppliers(document, binding)?;

    let crate_name = crate_name
        .map(str::to_owned)
        .unwrap_or_else(|| format!("zkc-verifier-{}", &document.artifact_id[..12]));
    let crate_ident = crate_name.replace('-', "_");

    let mut walk = Walk {
        document,
        binding,
        values: Default::default(),
        referenced: Default::default(),
        current_sponge: None,
        current_stream: None,
        body: String::new(),
        uses_group: false,
        uses_field: false,
    };
    walk.walk()?;
    let body = std::mem::take(&mut walk.body);
    let (uses_group, uses_field) = (walk.uses_group, walk.uses_field);

    // Features: the union over the implementations actually bound.
    let mut features: Vec<&str> = Vec::new();
    let add_feature = |feature: &'static str, features: &mut Vec<&str>| {
        if !features.contains(&feature) {
            features.push(feature);
        }
    };
    add_feature(binding.sponge_impl.feature(), &mut features);
    for (class, _) in &document.codecs {
        add_feature(
            binding.class(class).unwrap().implementation.feature(),
            &mut features,
        );
    }
    features.sort_unstable();

    // ---- src/lib.rs ----
    let mut lib = String::new();
    let _ = writeln!(
        lib,
        "//! A zkc-emitted verifier endpoint.\n//!\n\
         //! Generated from the canonical OIR document whose identity is\n\
         //! baked below; the emitter recomputed that identity from the\n\
         //! document bytes before reading a single row. This crate is the\n\
         //! projection's residual program: the transcript order, proof\n\
         //! ABI, checks, and decision of one sealed protocol, specialized\n\
         //! against one supplier binding. Do not edit; re-emit.\n"
    );
    lib.push_str("pub use zkc_rt::{self, Outcome, RejectClass, Verdict};\n");
    lib.push_str("use zkc_rt::ProofCursor;\n\n");
    let _ = writeln!(
        lib,
        "/// `SHA256(\"zkc/oir\\n\" ‖ document)` — the endpoint artifact."
    );
    let _ = writeln!(
        lib,
        "pub const ARTIFACT_ID: &str = \"{}\";",
        document.artifact_id
    );
    let _ = writeln!(
        lib,
        "/// The provenance-independent view (`zkc/oir-semantic`)."
    );
    let _ = writeln!(
        lib,
        "pub const SEMANTIC_ID: &str = \"{}\";",
        document.semantic_id
    );
    let _ = writeln!(lib, "/// The sealed protocol this endpoint projects.");
    let _ = writeln!(
        lib,
        "pub const SOURCE_PIR_ID: &str = \"{}\";",
        document.source
    );
    let _ = writeln!(lib, "/// The supplier binding and its file digest.");
    let _ = writeln!(lib, "pub const BINDING: &str = \"{}\";", binding.name);
    let _ = writeln!(
        lib,
        "pub const BINDING_DIGEST: &str = \"{}\";",
        binding.digest_of_file
    );
    let _ = writeln!(
        lib,
        "pub const EMITTER: &str = \"zkc-emit {}\";",
        env!("CARGO_PKG_VERSION")
    );
    lib.push('\n');
    if uses_group || uses_field {
        let algebra = binding.algebra.as_ref().unwrap();
        if uses_group {
            let _ = writeln!(lib, "const GROUP_MODULUS: u64 = {};", algebra.group);
        }
        if uses_field {
            let _ = writeln!(lib, "const FIELD_MODULUS: u64 = {};", algebra.field);
        }
        lib.push('\n');
    }

    lib.push_str("/// The public statement, typed and ordered as the endpoint ABI\n");
    lib.push_str("/// declares it; field names are the ABI labels, verbatim.\n");
    lib.push_str("/// Multi-limb values are little-endian 32-bit limbs.\n");
    lib.push_str("#[allow(non_snake_case)]\n");
    lib.push_str("#[allow(non_snake_case)]\npub struct Statement {\n");
    for (index, label) in document.statement_labels.iter().enumerate() {
        let Entry::Val(class) = &document.entry[index] else {
            unreachable!()
        };
        let ty = binding.class(class).unwrap().implementation.rust_type();
        let _ = writeln!(lib, "    pub {label}: {ty},");
    }
    lib.push_str("}\n\n");

    lib.push_str("/// One verifier execution over untrusted proof bytes: a verdict\n");
    lib.push_str("/// and the ordered challenge log. Statement range violations are\n");
    lib.push_str("/// `public_binding_failure`, exactly as the reference executor\n");
    lib.push_str("/// classifies them.\n");
    lib.push_str("pub fn verify(statement: &Statement, proof: &[u8]) -> Outcome {\n");
    // Linear resources take `mut` exactly when a row writes them, so the
    // emitted crate stays warning-free on shapes that never squeeze or
    // never read.
    let squeezes = document
        .rows
        .iter()
        .any(|row| matches!(row, Row::Squeeze { .. }));
    let reads = document
        .rows
        .iter()
        .any(|row| matches!(row, Row::Read { .. }));
    let _ = writeln!(
        lib,
        "    let {}challenges: Vec<String> = Vec::new();",
        if squeezes { "mut " } else { "" }
    );
    let _ = writeln!(
        lib,
        "    let {}cursor = ProofCursor::new(proof);",
        if reads { "mut " } else { "" }
    );
    lib.push_str(&body);
    lib.push_str("}\n");

    // ---- Cargo.toml ----
    let feature_list = features
        .iter()
        .map(|feature| format!("\"{feature}\""))
        .collect::<Vec<_>>()
        .join(", ");
    let cargo_toml = format!(
        "# Generated by zkc-emit; do not edit — re-emit.\n\
         [package]\n\
         name = \"{crate_name}\"\n\
         version = \"0.0.0\"\n\
         edition = \"2021\"\n\
         \n\
         [dependencies]\n\
         zkc-rt = {{ path = \"{rt_path}\", default-features = false, features = [{feature_list}] }}\n"
    );

    // ---- README.md ----
    let readme = format!(
        "# {crate_name}\n\n\
         A zkc-emitted verifier endpoint. Generated — do not edit; re-emit.\n\n\
         ## Identity chain\n\n\
         | Fact | Value |\n|---|---|\n\
         | OIR artifact id | `{artifact}` |\n\
         | OIR semantic id | `{semantic}` |\n\
         | Sealed source protocol | `{source}` |\n\
         | Supplier binding | `{binding_name}` (file sha256 `{binding_digest}`) |\n\
         | Emitter | zkc-emit {version} |\n\n\
         `verify(statement, proof)` returns the verdict and the ordered\n\
         challenge log. Reject classes are the normative set of\n\
         `docs/spec/endpoints.md` §4; supplier resolution happened at emit\n\
         time, so no run-time outcome means \"cannot judge\".\n\n\
         ## Scope\n\n\
         Acceptance under this binding, at these pins, established by the\n\
         enclosed conformance vectors. This crate makes no claim of\n\
         protocol soundness, zero knowledge, or conformance beyond those\n\
         vectors; those judgments live with the sealed protocol artifact,\n\
         under the identities above.\n",
        artifact = document.artifact_id,
        semantic = document.semantic_id,
        source = document.source,
        binding_name = binding.name,
        binding_digest = binding.digest_of_file,
        version = env!("CARGO_PKG_VERSION"),
    );

    // ---- tests/conformance.rs ----
    let conformance = match vectors {
        None => None,
        Some(vectors) => Some(emit_conformance(document, binding, vectors, &crate_ident)?),
    };

    Ok(EmittedCrate {
        crate_name,
        lib_rs: lib,
        cargo_toml,
        readme,
        conformance,
    })
}

fn statement_literal(
    document: &Document,
    binding: &Binding,
    case: &VectorCase,
) -> Result<String, String> {
    let mut fields = Vec::new();
    for (index, label) in document.statement_labels.iter().enumerate() {
        let Entry::Val(class) = &document.entry[index] else {
            unreachable!()
        };
        let implementation = binding.class(class).unwrap().implementation;
        let text = case
            .statement
            .iter()
            .find(|(name, _)| name == label)
            .map(|(_, value)| value.as_str())
            .ok_or_else(|| {
                format!(
                    "vector '{}' has no statement value for '{label}'",
                    case.name
                )
            })?;
        let literal = match implementation {
            ImplKind::ToyBe8 => {
                let limbs = decimal_to_limbs(text, 2)?;
                format!("{}u64", (limbs[1] as u64) << 32 | limbs[0] as u64)
            }
            ImplKind::P3Word => format!("{}u32", decimal_to_limbs(text, 1)?[0]),
            ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                let limbs = decimal_to_limbs(text, implementation.limbs())?;
                let words = limbs
                    .iter()
                    .map(|limb| format!("{limb}u32"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{words}]")
            }
            ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48 => {
                // The decimal statement value is the wire integer; the
                // typed constructor re-establishes canonicality.
                let limbs = decimal_to_limbs(text, implementation.limbs())?;
                let mut bytes = Vec::new();
                for limb in limbs.iter().rev() {
                    bytes.extend_from_slice(&limb.to_be_bytes());
                }
                let list = bytes
                    .iter()
                    .map(|byte| format!("0x{byte:02x}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let constructor = if implementation == ImplKind::BlsFrBe32 {
                    "fr_from_wire"
                } else {
                    "g1_from_wire"
                };
                format!(
                    "verifier::zkc_rt::kzg::{constructor}(&[{list}])\n            .expect(\"a canonical statement wire value\")"
                )
            }
        };
        fields.push(format!("{label}: {literal}"));
    }
    Ok(format!("Statement {{ {} }}", fields.join(", ")))
}

fn emit_conformance(
    document: &Document,
    binding: &Binding,
    vectors: &Vectors,
    crate_ident: &str,
) -> Result<String, String> {
    if vectors.artifact_id != document.artifact_id {
        return Err(format!(
            "the vectors file binds artifact {}, the document is {}; matching a sidecar to \
             the wrong artifact is exactly what the identity check refuses",
            vectors.artifact_id, document.artifact_id
        ));
    }
    if !vectors.cases.iter().any(|case| case.expect == "accept") {
        return Err(
            "the vectors file carries no accepting vector; a refusal battery without a \
             positive control asserts nothing (the wave-4 lesson)"
                .into(),
        );
    }

    let mut out = String::new();
    out.push_str("// Generated conformance suite: the committed golden vectors, replayed\n");
    out.push_str("// against the emitted endpoint. The same vectors drive the reference\n");
    out.push_str("// executor (zkc-run --vectors), so equality here is the differential\n");
    out.push_str("// gate between the emitted program and the reference semantics.\n\n");
    let _ = writeln!(out, "use {crate_ident} as verifier;\n");

    out.push_str("// An empty challenge list on a non-accepting vector means the log is\n");
    out.push_str("// unchecked for that vector (the corpus convention for corrupted-wire\n");
    out.push_str("// cases, where the verdict is the claim); an accepting vector always\n");
    out.push_str("// carries its full log.\n");
    out.push_str("fn run(name: &str, statement: verifier::Statement, proof: &[u8], expect: &str, challenges: Option<&[&str]>) {\n");
    out.push_str("    let outcome = verifier::verify(&statement, proof);\n");
    out.push_str(
        "    assert_eq!(outcome.verdict.as_str(), expect, \"vector '{name}' verdict\");\n",
    );
    out.push_str("    if let Some(challenges) = challenges {\n");
    out.push_str("        let logged: Vec<&str> = outcome.challenges.iter().map(String::as_str).collect();\n");
    out.push_str("        assert_eq!(logged, challenges, \"vector '{name}' challenge log\");\n");
    out.push_str("    }\n");
    out.push_str("}\n\n");

    if binding.sponge_impl == SpongeImpl::P3LenpadDuplex {
        out.push_str("#[test]\nfn permutation_known_answer() {\n");
        out.push_str("    verifier::zkc_rt::p3::permutation_self_check();\n}\n\n");
    }

    let _ = writeln!(
        out,
        "#[test]\nfn vectors_bind_this_artifact() {{\n    assert_eq!(verifier::ARTIFACT_ID, \"{}\");\n}}\n",
        vectors.artifact_id
    );

    out.push_str("#[test]\nfn golden_vectors() {\n");
    for case in &vectors.cases {
        let statement = statement_literal(document, binding, case)?;
        if case.proof_hex.len() % 2 != 0
            || !case
                .proof_hex
                .chars()
                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        {
            return Err(format!("vector '{}' proof is not lowercase hex", case.name));
        }
        let bytes = (0..case.proof_hex.len())
            .step_by(2)
            .map(|at| format!("0x{}", &case.proof_hex[at..at + 2]))
            .collect::<Vec<_>>()
            .join(", ");
        let challenges = if case.challenges.is_empty() && case.expect != "accept" {
            "None".to_owned()
        } else {
            let entries = case
                .challenges
                .iter()
                .map(|entry| format!("{entry:?}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("Some(&[{entries}])")
        };
        let _ = writeln!(
            out,
            "    run(\n        {:?},\n        verifier::{statement},\n        &[{bytes}],\n        {:?},\n        {challenges},\n    );",
            case.name, case.expect
        );
    }
    out.push_str("}\n");
    Ok(out)
}

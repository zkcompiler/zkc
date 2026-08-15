//! The staged interpreter: one emit function per canonical row kind,
//! mirroring the reference executor's dispatch
//! (`lib/Interpreter/Interpreter.cpp`) arm for arm. The reference walks
//! rows at run time against supplier objects; this walk happens once,
//! against the binding's concrete types, and writes down the residual
//! program. Anything the reference would refuse at run time — a missing
//! supplier, an inexecutable check, a foreign row — is refused here, at
//! emit time, so the emitted verifier has no "cannot judge" arm.
//!
//! One walk serves both endpoint frames. Everything before the frame —
//! the sponge, absorbs, squeezes, constants, and the toy algebra — is
//! literally the same code, which is the point: the two endpoints are
//! projections of one sealed spine, so their emitters share everything
//! but the four rows where the wire reverses direction.

use crate::binding::{Binding, CheckImpl, ClassBinding, ImplKind, Operand, SpongeImpl};
use crate::doc::{Document, Endpoint, Entry, Ref, Row};
use crate::rust;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

/// Stands where the sponge declaration's qualifier goes until the walk
/// knows whether anything absorbs or squeezes. `init` is a row, so the
/// declaration is written mid-body, before its own answer exists; every
/// other local is declared in the preamble, after the walk has run. The
/// byte is one no generated source can contain.
const SPONGE_QUALIFIER: &str = "\u{1}";

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
    pub cases: Cases,
}

/// Vector corpora are endpoint-shaped: a verifier replays untrusted
/// bytes to a verdict, a prover replays inputs to bytes. Keeping them
/// distinct at the type means a corpus can never be silently replayed
/// against the endpoint it does not describe.
pub enum Cases {
    Verifier(Vec<VectorCase>),
    Prover(Vec<ProverCase>),
}

pub struct VectorCase {
    pub name: String,
    pub statement: Vec<(String, String)>,
    pub proof_hex: String,
    pub expect: String,
    pub challenges: Vec<String>,
}

pub struct ProverCase {
    pub name: String,
    pub statement: Vec<(String, String)>,
    /// Witness label → lowercase-hex payload.
    pub witness: Vec<(String, String)>,
    /// `"ok"`, or the refusal kind (`"statement"`, `"fill"`).
    pub expect: String,
    /// The endpoint ABI label a refusal names; unused when `expect` is
    /// `"ok"`.
    pub label: String,
    /// The refusal's own sentence. Where a fill wrote it, this is the
    /// same text the reference supplier reports, so the corpus compares
    /// the diagnostic and not only the classification.
    pub message: String,
    pub proof_hex: String,
    pub challenges: Vec<String>,
}

struct Walk<'a> {
    document: &'a Document,
    binding: &'a Binding,
    /// Rust expression and class per value reference.
    values: HashMap<Ref, (String, VClass)>,
    /// Live handles: Rust expression and handle class. A handle is
    /// removed when consumed, so the carrier's exactly-once rule
    /// (zkc-E149) is a lookup failure here and a borrow-checker error in
    /// the emitted crate — the same rule, stated twice.
    handles: HashMap<Ref, (String, String)>,
    /// Which row results anything later refers to.
    referenced: HashSet<(usize, usize)>,
    current_sponge: Option<Ref>,
    current_stream: Option<Ref>,
    body: String,
    /// What the emitted body actually touched. The preamble declares
    /// these locals, and re-deriving that from the row list is how
    /// `cursor`, `sponge`, and `statement` came to be declared for
    /// bodies that never mention them: each guess was independently
    /// fallible. The walk knows, so the walk records.
    used: Used,
}

/// One emitted local: whether the body names it at all, and whether it
/// needs to be mutable. `challenges` and `proof` are always read (the
/// frame returns them), so only their mutability is in question.
#[derive(Default, Clone, Copy)]
struct Use {
    named: bool,
    mutated: bool,
}

impl Use {
    /// `""`, `"mut "`, or the `_` prefix an unnamed local needs.
    fn qualifier(self) -> &'static str {
        if self.mutated {
            "mut "
        } else {
            ""
        }
    }

    fn prefix(self) -> &'static str {
        if self.named {
            ""
        } else {
            "_"
        }
    }
}

#[derive(Default, Clone, Copy)]
struct Used {
    sponge: Use,
    cursor: Use,
    challenges: Use,
    proof: Use,
    statement: bool,
    group_modulus: bool,
    field_modulus: bool,
}

/// The normative reject classes (`docs/spec/endpoints.md` §4). The
/// emitter writes these spellings into generated code and admits them in
/// a vector corpus, so it holds the closed set; `zkc-rt` carries the same
/// set as the type the generated code returns.
const REJECT_CLASSES: &[&str] = &[
    "abi_decode_failure",
    "abi_validation_failure",
    "proof_trailing_data",
    "public_binding_failure",
    "transcript_failure",
    "check_failure",
];

/// The BLS12-381 scalar-field order: the only sample space the `fr`
/// challenge derivation is defined over.
const BLS12_381_R_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

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

    /// The implementation a row's class resolves to.
    ///
    /// Two authorities have to agree, and both are asked here. The
    /// document's codec map is what the artifact authorized — a class it
    /// does not route is one the reference executor refuses to run at
    /// all (zkc-E400, "artifact names no codec") — and the binding is
    /// what realizes that route. Asking only the binding emitted crates
    /// that used a codec the artifact never named.
    fn class_binding(&self, class: &str) -> Result<&'a ClassBinding, String> {
        if !self
            .document
            .codecs
            .iter()
            .any(|(routed, _)| routed == class)
        {
            return Err(format!(
                "no codec route for class '{class}': the artifact names no codec for it \
                 (zkc-E400's emit-time form)"
            ));
        }
        self.binding.class(class).ok_or_else(|| {
            format!(
                "binding '{}' supplies no implementation for class '{class}'",
                self.binding.name
            )
        })
    }

    fn class_impl(&self, class: &str) -> Result<ImplKind, String> {
        Ok(self.class_binding(class)?.implementation)
    }

    /// Resolve a value reference, recording that the emitted text now
    /// names whatever the expression names.
    fn value(&mut self, reference: Ref, context: &str) -> Result<(String, VClass), String> {
        let resolved = self
            .values
            .get(&reference)
            .cloned()
            .ok_or_else(|| format!("{context}: reference {reference:?} names no value"))?;
        if resolved.0.starts_with("statement.") {
            self.used.statement = true;
        }
        Ok(resolved)
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

    fn take_handle(&mut self, reference: Ref, context: &str) -> Result<(String, String), String> {
        self.handles.remove(&reference).ok_or_else(|| {
            format!(
                "{context}: reference {reference:?} names no live handle; a handle is consumed \
                 exactly once (zkc-E149's emit-time form)"
            )
        })
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

    /// The prover's refusal in statement position. There is no verdict
    /// channel: the run either produces bytes or says why it will not.
    fn refuse(variant: &str, label: &str, message: &str) -> String {
        format!(
            "return Err(ProveError::{variant} {{ label: {}.to_owned(), message: {}.to_owned() }});",
            rust::literal(label),
            rust::literal(message)
        )
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
                self.used.sponge = Use {
                    named: true,
                    mutated: true,
                };
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

        // Entry arguments: statement values, then (prover only) one
        // handle per witness label, then the stream — the argument order
        // the reference binds against.
        let statement_count = self.document.statement_labels.len();
        let witness_count = self.document.witness_labels.len();
        // The two generated structs are two naming scopes, and each
        // label is admitted once — a repeated one would be a repeated
        // field rather than a refusal.
        let mut statement_fields = rust::Scope::new("statement label");
        let mut witness_fields = rust::Scope::new("witness label");
        for (index, element) in self.document.entry.iter().enumerate() {
            match element {
                Entry::Val(class) => {
                    if index >= statement_count {
                        return Err(format!(
                            "entry argument {index} is a value but there are only \
                             {statement_count} statement labels"
                        ));
                    }
                    let label = statement_fields.ident(&self.document.statement_labels[index])?;
                    self.values.insert(
                        Ref::Arg(index),
                        (format!("statement.{label}"), VClass::Doc(class.clone())),
                    );
                }
                Entry::Handle(class) => {
                    // Witness handles occupy exactly the block after the
                    // statement values, in witness-label order — the
                    // reference's own `base + index` addressing.
                    let slot = index
                        .checked_sub(statement_count)
                        .filter(|slot| *slot < witness_count)
                        .ok_or_else(|| {
                            format!(
                                "entry argument {index} is a handle, but the {witness_count} \
                                 witness labels occupy arguments {statement_count}..\
                                 {}",
                                statement_count + witness_count
                            )
                        })?;
                    let (declared_label, declared) = &self.document.witness_labels[slot];
                    let label = witness_fields.ident(declared_label)?;
                    if declared != class {
                        return Err(format!(
                            "witness label '{label}' declares handle class '{declared}', but \
                             entry argument {index} carries '{class}'"
                        ));
                    }
                    // The field move is the handle's single use; rustc
                    // rejects a second one on its own.
                    self.handles
                        .insert(Ref::Arg(index), (format!("witness.{label}"), class.clone()));
                }
                Entry::Stream => {
                    if self.current_stream.is_some() {
                        return Err("more than one stream entry argument".into());
                    }
                    self.current_stream = Some(Ref::Arg(index));
                }
                Entry::Sponge => {
                    return Err(format!(
                        "entry argument {index} is a sponge; the transcript is opened by init, \
                         never passed in"
                    ))
                }
            }
        }
        if self.current_stream.is_none() {
            return Err("the entry has no proof stream argument".into());
        }
        if self.handles.len() != witness_count {
            return Err(format!(
                "the entry carries {} handle arguments for {witness_count} witness labels",
                self.handles.len()
            ));
        }

        // Statement binding gates, in label order, before any event —
        // exactly the reference's bindStatement sequencing. The verifier
        // classifies a violation as a verdict; the prover, whose
        // statement is its own input, refuses (zkc-E405).
        for (label, class) in &self.document.statement {
            if let Some(modulus) = self.class_binding(class)?.modulus {
                // The gate names the statement without going through
                // `value`, so it records the use itself.
                self.used.statement = true;
                self.line(1, &format!("if statement.{label} >= {modulus}u64 {{"));
                let refusal = match self.document.endpoint {
                    Endpoint::Verifier => Self::reject("PublicBindingFailure"),
                    Endpoint::ProverSkeleton => Self::refuse(
                        "Statement",
                        label,
                        "value is outside the range its class admits",
                    ),
                };
                self.line(2, &refusal);
                self.line(1, "}");
            }
        }

        // The rows.
        let rows: Vec<Row> = self.document.rows.to_vec();
        let last = rows.len().checked_sub(1).ok_or("empty program")?;
        for (index, row) in rows.iter().enumerate() {
            self.emit_row(index, row, index == last)?;
        }
        match (self.document.endpoint, rows.last()) {
            (Endpoint::Verifier, Some(Row::Decide { .. })) => {}
            (Endpoint::Verifier, _) => return Err("the verifier frame must end in decide".into()),
            (Endpoint::ProverSkeleton, Some(Row::Finish { .. })) => {}
            (Endpoint::ProverSkeleton, _) => {
                return Err("the prover frame must end in finish".into())
            }
        }
        if let Some((reference, (expression, class))) = self.handles.iter().next() {
            return Err(format!(
                "handle {reference:?} ({expression} : {class}) is never consumed; every handle \
                 chain ends in a consuming hole before finish (zkc-E149's emit-time form)"
            ));
        }
        Ok(())
    }

    fn emit_row(&mut self, index: usize, row: &Row, is_last: bool) -> Result<(), String> {
        // The frame gate: each endpoint's wire-direction rows belong to
        // it alone. The carrier already refuses a mixed program; this is
        // the emitter reading the same rule off the endpoint field.
        let frame = match row {
            Row::Read { .. }
            | Row::AssertEq { .. }
            | Row::CheckCall { .. }
            | Row::ExpectEnd { .. }
            | Row::Decide { .. } => Some((Endpoint::Verifier, "verifier")),
            Row::Write { .. }
            | Row::HoleCall { .. }
            | Row::EndStream { .. }
            | Row::Finish { .. } => Some((Endpoint::ProverSkeleton, "prover")),
            _ => None,
        };
        if let Some((owner, name)) = frame {
            if owner != self.document.endpoint {
                return Err(format!(
                    "row {index}: '{}' is a {name}-frame row, and this document declares endpoint \
                     '{}' (zkc-E409's emit-time form)",
                    row_kind(row),
                    self.document.endpoint_name
                ));
            }
        }
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
                // Declared here, qualified by what the rest of the walk
                // will do to it — an init with nothing absorbing or
                // squeezing after it leaves a local nobody reads.
                self.line(1, &format!("let {SPONGE_QUALIFIER}sponge = {constructor};"));
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
                self.used.cursor = Use {
                    named: true,
                    mutated: true,
                };
                let implementation = self.class_impl(class)?;
                let width = implementation.wire_width();
                let used = self.referenced.contains(&(index, 1));
                let name = format!("{}r{index}_1", if used { "" } else { "_" });
                let ty = implementation.rust_type();
                let comment = format!(
                    "// [\"read\", \"{}\" : {}]",
                    rust::comment(label),
                    rust::comment(class)
                );
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
                        if let Some(modulus) = self.class_binding(class)?.modulus {
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
                self.used.sponge = Use {
                    named: true,
                    mutated: true,
                };
                self.used.challenges = Use {
                    named: true,
                    mutated: true,
                };
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
                    "// [\"squeeze\", \"{}\" : {}, count {count}, domain \"{}\"]",
                    rust::comment(label),
                    rust::comment(class),
                    rust::comment(domain)
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
                                &format!("let digest = sponge.squeeze({});", rust::literal(domain)),
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
                                &format!("let digest = sponge.squeeze({});", rust::literal(domain)),
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
                self.line(
                    1,
                    &format!("// [\"assert_eq\", \"{}\"]", rust::comment(label)),
                );
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
                self.line(
                    1,
                    &format!(
                        "// [\"check_call\", \"{}\" : {}]",
                        rust::comment(label),
                        rust::comment(kind)
                    ),
                );
                self.line(
                    1,
                    &format!(
                        "let tau_g2_{index} = zkc_rt::kzg::g2_from_hex({})",
                        rust::literal(&check.tau_g2_hex)
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
                self.used.cursor.named = true;
                self.line(1, "if !cursor.at_end() {");
                self.line(2, &Self::reject("ProofTrailingData"));
                self.line(1, "}");
                Ok(())
            }

            Row::Decide { sponge } => {
                if !is_last {
                    return Err(format!("row {index}: decide before the end of the program"));
                }
                if self.current_stream.is_some() {
                    return Err(format!(
                        "row {index}: decide with the proof stream still open; without \
                         expect_end the emitted verifier would accept trailing bytes"
                    ));
                }
                self.consume_sponge(*sponge, index, Ref::Res(index, 0))?;
                self.line(1, "Outcome::accept(challenges)");
                Ok(())
            }

            Row::Write {
                stream,
                value,
                label,
                class,
            } => {
                self.consume_stream(*stream, index, Some(Ref::Res(index, 0)))?;
                self.used.proof = Use {
                    named: true,
                    mutated: true,
                };
                let (expr, value_class) = self.value(*value, &format!("row {index} (write)"))?;
                let implementation = self.class_impl(class)?;
                match &value_class {
                    VClass::Doc(name) if self.class_impl(name)? == implementation => {}
                    // A toy algebra result is a plain u64 residue, which
                    // is exactly the toy codec's own value domain.
                    VClass::Algebra if implementation == ImplKind::ToyBe8 => {}
                    other => {
                        return Err(format!(
                            "row {index}: write '{label}' emits a {other:?} value on a \
                             '{class}' slot"
                        ))
                    }
                }
                self.line(
                    1,
                    &format!(
                        "// [\"write\", \"{}\" : {}]",
                        rust::comment(label),
                        rust::comment(class)
                    ),
                );
                // Emitted proofs are canonical by construction: the gate
                // runs before any byte reaches the wire, so a refused run
                // leaves no partial proof. Where the bound type cannot
                // hold a non-canonical value, the reference's post-encode
                // self-check has nothing left to test and is dropped.
                match implementation {
                    ImplKind::ToyBe8 => {
                        if let Some(modulus) = self.class_binding(class)?.modulus {
                            self.line(1, &format!("if {expr} >= {modulus}u64 {{"));
                            self.line(
                                2,
                                &Self::refuse(
                                    "Fill",
                                    label,
                                    "fill produced a value outside its class's range",
                                ),
                            );
                            self.line(1, "}");
                        }
                        self.line(
                            1,
                            &format!("proof.extend_from_slice(&zkc_rt::toy::frame_be8({expr}));"),
                        );
                    }
                    ImplKind::P3Word | ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                        let words = if implementation == ImplKind::P3Word {
                            format!("[{expr}]")
                        } else {
                            expr.clone()
                        };
                        self.line(1, &format!("if !zkc_rt::p3::words_canonical(&{words}) {{"));
                        self.line(
                            2,
                            &Self::refuse(
                                "Fill",
                                label,
                                "fill produced a word outside the canonical field range",
                            ),
                        );
                        self.line(1, "}");
                        self.line(
                            1,
                            &format!("zkc_rt::p3::encode_words(&{words}, &mut proof);"),
                        );
                    }
                    ImplKind::BlsFrBe32 => self.line(
                        1,
                        &format!("proof.extend_from_slice(&zkc_rt::kzg::fr_to_wire(&{expr}));"),
                    ),
                    ImplKind::BlsG1Be48 => self.line(
                        1,
                        &format!("proof.extend_from_slice(&zkc_rt::kzg::g1_to_wire(&{expr}));"),
                    ),
                }
                Ok(())
            }

            Row::HoleCall { .. } => self.emit_hole_call(index, row),

            Row::EndStream { stream } => {
                self.consume_stream(*stream, index, None)?;
                Ok(())
            }

            Row::Finish { sponge } => {
                if !is_last {
                    return Err(format!("row {index}: finish before the end of the program"));
                }
                if self.current_stream.is_some() {
                    return Err(format!(
                        "row {index}: finish with the proof stream still open"
                    ));
                }
                self.consume_sponge(*sponge, index, Ref::Res(index, 0))?;
                self.line(1, "Ok(Prove { proof, challenges })");
                Ok(())
            }
        }
    }

    /// One supplier call. The reference marshals operands by splitting
    /// the row's mixed list by type and hands the fill four vectors; the
    /// emitter does the same split once, checks it against the bound
    /// fill's signature, and writes a monomorphic call — so the
    /// too-few/surplus-result arms (zkc-E408) have no run-time form.
    fn emit_hole_call(&mut self, index: usize, row: &Row) -> Result<(), String> {
        let Row::HoleCall {
            inputs,
            results,
            label,
            kind,
            digest,
            params,
            semantic_params,
        } = row
        else {
            unreachable!("emit_hole_call is reached from the hole_call arm alone")
        };
        // The pre-walk pass sees a peek by its sponge result. A hole that
        // takes the sponge and does not hand it back has no such result,
        // so it arrives here — and naming the peek is more use than the
        // "names no value" the generic operand path would report.
        if inputs
            .iter()
            .any(|input| Some(*input) == self.current_sponge)
        {
            return Err(peeking_fill_refusal(index, label, kind));
        }
        let Some(hole) = self.binding.hole(digest).cloned() else {
            return Err(format!(
                "row {index}: hole '{label}' (kind '{kind}', contract {digest}) has no fill in \
                 binding '{}'; the reference profiles refuse this at run time (zkc-E407) and the \
                 emitter refuses it here",
                self.binding.name
            ));
        };
        let signature = hole.implementation.signature();
        if !params.is_empty() || !semantic_params.is_empty() {
            return Err(format!(
                "row {index}: hole '{label}' cites parameters {params:?} / {semantic_params:?}; \
                 no fill in this vocabulary takes any"
            ));
        }

        // Operands, position by position against the fill's own
        // parameter list — the emitted call is positional, so a row that
        // interleaves values and handles differently from the fill is a
        // refusal here rather than a type error in generated code.
        if inputs.len() != signature.inputs.len() {
            return Err(format!(
                "row {index}: hole '{label}' passes {} operands; the bound fill takes {}",
                inputs.len(),
                signature.inputs.len()
            ));
        }
        let mut arguments = Vec::new();
        for (position, (input, want)) in inputs.iter().zip(signature.inputs).enumerate() {
            let context = format!("row {index} (hole_call)");
            match want {
                Operand::Handle(class) => {
                    let (expression, bound) = self.take_handle(*input, &context)?;
                    if bound != *class {
                        return Err(format!(
                            "row {index}: hole '{label}' operand {position} has handle class \
                             '{bound}', not the contract's '{class}'"
                        ));
                    }
                    arguments.push(expression);
                }
                Operand::Value(want) => {
                    let (expression, value_class) = self.value(*input, &context)?;
                    match &value_class {
                        VClass::Doc(name) if self.class_impl(name)? == *want => {}
                        VClass::Algebra if *want == ImplKind::ToyBe8 => {}
                        other => {
                            return Err(format!(
                                "row {index}: hole '{label}' operand {position} has class \
                                 {other:?}, which is not the contract's {want:?}"
                            ))
                        }
                    }
                    arguments.push(expression);
                }
            }
        }

        // Results, bound back positionally across the mixed list.
        if results.len() != signature.results.len() {
            return Err(format!(
                "row {index}: hole '{label}' binds {} results; the bound fill returns {}",
                results.len(),
                signature.results.len()
            ));
        }
        let mut names = Vec::new();
        for (slot, (result, want)) in results.iter().zip(signature.results).enumerate() {
            let bare = format!("r{index}_{slot}");
            // A handle result is always consumed — the walk enforces
            // that — but a value result need not be, and an unused local
            // would warn in a warning-free crate.
            let mut name = bare.clone();
            match (result, want) {
                (Entry::Val(class), Operand::Value(want)) if self.class_impl(class)? == *want => {
                    if !self.referenced.contains(&(index, slot)) {
                        name = format!("_{bare}");
                    }
                    self.values
                        .insert(Ref::Res(index, slot), (bare, VClass::Doc(class.clone())));
                }
                (Entry::Handle(class), Operand::Handle(want)) if class == want => {
                    self.handles
                        .insert(Ref::Res(index, slot), (bare, class.clone()));
                }
                (bound, want) => {
                    return Err(format!(
                        "row {index}: hole '{label}' binds result {slot} as {bound:?}, which is \
                         not the contract's {want:?}"
                    ))
                }
            }
            names.push(name);
        }

        self.line(
            1,
            &format!(
                "// [\"hole_call\", \"{}\" : {}]",
                rust::comment(label),
                rust::comment(kind)
            ),
        );
        let (pattern, destructure) = match names.as_slice() {
            [] => {
                return Err(format!(
                    "row {index}: hole '{label}' binds no results; a fill with nothing to bind \
                     has no effect the frame can observe"
                ))
            }
            [single] => (single.clone(), "value".to_owned()),
            many => (format!("({})", many.join(", ")), "results".to_owned()),
        };
        self.line(
            1,
            &format!(
                "let {pattern} = match {}({}) {{",
                hole.implementation.path(),
                arguments.join(", ")
            ),
        );
        self.line(2, &format!("Ok({destructure}) => {destructure},"));
        self.line(
            2,
            &format!(
                "Err(message) => return Err(ProveError::Fill {{ label: {}.to_owned(), message }}),",
                rust::literal(label)
            ),
        );
        self.line(1, "};");
        Ok(())
    }

    fn algebra_operand(
        &mut self,
        reference: &Ref,
        index: usize,
        op: &str,
    ) -> Result<String, String> {
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
            "f_neg" | "f_add" | "f_mul" => self.used.field_modulus = true,
            _ => self.used.group_modulus = true,
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
        // The field and group operations of docs/spec/endpoints.md §4,
        // in the sequencing the reference executor also uses: f_add
        // reduces each operand before the sum; the modular helpers own
        // the rest.
        let expr = match op {
            "f_add" => {
                format!("zkc_rt::toy::addmod({left}, {right}, FIELD_MODULUS)")
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
        Row::Init { .. } | Row::Const { .. } => Vec::new(),
        Row::CheckCall { inputs, .. } | Row::HoleCall { inputs, .. } => inputs.clone(),
        Row::Absorb { sponge, value } => vec![*sponge, *value],
        Row::Squeeze { sponge, .. } => vec![*sponge],
        Row::Read { stream, .. } => vec![*stream],
        Row::FNeg { operand } => vec![*operand],
        Row::FAdd { lhs, rhs }
        | Row::FMul { lhs, rhs }
        | Row::GExp { lhs, rhs }
        | Row::GMul { lhs, rhs }
        | Row::AssertEq { lhs, rhs, .. } => vec![*lhs, *rhs],
        Row::Write { stream, value, .. } => vec![*stream, *value],
        Row::ExpectEnd { stream } | Row::EndStream { stream } => vec![*stream],
        Row::Decide { sponge } | Row::Finish { sponge } => vec![*sponge],
    }
}

/// The row's grammar tag, for diagnostics that quote it.
fn row_kind(row: &Row) -> &'static str {
    match row {
        Row::Init { .. } => "init",
        Row::Absorb { .. } => "absorb",
        Row::Squeeze { .. } => "squeeze",
        Row::Read { .. } => "read",
        Row::Const { .. } => "const",
        Row::FNeg { .. } => "f_neg",
        Row::FAdd { .. } => "f_add",
        Row::FMul { .. } => "f_mul",
        Row::GExp { .. } => "g_exp",
        Row::GMul { .. } => "g_mul",
        Row::AssertEq { .. } => "assert_eq",
        Row::CheckCall { .. } => "check_call",
        Row::ExpectEnd { .. } => "expect_end",
        Row::Decide { .. } => "decide",
        Row::Write { .. } => "write",
        Row::HoleCall { .. } => "hole_call",
        Row::EndStream { .. } => "end_stream",
        Row::Finish { .. } => "finish",
    }
}

/// The transcript peek (`docs/spec/endpoints.md` §6.2): `pow_search`
/// threads the live sponge through its fill so the grind can read the
/// state it is grinding against. No supplier vocabulary implements a
/// peeking fill — not here, and not in the reference executor, which
/// refuses the same shape as zkc-E407.
fn peeking_fill_refusal(index: usize, label: &str, kind: &str) -> String {
    format!(
        "row {index}: hole '{label}' (kind '{kind}') threads the transcript through its fill — \
         the read-only peek of the specification's §6.2. No supplier vocabulary implements \
         transcript-peeking fills yet, so this artifact's prover is not emittable; the reference \
         executor refuses the same shape (zkc-E407)"
    )
}

/// Emit-time supplier gates: every codec route and construction pin must
/// be realized by the binding before any code exists. The sponge is
/// checked where it is opened, in the `init` arm.
fn gate_suppliers(document: &Document, binding: &Binding) -> Result<(), String> {
    // Ahead of the per-row supplier gates, because a peeking fill is not
    // a gap a binding can close: it names the phase this emitter does
    // not implement, where a missing fill names one someone can write.
    // The sponge is consumed exactly once, so a hole that peeks must
    // hand it back — the result list is where that shows.
    for (index, row) in document.rows.iter().enumerate() {
        if let Row::HoleCall {
            results,
            label,
            kind,
            ..
        } = row
        {
            if results.contains(&Entry::Sponge) {
                return Err(peeking_fill_refusal(index, label, kind));
            }
        }
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

    let prover = document.endpoint == Endpoint::ProverSkeleton;
    let (crate_name, crate_ident) =
        rust::crate_name(&crate_name.map(str::to_owned).unwrap_or_else(|| {
            format!(
                "zkc-{}-{}",
                if prover { "prover" } else { "verifier" },
                &document.artifact_id[..12]
            )
        }))?;

    let mut walk = Walk {
        document,
        binding,
        values: Default::default(),
        handles: Default::default(),
        referenced: Default::default(),
        current_sponge: None,
        current_stream: None,
        body: String::new(),
        used: Used::default(),
    };
    walk.walk()?;
    let used = walk.used;
    let body = std::mem::take(&mut walk.body).replace(
        SPONGE_QUALIFIER,
        &format!("{}{}", used.sponge.prefix(), used.sponge.qualifier()),
    );

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
    for row in &document.rows {
        if let Row::HoleCall { digest, .. } = row {
            add_feature(
                binding.hole(digest).unwrap().implementation.feature(),
                &mut features,
            );
        }
    }
    features.sort_unstable();

    // ---- src/lib.rs ----
    let mut lib = String::new();
    let _ = writeln!(
        lib,
        "//! A zkc-emitted {} endpoint.\n//!\n\
         //! Generated from the canonical OIR document whose identity is\n\
         //! baked below; the emitter recomputed that identity from the\n\
         //! document bytes before reading a single row. This crate is the\n\
         //! projection's residual program: the transcript order, proof\n\
         //! ABI, {}, and {} of one sealed protocol, specialized\n\
         //! against one supplier binding. Do not edit; re-emit.\n",
        if prover { "prover" } else { "verifier" },
        if prover { "fills" } else { "checks" },
        if prover { "emission" } else { "decision" },
    );
    if prover {
        lib.push_str("pub use zkc_rt::{self, Payload, Prove, ProveError};\n\n");
    } else {
        lib.push_str("pub use zkc_rt::{self, Outcome, RejectClass, Verdict};\n");
        lib.push_str("use zkc_rt::ProofCursor;\n\n");
    }
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
        "pub const SOURCE_PIR_ID: &str = {};",
        rust::literal(&document.source)
    );
    let _ = writeln!(lib, "/// The supplier binding and its file digest.");
    let _ = writeln!(
        lib,
        "pub const BINDING: &str = {};",
        rust::literal(&binding.name)
    );
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
    if prover {
        lib.push_str("/// The verifier-local checks this endpoint delegates, as\n");
        lib.push_str("/// `[event position, discharge kind]`. Their schema, uniqueness,\n");
        lib.push_str("/// and discharge kinds were checked at emit time; that they\n");
        lib.push_str("/// exhaust the source obligations is authenticated only where the\n");
        lib.push_str("/// sealed protocol is also present, and is not claimed here.\n");
        let rows = document
            .counterparty
            .iter()
            .map(|(position, kind)| format!("({position}, {})", rust::literal(kind)))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(lib, "pub const COUNTERPARTY: &[(u64, &str)] = &[{rows}];");
    }
    lib.push('\n');
    if used.group_modulus || used.field_modulus {
        let algebra = binding.algebra.as_ref().unwrap();
        if used.group_modulus {
            let _ = writeln!(lib, "const GROUP_MODULUS: u64 = {};", algebra.group);
        }
        if used.field_modulus {
            let _ = writeln!(lib, "const FIELD_MODULUS: u64 = {};", algebra.field);
        }
        lib.push('\n');
    }

    lib.push_str("/// The public statement, typed and ordered as the endpoint ABI\n");
    lib.push_str("/// declares it; field names are the ABI labels, verbatim.\n");
    lib.push_str("/// Multi-limb values are little-endian 32-bit limbs.\n");
    lib.push_str("#[allow(non_snake_case)]\npub struct Statement {\n");
    for (label, class) in &document.statement {
        let ty = binding.class(class).unwrap().implementation.rust_type();
        let _ = writeln!(lib, "    pub {label}: {ty},");
    }
    lib.push_str("}\n\n");

    // Every local below is declared from what the walk recorded
    // emitting, never from a second reading of the rows: a body that
    // never squeezes, reads, writes, or names its statement gets a
    // local it can leave alone, and the emitted crate stays
    // warning-free without anyone predicting which rows do what.
    let statement_parameter = if used.statement {
        "statement"
    } else {
        "_statement"
    };
    if prover {
        lib.push_str("/// The opaque witness payloads, by their endpoint ABI labels.\n");
        lib.push_str("/// Every payload is named, so the reference executor's\n");
        lib.push_str("/// missing-payload refusal has no run-time form here; and every\n");
        lib.push_str("/// payload moves, so a handle cannot be spent twice.\n");
        lib.push_str("#[allow(non_snake_case)]\npub struct Witness {\n");
        for (label, class) in &document.witness_labels {
            let _ = writeln!(lib, "    /// Handle class `{}`.", rust::comment(class));
            let _ = writeln!(lib, "    pub {label}: Payload,");
        }
        lib.push_str("}\n\n");

        lib.push_str("/// One prover run: the emitted proof bytes and the ordered\n");
        lib.push_str("/// challenge log of the replica sponge. There is no verdict —\n");
        lib.push_str("/// acceptance belongs to verifiers — so a failure is a refusal\n");
        lib.push_str("/// naming the input or the fill responsible.\n");
        let _ = writeln!(
            lib,
            "pub fn prove({statement_parameter}: &Statement, {}: Witness) -> Result<Prove, ProveError> {{",
            if document.witness_labels.is_empty() {
                "_witness"
            } else {
                "witness"
            }
        );
        let _ = writeln!(
            lib,
            "    let {}challenges: Vec<String> = Vec::new();",
            used.challenges.qualifier()
        );
        let _ = writeln!(
            lib,
            "    let {}proof: Vec<u8> = Vec::new();",
            used.proof.qualifier()
        );
    } else {
        lib.push_str("/// One verifier execution over untrusted proof bytes: a verdict\n");
        lib.push_str("/// and the ordered challenge log. Statement range violations are\n");
        lib.push_str("/// `public_binding_failure`, exactly as the reference executor\n");
        lib.push_str("/// classifies them.\n");
        let _ = writeln!(
            lib,
            "pub fn verify({statement_parameter}: &Statement, proof: &[u8]) -> Outcome {{"
        );
        let _ = writeln!(
            lib,
            "    let {}challenges: Vec<String> = Vec::new();",
            used.challenges.qualifier()
        );
        let _ = writeln!(
            lib,
            "    let {}{}cursor = ProofCursor::new(proof);",
            used.cursor.prefix(),
            used.cursor.qualifier()
        );
    }
    lib.push_str(&body);
    lib.push_str("}\n");

    // ---- Cargo.toml ----
    let feature_list = features
        .iter()
        .map(|feature| format!("\"{feature}\""))
        .collect::<Vec<_>>()
        .join(", ");
    // Witness payloads exist only on the prover side, so only a prover
    // crate offers the memory-hygiene switch — and it offers it as a
    // feature rather than expecting anyone to edit generated code.
    let optional_features = if prover {
        "\n[features]\n\
         # Zero witness payloads on drop; see this crate's README for what\n\
         # that does and does not claim.\n\
         zeroize = [\"zkc-rt/zeroize\"]\n"
    } else {
        ""
    };
    let cargo_toml = format!(
        "# Generated by zkc-emit; do not edit — re-emit.\n\
         [package]\n\
         name = \"{crate_name}\"\n\
         version = \"0.0.0\"\n\
         edition = \"2021\"\n\
         \n\
         [dependencies]\n\
         zkc-rt = {{ path = \"{rt_path}\", default-features = false, features = [{feature_list}] }}\n\
         {optional_features}"
    );

    // ---- README.md ----
    // Written as literal markdown rather than assembled, because this
    // text is the emitted crate's only statement of what it does not
    // claim, and it should read the same in the source as on the page.
    let entry_point = if prover {
        r"`prove(statement, witness)` returns the emitted proof bytes and the
ordered challenge log, or a refusal naming the statement value or fill
responsible. There is no verdict channel: acceptance belongs to
verifiers. Supplier resolution happened at emit time, so no run-time
outcome means `no supplier`.

## What this endpoint does not do

- **Secrets.** Witness payloads pass through as opaque bytes. The
  specification places confidentiality with the provider, runtime, and
  target (`docs/spec/endpoints.md` §6.4); the bound fills are test-grade
  and variable-time, and a deployment supplier owns its own
  constant-time discipline. Building this crate with the `zeroize`
  feature makes `Payload` zero on drop; without it, nothing is claimed
  either way, because memory hygiene is a property of a whole call
  chain, not of one type.
- **Nonces.** Nonce material arrives inside the witness payload.
  Deriving it, and never reusing it, is the caller's — for a
  Schnorr-shaped protocol, nonce reuse across two statements discloses
  the witness. Deterministic derivation in the style of RFC 6979 or
  EdDSA is the deployment-grade pattern; this crate neither generates
  nor checks nonces.
- **Witness computation.** Nothing here computes a witness from a
  relation. That layer is upstream, and the payload boundary is exactly
  where it stops.
- **Counterparty coverage.** The `COUNTERPARTY` rows say which checks
  the verifier performs. Their schema, uniqueness, and discharge kinds
  were checked at emit time; that they exhaust the source obligations is
  authenticated only where the sealed protocol is also present (§6.1).
"
    } else {
        r"`verify(statement, proof)` returns the verdict and the ordered
challenge log. Reject classes are the normative set of
`docs/spec/endpoints.md` §4; supplier resolution happened at emit time,
so no run-time outcome means `cannot judge`.
"
    };
    let readme = format!(
        "# {crate_name}\n\n\
         A zkc-emitted {kind} endpoint. Generated — do not edit; re-emit.\n\n\
         ## Identity chain\n\n\
         | Fact | Value |\n|---|---|\n\
         | OIR artifact id | `{artifact}` |\n\
         | OIR semantic id | `{semantic}` |\n\
         | Sealed source protocol | `{source}` |\n\
         | Supplier binding | `{binding_name}` (file sha256 `{binding_digest}`) |\n\
         | Emitter | zkc-emit {version} |\n\n\
         {entry_point}\n\
         ## Scope\n\n\
         Behavior under this binding, at these pins, established by the\n\
         enclosed conformance vectors. This crate makes no claim of\n\
         protocol soundness, zero knowledge, or conformance beyond those\n\
         vectors; those judgments live with the sealed protocol artifact,\n\
         under the identities above.\n",
        kind = if prover { "prover" } else { "verifier" },
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
    alias: &str,
    name: &str,
    statement: &[(String, String)],
) -> Result<String, String> {
    let mut fields = Vec::new();
    for (label, class) in &document.statement {
        let implementation = binding.class(class).unwrap().implementation;
        let text = statement
            .iter()
            .find(|(bound, _)| bound == label)
            .map(|(_, value)| value.as_str())
            .ok_or_else(|| format!("vector '{name}' has no statement value for '{label}'"))?;
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
                    "{alias}::zkc_rt::kzg::{constructor}(&[{list}])\n            .expect(\"a canonical statement wire value\")"
                )
            }
        };
        fields.push(format!("{label}: {literal}"));
    }
    Ok(format!("{alias}::Statement {{ {} }}", fields.join(", ")))
}

/// The borrowed kernels a generated suite pins before replaying a single
/// vector. A kernel that drifts derives different challenges or accepts
/// different proofs, and the vectors alone would not say which.
fn kernel_self_checks(document: &Document, binding: &Binding, alias: &str) -> String {
    let mut out = String::new();
    if binding.sponge_impl == SpongeImpl::P3LenpadDuplex {
        let _ = writeln!(
            out,
            "#[test]\nfn permutation_known_answer() {{\n    \
             {alias}::zkc_rt::p3::permutation_self_check();\n}}\n"
        );
    }
    let pairing = document.codecs.iter().any(|(class, _)| {
        matches!(
            binding.class(class).map(|bound| bound.implementation),
            Some(ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48)
        )
    });
    if pairing {
        let _ = writeln!(
            out,
            "#[test]\nfn pairing_is_nondegenerate() {{\n    \
             {alias}::zkc_rt::kzg::pairing_self_check();\n}}\n"
        );
    }
    out
}

/// Lowercase-hex payload text to a Rust byte-slice literal.
fn hex_literal(name: &str, what: &str, hex: &str) -> Result<String, String> {
    if !hex.len().is_multiple_of(2)
        || !hex
            .chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
    {
        return Err(format!("vector '{name}' {what} is not lowercase hex"));
    }
    Ok((0..hex.len())
        .step_by(2)
        .map(|at| format!("0x{}", &hex[at..at + 2]))
        .collect::<Vec<_>>()
        .join(", "))
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
    let cases = match (&vectors.cases, document.endpoint) {
        (Cases::Verifier(cases), Endpoint::Verifier) => cases,
        (Cases::Prover(cases), Endpoint::ProverSkeleton) => {
            return emit_prover_conformance(
                document,
                binding,
                vectors.artifact_id.as_str(),
                cases,
                crate_ident,
            )
        }
        _ => {
            return Err(format!(
                "the vectors file describes the other endpoint; this document is \
                 '{}'",
                document.endpoint_name
            ))
        }
    };
    for case in cases {
        let admitted = case.expect == "accept" || REJECT_CLASSES.contains(&case.expect.as_str());
        if !admitted {
            return Err(format!(
                "vector '{}' expects '{}', which is not a verdict: the reject classes are {}",
                case.name,
                case.expect,
                REJECT_CLASSES.join(", ")
            ));
        }
    }
    if !cases.iter().any(|case| case.expect == "accept") {
        return Err(
            "the vectors file carries no accepting vector; a refusal battery without a \
             positive control asserts nothing"
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

    out.push_str(&kernel_self_checks(document, binding, "verifier"));

    let _ = writeln!(
        out,
        "#[test]\nfn vectors_bind_this_artifact() {{\n    assert_eq!(verifier::ARTIFACT_ID, \"{}\");\n}}\n",
        vectors.artifact_id
    );

    out.push_str("#[test]\nfn golden_vectors() {\n");
    for case in cases {
        let statement =
            statement_literal(document, binding, "verifier", &case.name, &case.statement)?;
        let bytes = hex_literal(&case.name, "proof", &case.proof_hex)?;
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
            "    run(\n        {:?},\n        {statement},\n        &[{bytes}],\n        {:?},\n        {challenges},\n    );",
            case.name, case.expect
        );
    }
    out.push_str("}\n");
    Ok(out)
}

fn emit_prover_conformance(
    document: &Document,
    binding: &Binding,
    artifact_id: &str,
    cases: &[ProverCase],
    crate_ident: &str,
) -> Result<String, String> {
    if !cases.iter().any(|case| case.expect == "ok") {
        return Err(
            "the vectors file carries no producing vector; a refusal battery without a \
             positive control asserts nothing"
                .into(),
        );
    }

    let mut out = String::new();
    out.push_str("// Generated conformance suite: the committed golden vectors, replayed\n");
    out.push_str("// against the emitted endpoint. The same inputs drive the reference\n");
    out.push_str("// executor (zkc-run --prove), so byte equality here is the differential\n");
    out.push_str("// gate between the emitted program and the reference semantics — a\n");
    out.push_str("// stronger gate than any verdict comparison, since a prover's whole\n");
    out.push_str("// output is under test.\n\n");
    let _ = writeln!(out, "use {crate_ident} as prover;\n");

    // Each harness is written only when the corpus has a case for it;
    // an unused one would warn, and the emitted crates are warning-free.
    if cases.iter().any(|case| case.expect == "ok") {
        out.push_str("fn produce(name: &str, statement: prover::Statement, witness: prover::Witness, proof: &[u8], challenges: &[&str]) {\n");
        out.push_str("    let produced = match prover::prove(&statement, witness) {\n");
        out.push_str("        Ok(produced) => produced,\n");
        out.push_str("        Err(error) => panic!(\"vector '{name}': {error}\"),\n");
        out.push_str("    };\n");
        out.push_str("    assert_eq!(produced.proof, proof, \"vector '{name}' proof bytes\");\n");
        out.push_str("    let logged: Vec<&str> = produced.challenges.iter().map(String::as_str).collect();\n");
        out.push_str("    assert_eq!(logged, challenges, \"vector '{name}' challenge log\");\n");
        out.push_str("}\n\n");
    }

    if cases.iter().any(|case| case.expect != "ok") {
        out.push_str("// A refused run emits nothing: the gates that classify a refusal all\n");
        out.push_str("// run before the value they judge reaches the wire.\n");
        out.push_str("fn refuse(name: &str, statement: prover::Statement, witness: prover::Witness, kind: &str, label: &str, message: &str) {\n");
        out.push_str("    match prover::prove(&statement, witness) {\n");
        out.push_str(
            "        Ok(_) => panic!(\"vector '{name}': expected a refusal, got a proof\"),\n",
        );
        out.push_str("        Err(error) => {\n");
        out.push_str(
            "            assert_eq!(error.kind(), kind, \"vector '{name}' refusal kind\");\n",
        );
        out.push_str(
            "            assert_eq!(error.label(), label, \"vector '{name}' refusal label\");\n",
        );
        out.push_str("            assert_eq!(error.message(), message, \"vector '{name}' refusal message\");\n");
        out.push_str("        }\n");
        out.push_str("    }\n");
        out.push_str("}\n\n");
    }

    out.push_str(&kernel_self_checks(document, binding, "prover"));

    let _ = writeln!(
        out,
        "#[test]\nfn vectors_bind_this_artifact() {{\n    assert_eq!(prover::ARTIFACT_ID, \"{artifact_id}\");\n}}\n"
    );

    out.push_str("#[test]\nfn golden_vectors() {\n");
    for case in cases {
        let statement =
            statement_literal(document, binding, "prover", &case.name, &case.statement)?;
        let mut payloads = Vec::new();
        for (label, _) in &document.witness_labels {
            let hex = case
                .witness
                .iter()
                .find(|(bound, _)| bound == label)
                .map(|(_, hex)| hex.as_str())
                .ok_or_else(|| {
                    format!(
                        "vector '{}' has no witness payload for '{label}'",
                        case.name
                    )
                })?;
            // The hex boundary is the caller's, exactly as it is on the
            // reference executor's command line.
            let bytes = hex_literal(&case.name, "witness payload", hex)?;
            payloads.push(format!("{label}: prover::Payload::new(vec![{bytes}])"));
        }
        let witness = format!("prover::Witness {{ {} }}", payloads.join(", "));
        match case.expect.as_str() {
            "ok" => {
                let bytes = hex_literal(&case.name, "proof", &case.proof_hex)?;
                let challenges = case
                    .challenges
                    .iter()
                    .map(|entry| format!("{entry:?}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    out,
                    "    produce(\n        {:?},\n        {statement},\n        {witness},\n        &[{bytes}],\n        &[{challenges}],\n    );",
                    case.name
                );
            }
            kind @ ("statement" | "fill") => {
                if !case.proof_hex.is_empty() || !case.challenges.is_empty() {
                    return Err(format!(
                        "vector '{}' expects a refusal but carries proof or challenge \
                         expectations; a refused run produces neither",
                        case.name
                    ));
                }
                if case.label.is_empty() || case.message.is_empty() {
                    return Err(format!(
                        "vector '{}' expects a refusal but does not say which ABI label it \
                         names or what it reports",
                        case.name
                    ));
                }
                let _ = writeln!(
                    out,
                    "    refuse(\n        {:?},\n        {statement},\n        {witness},\n        {kind:?},\n        {:?},\n        {:?},\n    );",
                    case.name, case.label, case.message
                );
            }
            other => {
                return Err(format!(
                    "vector '{}' expects '{other}', which is neither 'ok' nor a refusal kind",
                    case.name
                ))
            }
        }
    }
    out.push_str("}\n");
    Ok(out)
}

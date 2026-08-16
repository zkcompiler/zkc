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

pub(crate) struct Walk<'a> {
    document: &'a Document,
    binding: &'a Binding,
    /// Rust expression and class per value reference.
    values: HashMap<Ref, (String, VClass)>,
    /// Counted bindings and their declared element counts: a vector
    /// value and a scalar of the same class are different shapes, and
    /// mis-wiring one into the other is a refusal here, never a type
    /// error in generated code. Populated only through `bind_value`,
    /// so a producer cannot record a class and forget the shape.
    vector_counts: HashMap<Ref, u64>,
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
pub(crate) struct Use {
    named: bool,
    mutated: bool,
}

impl Use {
    /// `""`, `"mut "`, or the `_` prefix an unnamed local needs.
    pub(crate) fn qualifier(self) -> &'static str {
        if self.mutated {
            "mut "
        } else {
            ""
        }
    }

    pub(crate) fn prefix(self) -> &'static str {
        if self.named {
            ""
        } else {
            "_"
        }
    }
}

#[derive(Default, Clone, Copy)]
pub(crate) struct Used {
    pub(crate) sponge: Use,
    pub(crate) cursor: Use,
    pub(crate) challenges: Use,
    pub(crate) proof: Use,
    pub(crate) statement: bool,
    pub(crate) group_modulus: bool,
    pub(crate) field_modulus: bool,
}

/// The BLS12-381 scalar-field order: the only sample space the `fr`
/// challenge derivation is defined over.
const BLS12_381_R_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

impl<'a> Walk<'a> {
    /// The one producer of value bindings: name, class, and — for a
    /// counted binding — the element count land together.
    fn bind_value(&mut self, at: Ref, name: String, class: VClass, count: Option<u64>) {
        self.values.insert(at, (name, class));
        if let Some(count) = count {
            self.vector_counts.insert(at, count);
        }
    }

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
        let statement = self.absorb_statement("sponge", expr, class, row)?;
        self.line(1, &statement);
        self.used.sponge = Use {
            named: true,
            mutated: true,
        };
        Ok(())
    }

    /// The absorb statement for `target`, one framing per implementation
    /// — the single source the live spine and a pow_search trial clone
    /// both write their absorbs from, so the trial's framing cannot
    /// drift from the check the verifier performs.
    fn absorb_statement(
        &self,
        target: &str,
        expr: &str,
        class: &VClass,
        row: usize,
    ) -> Result<String, String> {
        match class {
            VClass::Algebra => Err(format!(
                "row {row}: absorbing an algebra result has no framing codec; \
                 no admitted artifact does this"
            )),
            VClass::Doc(name) => Ok(match self.class_impl(name)? {
                ImplKind::ToyBe8 => {
                    format!("{target}.absorb(&zkc_rt::toy::frame_be8({expr}));")
                }
                ImplKind::P3Word => format!("{target}.absorb(&[{expr}]);"),
                ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                    format!("{target}.absorb(&{expr});")
                }
                ImplKind::BlsFrBe32 => {
                    format!("{target}.absorb(&zkc_rt::kzg::fr_to_wire(&{expr}));")
                }
                ImplKind::BlsG1Be48 => {
                    format!("{target}.absorb(&zkc_rt::kzg::g1_to_wire(&{expr}));")
                }
            }),
        }
    }

    pub(crate) fn walk(&mut self) -> Result<(), String> {
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
                // The statement ABI stays scalar: no minted artifact
                // binds a counted statement value.
                Entry::ValVec(class, _) => {
                    return Err(format!(
                        "entry argument {index} is a counted vector of class \
                         '{class}', but the statement ABI is scalar"
                    ))
                }
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
            Row::Init { sponge, iv } => self.emit_init(index, sponge, iv),

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
                count,
            } => self.emit_read(index, *stream, label, class, *count),

            Row::Squeeze {
                sponge,
                label,
                class,
                count,
                domain,
                rule,
                space,
            } => self.emit_squeeze(index, *sponge, label, class, *count, domain, rule, space),

            Row::Const { value, class } => self.emit_const(index, value, class),

            Row::FNeg { operand } => self.algebra_unary(index, operand, "f_neg"),
            Row::FAdd { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "f_add"),
            Row::FMul { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "f_mul"),
            Row::GExp { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "g_exp"),
            Row::GMul { lhs, rhs } => self.algebra_binary(index, lhs, rhs, "g_mul"),

            Row::AssertEq { lhs, rhs, label } => self.emit_assert_eq(index, *lhs, *rhs, label),

            Row::CheckCall {
                inputs,
                label,
                kind,
                digest,
                params,
            } => self.emit_check_call(index, inputs, label, kind, digest, params),

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
                count,
            } => self.emit_write(index, *stream, *value, label, class, *count),

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

    fn emit_init(&mut self, index: usize, sponge: &str, iv: &str) -> Result<(), String> {
        if index != 0 || self.current_sponge.is_some() {
            return Err(format!("row {index}: init must be the single first row"));
        }
        if sponge != self.binding.sponge_construction || *iv != self.binding.sponge_iv {
            return Err(format!(
                "row {index}: sponge '{sponge}' with iv '{iv}' has no supplier in \
                 binding '{}' (it supplies '{}' with iv '{}')",
                self.binding.name, self.binding.sponge_construction, self.binding.sponge_iv
            ));
        }
        let constructor = match (self.binding.sponge_impl, iv) {
            (SpongeImpl::ToyDuplex, "artifact-id") => {
                "zkc_rt::toy::ToyDuplex::new(SOURCE_PIR_ID)".to_owned()
            }
            (SpongeImpl::P3LenpadDuplex, "artifact-id") => {
                "zkc_rt::p3::P3Duplex::new(SOURCE_PIR_ID)".to_owned()
            }
            (SpongeImpl::P3LenpadDuplex, "zero") => "zkc_rt::p3::P3Duplex::new(\"\")".to_owned(),
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

    fn emit_read(
        &mut self,
        index: usize,
        stream: Ref,
        label: &str,
        class: &str,
        count: u64,
    ) -> Result<(), String> {
        self.consume_stream(stream, index, Some(Ref::Res(index, 0)))?;
        self.used.cursor = Use {
            named: true,
            mutated: true,
        };
        let implementation = self.class_impl(class)?;
        let width = implementation.wire_width();
        let used = self.referenced.contains(&(index, 1));
        let name = format!("{}r{index}_1", if used { "" } else { "_" });
        let ty = implementation.rust_type();
        if count > 1 {
            // A counted read decodes `count` elements at the class's
            // fixed width, in order — the schedule is the only width
            // authority (docs/spec/carrier.md §7). The whole vector is
            // one binding, exactly as a vector squeeze's.
            let decode = match implementation {
                ImplKind::P3Word => "zkc_rt::p3::decode_words::<1>(wire)[0]".to_owned(),
                ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                    format!(
                        "zkc_rt::p3::decode_words::<{}>(wire)",
                        implementation.limbs()
                    )
                }
                other => {
                    return Err(format!(
                        "row {index}: counted reads are implemented for the \
                         BabyBear classes only (class '{class}' has {other:?})"
                    ))
                }
            };
            let canonical = match implementation {
                ImplKind::P3Word => "element >= zkc_rt::p3::BB".to_owned(),
                _ => "!zkc_rt::p3::words_canonical(&element)".to_owned(),
            };
            self.line(
                1,
                &format!(
                    "// [\"read_vec\", \"{}\" : {} x {count}]",
                    rust::comment(label),
                    rust::comment(class)
                ),
            );
            self.line(1, &format!("let {name}: Vec<{ty}> = {{"));
            self.line(
                2,
                &format!("let mut elements = Vec::with_capacity({count});"),
            );
            self.line(2, &format!("for _ in 0..{count} {{"));
            self.line(
                3,
                &format!("let element: {ty} = match cursor.take({width}) {{"),
            );
            self.line(4, &format!("Some(wire) => {decode},"));
            self.line(4, &Self::reject_arm("AbiDecodeFailure"));
            self.line(3, "};");
            self.line(3, &format!("if {canonical} {{"));
            self.line(4, &Self::reject("AbiDecodeFailure"));
            self.line(3, "}");
            self.line(3, "elements.push(element);");
            self.line(2, "}");
            self.line(2, "elements");
            self.line(1, "};");
            let bare = format!("r{index}_1");
            self.bind_value(
                Ref::Res(index, 1),
                bare,
                VClass::Doc(class.to_owned()),
                Some(count),
            );
            return Ok(());
        }
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
            .insert(Ref::Res(index, 1), (bare, VClass::Doc(class.to_owned())));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_squeeze(
        &mut self,
        index: usize,
        sponge: Ref,
        label: &str,
        class: &str,
        count: u64,
        domain: &str,
        rule: &str,
        space: &str,
    ) -> Result<(), String> {
        self.consume_sponge(sponge, index, Ref::Res(index, 0))?;
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
        match (rule, count) {
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
        if count == 1 {
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
                        &format!("let value = zkc_rt::toy::derive_be8(&digest, {space}u64);"),
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
                    self.line(
                        2,
                        &format!(
                            "let value = zkc_rt::p3::squeeze_low_bits(&mut sponge, {space}u64);"
                        ),
                    );
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
                .insert(Ref::Res(index, 1), (bare, VClass::Doc(class.to_owned())));
        } else {
            // A counted vector is one event producing one log entry and
            // one SSA binding: the whole draw list is the value the
            // counted check contracts consume (docs/spec/carrier.md §7).
            if implementation != ImplKind::P3Word {
                return Err(format!(
                    "row {index}: counted squeezes are implemented for the word \
                     derivation only (class '{class}' has {implementation:?})"
                ));
            }
            let space: u64 = space
                .parse()
                .map_err(|_| format!("row {index}: sample space '{space}' does not fit u64"))?;
            if space < 2 {
                return Err(format!("row {index}: sample space {space} below 2"));
            }
            let used = self.referenced.contains(&(index, 1));
            let name = format!("{}r{index}_1", if used { "" } else { "_" });
            self.line(1, &format!("let {name}: Vec<u32> = {{"));
            self.line(2, "let mut entry = String::new();");
            self.line(2, &format!("let mut draws = Vec::with_capacity({count});"));
            self.line(2, &format!("for draw in 0..{count} {{"));
            self.line(
                3,
                &format!("let value = zkc_rt::p3::squeeze_low_bits(&mut sponge, {space}u64);"),
            );
            self.line(3, "if draw > 0 { entry.push('|'); }");
            self.line(3, "entry.push_str(&value.to_string());");
            self.line(3, "draws.push(value);");
            self.line(2, "}");
            self.line(2, "challenges.push(entry);");
            self.line(2, "draws");
            self.line(1, "};");
            let bare = format!("r{index}_1");
            self.bind_value(
                Ref::Res(index, 1),
                bare,
                VClass::Doc(class.to_owned()),
                Some(count),
            );
        }
        Ok(())
    }

    fn emit_const(&mut self, index: usize, value: &str, class: &str) -> Result<(), String> {
        let implementation = self.class_impl(class)?;
        let used = self.referenced.contains(&(index, 0));
        let name = format!("{}r{index}_0", if used { "" } else { "_" });
        let literal = match implementation {
            ImplKind::ToyBe8 => {
                let parsed: u64 = value
                    .parse()
                    .map_err(|_| format!("row {index}: constant '{value}' is not a decimal u64"))?;
                format!("{parsed}u64")
            }
            ImplKind::P3Word => {
                let parsed: u32 = value
                    .parse()
                    .map_err(|_| format!("row {index}: constant '{value}' is not a decimal u32"))?;
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
            (format!("r{index}_0"), VClass::Doc(class.to_owned())),
        );
        Ok(())
    }

    fn emit_assert_eq(
        &mut self,
        index: usize,
        lhs: Ref,
        rhs: Ref,
        label: &str,
    ) -> Result<(), String> {
        let (left, left_class) = self.value(lhs, &format!("row {index} (assert_eq)"))?;
        let (right, right_class) = self.value(rhs, &format!("row {index} (assert_eq)"))?;
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

    fn emit_check_call(
        &mut self,
        index: usize,
        inputs: &[Ref],
        label: &str,
        kind: &str,
        digest: &str,
        params: &[String],
    ) -> Result<(), String> {
        let Some(check) = self.binding.check(digest).cloned() else {
            return Err(format!(
                "row {index}: opaque check '{label}' (kind '{kind}', contract {digest}) \
                 has no executable adapter in binding '{}'; the reference profiles \
                 refuse this at run time (zkc-E403) and the emitter refuses it here",
                self.binding.name
            ));
        };
        // The KZG contracts' one static parameter is the suite; the
        // adapter must implement exactly the suite the row cites. The
        // BabyBear contracts' parameters travel into the call as
        // decimal literals below.
        if let Some(suite) = &check.suite {
            if params.len() != 1 || &params[0] != suite {
                return Err(format!(
                    "row {index}: check '{label}' cites parameters {params:?}; the bound \
                     adapter implements suite '{suite}'"
                ));
            }
        }
        let mut arguments = Vec::new();
        for input in inputs {
            arguments.push(self.value(*input, &format!("row {index} (check_call)"))?);
        }
        let vector_inputs: Vec<bool> = inputs
            .iter()
            .map(|input| self.vector_counts.contains_key(input))
            .collect();
        let expect_kind = |walk: &Self,
                           argument: &(String, VClass),
                           want: ImplKind,
                           role: &str|
         -> Result<String, String> {
            match &argument.1 {
                VClass::Doc(name) if walk.class_impl(name)? == want => Ok(argument.0.clone()),
                other => Err(format!(
                    "row {index}: check '{label}' {role} operand has class {other:?}, \
                     which is not the contract's {want:?}"
                )),
            }
        };
        // A vector binding and a scalar of the same class are different
        // shapes; the marshal refuses a mismatch here rather than
        // leaving it to the generated crate's type errors.
        let expect_shape = |positions: &[(usize, bool)]| -> Result<(), String> {
            for &(position, wants_vector) in positions {
                if vector_inputs[position] != wants_vector {
                    return Err(format!(
                        "row {index}: check '{label}' operand {position} is {}, but its \
                         segment takes {}",
                        if vector_inputs[position] {
                            "a counted vector"
                        } else {
                            "a scalar"
                        },
                        if wants_vector {
                            "a counted vector"
                        } else {
                            "a scalar"
                        }
                    ));
                }
            }
            Ok(())
        };
        self.line(
            1,
            &format!(
                "// [\"check_call\", \"{}\" : {}]",
                rust::comment(label),
                rust::comment(kind)
            ),
        );
        if let Some(tau) = &check.tau_g2_hex {
            self.line(
                1,
                &format!(
                    "let tau_g2_{index} = zkc_rt::kzg::g2_from_hex({})",
                    rust::literal(tau)
                ),
            );
            self.line(
                1,
                "    .expect(\"the binding-pinned tau_g2 point parses\");",
            );
        }
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
                let proof = expect_kind(self, &arguments[2 * n + 2], ImplKind::BlsG1Be48, "proof")?;
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
            CheckImpl::P3MerkleMultiOpening => {
                // The contract declares no static parameters; a row
                // citing any is mis-wired, refused here like every
                // other shape defect.
                if !params.is_empty() {
                    return Err(format!(
                        "row {index}: check '{label}' cites parameters {params:?}; the \
                         multi-opening contract declares none"
                    ));
                }
                // Segment order: root, indices, leaves, paths — one
                // vector binding per counted segment.
                if arguments.len() != 4 {
                    return Err(format!(
                        "row {index}: check '{label}' has {} operands; the multi-opening \
                         contract takes 4",
                        arguments.len()
                    ));
                }
                expect_shape(&[(0, false), (1, true), (2, true), (3, true)])?;
                let root = expect_kind(self, &arguments[0], ImplKind::P3Digest8, "root")?;
                let indices = expect_kind(self, &arguments[1], ImplKind::P3Word, "indices")?;
                let leaves = expect_kind(self, &arguments[2], ImplKind::P3Word, "leaves")?;
                let paths = expect_kind(self, &arguments[3], ImplKind::P3Digest8, "paths")?;
                self.line(
                    1,
                    &format!(
                        "if !zkc_rt::p3::merkle_multi_opening_accepts(&{root}, &{indices}, \
                         &{leaves}, &{paths}) {{"
                    ),
                );
                self.line(2, &Self::reject("CheckFailure"));
                self.line(1, "}");
            }
            CheckImpl::P3FriQueryConsistency => {
                // Parameter order is the contract's lexical order:
                // log_blowup, log_final_poly_len.
                if params.len() != 2
                    || params.iter().any(|parameter| {
                        parameter.is_empty() || !parameter.chars().all(|c| c.is_ascii_digit())
                    })
                {
                    return Err(format!(
                        "row {index}: check '{label}' cites parameters {params:?}; the \
                         consistency adapter reads two decimal logs"
                    ));
                }
                // One declarative segment table drives the shape gate,
                // the kind checks, and the slicing — the operand count
                // is 6 + 4k, so the fold depth falls out first.
                if arguments.len() < 10 || (arguments.len() - 6) % 4 != 0 {
                    return Err(format!(
                        "row {index}: check '{label}' has {} operands; the consistency \
                         contract takes 6 + 4k",
                        arguments.len()
                    ));
                }
                let rounds = (arguments.len() - 6) / 4;
                let segments: Vec<(&str, usize, ImplKind, bool)> = vec![
                    ("zeta", 1, ImplKind::P3Ext4, false),
                    ("opened", 1, ImplKind::P3Ext4, false),
                    ("alpha", 1, ImplKind::P3Ext4, false),
                    ("betas", rounds, ImplKind::P3Ext4, false),
                    ("final", 1, ImplKind::P3Ext4, false),
                    ("indices", 1, ImplKind::P3Word, true),
                    ("leaves", 1, ImplKind::P3Word, true),
                    ("roots", rounds, ImplKind::P3Digest8, false),
                    ("siblings", rounds, ImplKind::P3Ext4, true),
                    ("round_paths", rounds, ImplKind::P3Digest8, true),
                ];
                let mut names: Vec<Vec<String>> = Vec::new();
                let mut position = 0usize;
                for &(role, len, kind, wants_vector) in &segments {
                    let mut group = Vec::new();
                    for _ in 0..len {
                        expect_shape(&[(position, wants_vector)])?;
                        group.push(expect_kind(self, &arguments[position], kind, role)?);
                        position += 1;
                    }
                    names.push(group);
                }
                let flatten = |group: &[String]| -> String {
                    group
                        .iter()
                        .map(|name| format!("{name}.as_slice()"))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                // The per-round vectors flatten round-major, exactly
                // the wire's own order.
                self.line(
                    1,
                    &format!("let siblings_{index} = [{}].concat();", flatten(&names[8])),
                );
                self.line(
                    1,
                    &format!(
                        "let round_paths_{index} = [{}].concat();",
                        flatten(&names[9])
                    ),
                );
                self.line(
                    1,
                    &format!(
                        "if !zkc_rt::p3::fri_query_consistency_accepts({}usize, {}usize, \
                         {}, {}, {}, &[{}], &[{}], &{}, &{}, &[{}], &siblings_{index}, \
                         &round_paths_{index}) {{",
                        params[0],
                        params[1],
                        names[0][0],
                        names[1][0],
                        names[2][0],
                        names[3].join(", "),
                        names[4][0],
                        names[5][0],
                        names[6][0],
                        names[7].join(", ")
                    ),
                );
                self.line(2, &Self::reject("CheckFailure"));
                self.line(1, "}");
            }
        }
        Ok(())
    }

    fn emit_write(
        &mut self,
        index: usize,
        stream: Ref,
        value: Ref,
        label: &str,
        class: &str,
        count: u64,
    ) -> Result<(), String> {
        self.consume_stream(stream, index, Some(Ref::Res(index, 0)))?;
        self.used.proof = Use {
            named: true,
            mutated: true,
        };
        let (expr, value_class) = self.value(value, &format!("row {index} (write)"))?;
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
        if count > 1 {
            // A counted write encodes its vector element by element in
            // order, each behind the same canonicality gate; the row's
            // count is the schedule's, so a fill whose vector disagrees
            // is refused before any byte reaches the wire.
            match self.vector_counts.get(&value) {
                Some(declared) if *declared == count => {}
                Some(declared) => {
                    return Err(format!(
                        "row {index}: write '{label}' declares count {count}, but its \
                         value carries {declared} element(s)"
                    ))
                }
                None => {
                    return Err(format!(
                        "row {index}: write '{label}' declares count {count}, but its \
                         value is a scalar"
                    ))
                }
            }
            if !matches!(
                implementation,
                ImplKind::P3Word | ImplKind::P3Ext4 | ImplKind::P3Digest8
            ) {
                return Err(format!(
                    "row {index}: counted writes are implemented for the BabyBear \
                     classes only (class '{class}' has {implementation:?})"
                ));
            }
            self.line(
                1,
                &format!(
                    "// [\"write_vec\", \"{}\" : {} x {count}]",
                    rust::comment(label),
                    rust::comment(class)
                ),
            );
            self.line(1, &format!("if {expr}.len() != {count} {{"));
            self.line(
                2,
                &Self::refuse(
                    "Fill",
                    label,
                    "fill returned a vector whose length is not the schedule's count",
                ),
            );
            self.line(1, "}");
            self.line(1, &format!("for element in &{expr} {{"));
            let words = if implementation == ImplKind::P3Word {
                "[*element]".to_owned()
            } else {
                "*element".to_owned()
            };
            self.line(2, &format!("if !zkc_rt::p3::words_canonical(&{words}) {{"));
            self.line(
                3,
                &Self::refuse(
                    "Fill",
                    label,
                    "fill produced a word outside the canonical field range",
                ),
            );
            self.line(2, "}");
            self.line(
                2,
                &format!("zkc_rt::p3::encode_words(&{words}, &mut proof);"),
            );
            self.line(1, "}");
            return Ok(());
        }
        if self.vector_counts.contains_key(&value) {
            return Err(format!(
                "row {index}: write '{label}' is scalar, but its value is a counted \
                 vector"
            ));
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
        // A hole that touches the sponge — as operand or result — is the
        // transcript peek, judged by its own rules rather than by
        // positional value marshaling.
        if results.contains(&Entry::Sponge)
            || inputs
                .iter()
                .any(|input| Some(*input) == self.current_sponge)
        {
            return self.emit_pow_search(index, row);
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
        if !semantic_params.is_empty() {
            return Err(format!(
                "row {index}: hole '{label}' cites semantic parameters {semantic_params:?}; no \
                 fill in this vocabulary takes any"
            ));
        }
        // Static parameters lead the call, in the cited contract's own
        // name order — the order the row already carries them in, so
        // the emitted call is positional here exactly as it is for
        // operands.
        if params.len() != signature.params.len() {
            return Err(format!(
                "row {index}: hole '{label}' cites {} static parameters; the bound fill takes {}",
                params.len(),
                signature.params.len()
            ));
        }
        let mut arguments = Vec::new();
        for (position, (binding, rust_type)) in params.iter().zip(signature.params).enumerate() {
            if binding.is_empty() || !binding.chars().all(|c| c.is_ascii_digit()) {
                return Err(format!(
                    "row {index}: hole '{label}' parameter {position} is '{binding}', which is \
                     not the decimal the bound fill reads"
                ));
            }
            arguments.push(format!("{binding}{rust_type}"));
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
                Operand::Value(want) | Operand::VectorValue(want) => {
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
                    let wants_vector =
                        matches!(signature.inputs[position], Operand::VectorValue(_));
                    let is_vector = self.vector_counts.contains_key(input);
                    if wants_vector != is_vector {
                        return Err(format!(
                            "row {index}: hole '{label}' operand {position} is {}, but the \
                             bound fill takes {}",
                            if is_vector {
                                "a counted vector"
                            } else {
                                "a scalar"
                            },
                            if wants_vector {
                                "a counted vector"
                            } else {
                                "a scalar"
                            }
                        ));
                    }
                    arguments.push(expression);
                }
                Operand::Sponge => {
                    return Err(format!(
                        "row {index}: hole '{label}' reached value marshaling with a sponge \
                         operand; the peek path owns that shape"
                    ))
                }
            }
        }

        // Results, bound back positionally across the mixed list. A
        // signature with a repeating tail admits its fixed prefix plus
        // one or more whole repetitions — the instance's fold depth —
        // and the fill returns the repetitions as one Vec of groups.
        let repeat = signature.results_repeat;
        let repetitions = if repeat.is_empty() {
            if results.len() != signature.results.len() {
                return Err(format!(
                    "row {index}: hole '{label}' binds {} results; the bound fill returns {}",
                    results.len(),
                    signature.results.len()
                ));
            }
            0
        } else {
            let tail = results.len().checked_sub(signature.results.len());
            match tail {
                Some(tail) if tail > 0 && tail % repeat.len() == 0 => tail / repeat.len(),
                _ => {
                    return Err(format!(
                        "row {index}: hole '{label}' binds {} results; the bound fill \
                         returns {} plus whole groups of {}",
                        results.len(),
                        signature.results.len(),
                        repeat.len()
                    ))
                }
            }
        };
        let wants: Vec<&Operand> = signature
            .results
            .iter()
            .chain(repeat.iter().cycle().take(repetitions * repeat.len()))
            .collect();
        let mut names = Vec::new();
        for (slot, (result, &want)) in results.iter().zip(&wants).enumerate() {
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
                (Entry::ValVec(class, count), Operand::VectorValue(want))
                    if self.class_impl(class)? == *want =>
                {
                    if !self.referenced.contains(&(index, slot)) {
                        name = format!("_{bare}");
                    }
                    self.bind_value(
                        Ref::Res(index, slot),
                        bare,
                        VClass::Doc(class.clone()),
                        Some(*count),
                    );
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
        if repetitions > 0 {
            // Fixed prefix as a tuple, the repeating tail as one Vec
            // the generated code unpacks group by group, refusing a
            // fill whose group count is not the schedule's.
            let prefix: Vec<String> = names[..signature.results.len()].to_vec();
            let groups_name = format!("groups_{index}");
            self.line(
                1,
                &format!(
                    "let ({}, {groups_name}) = match {}({}) {{",
                    prefix.join(", "),
                    hole.implementation.path(),
                    arguments.join(", ")
                ),
            );
            self.line(2, "Ok(results) => results,");
            self.line(
                2,
                &format!(
                    "Err(message) => return Err(ProveError::Fill {{ label: {}.to_owned(), message }}),",
                    rust::literal(label)
                ),
            );
            self.line(1, "};");
            self.line(
                1,
                &format!("if {groups_name}.len() != {repetitions} {{"),
            );
            self.line(
                2,
                &Self::refuse(
                    "Fill",
                    label,
                    "fill returned a group count that is not the schedule's",
                ),
            );
            self.line(1, "}");
            self.line(
                1,
                &format!("let mut {groups_name} = {groups_name}.into_iter();"),
            );
            for group in 0..repetitions {
                let at = signature.results.len() + group * repeat.len();
                let members: Vec<String> = names[at..at + repeat.len()].to_vec();
                self.line(
                    1,
                    &format!(
                        "let Some(({})) = {groups_name}.next() else {{",
                        members.join(", ")
                    ),
                );
                self.line(
                    2,
                    &Self::refuse("Fill", label, "fill returned too few groups"),
                );
                self.line(1, "};");
            }
        } else {
            let (pattern, destructure) = match names.as_slice() {
                [] => {
                    return Err(format!(
                        "row {index}: hole '{label}' binds no results; a fill with nothing to \
                         bind has no effect the frame can observe"
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
        }
        Ok(())
    }

    /// The transcript peek (`docs/spec/endpoints.md` §6.2). The fill
    /// never receives the sponge: the emitted call passes a trial
    /// closure that clones it, replays the nonce absorb and the
    /// proof-of-work squeeze — the same forms the spine emits for the
    /// three rows that follow — and returns the derivation. Any other
    /// neighborhood refuses, because the trial the fill would run would
    /// not be the check the verifier performs. The hole's sponge result
    /// is the unchanged live state, so nothing is emitted for it.
    fn emit_pow_search(&mut self, index: usize, row: &Row) -> Result<(), String> {
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
            unreachable!("emit_pow_search is reached from emit_hole_call alone")
        };
        let Some(hole) = self.binding.hole(digest).cloned() else {
            return Err(format!(
                "row {index}: hole '{label}' (kind '{kind}', contract {digest}) has no fill in \
                 binding '{}'; the reference profiles refuse this at run time (zkc-E407) and the \
                 emitter refuses it here",
                self.binding.name
            ));
        };
        let mismatch = |what: &str| {
            format!(
                "row {index}: pow_search hole '{label}': {what}; the trial the fill would run \
                 is not the check the verifier performs (zkc-E412's emit-time form)"
            )
        };
        let signature = hole.implementation.signature();
        let [Operand::Sponge] = signature.inputs else {
            return Err(mismatch("the bound fill does not take the transcript peek"));
        };
        let [Operand::Value(nonce_kind), Operand::Sponge] = signature.results else {
            return Err(mismatch(
                "the bound fill does not return a nonce and the sponge",
            ));
        };
        let nonce_kind = *nonce_kind;
        if !semantic_params.is_empty() {
            return Err(mismatch(
                "no fill in this vocabulary takes semantic parameters",
            ));
        }
        let [bits_text] = params.as_slice() else {
            return Err(mismatch(
                "the contract's one static parameter must be the bit count",
            ));
        };
        let bits: u32 = match bits_text.parse() {
            Ok(bits) if (1..64).contains(&bits) => bits,
            _ => {
                return Err(mismatch(
                    "the bit count must be a positive integer below 64",
                ))
            }
        };
        if inputs.len() != 1 || Some(inputs[0]) != self.current_sponge {
            return Err(mismatch(
                "the hole must take the live sponge as its only operand",
            ));
        }
        let (mut nonce_slot, mut sponge_slot, mut nonce_class) = (None, None, None);
        for (slot, result) in results.iter().enumerate() {
            match result {
                Entry::Val(class) => {
                    nonce_slot = Some(slot);
                    nonce_class = Some(class.clone());
                }
                Entry::Sponge => sponge_slot = Some(slot),
                _ => {}
            }
        }
        let (Some(nonce_slot), Some(sponge_slot), Some(nonce_class), 2) =
            (nonce_slot, sponge_slot, nonce_class, results.len())
        else {
            return Err(mismatch(
                "the contract must yield exactly one nonce value and the state-identical sponge",
            ));
        };
        if self.class_impl(&nonce_class)? != nonce_kind {
            return Err(mismatch("the nonce class is not the bound fill's"));
        }
        let nonce_ref = Ref::Res(index, nonce_slot);
        let sponge_res = Ref::Res(index, sponge_slot);
        let neighborhood =
            "the three rows after the hole must write the nonce, absorb it, and squeeze \
             the proof of work";
        let Some([write, absorb, squeeze]) = self.document.rows.get(index + 1..index + 4) else {
            return Err(mismatch(neighborhood));
        };
        let Row::Write { value: written, .. } = write else {
            return Err(mismatch(neighborhood));
        };
        if *written != nonce_ref {
            return Err(mismatch(
                "the row after the hole must write the hole's nonce result",
            ));
        }
        let Row::Absorb {
            sponge: absorb_sponge,
            value: absorbed,
        } = absorb
        else {
            return Err(mismatch(neighborhood));
        };
        if *absorbed != nonce_ref || *absorb_sponge != sponge_res {
            return Err(mismatch(
                "the row after the write must absorb the nonce through the hole's sponge result",
            ));
        }
        let Row::Squeeze {
            sponge: squeeze_sponge,
            class: pow_class,
            count,
            domain,
            rule,
            space,
            ..
        } = squeeze
        else {
            return Err(mismatch(neighborhood));
        };
        if *squeeze_sponge != Ref::Res(index + 2, 0) {
            return Err(mismatch("the row after the absorb must squeeze from it"));
        }
        if *count != 1 || rule != "uniform" || *space != (1u64 << bits).to_string() {
            return Err(mismatch(
                "the proof-of-work squeeze must draw one uniform value from a space of \
                 exactly 2^bits",
            ));
        }
        // The search enumerates the nonce class's canonical values; its
        // domain is the class's own.
        let domain_argument = match nonce_kind {
            ImplKind::ToyBe8 => {
                let Some(modulus) = self.class_binding(&nonce_class)?.modulus else {
                    return Err(format!(
                        "row {index}: pow_search hole '{label}': binding '{}' pins no modulus \
                         for nonce class '{nonce_class}', so the search has no canonical domain",
                        self.binding.name
                    ));
                };
                format!("{modulus}u64")
            }
            ImplKind::P3Word => "zkc_rt::p3::BB".to_owned(),
            other => {
                return Err(mismatch(&format!(
                    "nonce implementation {other:?} has no search domain"
                )))
            }
        };
        let absorb_line =
            self.absorb_statement("trial", "nonce", &VClass::Doc(nonce_class.clone()), index)?;
        let derive_expr = match self.class_impl(pow_class)? {
            ImplKind::ToyBe8 => format!(
                "zkc_rt::toy::derive_be8(&trial.squeeze({}), {space}u64)",
                rust::literal(domain)
            ),
            ImplKind::P3Word => format!("zkc_rt::p3::squeeze_low_bits(&mut trial, {space}u64)"),
            other => {
                return Err(mismatch(&format!(
                    "proof-of-work class implementation {other:?} has no trial derivation"
                )))
            }
        };
        self.consume_sponge(inputs[0], index, sponge_res)?;
        self.used.sponge.named = true;
        let referenced = self.referenced.contains(&(index, nonce_slot));
        let name = format!("{}r{index}_{nonce_slot}", if referenced { "" } else { "_" });
        self.line(
            1,
            &format!(
                "// [\"hole_call\", \"{}\" : {}]",
                rust::comment(label),
                rust::comment(kind)
            ),
        );
        self.line(
            1,
            &format!(
                "let {name}: {} = match {}({domain_argument}, |nonce| {{",
                nonce_kind.rust_type(),
                hole.implementation.path()
            ),
        );
        self.line(2, "let mut trial = sponge.clone();");
        self.line(2, &absorb_line);
        self.line(2, &derive_expr);
        self.line(1, "}) {");
        self.line(2, "Ok(value) => value,");
        self.line(
            2,
            &format!(
                "Err(message) => return Err(ProveError::Fill {{ label: {}.to_owned(), message }}),",
                rust::literal(label)
            ),
        );
        self.line(1, "};");
        self.values.insert(
            nonce_ref,
            (format!("r{index}_{nonce_slot}"), VClass::Doc(nonce_class)),
        );
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

impl<'a> Walk<'a> {
    pub(crate) fn new(document: &'a Document, binding: &'a Binding) -> Self {
        Walk {
            document,
            binding,
            values: Default::default(),
            handles: Default::default(),
            referenced: Default::default(),
            vector_counts: Default::default(),
            current_sponge: None,
            current_stream: None,
            body: String::new(),
            used: Used::default(),
        }
    }

    /// The walk's output: the emitted body with the sponge declaration's
    /// qualifier resolved, and the use record the preamble declares from.
    pub(crate) fn finish(self) -> (String, Used) {
        let used = self.used;
        let body = self.body.replace(
            SPONGE_QUALIFIER,
            &format!("{}{}", used.sponge.prefix(), used.sponge.qualifier()),
        );
        (body, used)
    }
}

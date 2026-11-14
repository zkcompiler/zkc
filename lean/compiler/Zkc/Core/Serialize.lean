module

public import Zkc.Core.FiatShamir

public section

/-! The serialize step with the canonical layout.

The step threads a writer at the prover and a reader at the verifier, with the same
function as the Fiat–Shamir step, and supplies this rule:

- an exchange from the prover to the verifier: the prover puts the value on its writer;
  the verifier takes a value of the type from its reader, with a flag that says whether
  the reader had one, and guards the flag with the reason `reject`. Nothing is exchanged,
  and the site is gone;
- the entry: the verifier has one more input, the proof, and the prover one more
  output, the proof. The prover opens a writer and, after the body, closes it. The
  verifier opens a reader on the proof and, after the body, guards that it is
  exhausted;
- a draw between the transcript roles is refused: the program still needs a transport;
- an exchange of a type that has no value is refused: no reader gives a value of it.

The layout is rows of the package: one row that puts and one that takes per message
type, and the four rows of the entry. Every row is pure, so the writer, the reader and
the proof are populated types. Taking gives the flag, a value of the type (any value when
the flag is false) and the rest of the reader: on a proof that is too short or malformed
the verifier stops `reject`.

After the step the entry is not a closed two-party run: the verifier's proof is an
input and the prover's proof an output, and no operation connects them.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- A wire layout: the types of the writer, the reader and the proof, and the rows. -/
structure Layout (operations : List OperationSignature) where
  writer : Ty
  reader : Ty
  proof : Ty
  writerPopulated : Ty.allPopulated [writer] = true
  readerPopulated : Ty.allPopulated [reader] = true
  proofPopulated : Ty.allPopulated [proof] = true
  start : Var operations ⟨[], [writer], .pure⟩
  put : (type : Ty) → Option (Var operations ⟨[writer, type], [writer], .pure⟩)
  close : Var operations ⟨[writer], [proof], .pure⟩
  read : Var operations ⟨[proof], [reader], .pure⟩
  /-- The row that reads a value of a type from the reader: whether the reader has one, the
  value (any value when it has none) and the rest of the reader. -/
  take : (type : Ty) → Option (Var operations ⟨[reader], [.bool, type, reader], .pure⟩)
  exhausted : Var operations ⟨[reader], [.bool], .pure⟩

/-- The serialize rule of a layout. -/
@[expose] def serializeRule {operations : List OperationSignature} {functions : List FunctionHeader}
    (layout : Layout operations) : Rule ⟨layout.writer, layout.reader⟩ operations functions where
  exchange := fun {protocols deployed} place site type {_} value writer reader =>
    if populated : Ty.allPopulated [.bool, type, layout.reader] = true then
      match layout.put type, layout.take type with
      | some put, some take =>
          let written : Emitted (ProtocolDialect operations functions protocols deployed) _
              [⟨layout.writer, place.roles.prover⟩] :=
            Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
              (.at place.roles.prover (.op put layout.writerPopulated) .nil)
              (.cons writer (.cons value .nil)) .nil
          let taken : Emitted (ProtocolDialect operations functions protocols deployed)
              written.context
              [⟨.bool, place.roles.verifier⟩, ⟨type, place.roles.verifier⟩,
                ⟨layout.reader, place.roles.verifier⟩] :=
            Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
              (.at place.roles.verifier (.op take populated) .nil)
              (.cons (reader.extend written.grows) .nil) .nil
          let guarded : Emitted (ProtocolDialect operations functions protocols deployed)
              taken.context [] :=
            Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
              (.at place.roles.verifier (.guard .reject) .nil) (.cons (taken.values.get .here) .nil)
              .nil
          .ok (written.andThen (taken.andThen guarded .nil)
            (.cons ((taken.values.get (.there .here)).extend guarded.grows)
              (.cons (((written.values.get .here).extend taken.grows).extend guarded.grows)
                (.cons ((taken.values.get (.there (.there .here))).extend guarded.grows) .nil))))
      | _, _ => .error (.message place.definition site)
    else .error (.unpopulated place.definition site)
  derives := false
  draw := fun {_ _} place site {_ _} _ {_} _ _ => .error (.interactive place.definition site)
  entryRefusal := fun _ _ => none
  entryPorts := fun roles header =>
    ⟨⟨layout.proof, roles.verifier⟩ :: header.inputs, ⟨layout.proof, roles.prover⟩ :: header.outputs,
      ⟨header.agreements.inputs.map (·.under _), header.agreements.outputs.map (·.under _)⟩⟩
  entry := fun {protocols deployed} place header body =>
    let prover := place.roles.prover
    let verifier := place.roles.verifier
    let proof : Var (bindAll [⟨layout.proof, verifier⟩] header.inputs) ⟨layout.proof, verifier⟩ :=
      Var.here.weaken header.inputs
    let opened : Emitted (ProtocolDialect operations functions protocols deployed)
        (bindAll [⟨layout.proof, verifier⟩] header.inputs) [⟨layout.writer, prover⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at prover (.op layout.start layout.writerPopulated) .nil) .nil .nil
    let reading : Emitted (ProtocolDialect operations functions protocols deployed) opened.context
        [⟨layout.reader, verifier⟩] :=
      Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
        (.at verifier (.op layout.read layout.readerPopulated) .nil)
          (.cons (proof.extend opened.grows) .nil) .nil
    let rename : Renaming (bindAll [] header.inputs)
        (bindAll [⟨layout.proof, verifier⟩] header.inputs) :=
      Renaming.keepAll (Mapping.start (Δ := [⟨layout.proof, verifier⟩]) 1 rfl) header.inputs
    match body ((rename.extend opened.grows).extend reading.grows)
        ((opened.values.get .here).extend reading.grows) (reading.values.get .here) with
    | .ok threaded =>
        -- After the body: the final writer and reader, then the outputs of the entry.
        let writer : Var (bindAll (⟨layout.reader, verifier⟩ :: ⟨layout.writer, prover⟩ ::
            reading.context) header.outputs) ⟨layout.writer, prover⟩ :=
          (Var.there .here : Var (⟨layout.reader, verifier⟩ :: ⟨layout.writer, prover⟩ ::
            reading.context) _).weaken header.outputs
        let reader : Var (bindAll (⟨layout.reader, verifier⟩ :: ⟨layout.writer, prover⟩ ::
            reading.context) header.outputs) ⟨layout.reader, verifier⟩ :=
          (Var.here : Var (⟨layout.reader, verifier⟩ :: ⟨layout.writer, prover⟩ ::
            reading.context) _).weaken header.outputs
        let closed : Emitted (ProtocolDialect operations functions protocols deployed) _
            [⟨layout.proof, prover⟩] :=
          Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
            (.at prover (.op layout.close layout.proofPopulated) .nil) (.cons writer .nil) .nil
        let checked : Emitted (ProtocolDialect operations functions protocols deployed) closed.context
            [⟨.bool, verifier⟩] :=
          Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
            (.at verifier (.op layout.exhausted rfl) .nil)
            (.cons (reader.extend closed.grows) .nil) .nil
        let guarded : Emitted (ProtocolDialect operations functions protocols deployed)
            checked.context [] :=
          Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
            (.at verifier (.guard .reject) .nil) (.cons (checked.values.get .here) .nil) .nil
        let later := (closed.grows.trans checked.grows).trans guarded.grows
        .ok (opened.wrap (reading.wrap (.bind threaded
          (closed.wrap (checked.wrap (guarded.wrap
            (.ret (.cons (((closed.values.get .here).extend checked.grows).extend guarded.grows)
              ((Operands.newest header.outputs).extend later)))))))))
    | .error refusal => .error refusal
  idleEntry := true

/-- The layout that a declaration describes, over the rows of a package. -/
@[expose] def Layout.ofRaw {operations : List OperationSignature} (rows : Scope operations)
    (raw : Raw.Layout) : Option (Layout operations) :=
  match rowWith rows ⟨[], [raw.writer], .pure⟩ raw.start,
      rowWith rows ⟨[raw.writer], [raw.proof], .pure⟩ raw.close,
      rowWith rows ⟨[raw.proof], [raw.reader], .pure⟩ raw.read,
      rowWith rows ⟨[raw.reader], [.bool], .pure⟩ raw.exhausted with
  | some start, some close, some read, some exhausted =>
      if writerPopulated : Ty.allPopulated [raw.writer] = true then
        if readerPopulated : Ty.allPopulated [raw.reader] = true then
          if proofPopulated : Ty.allPopulated [raw.proof] = true then
            some { writer := raw.writer, reader := raw.reader, proof := raw.proof
                   writerPopulated, readerPopulated, proofPopulated, start := start
                   put := fun type =>
                     firstRowWith rows ⟨[raw.writer, type], [raw.writer], .pure⟩ raw.putting
                   close := close, read := read
                   take := fun type =>
                     firstRowWith rows ⟨[raw.reader], [.bool, type, raw.reader], .pure⟩ raw.taking
                   exhausted := exhausted }
          else none
        else none
      else none
  | _, _, _, _ => none

/-- The serialize step on the protocols that the Fiat–Shamir step produced, or on those
of a package whose construction is authored. The entry is the newest protocol. -/
@[expose] def serializeProtocols {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {protocols : List ProtocolHeader}
    (declaration : Raw.Declaration) (identities : Identities)
    (program : Protocols typeTable operations functions protocols) :
    Except StepRefusal (Stepped typeTable operations functions) :=
  match declaration.layout.bind (Layout.ofRaw (tableScope operations)) with
  | none => .error .row
  | some layout =>
      stepProtocols ⟨layout.writer, layout.reader⟩ (serializeRule layout) identities
        (protocols.length - 1)
        ⟨declaration.prover, declaration.verifier⟩ program

/-- Fiat–Shamir, then serialize, on a typed package. -/
@[expose] def construct (typed : Typed) (declaration : Raw.Declaration) :
    Except StepRefusal (Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :=
  match fiatShamir typed declaration with
  | .ok constructed => serializeProtocols declaration constructed.identities constructed.protocols
  | .error refusal => .error refusal

end Zkc.Core

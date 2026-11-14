module

public import Zkc.Core.SerializeReplayProgram
public import Zkc.Core.ThreadCompose

public section

/-! The serialize step replays: the prover's entry returns a proof on which the verifier's
entry returns its part of accepted outputs.

`serialize_entry_replays`: for a program on which the serialize step returns, and all laws
of the layout (`Layout.Lawful`): if every run of the declared entry for the side of the
prover and the verifier together returns outputs of which a condition holds, and every
`send` of the entry for the prover alone carries a value that the layout can write
(`Layout.Lawful.Writable`), then for every sampler there are such outputs and a proof such
that

- the serialized entry for the prover alone returns the proof and the prover's part of the
  outputs, and
- the serialized entry for the verifier alone, on that proof, returns the verifier's part of
  the outputs.

Each of the two runs starts from the counters of a run that has asked nothing.

The parts of the proof: the serialized entry for a side with one transcript role is the
entry interpreted by the handler of the step, between the start and the finish of the
serialize rule (`stepProtocols_entry`); the grouped entry and the two parts under these
handlers are related (`rewriteProtocols_replays`); the prover's start opens a writer and its
finish closes the writer that the messages were put on; and the verifier's start opens a
reader on that proof, from which the messages are taken and which is then exhausted
(`Layout.Lawful.round_trip`), so the guard of its finish passes.

What is assumed and not proved here: the laws of the layout, that every run of the grouped
entry returns, and that the value of every message of the prover is one that the layout can
write. That the layout has the rows that put and take a value of the type of every such
message is not assumed: the step refuses a program otherwise, so it follows from the equation
of the step (`rewriteProtocols_newest_carries`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Entry

variable {model : Model} {operations : List OperationSignature}

/-- The start of the serialize rule for the side of the prover: the writer that `start`
opens. -/
theorem Layout.opening_prover (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = true) (isVerifier : verifier = false)
      (proof : Held (model.Value layout.proof) verifier),
      layout.opening (model := model) prover verifier proof =
        .done (Held.of prover (layout.opened model), Held.absent verifier isVerifier)
  | true, false, _, _, _ => rfl

/-- The start of the serialize rule for the side of the verifier: the reader that `read`
opens on the proof. -/
theorem Layout.opening_verifier (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = false) (isVerifier : verifier = true)
      (proof : Held (model.Value layout.proof) verifier),
      layout.opening (model := model) prover verifier proof =
        .done (Held.absent prover isProver,
          Held.of verifier (layout.reading model (Held.value verifier isVerifier proof)))
  | false, true, _, _, _ => rfl

/-- The finish of the serialize rule for the side of the prover: the proof that `close`
makes of the writer. -/
theorem Layout.closing_prover (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = true) (isVerifier : verifier = false)
      (state : ThreadState model layout.threads prover verifier),
      layout.closing (model := model) prover verifier state =
        .done (Held.of prover (layout.closed model (Held.value prover isProver state.1)))
  | true, false, _, _, _ => rfl

/-- The finish of the serialize rule for the side of the verifier, on a reader that is
exhausted: the guard passes. -/
theorem Layout.closing_verifier (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = false) (isVerifier : verifier = true)
      (state : ThreadState model layout.threads prover verifier),
      layout.isExhausted model (Held.value verifier isVerifier state.2) = true →
      layout.closing (model := model) prover verifier state = .done (Held.absent prover isProver)
  | false, true, _, _, state, exhausted => by
      have unfolded : layout.closing (model := model) false true state =
          (cond (layout.isExhausted model state.2)
            (PIR.Process.done (Values.nil : Values (fun type => Held (model.Value type) true) []))
            (.halt Reason.reject.stop)).bind fun _ => .done PUnit.unit := rfl
      rw [unfolded]
      have same : layout.isExhausted model state.2 = true := exhausted
      rw [same]
      rfl

/-- The side of one role holds the role. -/
theorem single_holds (role bound : Nat) : (single role).Holds (some role) bound :=
  fun other _ => natBeq_swap other role

/-- The sides of two different roles are disjoint. -/
theorem singles_disjoint {first second : Nat} (differ : first ≠ second) :
    (single first).Disjoint (single second) := by
  intro role
  show (Nat.beq role first && Nat.beq role second) = false
  cases atFirst : Nat.beq role first with
  | false => rfl
  | true =>
      cases atSecond : Nat.beq role second with
      | false => rfl
      | true =>
          exact absurd ((Nat.eq_of_beq_eq_true atFirst).symm.trans (Nat.eq_of_beq_eq_true atSecond))
            differ

/-- A start that returns a state, a body that runs from it, and a finish that returns. -/
theorem returns_through {α β γ : Type} {start : PIR.Process (Effects model) α}
    {body : α → PIR.Process (Effects model) β} {finish : β → PIR.Process (Effects model) γ}
    {sampler : Sampler model} {asked final : Asked} {state : α} {result : β} {value : γ}
    (starts : start = .done state) (runs : RunsTo sampler (body state) asked result final)
    (finishes : finish result = .done value) :
    ReturnsAlone sampler (start.bind fun state => (body state).bind finish) asked value := by
  subst starts
  exact (runs.bind (by rw [finishes]; exact .done _ _)).returnsAlone

variable {typeTable : TypeTable} {functions : List FunctionHeader}

/-- What the serialize step guarantees of an entry and its serialized image, on inputs of a
run of the entry for the prover and the verifier together: if every run of the entry on them
returns outputs of which `holds` holds, and every `send` of the entry for the prover alone
carries a value that the layout can write, then for every sampler there are such outputs and
a proof such that the serialized entry for the prover alone returns the proof and the
prover's part of the outputs, and the serialized entry for the verifier alone on that proof
returns the verifier's part of the outputs. The prover's side holds no proof to start with
(`given` is the unit value), and the verifier's side returns none. Each run starts from the
counters of a run that has asked nothing. -/
@[expose] def SerializedReplaysOn (layout : Layout operations) (laws : layout.Lawful model)
    (roles : TranscriptRoles) (header : ProtocolHeader) (entry : header.Meaning model)
    (serialized : ((serializeRule (functions := functions) layout).entryHeader roles
      header).Meaning model)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs) : Prop :=
  ∀ (holds : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.outputs → Prop),
    EveryRun holds (entry [] ((single roles.prover).union (single roles.verifier)) inputs) →
    EverySend laws.Writable (fun _ => True)
      (entry [] (single roles.prover)
        (leftValues model (single roles.prover) (single roles.verifier) inputs)) →
    ∀ (sampler : Sampler model)
      (given : SideValue model (single roles.prover) ⟨layout.proof, roles.verifier⟩),
      ∃ (outputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
          header.outputs) (proof : model.Value layout.proof),
        holds outputs ∧
        ReturnsAlone sampler
          (serialized [] (single roles.prover)
            (Values.cons (Value := SideValue model (single roles.prover))
              (ty := ⟨layout.proof, roles.verifier⟩) given
              (leftValues model (single roles.prover) (single roles.verifier) inputs)))
          Asked.start
          (Values.cons (Value := SideValue model (single roles.prover))
            (ty := ⟨layout.proof, roles.prover⟩)
            (Held.of (single roles.prover roles.prover) proof)
            (leftValues model (single roles.prover) (single roles.verifier) outputs)) ∧
        ReturnsAlone sampler
          (serialized [] (single roles.verifier)
            (Values.cons (Value := SideValue model (single roles.verifier))
              (ty := ⟨layout.proof, roles.verifier⟩)
              (Held.of (single roles.verifier roles.verifier) proof)
              (rightValues model (single roles.prover) (single roles.verifier) inputs)))
          Asked.start
          (Values.cons (Value := SideValue model (single roles.verifier))
            (ty := ⟨layout.proof, roles.prover⟩)
            (Held.of (single roles.verifier roles.prover) proof)
            (rightValues model (single roles.prover) (single roles.verifier) outputs))

/-- What the serialize step guarantees of an entry and its serialized image: the statement
`SerializedReplaysOn` on all inputs. -/
@[expose] def SerializedReplays (layout : Layout operations) (laws : layout.Lawful model)
    (roles : TranscriptRoles) (header : ProtocolHeader) (entry : header.Meaning model)
    (serialized : ((serializeRule (functions := functions) layout).entryHeader roles
      header).Meaning model) : Prop :=
  ∀ inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs,
    SerializedReplaysOn layout laws roles header entry serialized inputs

/-- The serialize step replays: for a program on which the step returns, the declared entry
and its image, the newest protocol of the result, are related by `SerializedReplays` under
all laws of the layout. -/
theorem serialize_entry_replays (layout : Layout operations)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (program : Program typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols layout.threads (serializeRule layout) identities number roles
      program.protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var stepped.headers
        ((serializeRule (functions := functions) layout).entryHeader roles header),
      image.index = 0 ∧
      ∀ laws : layout.Lawful model,
        SerializedReplays layout laws roles header
          ((program.protocolTable model identities).get declared)
          ((stepped.protocols.table model (program.functionTable model) stepped.identities).get
            image) := by
  have quiet : QuietTable (program.functionTable model) := Functions.table_quiet program.functions
  obtain ⟨origin, earlier, newest, idleEntry⟩ :=
    stepProtocols_newest identities number roles program.protocols stepped steps declared isEntry
  obtain ⟨image, first, images⟩ := stepProtocols_entry (model := model) quiet
    (serializeRule_sound layout (program.functionTable model))
    (serializeEntry_sound layout (program.functionTable model)) identities number roles
    program.protocols stepped steps declared isEntry origin earlier newest (idleEntry rfl)
  refine ⟨image, first, ?_⟩
  intro laws inputs holds every sendable sampler given
  show ∃ outputs proof, holds outputs ∧ _ ∧ _
  obtain ⟨rewritten, rewrites, _⟩ :=
    stepProtocols_rewritten identities number roles program.protocols stepped steps
  have differ := stepProtocols_roles_differ identities number roles program.protocols stepped steps
  have reached : Reached (entryDemands old.length number roles) declared.index (.entry roles) := by
    unfold entryDemands
    rw [← isEntry]
    exact entry_reached roles declared.index
  have threaded : ThreadedReplays layout laws rewritten.marks
      (program.protocols.table model (program.functionTable model) identities) declared roles :=
    rewriteProtocols_replays layout laws quiet identities program.protocols _ rewritten rewrites
      declared (.entry roles) reached
  have marks : stepMarks layout.threads (serializeRule layout) identities number roles
      program.protocols = rewritten.marks.get declared roles := by
    rw [stepMarks_rewritten identities number roles program.protocols rewritten rewrites, ← isEntry,
      MarkTable.at_index]
  have isProver : single roles.prover roles.prover = true := Nat.beq_refl _
  have isVerifier : single roles.verifier roles.verifier = true := Nat.beq_refl _
  have disjoint := singles_disjoint differ
  obtain ⟨noReader, noWriter, _⟩ := roles_apart ⟨0, roles, false⟩ (single roles.prover)
    (single roles.verifier) disjoint isProver isVerifier
  have replays := threaded [] (single roles.prover) (single roles.verifier) disjoint
    (single_holds _ _) (single_holds _ _) _ _ _ _ rfl rfl rfl rfl isProver isVerifier
    (threadHandler (serializeMeaning layout)
      (marksBelow [] (stepMarks layout.threads (serializeRule layout) identities number roles
        program.protocols)) _ _)
    (threadHandler (serializeMeaning layout)
      (marksBelow [] (stepMarks layout.threads (serializeRule layout) identities number roles
        program.protocols)) _ _)
    (marks ▸ threadHandler_follows (serializeMeaning layout) _ _ _ [])
    (marks ▸ threadHandler_follows (serializeMeaning layout) _ _ _ []) inputs
  obtain ⟨outputs, messages, written, finalProver, finalVerifier, held, _, wrote, runsProver,
      runsVerifier⟩ :=
    replays.run holds (fun _ => True) every sendable sampler Asked.start Asked.start
      (Held.of (single roles.prover roles.prover) (layout.opened model),
        Held.absent (single roles.prover roles.verifier) noReader)
  obtain ⟨wroteMessages, _, sendableMessages⟩ := wrote
  have wroteOpened : layout.Written model (layout.opened model) messages
      (Held.value (single roles.prover roles.prover) isProver written.1) := by
    have wroteStart : layout.Written model
        (Held.value (single roles.prover roles.prover) isProver
          (Held.of (single roles.prover roles.prover) (layout.opened model))) messages
        (Held.value (single roles.prover roles.prover) isProver written.1) := wroteMessages
    rw [Held.value_of] at wroteStart
    exact wroteStart
  obtain ⟨reader, takes, exhausted⟩ := laws.round_trip sendableMessages wroteOpened
  refine ⟨outputs,
    layout.closed model (Held.value (single roles.prover roles.prover) isProver written.1), held,
    ?_, ?_⟩
  · refine Eq.mpr (congrArg (fun process => ReturnsAlone sampler process Asked.start _)
      (images [] (single roles.prover) (.inl ⟨isProver, noReader⟩) _)) ?_
    refine returns_through ?_ runsProver ?_
    · exact layout.opening_prover _ _ isProver noReader given
    · show (layout.closing _ _ written).bind _ = _
      rw [layout.closing_prover _ _ isProver noReader]
      rfl
  · refine Eq.mpr (congrArg (fun process => ReturnsAlone sampler process Asked.start _)
      (images [] (single roles.verifier) (.inr ⟨noWriter, isVerifier⟩) _)) ?_
    refine returns_through (final := finalVerifier)
      (state := (Held.absent (single roles.verifier roles.prover) noWriter,
        Held.of (single roles.verifier roles.verifier)
          (layout.reading model
            (Held.value (single roles.verifier roles.verifier) isVerifier
              (Held.of (single roles.verifier roles.verifier)
                (layout.closed model
                  (Held.value (single roles.prover roles.prover) isProver written.1)))))))
      (result := (rightValues model (single roles.prover) (single roles.verifier) outputs,
        (Held.absent (single roles.verifier roles.prover) noWriter,
          Held.of (single roles.verifier roles.verifier) reader)))
      ?_ ?_ ?_
    · exact layout.opening_verifier _ _ noWriter isVerifier _
    · refine runsVerifier _ _ ⟨?_, rfl⟩
      show layout.Takes model
        (Held.value _ isVerifier (Held.of _ (layout.reading model
          (Held.value _ isVerifier (Held.of _ _))))) messages
        (Held.value _ isVerifier (Held.of _ reader))
      rw [Held.value_of, Held.value_of, Held.value_of]
      exact takes
    · show (layout.closing _ _ _).bind _ = _
      rw [layout.closing_verifier _ _ noWriter isVerifier _
        (by
          show layout.isExhausted model (Held.value _ isVerifier (Held.of _ reader)) = true
          rw [Held.value_of]
          exact exhausted)]
      exact congrArg (fun head => PIR.Process.done (Values.cons head _))
        (Held.absent_unique _ noWriter _ _)

end Entry

end Zkc.Core

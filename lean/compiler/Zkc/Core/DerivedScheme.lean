module

public import Zkc.Core.SerializeReplayEntry
public import Zkc.Core.ThreadTogetherFiatShamir
public import Zkc.Core.DerivedCompleteness

public section

/-! Completeness of the scheme that the construction steps derive.

A derived scheme is complete when, for every sampler, the prover's program run alone returns
a proof on which the verifier's program run alone returns an accepted result
(`DerivedComplete`). This module proves it of the role programs that the pipeline of a
declaration constructs (`construct`: the Fiat–Shamir step, then the serialize step, then
projection), from completeness of the interactive entry for the prover and the verifier
together.

**The statements.**

- `construct_complete`: the pipeline of a declaration on a typed package.
- `serializeProtocols_complete`: the serialize step of a declaration alone, on a program
  whose Fiat–Shamir step is authored. It has no suite and no condition on the inputs.
- `fiatShamir_serialize_complete`, `serialize_complete`: the same two for the equations of
  `stepProtocols`, from which the two above follow.

In each, the derived prover runs on the prover's share of the inputs of the interactive run
(`inputsWithoutProof`, `proverShare`) and returns the proof first (`provedOutputs`); the
derived verifier runs on the proof and then the verifier's share (`proofInputs`,
`verifierShare`). The accepted results of the derived verifier are not a parameter: the
outputs of the derived verifier are the outputs of the interactive verifier, because the
proof is an output of the prover (`outputsWithoutProof`, which `inputsWithoutProof` inverts),
and a result is accepted when the interactive condition holds of it read so.

**What is assumed**, besides the equations that say which programs were constructed (the
result of the step or of the pipeline, the suite and the layout that the declaration names,
the position of the declared entry, the projection of the result and its two role programs):

- `GroupedComplete`: the interactive entry, for the side of the prover and the verifier
  together and on the given inputs, returns for every sampler outputs of which the
  interactive condition holds of the verifier's share;
- `Layout.Lawful`: the laws of the layout in the model;
- that every value that the interactive entry for the prover alone sends, whatever it
  receives and samples, is one that the layout can write (`EverySend` of
  `Layout.Lawful.Writable`);
- for the pipeline: `Suite.Returns`, and that the prover's and the verifier's copies of the
  statement among the inputs are equal (`StatementCopiesEqual`).

**What is derived**, and is a premise of no statement here: that the layout has the rows
that put and take the type of every message (`rewriteProtocols_newest_carries`); that the
Fiat–Shamir image of the entry for the prover alone sends the values that the entry sends
(`fiatShamir_sends`: the handler of the step sends the value of a rewritten exchange as it
is and derives a coin without an effect, and the start and the finish of the rule's entry
perform no effect); that the Fiat–Shamir image of the entry returns on every run on which
the entry does (`fiatShamir_together`); that the serialize step replays
(`serialize_entry_replays`); and that the role programs of the result have the meaning of
its entry for the side of each role alone (`projectProtocols_sound`). Nothing is assumed of
a handler, of the marks of a step, or of two programs run against each other.

**What is not proved here.** `Layout.Lawful` of any layout (for the canonical layout in the
model of the vocabulary the laws are derived, and `Zkc.Core.VocabularyScheme` states the
theorems without them); that the messages of a given protocol are writable; completeness of
a given interactive protocol. A protocol whose
entry reads an oracle, or has a role besides the prover and the verifier that exchanges
with them, satisfies `GroupedComplete` on no inputs: no run of such an entry for the two
roles together returns.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## The values of the two roles of a serialized entry -/

section Values

variable {model : Model}

/-- The outputs of the verifier of a serialized entry, read as its outputs of the entry
before the step: the proof is an output of the prover, which is another role, so the
verifier holds no value of it. -/
@[expose] def outputsWithoutProof (model : Model) {prover verifier : Nat} {proof : Ty}
    {rest : List Located}
    (outputs : Values model.Value (own verifier (⟨proof, prover⟩ :: rest))) :
    Values model.Value (own verifier rest) :=
  (unkeep (Nat.beq prover verifier) outputs).2

/-- The values of a role before which a value of another role was put are the values. -/
theorem outputsWithoutProof_inputsWithoutProof {role other : Nat} (differ : role ≠ other)
    {proof : Ty} {rest : List Located} (values : Values model.Value (own role rest)) :
    outputsWithoutProof model
        (inputsWithoutProof model (proof := proof) (rest := rest) differ values) = values := by
  have absent : Nat.beq other role = false := by
    cases same : Nat.beq other role with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  unfold outputsWithoutProof inputsWithoutProof
  exact unkeep_consKept_absent _ absent _ values

/-- A value that is not kept, put back before the values after it. -/
theorem consKept_unkeep_absent {type : Ty} {rest : List Ty} :
    ∀ (present : Bool) (absent : present = false) (value : present = true → model.Value type)
      (values : Values model.Value (keep present type rest)),
      consKept present value (unkeep present values).2 = values
  | false, _, _, _ => rfl

/-- The outputs of the verifier of a serialized entry are its outputs of the entry before
the step, with nothing before them: the two readings are inverse. -/
theorem inputsWithoutProof_outputsWithoutProof {role other : Nat} (differ : role ≠ other)
    {proof : Ty} {rest : List Located}
    (outputs : Values model.Value (own role (⟨proof, other⟩ :: rest))) :
    inputsWithoutProof model differ (outputsWithoutProof model outputs) = outputs := by
  have absent : Nat.beq other role = false := by
    cases same : Nat.beq other role with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  unfold outputsWithoutProof inputsWithoutProof
  exact consKept_unkeep_absent _ absent _ outputs

/-- A value that is kept, taken apart again. -/
theorem unkeep_consKept_value {type : Ty} {rest : List Ty} :
    ∀ (present : Bool) (value : model.Value type) (values : Values model.Value rest),
      unkeep present (consKept present (fun _ => value) values) = (Held.of present value, values)
  | true, _, _ => rfl
  | false, _, _ => rfl

/-- What a role holds of its own value before values of the side of the role alone: the
value before what it holds of them. -/
theorem ownValues_proof (role : Nat) {proof : Ty} {rest : List Located}
    (value : model.Value proof) (values : Values (SideValue model (single role)) rest) :
    ownValues model (single role) role (Side.single_inside role) (⟨proof, role⟩ :: rest)
        (Values.cons (Value := SideValue model (single role)) (ty := ⟨proof, role⟩)
          (Held.of (single role role) value) values) =
      proofInputs model role value
        (ownValues model (single role) role (Side.single_inside role) rest values) := by
  have key : onlyValues model role (⟨proof, role⟩ :: rest)
        (proofInputs model role value
          (ownValues model (single role) role (Side.single_inside role) rest values)) =
      Values.cons (Value := SideValue model (single role)) (ty := ⟨proof, role⟩)
        (Held.of (single role role) value) values := by
    show Values.cons (ty := (⟨proof, role⟩ : Located))
        (unkeep (Nat.beq role role)
          (proofInputs model role value
            (ownValues model (single role) role (Side.single_inside role) rest values))).1
        (onlyValues model role rest
          (unkeep (Nat.beq role role)
            (proofInputs model role value
              (ownValues model (single role) role (Side.single_inside role) rest values))).2) = _
    unfold proofInputs
    rw [unkeep_consKept_value, onlyValues_ownValues]
  rw [← key, ownValues_onlyValues]

/-- What a role holds of a value of another role before values of the side of the role
alone: what it holds of them. -/
theorem ownValues_withoutProof {role other : Nat} (differ : role ≠ other) {proof : Ty}
    {rest : List Located} (held : SideValue model (single role) ⟨proof, other⟩)
    (values : Values (SideValue model (single role)) rest) :
    ownValues model (single role) role (Side.single_inside role) (⟨proof, other⟩ :: rest)
        (Values.cons (Value := SideValue model (single role)) (ty := ⟨proof, other⟩) held values) =
      inputsWithoutProof model differ
        (ownValues model (single role) role (Side.single_inside role) rest values) := by
  have absent : Nat.beq other role = false := by
    cases same : Nat.beq other role with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  have key : onlyValues model role (⟨proof, other⟩ :: rest)
        (inputsWithoutProof model differ
          (ownValues model (single role) role (Side.single_inside role) rest values)) =
      Values.cons (Value := SideValue model (single role)) (ty := ⟨proof, other⟩) held values := by
    show Values.cons (ty := (⟨proof, other⟩ : Located))
        (unkeep (Nat.beq other role)
          (inputsWithoutProof model differ
            (ownValues model (single role) role (Side.single_inside role) rest values))).1
        (onlyValues model role rest
          (unkeep (Nat.beq other role)
            (inputsWithoutProof model differ
              (ownValues model (single role) role (Side.single_inside role) rest values))).2) = _
    unfold inputsWithoutProof
    rw [unkeep_consKept_absent _ absent, onlyValues_ownValues]
    exact congrArg
      (fun head => Values.cons (Value := SideValue model (single role)) (ty := ⟨proof, other⟩) head
        values)
      (Held.absent_unique (Nat.beq other role) absent _ _)
  rw [← key, ownValues_onlyValues]

/-- A run that returns a value, followed by a function of the value, returns the function's
value. -/
theorem ReturnsAlone.map {sampler : Sampler model} {α β : Type}
    {process : PIR.Process (Effects model) α} {asked : Asked} {value : α}
    (returns : ReturnsAlone sampler process asked value) (pack : α → β) :
    ReturnsAlone sampler (process.bind fun result => .done (pack result)) asked (pack value) := by
  induction returns with
  | done value asked => exact .done (pack value) asked
  | draw site law inputs next asked value _ ih =>
      exact .draw site law inputs (fun reply => (next reply).bind fun result => .done (pack result))
        asked (pack value) ih
  | sample site law inputs next asked value _ ih =>
      exact .sample site law inputs
        (fun reply => (next reply).bind fun result => .done (pack result)) asked (pack value) ih

end Values

/-! ## What the handler of a step sends for the side of the prover -/

section Sends

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {t : Threads}

/-- What the meaning of a rule sends for a side that holds the prover and not the verifier:
at an exchange of a value of which the condition holds, and at a draw, only values of which
the condition holds. -/
structure RuleResends (sem : RuleMeaning model t operations)
    (Sendable : (type : Ty) → model.Value type → Prop) : Prop where
  exchange : ∀ (place : Place) (number : Nat) (site : Site) (type : Ty)
    (value : model.Value type) (state : ThreadState model t true false), Sendable type value →
    EverySend Sendable (fun _ => True) (sem.exchange true false place number site type value state)
  draw : ∀ (place : Place) (number : Nat) (site : Site) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (state : ThreadState model t true false),
    EverySend Sendable (fun _ => True) (sem.draw true false place number site law state)

/-- The handler of a step, for a side that holds the prover and not the verifier, sends only
values of which the condition holds when the meaning of the rule does: at an operation that
the step rewrote it performs the rule's action, and every other effect as it is. -/
theorem threadHandler_resends {sem : RuleMeaning model t operations}
    {Sendable : (type : Ty) → model.Value type → Prop} (resends : RuleResends sem Sendable)
    (marks : Site → Option (Mark operations)) :
    ∀ (prover verifier : Bool), prover = true → verifier = false →
      Resends Sendable (threadHandler sem marks prover verifier)
  | true, false, _, _ => by
      intro effect state sends
      show EverySend Sendable (fun _ => True) (proverAct sem (marks effect.site) effect state)
      generalize marks effect.site = mark
      cases effect with
      | send site type value =>
          cases mark with
          | none => exact passEffect_sends _ state sends
          | some mark =>
              cases mark with
              | exchange place number =>
                  exact (everySend_bind Sendable _ _ _).mpr
                    (EverySend.mono (fun _ _ carried => carried) (fun _ _ => True.intro)
                      (resends.exchange place number site type value state sends))
              | draw byVerifier place number law =>
                  cases byVerifier <;> exact passEffect_sends _ state sends
      | receive site type =>
          cases mark with
          | none => exact passEffect_sends _ state sends
          | some mark =>
              cases mark with
              | exchange place number => exact passEffect_sends _ state sends
              | draw byVerifier place number law =>
                  cases byVerifier with
                  | false => exact passEffect_sends _ state sends
                  | true =>
                      show EverySend Sendable (fun _ => True) (dite _ _ _)
                      split
                      · exact (everySend_bind Sendable _ _ _).mpr
                          (EverySend.mono (fun _ _ carried => carried) (fun _ _ => True.intro)
                            (resends.draw place number site law state))
                      · exact passEffect_sends _ state sends
      | draw site row inputs =>
          cases mark with
          | none => exact passEffect_sends _ state sends
          | some mark =>
              cases mark with
              | exchange place number => exact passEffect_sends _ state sends
              | draw byVerifier place number law =>
                  cases byVerifier with
                  | true => exact passEffect_sends _ state sends
                  | false =>
                      show EverySend Sendable (fun _ => True) (dite _ _ _)
                      split
                      · exact (everySend_bind Sendable _ _ _).mpr
                          (EverySend.mono (fun _ _ carried => carried) (fun _ _ => True.intro)
                            (resends.draw place number site law state))
                      · exact passEffect_sends _ state sends
      | sample site row inputs =>
          cases mark with
          | none => exact passEffect_sends _ state sends
          | some mark =>
              cases mark with
              | exchange place number => exact passEffect_sends _ state sends
              | draw byVerifier place number law =>
                  cases byVerifier <;> exact passEffect_sends _ state sends
      | read site type position =>
          cases mark with
          | none => exact passEffect_sends _ state sends
          | some mark =>
              cases mark with
              | exchange place number => exact passEffect_sends _ state sends
              | draw byVerifier place number law =>
                  cases byVerifier <;> exact passEffect_sends _ state sends

/-- A role's derivation performs no effect over functions that perform none. -/
theorem Deriver.run_quiet {functionTable : FunctionTable model functions}
    (quiet : QuietTable functionTable) {state output : Ty}
    (deriver : Deriver operations functions state output) (present : Bool)
    (current : Held (model.Value state) present) :
    (deriver.run functionTable present current).Quiet := by
  cases deriver with
  | row label name derive applies =>
      exact PIR.Process.Quiet.bind
        (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _)
        fun _ => PIR.Process.Quiet.done _
  | handler callee =>
      exact PIR.Process.Quiet.bind (performStep_quiet (fun values => quiet callee values) _ _)
        fun _ => PIR.Process.Quiet.done _

/-- What the Fiat–Shamir rule sends for a side that holds the prover and not the verifier:
at an exchange it sends the value as it is and then absorbs without an effect; at a draw it
derives the coin without an effect. -/
theorem fiatShamirMeaning_resends (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    (Sendable : (type : Ty) → model.Value type → Prop) :
    RuleResends (fiatShamirMeaning suite functionTable) Sendable := by
  refine ⟨?_, ?_⟩
  · intro place number site type value state sends
    simp only [fiatShamirMeaning]
    split
    · exact And.intro sends
        (EverySend.of_quiet
          (PIR.Process.Quiet.bind (PIR.Process.Quiet.done _) fun _ =>
            PIR.Process.Quiet.bind (Absorber.run_quiet quiet _ _ _ _) fun _ =>
              PIR.Process.Quiet.bind (Absorber.run_quiet quiet _ _ _ _) fun _ =>
                PIR.Process.Quiet.done _)
          fun _ => True.intro)
    · exact True.intro
  · intro place number site inputs output law state
    refine EverySend.of_quiet ?_ fun _ => True.intro
    simp only [fiatShamirMeaning]
    split
    · split
      · exact PIR.Process.Quiet.bind (Deriver.run_quiet quiet _ _ _) fun _ =>
          PIR.Process.Quiet.bind (Deriver.run_quiet quiet _ _ _) fun _ =>
            PIR.Process.Quiet.done _
      · exact PIR.Process.Quiet.halt _
    · exact PIR.Process.Quiet.halt _

end Sends

/-! ## The Fiat–Shamir image of an entry for the side of the prover -/

section FiatShamir

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The Fiat–Shamir image of an entry, whether the step rewrote the entry or copied it, for a
side that holds the prover and not the verifier: the image sends only values of which a
condition holds, and returns values of which another holds, when the entry does. The image
is the entry interpreted by the handler of the step, which sends the value of a rewritten
exchange as it is and derives a coin instead of receiving it, between a start and a finish
that perform no effect. -/
theorem fiatShamir_sends (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var once.headers header, image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = false →
      ∀ (arguments : Values (SideValue model side) header.inputs)
        (Sendable : (type : Ty) → model.Value type → Prop)
        (after : Values (SideValue model side) header.outputs → Prop),
        EverySend Sendable after
            ((protocols.table model functionTable identities).get declared path side arguments) →
          EverySend Sendable after
            ((once.protocols.table model functionTable once.identities).get image path side
              arguments) := by
  cases rewrote : once.rewroteEntry with
  | true =>
      obtain ⟨image, newest, threads⟩ := stepProtocols_entry_rewritten quiet
        (fiatShamirRule_sound suite functionTable) (fiatShamirEntry_sound suite functionTable)
        identities number roles protocols once steps declared isEntry rewrote
      refine ⟨image, newest, fun path side isProver noVerifier arguments Sendable after sent => ?_⟩
      refine Eq.mpr (congrArg (EverySend Sendable after)
        (threads path side (.inl ⟨isProver, noVerifier⟩) arguments)) ?_
      refine EverySend.after_quiet
        ((fiatShamirEntry_sound suite functionTable).startQuiet quiet side roles header arguments)
        fun state => ?_
      exact (everySend_bind Sendable after _ _).mpr
        (EverySend.interpretWith
          (threadHandler_resends (fiatShamirMeaning_resends suite quiet Sendable) _ _ _ isProver
            noVerifier)
          _ state sent)
  | false =>
      obtain ⟨image, newest, same⟩ := stepProtocols_entry_copied (model := model)
        (functionTable := functionTable) identities number roles protocols once steps declared
        isEntry rewrote
      refine ⟨image, newest, fun path side _ _ arguments Sendable after sent => ?_⟩
      rw [same]
      exact sent

end FiatShamir

/-! ## The two steps -/

section Steps

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The Fiat–Shamir step and then the serialize step replay: for a program on which the two
steps return, as `construct` calls them, the declared entry and its image after both steps,
the newest protocol of the result, are related by `SerializedReplaysOn`, for a suite that
returns, all laws of the layout and every inputs on which the prover's and the verifier's
copies of the statement are equal. The premises of that statement are about the declared
entry: every run of it for the prover and the verifier together returns, and every value
that it sends for the prover alone is one that the layout can write. -/
theorem fiatShamir_serialize_replays (suite : Suite operations functions)
    (layout : Layout operations) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (program : Program typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (stepsOnce : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles program.protocols = .ok once)
    (twice : Stepped typeTable operations functions)
    (stepsTwice : stepProtocols layout.threads (serializeRule layout) once.identities
      (once.headers.length - 1) roles once.protocols = .ok twice)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var twice.headers
        ((serializeRule (functions := functions) layout).entryHeader roles header),
      image.index = 0 ∧
      ∀ (returns : suite.Returns (program.functionTable model)) (laws : layout.Lawful model)
        (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
          header.inputs),
        StatementCopiesEqual model ((single roles.prover).union (single roles.verifier)) roles
          header inputs →
        SerializedReplaysOn layout laws roles header
          ((program.protocolTable model identities).get declared)
          ((twice.protocols.table model (program.functionTable model) twice.identities).get image)
          inputs := by
  have quiet : QuietTable (program.functionTable model) := Functions.table_quiet program.functions
  have differ := stepProtocols_roles_differ identities number roles program.protocols once stepsOnce
  obtain ⟨inner, innerNewest, sends⟩ := fiatShamir_sends suite quiet identities number roles
    program.protocols once stepsOnce declared isEntry
  obtain ⟨image, newest, replays⟩ := serialize_entry_replays (model := model) layout
    once.identities (once.headers.length - 1) roles
    (⟨program.functions, once.protocols⟩ : Program typeTable operations functions once.headers)
    twice stepsTwice inner (by rw [innerNewest]; omega)
  refine ⟨image, newest, fun returns laws inputs agrees holds every writable sampler given => ?_⟩
  obtain ⟨other, otherNewest, together⟩ := fiatShamir_together suite returns identities number
    roles program.protocols once stepsOnce declared isEntry
  have same : other = inner := Var.ext (otherNewest.trans innerNewest.symm)
  subst same
  have noReader : single roles.prover roles.verifier = false := by
    show Nat.beq roles.verifier roles.prover = false
    cases same : Nat.beq roles.verifier roles.prover with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  exact replays laws inputs holds
    (together [] ((single roles.prover).union (single roles.verifier))
      (union_first (first := single roles.prover) (Nat.beq_refl _))
      (union_second (second := single roles.verifier) (Nat.beq_refl _)) inputs agrees holds every)
    (sends [] (single roles.prover) (Nat.beq_refl _) noReader _ _ _ writable) sampler given

end Steps

/-! ## The role programs of a serialized entry -/

section Roles

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- From the statement about the two sides of a serialized entry to completeness of the
scheme of its two role programs. `table` and `called` are the meanings of the protocols and
of the role programs of the result; `constructed` is the serialized entry, related to an
interactive entry by `SerializedReplaysOn` on the given inputs. When the interactive entry
is complete on them for the prover and the verifier together, and every value that it sends
for the prover alone is one that the layout can write: for every sampler the program of the
prover, on the prover's share of the inputs, returns a proof before its other outputs, and
the program of the verifier, on that proof before the verifier's share of the inputs,
returns outputs that are accepted, read as the outputs of the interactive verifier. -/
theorem SerializedReplaysOn.derivedComplete {new : List ProtocolHeader}
    {programs : List RoleHeader} {table : ProtocolTable model new}
    {called : RoleTable model programs} {callees : ProjectedCallees new programs}
    (sound : CalleesSound model table called callees) (layout : Layout operations)
    (laws : layout.Lawful model) (roles : TranscriptRoles)
    (differ : roles.prover ≠ roles.verifier) {header : ProtocolHeader}
    (entry : header.Meaning model)
    (constructed : Var new
      ((serializeRule (functions := functions) layout).entryHeader roles header))
    (derivedProver : Var programs
      (roleHeader roles.prover
        ((serializeRule (functions := functions) layout).entryHeader roles header)))
    (derivedVerifier : Var programs
      (roleHeader roles.verifier
        ((serializeRule (functions := functions) layout).entryHeader roles header)))
    (namedProver : callees.find constructed roles.prover = some derivedProver)
    (namedVerifier : callees.find constructed roles.verifier = some derivedVerifier)
    (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
      header.inputs)
    (replays : SerializedReplaysOn layout laws roles header entry (table.get constructed) inputs)
    (writable : EverySend laws.Writable (fun _ => True)
      (entry [] (single roles.prover)
        (leftValues model (single roles.prover) (single roles.verifier) inputs)))
    (acceptedInteractive : Values model.Value (own roles.verifier header.outputs) → Prop)
    (complete : GroupedComplete
      (entry [] ((single roles.prover).union (single roles.verifier)) inputs)
      fun outputs => acceptedInteractive (verifierShare model roles outputs)) :
    DerivedComplete
      ((called.get derivedProver []
          (inputsWithoutProof model differ (proverShare model roles inputs))).bind fun outputs =>
        .done (provedOutputs model roles.prover outputs))
      (fun proof =>
        called.get derivedVerifier []
          (proofInputs model roles.verifier proof (verifierShare model roles inputs)))
      (fun outputs => acceptedInteractive (outputsWithoutProof model outputs)) := by
  intro sampler
  have noReader : single roles.prover roles.verifier = false := by
    show Nat.beq roles.verifier roles.prover = false
    cases same : Nat.beq roles.verifier roles.prover with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differ
  obtain ⟨outputs, proof, accepts, proves, verifies⟩ :=
    replays _ complete.everyRun writable sampler (Held.absent _ noReader)
  refine ⟨proof, proverShare model roles outputs, ?_,
    inputsWithoutProof model differ.symm (verifierShare model roles outputs), ?_, ?_⟩
  · -- The program of the prover is the serialized entry for the prover alone.
    have meaning := sound.program constructed roles.prover derivedProver namedProver []
      (single roles.prover) (Side.only_single _ _) (Side.single_inside _)
      (Values.cons (Value := SideValue model (single roles.prover))
        (ty := ⟨layout.proof, roles.verifier⟩) (Held.absent _ noReader)
        (leftValues model (single roles.prover) (single roles.verifier) inputs))
    have atInputs := (congrArg (called.get derivedProver [])
      (ownValues_withoutProof differ (Held.absent _ noReader)
        (leftValues model (single roles.prover) (single roles.verifier) inputs))).symm.trans meaning
    refine Eq.mpr (congrArg (fun process => ReturnsAlone sampler
      (process.bind fun outputs => .done (provedOutputs model roles.prover outputs)) Asked.start _)
      atInputs) ?_
    have returned := (proves.map
      (ownValues model (single roles.prover) roles.prover (Side.single_inside _)
        (⟨layout.proof, roles.prover⟩ :: header.outputs))).map (provedOutputs model roles.prover)
    exact Eq.mp (congrArg (ReturnsAlone sampler _ Asked.start)
      ((congrArg (provedOutputs model roles.prover)
        (ownValues_proof roles.prover proof
          (leftValues model (single roles.prover) (single roles.verifier) outputs))).trans
        (provedOutputs_proofInputs roles.prover proof _))) returned
  · -- The program of the verifier is the serialized entry for the verifier alone.
    have meaning := sound.program constructed roles.verifier derivedVerifier namedVerifier []
      (single roles.verifier) (Side.only_single _ _) (Side.single_inside _)
      (Values.cons (Value := SideValue model (single roles.verifier))
        (ty := ⟨layout.proof, roles.verifier⟩)
        (Held.of (single roles.verifier roles.verifier) proof)
        (rightValues model (single roles.prover) (single roles.verifier) inputs))
    have atInputs := (congrArg (called.get derivedVerifier [])
      (ownValues_proof roles.verifier proof
        (rightValues model (single roles.prover) (single roles.verifier) inputs))).symm.trans
        meaning
    refine Eq.mpr (congrArg (fun process => ReturnsAlone sampler process Asked.start _) atInputs) ?_
    have returned := verifies.map
      (ownValues model (single roles.verifier) roles.verifier (Side.single_inside _)
        (⟨layout.proof, roles.prover⟩ :: header.outputs))
    exact Eq.mp (congrArg (ReturnsAlone sampler _ Asked.start)
      (ownValues_withoutProof differ.symm (Held.of (single roles.verifier roles.prover) proof)
        (rightValues model (single roles.prover) (single roles.verifier) outputs))) returned
  · exact Eq.mpr (congrArg acceptedInteractive
      (outputsWithoutProof_inputsWithoutProof differ.symm _)) accepts

end Roles

/-! ## The scheme of the results of the steps -/

section Scheme

-- The hypotheses under the quantifier of a statement are named for what they say.
set_option linter.unusedVariables false

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- Completeness of the scheme that the serialize step derives from an interactive program
(a construction whose Fiat–Shamir step is authored). The newest protocol of the result is
the serialized entry (`constructed`), and the derived prover and verifier are its role
programs. For all laws of the layout and the inputs of a run of the declared entry for the
prover and the verifier together: when every value that the entry sends for the prover
alone is one that the layout can write, and the entry is complete for every sampler with
the verifier's share of its outputs accepted, then for every sampler the derived prover, on
the prover's share of the inputs, returns a proof before its other outputs, and the derived
verifier, on that proof before the verifier's share of the inputs, returns outputs that are
accepted, read as the outputs of the interactive verifier. -/
theorem serialize_complete (layout : Layout operations) (identities : Identities) (number : Nat)
    (roles : TranscriptRoles) {old : List ProtocolHeader}
    (program : Program typeTable operations functions old)
    (serialized : Stepped typeTable operations functions)
    (steps : stepProtocols layout.threads (serializeRule layout) identities number roles
      program.protocols = .ok serialized)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (derived : Projected operations functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := functions) layout).entryHeader roles header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader roles.prover
            ((serializeRule (functions := functions) layout).entryHeader roles header)))
        (derivedVerifier : Var derived.headers
          (roleHeader roles.verifier
            ((serializeRule (functions := functions) layout).entryHeader roles header)))
        (namedDerivedProver : derived.callees.find constructed roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed roles.verifier = some derivedVerifier)
        (laws : layout.Lawful model)
        (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
          header.inputs)
        (writable : EverySend laws.Writable (fun _ => True)
          ((program.protocolTable model identities).get declared [] (single roles.prover)
            (leftValues model (single roles.prover) (single roles.verifier) inputs)))
        (acceptedInteractive : Values model.Value (own roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((program.protocolTable model identities).get declared []
            ((single roles.prover).union (single roles.verifier)) inputs)
          fun outputs => acceptedInteractive (verifierShare model roles outputs)),
        DerivedComplete
          (((derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedProver []
              (inputsWithoutProof model
                (stepProtocols_roles_differ identities number roles program.protocols serialized
                  steps)
                (proverShare model roles inputs))).bind fun outputs =>
            .done (provedOutputs model roles.prover outputs))
          (fun proof =>
            (derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedVerifier []
              (proofInputs model roles.verifier proof (verifierShare model roles inputs)))
          (fun outputs => acceptedInteractive (outputsWithoutProof model outputs)) := by
  obtain ⟨constructed, newest, replays⟩ := serialize_entry_replays (model := model) layout
    identities number roles program serialized steps declared isEntry
  refine ⟨constructed, newest, ?_⟩
  intro derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier laws inputs writable
    acceptedInteractive complete
  exact SerializedReplaysOn.derivedComplete
    (projectProtocols_sound (functionTable := program.functionTable model) serialized.identities
      serialized.protocols derived projectsDerived)
    layout laws roles _ _ constructed derivedProver derivedVerifier namedDerivedProver
    namedDerivedVerifier inputs (replays laws inputs) writable acceptedInteractive complete

/-- Completeness of the scheme that the Fiat–Shamir step and then the serialize step derive
from an interactive program, as `construct` calls them: the second step runs on the result
of the first, with its newest protocol as the entry and the identities that the first step
left. The newest protocol of the result is the constructed entry (`constructed`), and the
derived prover and verifier are its role programs. For a suite that returns, all laws of the
layout and inputs of a run of the declared entry for the prover and the verifier together on
which their copies of the statement are equal: when every value that the entry sends for
the prover alone is one that the layout can write, and the entry is complete for every
sampler with the verifier's share of its outputs accepted, then for every sampler the
derived prover, on the prover's share of the inputs, returns a proof before its other
outputs, and the derived verifier, on that proof before the verifier's share of the inputs,
returns outputs that are accepted, read as the outputs of the interactive verifier. Whether
the Fiat–Shamir step rewrote the entry or copied it is not a premise. -/
theorem fiatShamir_serialize_complete (suite : Suite operations functions)
    (layout : Layout operations) (identities : Identities) (number : Nat)
    (roles : TranscriptRoles) {old : List ProtocolHeader}
    (program : Program typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (stepsOnce : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles program.protocols = .ok once)
    (serialized : Stepped typeTable operations functions)
    (stepsTwice : stepProtocols layout.threads (serializeRule layout) once.identities
      (once.headers.length - 1) roles once.protocols = .ok serialized)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (derived : Projected operations functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := functions) layout).entryHeader roles header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader roles.prover
            ((serializeRule (functions := functions) layout).entryHeader roles header)))
        (derivedVerifier : Var derived.headers
          (roleHeader roles.verifier
            ((serializeRule (functions := functions) layout).entryHeader roles header)))
        (namedDerivedProver : derived.callees.find constructed roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed roles.verifier = some derivedVerifier)
        (returns : suite.Returns (program.functionTable model)) (laws : layout.Lawful model)
        (inputs : Values (SideValue model ((single roles.prover).union (single roles.verifier)))
          header.inputs)
        (agrees : StatementCopiesEqual model
          ((single roles.prover).union (single roles.verifier)) roles header inputs)
        (writable : EverySend laws.Writable (fun _ => True)
          ((program.protocolTable model identities).get declared [] (single roles.prover)
            (leftValues model (single roles.prover) (single roles.verifier) inputs)))
        (acceptedInteractive : Values model.Value (own roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((program.protocolTable model identities).get declared []
            ((single roles.prover).union (single roles.verifier)) inputs)
          fun outputs => acceptedInteractive (verifierShare model roles outputs)),
        DerivedComplete
          (((derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedProver []
              (inputsWithoutProof model
                (stepProtocols_roles_differ identities number roles program.protocols once
                  stepsOnce)
                (proverShare model roles inputs))).bind fun outputs =>
            .done (provedOutputs model roles.prover outputs))
          (fun proof =>
            (derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedVerifier []
              (proofInputs model roles.verifier proof (verifierShare model roles inputs)))
          (fun outputs => acceptedInteractive (outputsWithoutProof model outputs)) := by
  obtain ⟨constructed, newest, replays⟩ := fiatShamir_serialize_replays (model := model) suite
    layout identities number roles program once stepsOnce serialized stepsTwice declared isEntry
  refine ⟨constructed, newest, ?_⟩
  intro derivedProver derivedVerifier namedDerivedProver namedDerivedVerifier returns laws inputs
    agrees writable acceptedInteractive complete
  exact SerializedReplaysOn.derivedComplete
    (projectProtocols_sound (functionTable := program.functionTable model) serialized.identities
      serialized.protocols derived projectsDerived)
    layout laws roles _ _ constructed derivedProver derivedVerifier namedDerivedProver
    namedDerivedVerifier inputs (replays returns laws inputs agrees) writable acceptedInteractive
    complete

end Scheme

/-! ## The scheme of a declaration -/

section Declaration

-- The hypotheses under the quantifier of a statement are named for what they say.
set_option linter.unusedVariables false

variable {model : Model}

/-- What the serialize step of a declaration computed on a program: the step of the
serialize rule of the declared layout, with the newest protocol as the entry and the
declared roles. -/
theorem serializeProtocols_steps {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} {old : List ProtocolHeader} (declaration : Raw.Declaration)
    (identities : Identities) (protocols : Protocols typeTable operations functions old)
    (layout : Layout operations)
    (isLayout : declaration.layout.bind (Layout.ofRaw (tableScope operations)) = some layout)
    (serialized : Stepped typeTable operations functions)
    (serializes : serializeProtocols declaration identities protocols = .ok serialized) :
    stepProtocols layout.threads (serializeRule layout) identities (old.length - 1)
        declaration.roles protocols = .ok serialized := by
  unfold serializeProtocols at serializes
  rw [isLayout] at serializes
  exact serializes

/-- Completeness of the scheme that the serialize step of a declaration derives from a
program whose Fiat–Shamir step is authored (`serializeProtocols`: the entry is the newest
protocol). The premises say which programs were constructed: the result of the step, the
layout that the declaration names, the entry, and the projection of the result with its two
role programs. Then, for all laws of the layout and the inputs of a run of the entry for the
prover and the verifier together: when every value that the entry sends for the prover
alone is one that the layout can write, and the entry is complete for every sampler with
the verifier's share of its outputs accepted, the derived scheme is complete, with the
outputs of the derived verifier accepted when they are, read as the outputs of the
interactive verifier. -/
theorem serializeProtocols_complete {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {old : List ProtocolHeader} (declaration : Raw.Declaration) (identities : Identities)
    (program : Program typeTable operations functions old)
    (serialized : Stepped typeTable operations functions)
    (serializes : serializeProtocols declaration identities program.protocols = .ok serialized)
    (layout : Layout operations)
    (isLayout : declaration.layout.bind (Layout.ofRaw (tableScope operations)) = some layout)
    {header : ProtocolHeader} (declared : Var old header) (isEntry : declared.index = 0)
    (derived : Projected operations functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := functions) layout).entryHeader declaration.roles header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader declaration.roles.prover
            ((serializeRule (functions := functions) layout).entryHeader declaration.roles
              header)))
        (derivedVerifier : Var derived.headers
          (roleHeader declaration.roles.verifier
            ((serializeRule (functions := functions) layout).entryHeader declaration.roles
              header)))
        (namedDerivedProver :
          derived.callees.find constructed declaration.roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed declaration.roles.verifier = some derivedVerifier)
        (laws : layout.Lawful model)
        (inputs : Values
          (SideValue model
            ((single declaration.roles.prover).union (single declaration.roles.verifier)))
          header.inputs)
        (writable : EverySend laws.Writable (fun _ => True)
          ((program.protocolTable model identities).get declared []
            (single declaration.roles.prover)
            (leftValues model (single declaration.roles.prover)
              (single declaration.roles.verifier) inputs)))
        (acceptedInteractive :
          Values model.Value (own declaration.roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((program.protocolTable model identities).get declared []
            ((single declaration.roles.prover).union (single declaration.roles.verifier)) inputs)
          fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)),
        DerivedComplete
          (((derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedProver []
              (inputsWithoutProof model
                (stepProtocols_roles_differ identities (old.length - 1) declaration.roles
                  program.protocols serialized
                  (serializeProtocols_steps declaration identities program.protocols layout
                    isLayout serialized serializes))
                (proverShare model declaration.roles inputs))).bind fun outputs =>
            .done (provedOutputs model declaration.roles.prover outputs))
          (fun proof =>
            (derived.programs.table model (program.functionTable model)
                serialized.identities).get derivedVerifier []
              (proofInputs model declaration.roles.verifier proof
                (verifierShare model declaration.roles inputs)))
          (fun outputs => acceptedInteractive (outputsWithoutProof model outputs)) :=
  serialize_complete layout identities (old.length - 1) declaration.roles program serialized
    (serializeProtocols_steps declaration identities program.protocols layout isLayout serialized
      serializes)
    declared (by rw [isEntry]; omega) derived projectsDerived

/-- A declaration whose pipeline has a result names two different roles. -/
theorem construct_roles_differ (typed : Typed) (declaration : Raw.Declaration)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized) :
    declaration.roles.prover ≠ declaration.roles.verifier := by
  obtain ⟨_, _, once, _, _, derives, _, _⟩ :=
    construct_steps typed declaration serialized constructs
  exact fiatShamir_roles_differ typed declaration once derives

/-- Completeness of the scheme that the pipeline of a declaration derives from a typed
package (`construct`: the Fiat–Shamir step, then the serialize step).

The premises say which programs were constructed: the result of the pipeline, the suite and
the layout that the declaration names, the declared entry, and the projection of the result
with its two role programs; the newest protocol of the result is the constructed entry
(`constructed`). Then, for a suite that returns, all laws of the layout and inputs of a run
of the declared entry for the prover and the verifier together on which their copies of the
statement are equal: when every value that the interactive entry sends for the prover alone
is one that the layout can write, and the interactive entry is complete for every sampler
with the verifier's share of its outputs accepted, then for every sampler the constructed
prover, on the prover's share of the inputs, returns a proof before its other outputs, and
the constructed verifier, on that proof before the verifier's share of the inputs, returns
outputs that are accepted, read as the outputs of the interactive verifier
(`outputsWithoutProof`: the proof is an output of the prover). -/
theorem construct_complete (typed : Typed) (declaration : Raw.Declaration)
    (serialized : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions)
    (constructs : construct typed declaration = .ok serialized)
    (suite : Suite (typed.table.map (·.signature)) typed.functions)
    (isSuite : declaration.suite.map
        (Suite.ofRaw (tableScope (typed.table.map (·.signature))) (tableScope typed.functions)) =
      some suite)
    (layout : Layout (typed.table.map (·.signature)))
    (isLayout : declaration.layout.bind
        (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    {header : ProtocolHeader} (declared : Var typed.protocols header)
    (isEntry : declared.index = typed.protocols.length - 1 - declaration.entry)
    (derived : Projected (typed.table.map (·.signature)) typed.functions serialized.headers)
    (projectsDerived : projectProtocols serialized.protocols = .ok derived) :
    ∃ constructed : Var serialized.headers
        ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
          header),
      constructed.index = 0 ∧
      ∀ (derivedProver : Var derived.headers
          (roleHeader declaration.roles.prover
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (derivedVerifier : Var derived.headers
          (roleHeader declaration.roles.verifier
            ((serializeRule (functions := typed.functions) layout).entryHeader declaration.roles
              header)))
        (namedDerivedProver :
          derived.callees.find constructed declaration.roles.prover = some derivedProver)
        (namedDerivedVerifier :
          derived.callees.find constructed declaration.roles.verifier = some derivedVerifier)
        (returns : suite.Returns (typed.program.functionTable model))
        (laws : layout.Lawful model)
        (inputs : Values
          (SideValue model
            ((single declaration.roles.prover).union (single declaration.roles.verifier)))
          header.inputs)
        (agrees : StatementCopiesEqual model
          ((single declaration.roles.prover).union (single declaration.roles.verifier))
          declaration.roles header inputs)
        (writable : EverySend laws.Writable (fun _ => True)
          ((typed.program.protocolTable model Identities.written).get declared []
            (single declaration.roles.prover)
            (leftValues model (single declaration.roles.prover)
              (single declaration.roles.verifier) inputs)))
        (acceptedInteractive :
          Values model.Value (own declaration.roles.verifier header.outputs) → Prop)
        (complete : GroupedComplete
          ((typed.program.protocolTable model Identities.written).get declared []
            ((single declaration.roles.prover).union (single declaration.roles.verifier)) inputs)
          fun outputs => acceptedInteractive (verifierShare model declaration.roles outputs)),
        DerivedComplete
          (((derived.programs.table model (typed.program.functionTable model)
                serialized.identities).get derivedProver []
              (inputsWithoutProof model
                (construct_roles_differ typed declaration serialized constructs)
                (proverShare model declaration.roles inputs))).bind fun outputs =>
            .done (provedOutputs model declaration.roles.prover outputs))
          (fun proof =>
            (derived.programs.table model (typed.program.functionTable model)
                serialized.identities).get derivedVerifier []
              (proofInputs model declaration.roles.verifier proof
                (verifierShare model declaration.roles inputs)))
          (fun outputs => acceptedInteractive (outputsWithoutProof model outputs)) := by
  obtain ⟨foundSuite, foundLayout, once, namesSuite, namesLayout, _, stepsOnce, stepsTwice⟩ :=
    construct_steps typed declaration serialized constructs
  have sameSuite : foundSuite = suite := Option.some.inj (namesSuite.symm.trans isSuite)
  have sameLayout : foundLayout = layout := Option.some.inj (namesLayout.symm.trans isLayout)
  subst sameSuite sameLayout
  exact fiatShamir_serialize_complete foundSuite foundLayout Identities.written declaration.entry
    declaration.roles typed.program once stepsOnce serialized stepsTwice declared isEntry derived
    projectsDerived

end Declaration

end Zkc.Core

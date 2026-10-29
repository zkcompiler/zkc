module

public import ZkcExamples.Construction.SumcheckSourceConnection
public import ZkcExamples.Structured.OriginalSumcheckLibrary
public import ZkcExamples.Structured.SumcheckSourceContracts
public import ZkcExamples.Executable.SumcheckShape
public import ZkcExamples.Executable.SumcheckMetadata
public import Zkc.Construction.Uniform.ScalarCheckedFrames
public import Zkc.Construction.Uniform.ScalarSourceCost

@[expose] public section

/-! The retained round's full return invariant from its stored root connection.
The symbolic frame and source callback are projections of that same root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Executable.SumcheckCheckedRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Executable
open Uniform NormalForm ConnectionCertificate
open ZkcExamples.Structured
attribute [local implicit_reducible] CheckedProtocol.signature

abbrev program := ZkcExamples.Construction.SumcheckProof.program
abbrev context := ZkcExamples.Construction.SumcheckProof.context
abbrev routing := Generated.Connections.SmallSumcheck.validatorRouting
abbrev root := Generated.Connections.SmallSumcheck.validator

def extracted := (ScalarCheckedFrames.loops root.alignment.alignment)[0]'(by decide +kernel)
def frame := extracted.withOutput SumcheckVerifierBodies.repeatState (by kernel_rfl)
def library : ConnectionLibrary.Library program.payload frame.callees :=
  (root.library.library.entry ⟨0, by decide +kernel⟩).earlier

theorem source_payload : program.payload = SumcheckSourceViews.unit := by kernel_rfl

theorem helperBodies : SumcheckVerifierHelpers.Bodies program.payload.definitions := by
  rw [source_payload]
  exact SumcheckSourceVerifier.helperBodies

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def binders (values : List F) (claim : F) (rounds index : Nat) (point : List F) (current : F) :
    Binders (ringModel F G) frame.scope :=
  .cons index (.cons (SumcheckVerifierLaws.embedV (G := G) (some point, some current))
    (.cons (.cons (some []) (.cons (some claim) .nil))
      (.cons (.cons [] (.cons claim .nil)) (.cons values (.cons claim (.cons rounds .nil))))))

def inputs (values : List F) (claim : F) (rounds : Nat)
    (initial : Domain.History (uniformCarriers F G)) (index : Nat) (point : List F) (current : F)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim),
    .data (.index rounds), .transcript context.suite initial,
    .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" claim),
    .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" claim),
    .data (.index index), .data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" current),
    .transcript context.suite history]

theorem input_frame (values : List F) (claim : F) (rounds : Nat)
    (initial : Domain.History (uniformCarriers F G)) (index : Nat) (point : List F) (current : F)
    (history : Domain.History (uniformCarriers F G)) :
    ConnectionFrame.Holds (ringModel F G) (binders values claim rounds index point current) history frame.layout
      (inputs values claim rounds initial index point current history) :=
  ScalarCheckedFrames.realize_holds (ringModel F G)
    (binders values claim rounds index point current) history frame.layout
    (inputs values claim rounds initial index point current history)
    (inputs values claim rounds initial index point current history) (by rfl)

/-- Full frame simulation, reusing the selected subderivation and its original
normalizer equation instead of reconstructing physical slots or event routes. -/
def connection (values : List F) (claim : F) (rounds : Nat)
    (initial : Domain.History (uniformCarriers F G)) (index : Nat) (point : List F) (current : F)
    (history : Domain.History (uniformCarriers F G)) :=
  Alignment.librarySimulation library frame.checked (ringModel F G)
    {frames := frame.frames.eval (ringModel F G) (binders values claim rounds index point current), history := history}
    [] (binders values claim rounds index point current) rfl
    (inputs values claim rounds initial index point current history)
    (input_frame values claim rounds initial index point current history) (by simp [ArtifactBinding.Captures])

theorem callback_context : frame.context = SumcheckSourceVerifier.childContext := by kernel_rfl

theorem callback_role : frame.role = 1 := by kernel_rfl

theorem callback_identity : frame.region = SumcheckVerifierBodies.roundBody := by kernel_rfl

theorem callback_inputs (values : List F) (claim : F) (rounds index : Nat) (point : List F) (current : F) :
    Comps.eval (LawResults.empty (ringModel F G)) frame.inputs (binders values claim rounds index point current) =
      (.cons (some index) ((SumcheckVerifierLaws.embedV (G := G) (some point, some current)).append
        (.cons (some routing.selectedHandle) .nil))) := by kernel_rfl

theorem source_equation (values : List F) (claim : F) (rounds index : Nat) (point : List F) (current : F) :
    frame.form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) program.payload)
      (LawResults.empty (ringModel F G)) frame.context
      (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations (Occurrence.helpers (ringModel F G) program.payload)
        (Occurrence.table (ringModel F G) program.payload) frame.context frame.role)
      (library.processes (ringModel F G)) (binders values claim rounds index point current) =
    ((SumcheckVerifierLaws.roundPlain (G := G) frame.context (some routing.selectedHandle) (some point, some current)).interpret
      OriginalSumcheckLibrary.actions).bind (fun result => .done (SumcheckVerifierLaws.embedV result)) := by
  refine (frame.source_eq library (ringModel F G) (binders values claim rounds index point current)).symm.trans ?_
  have round := OriginalSumcheckLibrary.round_on (G := G) program.payload frame.context (frame.context.roles frame.role)
    (Occurrence.table (ringModel F G) program.payload) Occurrence.iterations
    (.cons (some index) ((SumcheckVerifierLaws.embedV (G := G) (some point, some current)).append
      (.cons (some routing.selectedHandle) .nil)))
  rw [OriginalSumcheckLibrary.helpers_on] at round
  rw [callback_identity, callback_inputs]
  have role : frame.context.roles frame.role = frame.context.roles 1 :=
    congrArg frame.context.roles callback_role
  have separate : frame.context.roles 0 ≠ frame.context.roles frame.role := by
    rw [callback_context, callback_role]
    decide
  exact round.trans (OriginalSumcheckLibrary.round_verifier program.payload
    helperBodies frame.context (frame.context.roles frame.role) role separate
    index (some routing.selectedHandle) (some point) (some current))

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Every source return appends exactly one arbitrary challenge reply. -/
theorem source_yields (point : List F) (current : F) :
    PIR.Yields (fun result => ∃ next value,
      result = SumcheckVerifierLaws.embedV (G := G) (some next, some value) ∧
        next.length = point.length + 1)
      (((SumcheckVerifierLaws.roundPlain (G := G) frame.context (some routing.selectedHandle)
        (some point, some current)).interpret OriginalSumcheckLibrary.actions).bind
        (fun result => .done (SumcheckVerifierLaws.embedV result))) := by
  have raw : PIR.Yields (fun result => ∃ next value,
      result = (some next, some value) ∧ next.length = point.length + 1)
      (SumcheckVerifierLaws.roundPlain (G := G) frame.context (some routing.selectedHandle)
        (some point, some current)) := by
    simp only [SumcheckVerifierLaws.roundPlain, PIR.Yields]
    intro low high
    split
    · intro answer ignored
      change F at answer
      exact ⟨point ++ [answer], _, rfl, by simp⟩
    · trivial
  exact (raw.interpret OriginalSumcheckLibrary.actions).bind (by
    intro result valid
    obtain ⟨next, value, rfl, length⟩ := valid
    exact ⟨next, value, rfl, length⟩)

abbrev names := SumcheckShape.Names.of ZkcExamples.Construction.SumcheckProof.participant.instructions

theorem target_equation (environment : Domain.Environment (uniformCarriers F G)) :
    frame.target (ringModel F G) environment =
      Domain.evaluate (ringModel F G) program context (SumcheckShape.roundBody names) environment := by
  kernel_rfl


def SourceInvariant (count : Nat) (result : Values (Component (assignment F G)) frame.out) : Prop :=
  ∃ next value, result = SumcheckVerifierLaws.embedV (some next, some value) ∧ next.length = count

def TargetInvariant (count : Nat) (final : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ next value suffix, Domain.read final SumcheckShape.yielded = some
    [.data (.vector "bls12-381.fr" next), .data (.field "bls12-381.fr" value),
      .transcript context.suite suffix] ∧ next.length = count

theorem form_yields (values : List F) (claim : F) (rounds index : Nat) (point : List F) (current : F) :
    PIR.Yields (SourceInvariant (G := G) (point.length + 1))
      (frame.form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) program.payload)
        (LawResults.empty (ringModel F G)) frame.context
        (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations (Occurrence.helpers (ringModel F G) program.payload)
          (Occurrence.table (ringModel F G) program.payload) frame.context frame.role)
        (library.processes (ringModel F G)) (binders values claim rounds index point current)) := by
  rw [source_equation]
  exact source_yields point current

/-- Complete checked returns supply the carried row, including its history. -/
theorem returns_read (count : Nat) (original : Values (Component (assignment F G)) frame.out ×
    Original.State (uniformCarriers F G)) (final : Domain.Environment (uniformCarriers F G))
    (frames : Original.Frames)
    (related : Returns (model := ringModel F G) routing frame.role frame.scopes frame.outputs frame.history frames [] original final)
    (valid : SourceInvariant count original.1) : TargetInvariant count final := by
  obtain ⟨next, value, presented, length⟩ := valid
  obtain ⟨data, encoded, read⟩ := Original.outputReferences_read
    (maskValues frame.role frame.scopes original.1)
    (show Original.outputReferences frame.role frame.scopes frame.outputs = some [29,34] by decide +kernel)
    related.1
  have encoding : Original.roleOutputValues frame.role frame.scopes
      (maskValues frame.role frame.scopes (SumcheckVerifierLaws.embedV (G := G) (some next, some value))) =
        some [.data (.vector "bls12-381.fr" next), .data (.field "bls12-381.fr" value)] := by kernel_rfl
  rw [presented, encoding] at encoded
  cases encoded
  have profile : Original.profileReferences routing.context [29,34] frame.history = some SumcheckShape.yielded := by kernel_rfl
  have located := historyLocation_of_profile (model := ringModel F G) profile related.2.2.1
  have full := Original.profileReferences_read profile read located
  exact ⟨next, value, original.2.history, full, length⟩

/-- The stored round subderivation transports the source append invariant for
all replies. No physical instruction simulation is repeated. -/
theorem target_yields (values : List F) (claim : F) (rounds : Nat)
    (initial : Domain.History (uniformCarriers F G)) (index : Nat) (point : List F) (current : F)
    (history : Domain.History (uniformCarriers F G)) :
    PIR.Yields (TargetInvariant (point.length + 1))
      (Domain.evaluate (ringModel F G) program context (SumcheckShape.roundBody names)
        (inputs values claim rounds initial index point current history)) := by
  rw [← target_equation]
  refine ScalarSourceCost.yields
    (connection values claim rounds initial index point current history)
    (fun original => SourceInvariant (G := G) (point.length + 1) original.1)
    (TargetInvariant (G := G) (point.length + 1)) ?_ ?_
  · exact ScalarSourceCost.yields_state _ (Original.operations routing) _ _
      (form_yields values claim rounds index point current)
  · exact fun original final related valid => returns_read _ original final _ related valid

end ZkcExamples.Executable.SumcheckCheckedRound

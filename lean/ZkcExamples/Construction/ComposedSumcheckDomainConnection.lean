module

public import ZkcExamples.Construction.ComposedSumcheckProofData
public import ZkcExamples.Construction.ComposedSumcheckProofParticipant
public import ZkcExamples.Construction.ComposedSumcheckSourceRouting
public import ZkcExamples.Structured.Generated.Constructed.ComposedSumcheckValidator
public import Zkc.Construction.Compiled

@[expose] public section

/-! All-reply connection of the actual composed Sumcheck artifact. The exact
TwoSums source and artifact identities reuse its independent complete validator
certificate. Scalar keys are projected before the existing oracle/cache acts.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.ComposedSumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured

abbrev imported := Generated.Bindings.TwoSumsInputs.imported
abbrev program := imported.program
abbrev context := ComposedSumcheckSourceRouting.Retained.context
abbrev artifact := ComposedSumcheckProofParticipant.participant
abbrev routing := ComposedSumcheckSourceRouting.Retained.routing

/-- Complete literal identities, including metadata, helper/protocol bodies,
all loop bounds, captures, physical outputs and the return permutation. -/
theorem source_identity : program.snapshot = ComposedSumcheckProofData.snapshot := by kernel_rfl

theorem artifact_identity :
    ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.artifact = artifact := by kernel_rfl

theorem view_identity : Generated.Constructed.ComposedSumcheckValidator.artifact = artifact := rfl

theorem checked : Construction.checkCompiled imported artifact = .ok () := by decide +kernel

theorem context_checked : exportContext program.snapshot artifact = some context := by decide +kernel

def selection : Construction.Selection program.payload.entry.outputs :=
  ⟨context, 0, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr",
    .field "bls12-381.fr", .index], inputSlots context artifact.policy program.payload.entry.inputs, .here⟩

theorem selected : Construction.select imported artifact = some selection := by kernel_rfl

theorem selection_checked : selection.check imported artifact = true := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (left right : List F) (leftClaim rightClaim : F) (count handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
    (.cons (some count) (.cons (some handle) .nil)))))

def sourceVerifier (left right : List F) (leftClaim rightClaim : F) (count handle : Nat) :
    PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs left right leftClaim rightClaim count handle)).interpret
    CommonAdapter.project).bind fun outputs => .done (outputs.get .here)

def inputs (left right : List F) (leftClaim rightClaim : F) (count : Nat) :
    Domain.Environment (uniformCarriers F G) :=
  ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.inputs
    left right leftClaim rightClaim count []

theorem input_sorts (left right : List F) (leftClaim rightClaim : F) (count : Nat) :
    Domain.sortsMatch artifact.inputs (inputs (G := G) left right leftClaim rightClaim count) = true := by kernel_rfl

section Handler
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Every input, reply, malformed proof head, zero/excess bound and source stop.
The arbitrary initial legacy history remains outside nominal serialization. -/
theorem domain_to_source (challenge : History F G → m F)
    (left right : List F) (leftClaim rightClaim : F) (count handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    runK Origin.withoutCoordinates initial challenge
      (Domain.participant (ringModel F G) program context artifact
        (inputs left right leftClaim rightClaim count)) proof
      (fun result unread => pure (.returned (SourceProcess.acceptance result.values), unread)) =
    transform context challenge (sourceVerifier left right leftClaim rightClaim count handle) initial proof := by
  have certificate := ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.validator
    (F := F) (G := G) left right leftClaim rightClaim count handle []
  have structural := simulation_runK certificate Origin.withoutCoordinates initial challenge proof
    (fun original unread => pure (.returned (original.1.get .here), unread))
    (fun actual unread => pure (.returned (SourceProcess.acceptance actual.values), unread))
    (by
      intro original actual unread related
      obtain ⟨decision, sourceEq, valuesEq, _, _, _⟩ := related
      rw [sourceEq, valuesEq]
      rfl)
  rw [artifact_identity] at structural
  change runK Origin.withoutCoordinates initial challenge
      (Original.fold (routing handle)
        (Occurrence.participant (ringModel F G) program 1
          (sourceInputs left right leftClaim rightClaim count handle)) ⟨[], []⟩) proof
      (fun original unread => pure (.returned (original.1.get .here), unread)) =
    runK Origin.withoutCoordinates initial challenge
      (Domain.participant (ringModel F G) program context artifact
        (inputs left right leftClaim rightClaim count)) proof
      (fun actual unread => pure (.returned (SourceProcess.acceptance actual.values), unread)) at structural
  rw [← structural]
  rw [← runK_operations]
  let sourceLaw := (ComposedSumcheckSourceRouting.participant (G := G)
    left right leftClaim rightClaim count handle).simulation rfl _ rfl []
  have routed := simulation_runK sourceLaw SourceProcess.legacyOrigin initial challenge proof
    (fun scalar unread => pure (.returned (scalar.1.get .here), unread))
    (fun original unread => pure (.returned (original.1.get .here), unread))
    (by intro scalar original unread related; rw [related.1])
  refine routed.symm.trans ?_
  have shared := SourceProcess.sourceView_transform_map context challenge
    (((Occurrence.participant (ringModel F G) program 1
      (sourceInputs left right leftClaim rightClaim count handle)).interpret Occurrence.erase).interpret
        CommonAdapter.project) (fun outputs => outputs.get .here) initial proof
  have erased := scalar_participant (F := F) (G := G) program 1
    (sourceInputs left right leftClaim rightClaim count handle)
  have selectedErasure :
      ((((Occurrence.participant (ringModel F G) program 1
        (sourceInputs left right leftClaim rightClaim count handle)).interpret Occurrence.erase).interpret
          CommonAdapter.project).bind fun outputs => .done (outputs.get .here)) =
      sourceVerifier left right leftClaim rightClaim count handle :=
    congrArg (fun process : PIR.Process (Actions F G)
      (Values (Component (assignment F G)) program.payload.entry.outputs) =>
        process.bind fun outputs => .done (outputs.get .here)) erased
  exact shared.trans (congrArg (fun process : PIR.Process (Actions F G) (Option Bool) =>
    transform context challenge process initial proof) selectedErasure)

/-- Installed runtime connection, preserving the complete selected outcome and
unread proof. Full physical frames stay in the existing Domain runtime. -/
theorem actual_transform (challenge : History F G → m F)
    (left right : List F) (leftClaim rightClaim : F) (count handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => SourceProcess.acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle Origin.withoutCoordinates initial challenge)
        (Domain.participant (ringModel F G) program context artifact
          (inputs left right leftClaim rightClaim count))
        ⟨inputs left right leftClaim rightClaim count, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier left right leftClaim rightClaim count handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact
    (inputs left right leftClaim rightClaim count)
  let project := fun result : Domain.Result (uniformCarriers F G) => SourceProcess.acceptance result.values
  have installed := run_actual Origin.withoutCoordinates initial challenge actual
    (inputs left right leftClaim rightClaim count) proof
  have selectedRun := congrArg (fun action =>
    (fun result => (mapOutcome project result.1, result.2)) <$> action) installed
  simp only [Functor.map_map, Function.comp_def] at selectedRun
  calc
    _ = (fun result => (mapOutcome project result.1, embedProof result.2)) <$>
        run Origin.withoutCoordinates initial challenge actual proof := selectedRun
    _ = (fun result => (result.1, embedProof result.2)) <$>
        runK Origin.withoutCoordinates initial challenge actual proof
          (fun returned unread => pure (.returned (project returned), unread)) := by
      rw [← Zkc.Construction.Uniform.DomainAdapter.run_map Origin.withoutCoordinates initial challenge actual project proof]
      simp only [Functor.map_map]
    _ = _ := by rw [domain_to_source challenge left right leftClaim rightClaim count handle initial proof]

end Handler
end ZkcExamples.Construction.ComposedSumcheckDomainConnection

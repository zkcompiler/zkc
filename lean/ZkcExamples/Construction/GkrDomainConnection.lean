module

public import ZkcExamples.Construction.GkrDomainRoot
public import Zkc.Construction.Compiled

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainRoot

theorem source_identity : program.snapshot = GkrSourceData.snapshot := rfl

theorem view_identity : Generated.Constructed.GkrValidator.artifact = artifact := rfl

def selection : Construction.Selection program.payload.entry.outputs :=
  ⟨context, 0, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
    .vector "bls12-381.fr", .index, .index, .index],
    inputSlots context artifact.policy program.payload.entry.inputs, .here⟩

theorem selected : Construction.select imported artifact = some selection := by kernel_rfl

theorem selection_checked : selection.check imported artifact = true := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The complete public tuple and initial nominal suffix have the exact
selected artifact schema for every typed public value. -/
theorem input_sorts (inputs outputs add mul : List F) (count selector width : Nat)
    (suffix : Domain.History (uniformCarriers F G)) :
    Domain.sortsMatch artifact.inputs
      (artifactInputs (G := G) inputs outputs add mul count selector width suffix) = true := by kernel_rfl

section Handler
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- All four public tables, arbitrary layers, selector and width, every reply,
malformed proof head, zero/excess bound and stopped helper. The actual root and
its source participant are connected before any ArkLib reference hypotheses. -/
theorem domain_to_source (challenge : History F G → m F)
    (inputs outputs add mul : List F) (count selector width handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    runK Origin.withoutCoordinates initial challenge
      (Domain.participant (ringModel F G) program context artifact
        (artifactInputs inputs outputs add mul count selector width [])) proof
      (fun result unread => pure (.returned (SourceProcess.acceptance result.values), unread)) =
    transform context challenge (sourceVerifier inputs outputs add mul count selector width handle) initial proof := by
  have certificate := GkrDomainRoot.participant (G := G) inputs outputs add mul count selector width handle []
  have structural := simulation_runK certificate SourceProcess.legacyOrigin initial challenge proof
    (fun source unread => pure (.returned (some source.1), unread))
    (fun actual unread => pure (.returned (SourceProcess.acceptance actual.values), unread))
    (by
      intro source actual unread related
      obtain ⟨decision, suffix, sourceEq, valuesEq⟩ := related
      rw [sourceEq, valuesEq]
      rfl)
  rw [runK_operations] at structural
  refine structural.symm.trans ?_
  have shared := SourceProcess.sourceView_transform_map context challenge
    (verifier inputs outputs add mul count selector width handle) some initial proof
  exact shared.trans (congrArg (fun process : PIR.Process (Actions F G) (Option Bool) =>
    transform context challenge process initial proof)
      (source_equation inputs outputs add mul count selector width handle).symm)

/-- Installed runtime connection, preserving the complete selected outcome and
unread proof. Full physical frames stay in the existing Domain runtime. -/
theorem actual_transform (challenge : History F G → m F)
    (inputs outputs add mul : List F) (count selector width handle : Nat)
    (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => SourceProcess.acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle Origin.withoutCoordinates initial challenge)
        (Domain.participant (ringModel F G) program context artifact
          (artifactInputs inputs outputs add mul count selector width []))
        ⟨artifactInputs inputs outputs add mul count selector width [], embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier inputs outputs add mul count selector width handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact
    (artifactInputs inputs outputs add mul count selector width [])
  let project := fun result : Domain.Result (uniformCarriers F G) => SourceProcess.acceptance result.values
  have installed := run_actual Origin.withoutCoordinates initial challenge actual
    (artifactInputs inputs outputs add mul count selector width []) proof
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
    _ = _ := by rw [domain_to_source challenge inputs outputs add mul count selector width handle initial proof]

end Handler
end ZkcExamples.Construction.GkrDomainConnection

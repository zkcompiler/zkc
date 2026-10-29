module

public import ZkcExamples.Construction.GkrSourceHandles
public import ZkcExamples.Structured.Generated.Connections.Gkr
public import Zkc.Construction.ScalarConnection
public import Zkc.Construction.Uniform.ScalarSupportProposer
public import Zkc.Construction.Compiled

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol

theorem source_identity : program.snapshot = GkrSourceData.snapshot := rfl

theorem view_identity : Generated.Constructed.GkrValidator.artifact = artifact := rfl

def selection : Construction.Selection program.payload.entry.outputs :=
  ⟨context, 0, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr",
    .vector "bls12-381.fr", .index, .index, .index],
    inputSlots context artifact.policy program.payload.entry.inputs, .here⟩

theorem selected : Construction.select imported artifact = some selection := by kernel_rfl

theorem selection_checked : selection.check imported artifact = true := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The fixed public source order and transcript suffix, independent of any
mathematical circuit-validity condition. -/
def artifactInputs (inputs outputs add mul : List F) (count selector width : Nat)
    (suffix : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" inputs), .data (.vector "bls12-381.fr" outputs),
   .data (.vector "bls12-381.fr" add), .data (.vector "bls12-381.fr" mul),
   .data (.index count), .data (.index selector), .data (.index width),
   .transcript context.suite suffix]

def sourceABI : Original.InputABI :=
  (SourceConnection.canonicalABI program 1 artifact).toOption.get (by decide +kernel)

/-- The retained consumer reuses the exact root connection used by the nominal
completeness and soundness clients. Its derivation is not repeated here. -/
theorem checkedConnection : SourceConnection.Connected program
    Generated.Connections.Gkr.validatorRouting 1 sourceABI artifact :=
  ScalarConnection.canonicalize Generated.Connections.Gkr.validatorConnected (by rfl)


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
  let canonical := Generated.Connections.Gkr.validatorRouting.selectedHandle
  have law := ScalarConnection.transform (F := F) (G := G) checkedConnection
    rfl _ rfl (by decide +kernel)
    (artifactInputs inputs outputs add mul count selector width [])
    (sourceInputs inputs outputs add mul count selector width canonical)
    (by kernel_rfl) (by kernel_rfl) (by derive_scalar_support)
    .here (by rfl) challenge initial proof
  change _ = transform context challenge
    (sourceVerifier inputs outputs add mul count selector width canonical) initial proof at law
  have relabel := Uniform.ScalarHandles.transform context canonical challenge
    (sourceVerifier (G := G) inputs outputs add mul count selector width handle) initial proof
  rw [GkrSourceHandles.source_handle] at relabel
  have position : scopePosition 1 program.payload.entry.outputScopes
      (Var.here : Var program.payload.entry.outputs .boolean) = 0 := rfl
  have actualContext : Generated.Connections.Gkr.validatorRouting.context = context := by kernel_rfl
  have actualOrigin : ScalarVerifier.origin artifact = Origin.withoutCoordinates := by
    funext origin
    rfl
  simpa only [position, actualContext, actualOrigin, ScalarConnection.acceptance_first]
    using law.trans relabel

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

module

public import Zkc.Applications.IR.Construction.SchnorrAndProofData
public import Zkc.Applications.IR.Construction.SchnorrAndProofBodies
public import Zkc.Applications.IR.Construction.SchnorrAndProofModel
public import Zkc.Applications.IR.Construction.SchnorrAndProofParticipant
public import Zkc.IR.Construction.ScalarConnection
public import Zkc.IR.Construction.Uniform.ScalarSupportProposer
public import Zkc.IR.Construction.Uniform.ScalarHandles
public import Zkc.Applications.IR.Structured.Generated.Connections.SchnorrAnd
public import Zkc.Applications.IR.Construction.SchnorrAndProofPresentation
public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.Generated.Constructed.SchnorrAndValidator
public import Zkc.Program.Semantics.ReturnView

@[expose] public section

/-! Connection of the exact retained SchnorrAnd artifact and admitted source.
The full returned tuple and transcript suffix are preserved before selecting
Uniform.SourceProcess.acceptance. No relation or honest-input premise restricts public inputs. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SchnorrAndDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.SourceProcess

open SchnorrAndProof

abbrev artifact := participant

theorem artifact_identity : ZkcExamples.Structured.Generated.Constructed.SchnorrAndValidator.artifact = artifact := rfl

/-- Admission retains the entire literal source snapshot, including its
metadata and typed bodies, rather than only its digest. -/
theorem source_identity : program.snapshot = SchnorrAndProofData.snapshot :=
  imported.exactSubject

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some firstPoint) (.cons (some secondBase) (.cons (some secondPoint) (.cons (none) (.cons (none) (.cons (none) (.cons (some handle) (.nil))))))))

def sourceVerifier (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs firstBase firstPoint secondBase secondPoint handle)).bind fun outputs =>
    .done (outputs.get .here)).interpret CommonAdapter.project

/-- The actual source Process has this finite normal form for every reply. -/
theorem source_equation (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = Zkc.Protocols.Schnorr.Variants.conjunction SchnorrAndProof.wiring firstBase firstPoint secondBase secondPoint handle :=
  SchnorrAndProof.verifier_correspondence firstBase firstPoint secondBase secondPoint handle

def sourceDecision (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) : PIR.Process (Actions F G) Bool :=
  (sourceVerifier firstBase firstPoint secondBase secondPoint handle).bind fun decision => .done (decision.getD false)

theorem source_decision (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle =
      (sourceDecision firstBase firstPoint secondBase secondPoint handle).bind fun decision => .done (some decision) := by
  apply PIR.Process.reconstruct_from_reachable_view _ (fun decision ↦ decision.getD false) some
    _ (sourceDecision firstBase firstPoint secondBase secondPoint handle) rfl
  rw [source_equation]
  intro firstCommitment secondCommitment challenge sent firstResponse secondResponse
  rfl

def inputs (firstBase firstPoint secondBase secondPoint : G) : Domain.Environment (uniformCarriers F G) :=
  [.data (.group "bls12-381.g1" firstBase), .data (.group "bls12-381.g1" firstPoint), .data (.group "bls12-381.g1" secondBase), .data (.group "bls12-381.g1" secondPoint), .transcript context.suite []]

theorem input_sorts (firstBase firstPoint secondBase secondPoint : G) :
    Domain.sortsMatch artifact.inputs (inputs (F := F) (G := G) firstBase firstPoint secondBase secondPoint) = true := by kernel_rfl

def sourceABI : Original.InputABI :=
  (SourceConnection.canonicalABI program 1 artifact).toOption.get (by decide +kernel)

/-- The exact retained artifact uses the existing generic checked connection. -/
theorem checkedConnection : SourceConnection.Connected program
    ZkcExamples.Structured.Generated.Connections.SchnorrAnd.validatorRouting 1 sourceABI artifact :=
  ScalarConnection.canonicalize
    ZkcExamples.Structured.Generated.Connections.SchnorrAnd.validatorConnected (by rfl)

/-- Method-independent endpoint admission uses this same complete connection. -/
theorem requiredConnection : ConnectionAdmission.Required program context .validator artifact :=
  ConnectionAdmission.ofConnected (boundary := ⟨sourceABI,
    ZkcExamples.Structured.Generated.Connections.SchnorrAnd.validatorRouting⟩)
    (by kernel_rfl) checkedConnection

/-- Source-only presentation law for the capability label unobserved by the scalar handler. -/
theorem source_handle (firstBase firstPoint secondBase secondPoint : G) (original replacement : Nat) :
    (sourceVerifier (F := F) firstBase firstPoint secondBase secondPoint original).interpret (Uniform.ScalarHandles.replace replacement) =
      sourceVerifier firstBase firstPoint secondBase secondPoint replacement := by
  simp only [source_equation]
  rfl

section Boundary
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The full checked connection supplies execution transport for all proofs and replies. -/
theorem domain_transform (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
      (Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint)) proof
      (fun result unread => pure (.returned (Uniform.SourceProcess.acceptance result.values), unread)) =
    transform context challenge (sourceVerifier firstBase firstPoint secondBase secondPoint handle) initial proof := by
  let canonical := ZkcExamples.Structured.Generated.Connections.SchnorrAnd.validatorRouting.selectedHandle
  have law := ScalarConnection.transform (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    (inputs firstBase firstPoint secondBase secondPoint) (sourceInputs firstBase firstPoint secondBase secondPoint canonical) (by kernel_rfl) (by kernel_rfl)
    (by derive_scalar_support) .here (by rfl) challenge initial proof
  change _ = transform context challenge (sourceVerifier firstBase firstPoint secondBase secondPoint canonical) initial proof at law
  have relabel := Uniform.ScalarHandles.transform context canonical challenge
    (sourceVerifier (F := F) firstBase firstPoint secondBase secondPoint handle) initial proof
  rw [source_handle] at relabel
  have position : scopePosition 1 program.payload.entry.outputScopes
      (Var.here : Var program.payload.entry.outputs .boolean) = 0 := rfl
  have actualContext : ZkcExamples.Structured.Generated.Connections.SchnorrAnd.validatorRouting.context = context := by
    kernel_rfl
  have actualOrigin : ScalarVerifier.origin artifact = legacyOrigin := by
    funext origin
    rfl
  simpa only [position, actualContext, actualOrigin, ScalarConnection.acceptance_first]
    using law.trans relabel

/-- The installed Domain runtime has the same complete outcome and unread
proof after selecting Uniform.SourceProcess.acceptance. Physical frames remain with Domain.run.
No nominal random-oracle game is identified with the legacy oracle. -/
theorem actual_transform (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => Uniform.SourceProcess.acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle legacyOrigin initial challenge)
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint))
        ⟨inputs firstBase firstPoint secondBase secondPoint, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier firstBase firstPoint secondBase secondPoint handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint)
  let project := fun result : Domain.Result (uniformCarriers F G) => Uniform.SourceProcess.acceptance result.values
  have installed := run_actual legacyOrigin initial challenge actual (inputs firstBase firstPoint secondBase secondPoint) proof
  have selected := congrArg (fun action =>
    (fun result => (mapOutcome project result.1, result.2)) <$> action) installed
  simp only [Functor.map_map, Function.comp_def] at selected
  calc
    _ = (fun result => (mapOutcome project result.1, embedProof result.2)) <$>
        run legacyOrigin initial challenge actual proof := selected
    _ = (fun result => (result.1, embedProof result.2)) <$>
        runK legacyOrigin initial challenge actual proof
          (fun returned unread => pure (.returned (project returned), unread)) := by
      rw [← run_map legacyOrigin initial challenge actual project proof]
      simp only [Functor.map_map]
    _ = _ := by rw [domain_transform challenge firstBase firstPoint secondBase secondPoint handle]

end Boundary

end ZkcExamples.Construction.SchnorrAndDomainConnection

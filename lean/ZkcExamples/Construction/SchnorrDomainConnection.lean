module

public import ZkcExamples.Construction.SchnorrProofData
public import ZkcExamples.Construction.SchnorrProofBodies
public import ZkcExamples.Construction.SchnorrProofModel
public import ZkcExamples.Construction.SchnorrProofParticipant
public import Zkc.Construction.ScalarConnection
public import Zkc.Construction.Uniform.ScalarSupportProposer
public import Zkc.Construction.Uniform.ScalarHandles
public import Zkc.Construction.Uniform.ScalarPresentation
public import ZkcExamples.Structured.Generated.Connections.SchnorrRandomized
public import ZkcExamples.Construction.SchnorrArtifact
public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator

@[expose] public section

/-! Connection of the exact retained Schnorr artifact and admitted source.
The full returned tuple and transcript suffix are preserved before selecting
Uniform.SourceProcess.acceptance. No relation or honest-input premise restricts public inputs. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SchnorrDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.SourceProcess

open SchnorrProof

abbrev artifact := participant

theorem artifact_identity : ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.artifact = artifact := rfl

/-- Admission retains the entire literal source snapshot, including its
metadata and typed bodies, rather than only its digest. -/
theorem source_identity : program.snapshot = SchnorrProofData.snapshot :=
  imported.exactSubject

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (base point : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some base) (.cons (some point) (.cons (none) (.cons (none) (.cons (some handle) (.nil)))))

def sourceVerifier (base point : G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs base point handle)).bind fun outputs =>
    .done (outputs.get .here)).interpret CommonAdapter.project

/-- The actual source Process has this finite normal form for every reply. -/
theorem source_equation (base point : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) base point handle = Zkc.Protocols.Schnorr.Common.experiment SchnorrProof.wiring base point handle := by kernel_rfl

def sourceDecision (base point : G) (handle : Nat) : PIR.Process (Actions F G) Bool :=
  (sourceVerifier base point handle).bind fun decision => .done (decision.getD false)

theorem source_decision (base point : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) base point handle =
      (sourceDecision base point handle).bind fun decision => .done (some decision) := by
  rw [source_equation]
  simp only [sourceDecision, source_equation]
  kernel_rfl

def inputs (base point : G) : Domain.Environment (uniformCarriers F G) :=
  [.data (.group "bls12-381.g1" base), .data (.group "bls12-381.g1" point), .transcript context.suite []]

theorem input_sorts (base point : G) :
    Domain.sortsMatch artifact.inputs (inputs (F := F) (G := G) base point) = true := by kernel_rfl

def sourceABI : Original.InputABI :=
  (SourceConnection.canonicalABI program 1 artifact).toOption.get (by decide +kernel)

/-- The exact retained artifact consumes the same generic checked root as nominal clients. -/
theorem checkedConnection : SourceConnection.Connected program
    ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validatorRouting 1
    sourceABI artifact :=
  ScalarConnection.canonicalize
    ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validatorConnected (by rfl)

/-- Method-independent endpoint admission uses this same complete connection. -/
theorem requiredConnection : ConnectionAdmission.Required program context .validator artifact :=
  ConnectionAdmission.ofConnected (boundary := ⟨sourceABI,
    ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validatorRouting⟩)
    (by kernel_rfl) checkedConnection

/-- Capability labels are unobserved by the retained scalar API. This equation
is source mathematics; the nominal connection retains its canonical label. -/
theorem source_handle (base point : G) (original replacement : Nat) :
    (sourceVerifier (F := F) base point original).interpret (Uniform.ScalarHandles.replace replacement) =
      sourceVerifier base point replacement := by
  simp only [source_equation]
  rfl

/-- Complete source result as a presentation of the existing family process. -/
theorem source_values (base point : G) (handle : Nat) :
    (program.participant F G 1 (sourceInputs base point handle)).interpret CommonAdapter.project =
      (sourceDecision base point handle).bind fun decision => .done (.cons (some decision) .nil) := by
  kernel_rfl

/-- Complete values and transcript follow from the generic connection. -/
theorem participant_values (base point : G) (handle : Nat) :
    ((Domain.participant (ringModel F G) program context artifact (inputs base point)).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (sourceView context (sourceDecision base point handle) []).bind
      fun result => .done (returnValues context.suite result) := by
  let canonical := ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validatorRouting.selectedHandle
  have law := Uniform.ScalarPresentation.connected (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    (inputs base point) (sourceInputs base point canonical) (by kernel_rfl) (by kernel_rfl)
    (by derive_scalar_support)
  change _ = (sourceView context
    ((program.participant F G 1 (sourceInputs base point canonical)).interpret CommonAdapter.project) []).bind
      (fun result => .done (Uniform.ScalarPresentation.values program.payload.entry.signature context 1 result)) at law
  rw [source_values, Uniform.LoopedSourceProcess.sourceView_bind] at law
  simp only [PIR.Process.bind_assoc, sourceView, PIR.Process.bind] at law
  have relabel := Uniform.ScalarHandles.sourceView context canonical (sourceDecision (F := F) base point handle) []
  have handles : (sourceDecision (F := F) base point handle).interpret (Uniform.ScalarHandles.replace canonical) =
      sourceDecision base point canonical := by
    unfold sourceDecision
    rw [PIR.Process.interpret_bind, source_handle]
    rfl
  rw [handles] at relabel
  rw [← relabel]
  exact law

section Boundary
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The retained scalar equation is derived from Connected, independent reached
coverage and checked scalar support, preserving every proof and oracle reply. -/
theorem domain_transform (challenge : History F G → m F)
    (base point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs base point)) proof
        (fun result unread => pure (.returned (Uniform.SourceProcess.acceptance result.values), unread)) =
      transform context challenge (sourceVerifier base point handle) initial proof := by
  let canonical := ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validatorRouting.selectedHandle
  have law := ScalarConnection.transform (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    (inputs base point) (sourceInputs base point canonical) (by kernel_rfl) (by kernel_rfl)
    (by derive_scalar_support) .here (by rfl) challenge initial proof
  change _ = transform context challenge (sourceVerifier base point canonical) initial proof at law
  have relabel := Uniform.ScalarHandles.transform context canonical challenge
    (sourceVerifier (F := F) base point handle) initial proof
  rw [source_handle] at relabel
  exact law.trans relabel

/-- The installed Domain runtime has the same complete outcome and unread
proof after selecting Uniform.SourceProcess.acceptance. Physical frames remain with Domain.run.
No nominal random-oracle game is identified with the legacy oracle. -/
theorem actual_transform (challenge : History F G → m F)
    (base point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => Uniform.SourceProcess.acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle legacyOrigin initial challenge)
        (Domain.participant (ringModel F G) program context artifact (inputs base point))
        ⟨inputs base point, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier base point handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact (inputs base point)
  let project := fun result : Domain.Result (uniformCarriers F G) => Uniform.SourceProcess.acceptance result.values
  have installed := run_actual legacyOrigin initial challenge actual (inputs base point) proof
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
    _ = _ := by rw [domain_transform challenge base point handle]

end Boundary

end ZkcExamples.Construction.SchnorrDomainConnection

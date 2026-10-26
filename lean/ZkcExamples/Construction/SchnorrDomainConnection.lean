module

public import ZkcExamples.Construction.SchnorrProofData
public import ZkcExamples.Construction.SchnorrProofBodies
public import ZkcExamples.Construction.SchnorrProofModel
public import ZkcExamples.Construction.SchnorrProofParticipant
public import Zkc.Construction.Uniform.SourceProcess
public import Zkc.Construction.Uniform.Compiled
public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator

@[expose] public section

/-! Connection of the exact retained Schnorr artifact and admitted source.
The full returned tuple and transcript suffix are preserved before selecting
acceptance. No relation or honest-input premise restricts public inputs. -/
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

structured_views ZkcExamples.Construction.SchnorrProofData.snapshot
  helpers [formula := ZkcExamples.Construction.SchnorrProofBodies.formula]
  protocols [proof := ZkcExamples.Construction.SchnorrProofBodies.proof]

theorem admitted : Structured.check ZkcExamples.Construction.SchnorrProofData.snapshot = .ok program := kernel_admission


abbrev artifact := SchnorrProofParticipant.participant

def context : Context := Context.fiatShamir ZkcExamples.Construction.SchnorrProofData.snapshot.entry ["role00000000", "role00000001"] 0 1 4 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) artifact.policy.suite [("label_6368616c6c656e6765", "label_64656c6976657279_0")]

/-- Structural selection checks the entire source/artifact pair, including
body, policy, ABI and return projection; digest spelling alone is insufficient. -/
theorem checked : Uniform.checkCompiled imported artifact = .ok () := by decide +kernel

theorem context_checked : Uniform.exportContext SchnorrProofData.snapshot artifact = some context := by decide +kernel

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

/-- Exact Domain participant return, including the transcript and all stops;
only administrative checkpoint effects are projected away. -/
theorem participant_values (base point : G) (handle : Nat) :
    ((Domain.participant (ringModel F G) program context artifact (inputs base point)).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (sourceView context (sourceDecision base point handle) []).bind
      fun result => .done (returnValues context.suite result) := by
  rw [← artifact_identity, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.participant_eq]
  simp only [ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.view, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.inputSorts, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.outputSorts,
    ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.returned, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.body,
    ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep0, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep1, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep2, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep3, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep4, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep5, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep6, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep7, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep8, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep9, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep10, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep11, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep12, ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.bodyStep13]
  normalize_scalar_connection
    unfolding [inputs, context, artifact, SchnorrProofParticipant.participant, SchnorrProofData.snapshot, sourceDecision, source_equation,
      Zkc.Protocols.Schnorr.Common.experiment, SchnorrProof.wiring]


section Boundary
variable {m : Type → Type} [Monad m]

/-- All returns, stops and unread proof suffixes of the actual participant,
with an arbitrary consumer of its complete returned tuple. -/
theorem participant_run {R : Type} (challenge : History F G → m F)
    (base point : G) (handle : Nat) (initial : History F G) (proof : Proof F G)
    (next : Domain.Environment (uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs base point)) proof
        (fun result unread => next result.values unread) =
      runK legacyOrigin initial challenge (sourceView context (sourceDecision base point handle) []) proof
        (fun result unread => next (returnValues context.suite result) unread) := by
  have equation := participant_values (F := F) (G := G) base point handle
  have handled := congrArg (fun process => runK legacyOrigin initial challenge process proof next) equation
  rw [runK_forgetCheckpoints legacyOrigin initial challenge _ proof next] at handled
  rw [runK_bind, runK_bind] at handled
  simpa only [runK] using handled

variable [LawfulMonad m]

/-- The replacement for the retained scalar compiled-transform consumer:
all typed public values, every proof and challenge function in any lawful monad.
The legacy key adapter runs before the existing challenge oracle. -/
theorem domain_transform (challenge : History F G → m F)
    (base point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs base point)) proof
        (fun result unread => pure (.returned (acceptance result.values), unread)) =
      transform context challenge (sourceVerifier base point handle) initial proof := by
  rw [participant_run challenge base point handle initial proof
    (fun values unread => pure (.returned (acceptance values), unread))]
  have law := sourceView_transform_map context challenge
    (sourceDecision (F := F) (G := G) base point handle) some initial proof
  rw [← source_decision] at law
  exact law

/-- The installed Domain runtime has the same complete outcome and unread
proof after selecting acceptance. Physical frames remain with Domain.run.
No nominal random-oracle game is identified with the legacy oracle. -/
theorem actual_transform (challenge : History F G → m F)
    (base point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle legacyOrigin initial challenge)
        (Domain.participant (ringModel F G) program context artifact (inputs base point))
        ⟨inputs base point, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier base point handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact (inputs base point)
  let project := fun result : Domain.Result (uniformCarriers F G) => acceptance result.values
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

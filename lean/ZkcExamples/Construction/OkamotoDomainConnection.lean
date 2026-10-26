module

public import ZkcExamples.Structured.Generated.Constructed.OkamotoValidator
public import ZkcExamples.Construction.OkamotoProofData
public import ZkcExamples.Construction.OkamotoProofBodies
public import ZkcExamples.Construction.OkamotoProofModel
public import Zkc.Construction.Uniform.SourceProcess
public import Zkc.Construction.Uniform.Compiled
public import Zkc.Source.Structured.UnitViews

@[expose] public section


/-! Connection of the exact retained Okamoto artifact and admitted source.
The full returned tuple and transcript suffix are preserved before selecting
acceptance. No relation or honest-input premise restricts public inputs. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.OkamotoDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.SourceProcess
open ZkcExamples.Structured.Generated.Constructed

structured_views ZkcExamples.Construction.OkamotoProofData.snapshot
  helpers [formula := ZkcExamples.Construction.OkamotoProofBodies.formula]
  protocols [proof := ZkcExamples.Construction.OkamotoProofBodies.proof]

theorem admitted : Structured.check ZkcExamples.Construction.OkamotoProofData.snapshot = .ok program := kernel_admission


abbrev artifact := OkamotoProofParticipant.participant

def context : Context := Context.fiatShamir ZkcExamples.Construction.OkamotoProofData.snapshot.entry ["role00000000", "role00000001"] 0 1 6 "random.bls12-381.fr/0" (some (.draw "bls12-381.fr")) artifact.policy.suite [("label_6368616c6c656e6765", "label_64656c6976657279_0")]

/-- Structural selection checks the entire source/artifact pair, including
body, policy, ABI and return projection; digest spelling alone is insufficient. -/
theorem checked : Uniform.checkCompiled imported artifact = .ok () := by decide +kernel

theorem context_checked : Uniform.exportContext OkamotoProofData.snapshot artifact = some context := by decide +kernel

theorem artifact_identity : OkamotoValidator.artifact = artifact := rfl

/-- Admission retains the entire literal source snapshot, including its
metadata and typed bodies, rather than only its digest. -/
theorem source_identity : program.snapshot = OkamotoProofData.snapshot :=
  imported.exactSubject

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (firstBase secondBase point : G) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some firstBase) (.cons (some secondBase) (.cons (some point) (.cons (none) (.cons (none) (.cons (none) (.cons (some handle) (.nil)))))))

def sourceVerifier (firstBase secondBase point : G) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs firstBase secondBase point handle)).bind fun outputs =>
    .done (outputs.get .here)).interpret CommonAdapter.project

/-- The actual source Process has this finite normal form for every reply. -/
theorem source_equation (firstBase secondBase point : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) firstBase secondBase point handle = Zkc.Protocols.Schnorr.Variants.representation OkamotoProof.wiring firstBase secondBase point handle := by kernel_rfl

def sourceDecision (firstBase secondBase point : G) (handle : Nat) : PIR.Process (Actions F G) Bool :=
  (sourceVerifier firstBase secondBase point handle).bind fun decision => .done (decision.getD false)

theorem source_decision (firstBase secondBase point : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) firstBase secondBase point handle =
      (sourceDecision firstBase secondBase point handle).bind fun decision => .done (some decision) := by
  rw [source_equation]
  simp only [sourceDecision, source_equation]
  kernel_rfl

def inputs (firstBase secondBase point : G) : Domain.Environment (uniformCarriers F G) :=
  [.data (.group "bls12-381.g1" firstBase), .data (.group "bls12-381.g1" secondBase), .data (.group "bls12-381.g1" point), .transcript context.suite []]

theorem input_sorts (firstBase secondBase point : G) :
    Domain.sortsMatch artifact.inputs (inputs (F := F) (G := G) firstBase secondBase point) = true := by kernel_rfl

/-- Exact Domain participant return, including the transcript and all stops;
only administrative checkpoint effects are projected away. -/
theorem participant_values (firstBase secondBase point : G) (handle : Nat) :
    ((Domain.participant (ringModel F G) program context artifact (inputs firstBase secondBase point)).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (sourceView context (sourceDecision firstBase secondBase point handle) []).bind
      fun result => .done (returnValues context.suite result) := by
  rw [← artifact_identity, OkamotoValidator.participant_eq]
  simp only [OkamotoValidator.view, OkamotoValidator.inputSorts, OkamotoValidator.outputSorts,
    OkamotoValidator.returned, OkamotoValidator.body,
    OkamotoValidator.bodyStep0, OkamotoValidator.bodyStep1, OkamotoValidator.bodyStep2, OkamotoValidator.bodyStep3, OkamotoValidator.bodyStep4, OkamotoValidator.bodyStep5, OkamotoValidator.bodyStep6, OkamotoValidator.bodyStep7, OkamotoValidator.bodyStep8, OkamotoValidator.bodyStep9, OkamotoValidator.bodyStep10, OkamotoValidator.bodyStep11, OkamotoValidator.bodyStep12, OkamotoValidator.bodyStep13, OkamotoValidator.bodyStep14, OkamotoValidator.bodyStep15, OkamotoValidator.bodyStep16, OkamotoValidator.bodyStep17, OkamotoValidator.bodyStep18]
  normalize_scalar_connection
    unfolding [inputs, context, artifact, OkamotoProofParticipant.participant, OkamotoProofData.snapshot, sourceDecision, source_equation,
      Zkc.Protocols.Schnorr.Variants.representation, OkamotoProof.wiring]


section Boundary
variable {m : Type → Type} [Monad m]

/-- All returns, stops and unread proof suffixes of the actual participant,
with an arbitrary consumer of its complete returned tuple. -/
theorem participant_run {R : Type} (challenge : History F G → m F)
    (firstBase secondBase point : G) (handle : Nat) (initial : History F G) (proof : Proof F G)
    (next : Domain.Environment (uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase secondBase point)) proof
        (fun result unread => next result.values unread) =
      runK legacyOrigin initial challenge (sourceView context (sourceDecision firstBase secondBase point handle) []) proof
        (fun result unread => next (returnValues context.suite result) unread) := by
  have equation := participant_values (F := F) (G := G) firstBase secondBase point handle
  have handled := congrArg (fun process => runK legacyOrigin initial challenge process proof next) equation
  rw [runK_forgetCheckpoints legacyOrigin initial challenge _ proof next] at handled
  rw [runK_bind, runK_bind] at handled
  simpa only [runK] using handled

variable [LawfulMonad m]

/-- The replacement for the retained scalar compiled-transform consumer:
all typed public values, every proof and challenge function in any lawful monad.
The legacy key adapter runs before the existing challenge oracle. -/
theorem domain_transform (challenge : History F G → m F)
    (firstBase secondBase point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase secondBase point)) proof
        (fun result unread => pure (.returned (acceptance result.values), unread)) =
      transform context challenge (sourceVerifier firstBase secondBase point handle) initial proof := by
  rw [participant_run challenge firstBase secondBase point handle initial proof
    (fun values unread => pure (.returned (acceptance values), unread))]
  have law := sourceView_transform_map context challenge
    (sourceDecision (F := F) (G := G) firstBase secondBase point handle) some initial proof
  rw [← source_decision] at law
  exact law

/-- The installed Domain runtime has the same complete outcome and unread
proof after selecting acceptance. Physical frames remain with Domain.run.
No nominal random-oracle game is identified with the legacy oracle. -/
theorem actual_transform (challenge : History F G → m F)
    (firstBase secondBase point : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle legacyOrigin initial challenge)
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase secondBase point))
        ⟨inputs firstBase secondBase point, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier firstBase secondBase point handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact (inputs firstBase secondBase point)
  let project := fun result : Domain.Result (uniformCarriers F G) => acceptance result.values
  have installed := run_actual legacyOrigin initial challenge actual (inputs firstBase secondBase point) proof
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
    _ = _ := by rw [domain_transform challenge firstBase secondBase point handle]

end Boundary

end ZkcExamples.Construction.OkamotoDomainConnection

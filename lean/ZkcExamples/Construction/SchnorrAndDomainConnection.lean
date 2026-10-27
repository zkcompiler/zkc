module

public import ZkcExamples.Construction.SchnorrAndProofData
public import ZkcExamples.Construction.SchnorrAndProofBodies
public import ZkcExamples.Construction.SchnorrAndProofModel
public import ZkcExamples.Construction.SchnorrAndProofParticipant
public import Zkc.Construction.Uniform.SourceProcess
public import ZkcExamples.Construction.SchnorrAndArtifact
public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator

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

theorem artifact_identity : ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.artifact = artifact := rfl

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
    sourceVerifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = Zkc.Protocols.Schnorr.Variants.conjunction SchnorrAndProof.wiring firstBase firstPoint secondBase secondPoint handle := by kernel_rfl

def sourceDecision (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) : PIR.Process (Actions F G) Bool :=
  (sourceVerifier firstBase firstPoint secondBase secondPoint handle).bind fun decision => .done (decision.getD false)

theorem source_decision (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    sourceVerifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle =
      (sourceDecision firstBase firstPoint secondBase secondPoint handle).bind fun decision => .done (some decision) := by
  rw [source_equation]
  simp only [sourceDecision, source_equation]
  kernel_rfl

def inputs (firstBase firstPoint secondBase secondPoint : G) : Domain.Environment (uniformCarriers F G) :=
  [.data (.group "bls12-381.g1" firstBase), .data (.group "bls12-381.g1" firstPoint), .data (.group "bls12-381.g1" secondBase), .data (.group "bls12-381.g1" secondPoint), .transcript context.suite []]

theorem input_sorts (firstBase firstPoint secondBase secondPoint : G) :
    Domain.sortsMatch artifact.inputs (inputs (F := F) (G := G) firstBase firstPoint secondBase secondPoint) = true := by kernel_rfl

/-- Exact Domain participant return, including the transcript and all stops;
only administrative checkpoint effects are projected away. -/
theorem participant_values (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    ((Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint)).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (sourceView context (sourceDecision firstBase firstPoint secondBase secondPoint handle) []).bind
      fun result => .done (returnValues context.suite result) := by
  rw [← artifact_identity, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.participant_eq]
  simp only [ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.view, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.inputSorts, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.outputSorts,
    ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.returned, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.body,
    ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep0, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep1, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep2, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep3, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep4, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep5, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep6, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep7, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep8, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep9, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep10, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep11, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep12, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep13, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep14, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep15, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep16, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep17, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep18, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep19, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep20, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep21, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep22, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep23, ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator.bodyStep24]
  normalize_scalar_connection
    unfolding [inputs, context, artifact, SchnorrAndProofParticipant.participant, SchnorrAndProofData.snapshot, sourceDecision, source_equation,
      Zkc.Protocols.Schnorr.Variants.conjunction, SchnorrAndProof.wiring]


section Boundary
variable {m : Type → Type} [Monad m]

/-- All returns, stops and unread proof suffixes of the actual participant,
with an arbitrary consumer of its complete returned tuple. -/
theorem participant_run {R : Type} (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) (proof : Proof F G)
    (next : Domain.Environment (uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint)) proof
        (fun result unread => next result.values unread) =
      runK legacyOrigin initial challenge (sourceView context (sourceDecision firstBase firstPoint secondBase secondPoint handle) []) proof
        (fun result unread => next (returnValues context.suite result) unread) := by
  have equation := participant_values (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle
  have handled := congrArg (fun process => runK legacyOrigin initial challenge process proof next) equation
  rw [runK_forgetCheckpoints legacyOrigin initial challenge _ proof next] at handled
  rw [runK_bind, runK_bind] at handled
  simpa only [runK] using handled

variable [LawfulMonad m]

/-- The replacement for the retained scalar compiled-transform consumer:
all typed public values, every proof and challenge function in any lawful monad.
The legacy key adapter runs before the existing challenge oracle. -/
theorem domain_transform (challenge : History F G → m F)
    (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs firstBase firstPoint secondBase secondPoint)) proof
        (fun result unread => pure (.returned (Uniform.SourceProcess.acceptance result.values), unread)) =
      transform context challenge (sourceVerifier firstBase firstPoint secondBase secondPoint handle) initial proof := by
  rw [participant_run challenge firstBase firstPoint secondBase secondPoint handle initial proof
    (fun values unread => pure (.returned (Uniform.SourceProcess.acceptance values), unread))]
  have law := sourceView_transform_map context challenge
    (sourceDecision (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle) some initial proof
  rw [← source_decision] at law
  exact law

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

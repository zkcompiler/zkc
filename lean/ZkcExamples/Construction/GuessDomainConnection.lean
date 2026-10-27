module

public import ZkcExamples.Structured.Generated.Constructed.GuessValidator
public import ZkcExamples.Construction.GuessProofData
public import ZkcExamples.Construction.GuessProofBodies
public import ZkcExamples.Construction.GuessProofModel
public import Zkc.Construction.Uniform.SourceProcess
public import ZkcExamples.Construction.GuessArtifact
public import Zkc.Source.Structured.UnitViews

@[expose] public section


/-! Connection of the exact retained Guess artifact and admitted source.
The full returned tuple and transcript suffix are preserved before selecting
Uniform.SourceProcess.acceptance. No relation or honest-input premise restricts public inputs. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.GuessDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.Uniform.SourceProcess
open ZkcExamples.Structured.Generated.Constructed

open GuessProof

abbrev artifact := participant

theorem artifact_identity : GuessValidator.artifact = artifact := rfl

/-- Admission retains the entire literal source snapshot, including its
metadata and typed bodies, rather than only its digest. -/
theorem source_identity : program.snapshot = GuessProofData.snapshot :=
  imported.exactSubject

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (offset : F) (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some offset) (.cons (none) (.cons (some handle) (.nil)))

def sourceVerifier (offset : F) (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs offset handle)).bind fun outputs =>
    .done (outputs.get .here)).interpret CommonAdapter.project

/-- The actual source Process has this finite normal form for every reply. -/
theorem source_equation (offset : F) (handle : Nat) :
    sourceVerifier (F := F) (G := G) offset handle = GuessProof.experiment offset handle := by kernel_rfl

def sourceDecision (offset : F) (handle : Nat) : PIR.Process (Actions F G) Bool :=
  (sourceVerifier offset handle).bind fun decision => .done (decision.getD false)

theorem source_decision (offset : F) (handle : Nat) :
    sourceVerifier (F := F) (G := G) offset handle =
      (sourceDecision offset handle).bind fun decision => .done (some decision) := by
  rw [source_equation]
  simp only [sourceDecision, source_equation]
  kernel_rfl

def inputs (offset : F) : Domain.Environment (uniformCarriers F G) :=
  [.data (.field "bls12-381.fr" offset), .transcript context.suite []]

theorem input_sorts (offset : F) :
    Domain.sortsMatch artifact.inputs (inputs (F := F) (G := G) offset) = true := by kernel_rfl

/-- Exact Domain participant return, including the transcript and all stops;
only administrative checkpoint effects are projected away. -/
theorem participant_values (offset : F) (handle : Nat) :
    ((Domain.participant (ringModel F G) program context artifact (inputs offset)).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (sourceView context (sourceDecision offset handle) []).bind
      fun result => .done (returnValues context.suite result) := by
  rw [← artifact_identity, GuessValidator.participant_eq]
  simp only [GuessValidator.view, GuessValidator.inputSorts, GuessValidator.outputSorts,
    GuessValidator.returned, GuessValidator.body,
    GuessValidator.bodyStep0, GuessValidator.bodyStep1, GuessValidator.bodyStep2, GuessValidator.bodyStep3, GuessValidator.bodyStep4, GuessValidator.bodyStep5, GuessValidator.bodyStep6, GuessValidator.bodyStep7, GuessValidator.bodyStep8]
  normalize_scalar_connection
    unfolding [inputs, context, artifact, GuessProofParticipant.participant, GuessProofData.snapshot, sourceDecision, source_equation,
      GuessProof.experiment, GuessProof.experiment]


section Boundary
variable {m : Type → Type} [Monad m]

/-- All returns, stops and unread proof suffixes of the actual participant,
with an arbitrary consumer of its complete returned tuple. -/
theorem participant_run {R : Type} (challenge : History F G → m F)
    (offset : F) (handle : Nat) (initial : History F G) (proof : Proof F G)
    (next : Domain.Environment (uniformCarriers F G) → Proof F G → m (PIR.Outcome R × Proof F G)) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs offset)) proof
        (fun result unread => next result.values unread) =
      runK legacyOrigin initial challenge (sourceView context (sourceDecision offset handle) []) proof
        (fun result unread => next (returnValues context.suite result) unread) := by
  have equation := participant_values (F := F) (G := G) offset handle
  have handled := congrArg (fun process => runK legacyOrigin initial challenge process proof next) equation
  rw [runK_forgetCheckpoints legacyOrigin initial challenge _ proof next] at handled
  rw [runK_bind, runK_bind] at handled
  simpa only [runK] using handled

variable [LawfulMonad m]

/-- The replacement for the retained scalar compiled-transform consumer:
all typed public values, every proof and challenge function in any lawful monad.
The legacy key adapter runs before the existing challenge oracle. -/
theorem domain_transform (challenge : History F G → m F)
    (offset : F) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK legacyOrigin initial challenge
        (Domain.participant (ringModel F G) program context artifact (inputs offset)) proof
        (fun result unread => pure (.returned (Uniform.SourceProcess.acceptance result.values), unread)) =
      transform context challenge (sourceVerifier offset handle) initial proof := by
  rw [participant_run challenge offset handle initial proof
    (fun values unread => pure (.returned (Uniform.SourceProcess.acceptance values), unread))]
  have law := sourceView_transform_map context challenge
    (sourceDecision (F := F) (G := G) offset handle) some initial proof
  rw [← source_decision] at law
  exact law

/-- The installed Domain runtime has the same complete outcome and unread
proof after selecting Uniform.SourceProcess.acceptance. Physical frames remain with Domain.run.
No nominal random-oracle game is identified with the legacy oracle. -/
theorem actual_transform (challenge : History F G → m F)
    (offset : F) (handle : Nat) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome (fun returned => Uniform.SourceProcess.acceptance returned.values) result.outcome,
        result.state.proof)) <$>
      Domain.run .validator (oracle legacyOrigin initial challenge)
        (Domain.participant (ringModel F G) program context artifact (inputs offset))
        ⟨inputs offset, embedProof proof, ()⟩ =
    (fun result => (result.1, embedProof result.2)) <$>
      transform context challenge (sourceVerifier offset handle) initial proof := by
  let actual := Domain.participant (ringModel F G) program context artifact (inputs offset)
  let project := fun result : Domain.Result (uniformCarriers F G) => Uniform.SourceProcess.acceptance result.values
  have installed := run_actual legacyOrigin initial challenge actual (inputs offset) proof
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
    _ = _ := by rw [domain_transform challenge offset handle]

end Boundary

end ZkcExamples.Construction.GuessDomainConnection

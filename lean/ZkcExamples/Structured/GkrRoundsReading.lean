module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcExamples.Structured.GkrSourceLaws
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import Zkc.Source.Structured.CommonAdapter

@[expose] public section

/-! The actual eight-input Pending Rounds verifier. The carried initial point
is preserved through every adversarial reply and every refusal branch. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
namespace ZkcExamples.Structured.GkrRoundsReading
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev closed : HelperTable (assignment F G) (participantInterface F G) :=
  (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed

theorem invoke_law (helper : Helper) (arguments : Values (assignment F G) helper.inputs)
    (results : Values (assignment F G) helper.outputs)
    (law : invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments = .done results) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed helper arguments = .done results := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments).interpret _ = _
  rw [law]
  rfl

theorem append_plain (xs : List F) (x : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.appendHelper (.cons xs (.cons x .nil)) =
      .done (.cons (xs ++ [x]) .nil) :=
  invoke_law _ _ _ (GkrSourceLaws.append_equation xs x)

theorem empty_plain :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.emptyHelper .nil = .done (.cons [] .nil) :=
  invoke_law _ _ _ GkrSourceLaws.empty_equation

/-! ## One step of each loop -/

/-- One round of a layer Sumcheck application of the original, over the common
actions, is one round of the plain verifier. -/
theorem round_reads (ctx : ProtocolContext) (handle : Nat) (state : List F × F) :
    (Generated.Presentations.Gkr.Rounds.verifierProcess (F := F) (G := G) ctx (some handle) (some state.1)
        (some state.2)).interpret CommonAdapter.project =
      (GkrVerifier.round ctx handle state).bind (fun next => .done (some next.1, some next.2)) := by
  simp only [Generated.Presentations.Gkr.Rounds.verifierProcess, GkrVerifier.round, GkrVerifier.roundFirst,
    GkrVerifier.roundSecond, GkrVerifier.roundCheck, PIR.Process.interpret, CommonAdapter.project,
    PIR.Process.bind, append_plain]
  refine congrArg (PIR.Process.call _) (funext fun c0 => congrArg (PIR.Process.call _) (funext fun c1 =>
    congrArg (PIR.Process.call _) (funext fun c2 => ?_)))
  split
  · simp only [PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind, GkrVerifier.roundChallenge]
    rfl
  · rfl

theorem repeatN_reads {I J : PIR.Signature} (operations : PIR.OperationInterpretation I J)
    {S T : Type} (process : S → PIR.Process I S) (step : T → PIR.Process J T) (embed : T → S)
    (same : ∀ state, (process (embed state)).interpret operations =
      (step state).bind (fun next => .done (embed next))) :
    ∀ (count : Nat) (state : T), (PIR.repeatN count process (embed state)).interpret operations =
      (PIR.repeatN count step state).bind (fun next => .done (embed next))
  | 0, _ => rfl
  | count + 1, state => by
      simp only [PIR.repeatN, PIR.Process.interpret_bind, same, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext next
      exact repeatN_reads operations process step embed same count next

def roundsResults (result : List F × F) :
    Values (Component (assignment F G)) Generated.Presentations.Gkr.Rounds.roundsOutputs :=
  .cons none (.cons none (.cons none (.cons none (.cons none (.cons (some result.1)
    (.cons (some result.2) .nil))))))


omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Prefix transport concerns the full process, including failed round checks. -/
theorem round_prefix (ctx : ProtocolContext) (handle : Nat) (pointPrefix : List F)
    (state : List F × F) :
    GkrVerifier.round (G := G) ctx handle (pointPrefix ++ state.1, state.2) =
      (GkrVerifier.round ctx handle state).bind
        (fun next => .done (pointPrefix ++ next.1, next.2)) := by
  simp only [GkrVerifier.round, PIR.Process.bind]
  apply congrArg (PIR.Process.call _)
  funext c0
  simp only [GkrVerifier.roundFirst, PIR.Process.bind]
  apply congrArg (PIR.Process.call _)
  funext c1
  simp only [GkrVerifier.roundSecond, PIR.Process.bind]
  apply congrArg (PIR.Process.call _)
  funext c2
  unfold GkrVerifier.roundCheck
  split
  · simp only [PIR.Process.bind]
    apply congrArg (PIR.Process.call _)
    funext challenge
    simp only [GkrVerifier.roundChallenge, PIR.Process.bind]
    apply congrArg (PIR.Process.call _)
    funext ignored
    simp only [List.append_assoc]
  · rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A pending point pointPrefix changes only the returned point, never actions. -/
theorem repeat_prefix (ctx : ProtocolContext) (handle count : Nat) (pointPrefix : List F)
    (state : List F × F) :
    PIR.repeatN count (GkrVerifier.round (G := G) ctx handle) (pointPrefix ++ state.1, state.2) =
      (PIR.repeatN count (GkrVerifier.round ctx handle) state).bind
        (fun next => .done (pointPrefix ++ next.1, next.2)) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    simp only [PIR.repeatN, round_prefix, PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext next
    exact ih next

theorem tuple40_plain (point : List F) (claim : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper40Helper
      (.cons point (.cons claim .nil)) = .done (.cons point (.cons claim .nil)) := by
  kernel_rfl

theorem tuple49_plain (point : List F) (claim : F) :
    invoke (closed (F := F) (G := G)) GkrSourceBodies.sourceHelper49Helper
      (.cons point (.cons claim .nil)) = .done (.cons point (.cons claim .nil)) := by
  kernel_rfl

/-- Exact current-source Rounds binding, from any pending initial point. -/
theorem reads (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle count : Nat) (bounded : count ≤ 4) (initialPoint : List F) (claim : F) :
    (Generated.Presentations.Gkr.Rounds.verifierRoundsProcess (F := F) (G := G) ctx (some initialPoint)
      (some claim) (some count) (some handle)).interpret CommonAdapter.project =
      (GkrVerifier.rounds ctx handle count claim).bind
        (fun result => .done (roundsResults (initialPoint ++ result.1, result.2))) := by
  unfold Generated.Presentations.Gkr.Rounds.verifierRoundsProcess
  simp only [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program, tuple40_plain, PIR.Process.bind, Values.get_cons]
  erw [Generated.Presentations.Gkr.Rounds.verifier_fold ctx (.ofSeparate separate (by decide)) (some handle) count bounded
    (.cons none (.cons none (.cons none (.cons none (.cons none (.cons (some initialPoint)
      (.cons (some claim) .nil)))))))
    (some initialPoint, some claim)
    (Generated.Presentations.Gkr.Rounds.verifierState_masked ctx _ rfl (some initialPoint) (some claim))]
  rw [Finite.fold_range_repeatN (fun result => Generated.Presentations.Gkr.Rounds.verifierProcess ctx
    (some handle) result.1 result.2) 0 count (some initialPoint, some claim)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret_bind]
  rw [repeatN_reads CommonAdapter.project _ (GkrVerifier.round ctx handle)
    (fun state : List F × F => (some state.1, some state.2))
    (fun state => round_reads ctx handle state) count (initialPoint, claim)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, Values.get_cons]
  simp only [tuple49_plain, PIR.Process.interpret, PIR.Process.bind]
  have pointPrefix := repeat_prefix (G := G) ctx handle count initialPoint ([], claim)
  simp only [List.append_nil] at pointPrefix
  rw [pointPrefix]
  simp only [Generated.Presentations.Gkr.Rounds.verifierState, Values.get_cons, tuple49_plain,
    PIR.Process.interpret, PIR.Process.bind_assoc, PIR.Process.bind, GkrVerifier.rounds]
  rfl

end ZkcExamples.Structured.GkrRoundsReading

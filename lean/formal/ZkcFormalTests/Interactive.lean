module

import ZkcFormal.Interactive
import Init.GrindInstances.Ring.Int

namespace ZkcFormalTests.Interactive
open Zkc.Core ZkcFormal.Interactive Sumcheck

-- The verifier uses only ring operations on these integer messages, challenges and table entries.
inductive Request where
  | message | challenge | missing

def Reply : Request → Type
  | .message => Int × Int
  | .challenge | .missing => Int

def signature : Sig := ⟨Request, Reply⟩

/-- The peer learns each public coin through its service state. Before a draw it
chooses the line x. After observing one it can switch to the line 1-x. -/
def experiment : Experiment signature Bool where
  answer
    | .message, seenOne => FiniteLaw.certain ((if seenOne then (1, 0) else (0, 1)), seenOne)
    | .challenge, _ => FiniteLaw.uniform [((0 : Int), false), ((1 : Int), true)] (by decide)
    | .missing, _ => ⟨[], by decide⟩

def receive : Process signature Unit (Int × Int) := .call .message .done
def draw : Process signature Unit Int := .call .challenge .done

def verifier : Verifier (S := signature) Unit Int (Int × Int) :=
  ⟨fun _ _ => receive, fun _ _ _ => draw, (), fun m => m.1 + m.2, line⟩

theorem false_sum_one_round :
    experiment.probability (verifier.checkTable 1 (0, 0) 1) false (fun _ _ => true) = 1/2 := by
  decide +kernel

theorem zero_round_rejects_false_claim :
    experiment.probability (verifier.checkTable 0 0 1) false (fun _ _ => true) = 0 := by
  decide +kernel

theorem zero_round_accepts_true_claim :
    experiment.probability (verifier.checkTable 0 0 0) false (fun _ _ => true) = 1 := by
  decide +kernel

theorem boundary_rejects_wrong_message :
    experiment.probability (verifier.checkTable 1 (0, 0) 2) false (fun _ _ => true) = 0 := by
  decide +kernel

theorem no_acceptance_after_one :
    experiment.probability (verifier.checkTable 1 (0, 0) 1) false
      (fun _ seenOne => seenOne) = 0 := by
  decide +kernel

def revealFirst : Process signature Unit Int := draw.bind fun r => receive.map fun m => line m r

theorem revealing_first_allows_adaptation :
    experiment.probability revealFirst false (fun x _ => decide (x = 0)) = 1 := by
  decide +kernel

def loseHalf : Process signature Unit Int :=
  draw.bind fun r => if r = 1 then .call .missing .done else .done r

theorem missing_reply_loses_half :
    experiment.probability loseHalf false (fun _ _ => true) = 1/2 := by
  decide +kernel

theorem cube_sum : Cube.sum (F := Int) 2 ((1, 3), (5, 9)) = 18 := by
  decide +kernel

theorem cube_evaluate_high_low : Cube.evaluate (F := Int) 2 ((1, 3), (5, 9)) [1, 0] = some 5 := by
  decide +kernel

theorem cube_evaluate_low_high : Cube.evaluate (F := Int) 2 ((1, 3), (5, 9)) [0, 1] = some 3 := by
  decide +kernel

-- Four gate rounds inspect claim depths zero through four.
private def fourRoundClaims : Claims Rat where
  State _ := Unit
  value n _ := if n ≤ 4 then 0 else 1
  restrict _ _ _ := ()

private def zeroQuadratic : Quadratic Rat := ⟨0, 0, 0⟩

example (d : Fin 4) (r : Rat) :
    fourRoundClaims.value (d.val+1) () = zeroQuadratic.boundary ∧
    fourRoundClaims.value d.val (fourRoundClaims.restrict d.val () r) = zeroQuadratic.eval r := by
  have upper : d.val+1 ≤ 4 := d.isLt
  have lower : d.val ≤ 4 := Nat.le_of_lt d.isLt
  simp [fourRoundClaims, upper, lower, zeroQuadratic, Quadratic.boundary, Quadratic.eval] <;> grind

example (honest : ∀ d, fourRoundClaims.State (d+1) → Quadratic Rat)
    (sum : ∀ d x, fourRoundClaims.value (d+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, fourRoundClaims.value d (fourRoundClaims.restrict d x r) = (honest d x).eval r) :
    False := by
  have left := restricted 4 () 0
  have right := restricted 4 () 1
  have next := sum 4 ()
  change 0 = _ at left right
  change (1 : Rat) = (honest 4 ()).eval 0 + (honest 4 ()).eval 1 at next
  rw [← left, ← right] at next
  exact (by decide +kernel : (1 : Rat) ≠ 0 + 0) next

section
open ReductionRound

/-- If a peer never provides a message, the source verifier never requests a coin
regardless of the service's behavior on a hypothetical draw. -/
theorem noMessage_freshFrom {V : Vocabulary} {hs : Headers V} {t state : V.Ty} {events : Events t}
    {Γ : Ctx (LTy V)} {running : Var Γ (shared t)} {outs : List (LTy V)}
    {term : Term (protocolDialect V hs) Γ outs} {count : Nat} (rounds : Sequence hs events state running term count)
    (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) {σ : Type} (K : Experiment (RSig M) σ)
    (blocked : ∀ msg path key s m after, ¬ K.Reaches (ReductionRound.receive M msg path key) s m after)
    (points : List (M.Val t)) (positive : 0 < points.length) (path : List Frame) (env : Env (RV M 1) Γ) (s : σ) :
    rounds.FreshFrom M fns roles K points positive path env s := by
  induction rounds generalizing s with
  | done => trivial
  | more round key index ns binders next ih =>
    exact ⟨fun m after reached _ => False.elim (blocked _ _ _ s m after reached),fun _ _ _ => ih _ _⟩

def biasedWithoutMessage : Experiment signature Unit where
  answer
    | .challenge, _ => FiniteLaw.certain ((0 : Int),())
    | .message, _ => ⟨[], by decide⟩
    | .missing, _ => ⟨[], by decide⟩

theorem unused_biased_draw : ¬ Fresh biasedWithoutMessage [(0 : Int),1] (by decide) draw () := by
  intro h
  let event : Int → Bool := fun | .ofNat 0 => true | _ => false
  have impossible : ¬ (biasedWithoutMessage.probability draw () (fun r _ => event r) ≤
      (FiniteLaw.uniform [(0 : Int),1] (by decide)).expect fun r => if event r then 1 else 0) := by decide +kernel
  exact impossible (h event)

theorem abort_before_biased_draw :
    biasedWithoutMessage.probability (verifier.checkTable 1 (0,0) 1) () (fun _ _ => true) = 0 := by
  decide +kernel

end
end ZkcFormalTests.Interactive

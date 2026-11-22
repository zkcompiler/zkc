module

public import ZkcFormal.FiniteService
public import ZkcFormal.Written.Source
public import ZkcFormal.Interactive.AppliedReduction
public import Zkc.Core.World.Stack

@[expose] public section
namespace ZkcFormal.Written.RoundService
open Zkc.Core Interactive Sumcheck ReductionRound FiniteService

variable {V : Vocabulary} {t : V.Ty} {σ : Type} {n : Nat}

/-- At the verifier's uniform draw, sample a fresh position and allow its successor state
to depend on the reply. All other operations use the given stateful strategy. -/
def challengeSlots (M : Model V) (events : Events t) (alphabet : Fin (n+1) → M.Val t)
    (advance : Occurrence → M.Val t → σ → σ) (other : Slots (RSig M) σ)
    (op : ROp M) (s : σ) : (k : Nat) × (Fin (k+1) → Option ((RSig M).Reply op) × σ) :=
  let port : InputPort V := .own (.coin events.law) [0] op.occurrence t
  if h : InputPort.ofOp M op = some port then
    let eq := congrArg (RSig M).Reply (InputPort.operation_ofOp M h).symm
    ⟨n, fun i => (some (cast eq (alphabet i)), advance op.occurrence (alphabet i) s)⟩
  else ⟨other.width op s, other.answer op s⟩

def withChallenge (M : Model V) (events : Events t) (alphabet : Fin (n+1) → M.Val t)
    (advance : Occurrence → M.Val t → σ → σ) (other : Slots (RSig M) σ) : Slots (RSig M) σ :=
  ⟨fun op s => (challengeSlots M events alphabet advance other op s).1,
   fun op s => (challengeSlots M events alphabet advance other op s).2⟩

private theorem ticket_count {R : Type} (width : Nat) (xs : List R) (next : R → σ)
    (event : R → Bool) :
    Weighted.total (fun rs => if event rs.1 then 1 else 0)
      (tickets width (xs.map (fun r => (some r, next r)))) =
        (xs.countP event : Mass) * slotWeight width := by
  induction xs with
  | nil => simp [tickets, Weighted.total]
  | cons x xs ih =>
    simp only [List.map_cons, tickets, Weighted.total, List.countP_cons, ih]
    cases event x <;> simp [Mass.natCast_add, Mass.add_mul, Mass.add_comm]

/-- The finite interpreter of the answering service meets the conditional fresh-draw
obligation at every history, including after renaming the callee's roles. -/
theorem fresh (M : Model V) (events : Events t) (alphabet : Fin (n+1) → M.Val t)
    (advance : Occurrence → M.Val t → σ → σ) (other : Slots (RSig M) σ)
    (path : List Frame) (key : Key) (s : σ) :
    Fresh ((finite (withChallenge M events alphabet advance other)).renamePeers peerMap.to)
      (List.ofFn alphabet) (by simp) (challenge M events path key) s := by
  intro event
  rw [FiniteLaw.uniform_event]
  let at_ : Occurrence := ⟨path,key⟩
  let op : ROp M := .own (.coin events.law) [0] at_ [] .nil t
  change Weighted.total (fun rs => if event rs.1 then 1 else 0)
    (tickets ((withChallenge M events alphabet advance other).width op s) (List.ofFn ((withChallenge M events alphabet advance other).answer op s))) ≤ _
  have selected : challengeSlots M events alphabet advance other op s =
      ⟨n, fun i => (some (alphabet i), advance at_ (alphabet i) s)⟩ := dite_eq_left rfl
  let convert (choices : (k : Nat) × (Fin (k+1) → Option (M.Val t) × σ)) :=
    tickets choices.1 (List.ofFn choices.2)
  change Weighted.total _ (convert (challengeSlots M events alphabet advance other op s)) ≤ _
  rw [selected]
  dsimp only [convert]
  rw [show List.ofFn (fun i => (some (alphabet i), advance at_ (alphabet i) s)) =
    (List.ofFn alphabet).map (fun r => (some r, advance at_ r s)) from by rw [List.map_ofFn]; rfl, ticket_count]
  simp only [List.length_ofFn]
  have weight : slotWeight n = ((n+1 : Nat) : Mass)⁻¹ :=
    Mass.ofFraction_eq.mpr (by simp [Mass.Fraction.inv, Mass.Fraction.ofNat])
  rw [weight, Mass.div_def]
  exact Mass.le_refl

end ZkcFormal.Written.RoundService

module

public import ZkcSecurity.FiatShamir.Interface
public import Zkc.Transcript.Budget

@[expose] public section

/-! # The typed engine's path bounds as walks

The query count (`Typed.QueryBound`), the cost with an error per occurrence
(`Typed.CostBound`) and the charged cost from a history (`Typed.ChargedCostBound`)
are path bounds of the shared combinator `Zkc.Transcript.Walk.Bound`, each with
its own metric (`queryBound_iff`, `costBound_iff`, `chargedCostBound_iff`): the
first two walk without positions and constrain every reply of a receive; the
charged cost walks absorbed histories and constrains only the replies a
receive's absorbed event recovers.

The metrics are connected by conversions, not identified: a bound without
positions holds at every history (`replyWalk_walk`), and `Walk.Bound.convert`
with the map `n ↦ n * bound` turns a query count into a charged cost whenever
every charge is at most `bound` (`QueryBound.chargedCostBound_of_walk`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Typed
open Zkc.Transcript

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} (absorb : Interface I E P Raw)

/-- The query count is the walk without positions charging one per query. -/
theorem queryBound_iff :
    ∀ (process : PIR.Process I A) (budget : ℕ),
      QueryBound absorb process budget ↔
        (absorb.replyWalk absorb.queryCharge).Bound process () budget
  | .done _, _ => Iff.rfl
  | .halt _, _ => Iff.rfl
  | .call operation next, budget => by
      have ih := fun reply => queryBound_iff (next reply)
      rw [Walk.bound_call]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      all_goals simp only [QueryBound, absorbed, Interface.replyWalk_admits,
        Interface.replyWalk_charge, Interface.replyWalk_next, Interface.queryCharge, true_and,
        true_implies, zero_add, IsEmpty.forall_iff, implies_true, and_true]
      · constructor
        · exact fun bounded =>
            ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩ reply
          exact (ih reply budget).mpr (Walk.Bound.mono _ _ (bounded reply ()) le)
      · constructor
        · exact fun bounded => ⟨budget, le_rfl, fun reply _ same => same ▸ (ih value budget).mp bounded⟩
        · rintro ⟨remaining, le, bounded⟩
          exact (ih value budget).mpr (Walk.Bound.mono _ _ (bounded value () rfl) le)
      · constructor
        · rintro ⟨positive, bounded⟩
          exact ⟨budget - 1, by omega, fun reply _ => (ih reply (budget - 1)).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨by omega, fun reply => (ih reply (budget - 1)).mpr
            (Walk.Bound.mono _ _ (bounded reply ()) (by omega))⟩
      · exact ⟨fun _ => ⟨budget, le_rfl⟩, fun _ => trivial⟩

/-- The cost with an error per occurrence is the walk without positions charging
each query its occurrence's error. -/
theorem costBound_iff (error : E → ENNReal) :
    ∀ (process : PIR.Process I A) (cost : ENNReal),
      CostBound absorb error process cost ↔
        (absorb.replyWalk (absorb.errorCharge error)).Bound process () cost
  | .done _, _ => Iff.rfl
  | .halt _, _ => Iff.rfl
  | .call operation next, cost => by
      have ih := fun reply => costBound_iff error (next reply)
      rw [Walk.bound_call]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      all_goals simp only [CostBound, absorbed, Interface.replyWalk_admits,
        Interface.replyWalk_charge, Interface.replyWalk_next, Interface.errorCharge, true_and,
        true_implies, zero_add, IsEmpty.forall_iff, implies_true, and_true]
      · constructor
        · exact fun bounded => ⟨cost, le_rfl, fun reply _ => (ih reply cost).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩ reply
          exact (ih reply cost).mpr (Walk.Bound.mono _ _ (bounded reply ()) le)
      · constructor
        · exact fun bounded => ⟨cost, le_rfl, fun reply _ same => same ▸ (ih value cost).mp bounded⟩
        · rintro ⟨remaining, le, bounded⟩
          exact (ih value cost).mpr (Walk.Bound.mono _ _ (bounded value () rfl) le)
      · constructor
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨remaining, le, fun reply _ => (ih reply remaining).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨remaining, le, fun reply => (ih reply remaining).mpr (bounded reply ())⟩
      · exact ⟨fun _ => ⟨cost, le_rfl⟩, fun _ => trivial⟩

/-- The charged cost from a history is the walk over absorbed histories charging
each query its key. -/
theorem chargedCostBound_iff (charge : List E → E → ENNReal) :
    ∀ (process : PIR.Process I A) (history : List E) (cost : ENNReal),
      ChargedCostBound absorb charge process history cost ↔
        (absorb.walk (absorb.lossCharge charge)).Bound process history cost
  | .done _, _, _ => Iff.rfl
  | .halt _, _, _ => Iff.rfl
  | .call operation next, history, cost => by
      have ih := fun reply => chargedCostBound_iff charge (next reply)
      rw [Walk.bound_call]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      all_goals simp only [ChargedCostBound, absorbed, Interface.walk_admits,
        Interface.walk_charge, Interface.walk_next, Interface.lossCharge, true_and, zero_add,
        IsEmpty.forall_iff, implies_true, and_true]
      · constructor
        · refine fun bounded => ⟨cost, le_rfl, fun reply after ⟨message, recovered, same⟩ => ?_⟩
          subst same
          exact (ih reply _ cost).mp (bounded message reply recovered)
        · rintro ⟨remaining, le, bounded⟩ message reply recovered
          exact (ih reply _ cost).mpr
            (Walk.Bound.mono _ _ (bounded reply _ ⟨message, recovered, rfl⟩) le)
      · constructor
        · refine fun bounded => ⟨cost, le_rfl, fun reply after ⟨same, extended⟩ => ?_⟩
          subst same extended
          exact (ih _ _ cost).mp bounded
        · rintro ⟨remaining, le, bounded⟩
          exact (ih value _ cost).mpr (Walk.Bound.mono _ _ (bounded value _ ⟨rfl, rfl⟩) le)
      · constructor
        · rintro ⟨remaining, le, bounded⟩
          refine ⟨remaining, le, fun reply after same => ?_⟩
          subst same
          exact (ih reply _ remaining).mp (bounded reply)
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨remaining, le, fun reply => (ih reply _ remaining).mpr (bounded reply _ rfl)⟩
      · exact ⟨fun _ => ⟨cost, le_rfl⟩, fun _ => trivial⟩

/-- A bound without positions holds at every history, for the same charges:
the interface walk follows a subset of the transitions without positions. -/
theorem replyWalk_walk {Cost : Type} [AddCommMonoid Cost] [Preorder Cost]
    (charge : I.Op → Cost) :
    ∀ (process : PIR.Process I A) (budget : Cost),
      (absorb.replyWalk charge).Bound process () budget →
        ∀ history, (absorb.walk fun _ operation => charge operation).Bound process history budget
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, _, ⟨_, remaining, le, bounded⟩, history => by
      refine ⟨trivial, remaining, le, fun reply after step => ?_⟩
      refine replyWalk_walk charge (next reply) remaining (bounded reply () ?_) after
      rw [Interface.walk_next] at step
      rw [Interface.replyWalk_next]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _ <;> simp only [absorbed] at step ⊢
      exact step.1

/-- Queries to charged cost, through the conversion `n ↦ n * bound`: when every
charge is at most `bound`, a query count `budget` bounds the charged cost by
`budget * bound` from every history. -/
theorem QueryBound.chargedCostBound_of_walk {charge : List E → E → ENNReal} {bound : ENNReal}
    (bounded : ∀ history event, charge history event ≤ bound) (process : PIR.Process I A)
    (budget : ℕ) (counted : QueryBound absorb process budget) (history : List E) :
    ChargedCostBound absorb charge process history (budget * bound) := by
  have walked := replyWalk_walk absorb absorb.queryCharge process budget
    ((queryBound_iff absorb process budget).mp counted) history
  refine (chargedCostBound_iff absorb charge process history _).mpr ?_
  refine Walk.Bound.convert _ (absorb.walk (absorb.lossCharge charge))
    ((AddMonoidHom.mulRight bound).comp (Nat.castAddMonoidHom ENNReal))
    (fun first second le => by simpa using mul_le_mul_left (Nat.cast_le.mpr le) bound)
    (fun _ _ _ => trivial) (fun history operation => ?_) (fun _ _ _ _ step => step) process walked
  simp only [Interface.walk_charge, Interface.lossCharge, Interface.queryCharge,
    AddMonoidHom.coe_comp, Function.comp_apply, Nat.coe_castAddMonoidHom, AddMonoidHom.coe_mulRight]
  cases absorb operation <;> simp [bounded]

end ZkcSecurity.FiatShamir.Typed

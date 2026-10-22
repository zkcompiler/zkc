module

public import ZkcSecurity.Commitment.Charges
public import ZkcSecurity.Commitment.Replay
public import Zkc.Transcript.Budget

@[expose] public section

/-! # Charges of verifiers with committed tables

`Charged` bounds the charges on every path of a verifier with committed tables, in any ordered
additive monoid: a transcript query is charged its occurrence's charge, a read `readCharge`, and
every committed shape is admissible. The concrete reading inherits the bound when every
authentication at an admissible shape makes at most `authCalls` hash calls:

* `run_costBound`: with the error of each occurrence as its charge and `authCalls · hashError`
  per read, the concrete reading's worst-case cost on the joint oracle is at most the bound;
* `run_queryBound`: with charge `1` per query and `authCalls` per read, the concrete reading makes
  at most the bound of oracle calls.

Admissibility carries the authentication bound from the statement's roots and the verifier's own
commitments to every read.

`Charged` and the commitment count `CommitBound` are path bounds of the shared combinator
`Zkc.Transcript.Walk.Bound` without positions (`charged_iff`, `commitBound_iff`), with their own
transition charges; shape admissibility is the walk's admission predicate, kept apart from the
charges.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A : Type} {Raw : E → Type}

section Charged
variable (absorb : Typed.Interface J E P Raw) (admissible : Shape → Prop)

/-- Every path of a verifier with committed tables charges at most `budget`: a transcript query
its occurrence's charge, a read `readCharge`; every committed shape is admissible. -/
def Charged {ω : Type} [AddCommMonoid ω] [Preorder ω] (charge : E → ω) (readCharge : ω) :
    PIR.Process (committed J Shape Value) A → ω → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call (.base operation) next, budget =>
      match absorb operation with
      | .query event _ => ∃ rest, charge event + rest ≤ budget ∧
          ∀ reply, Charged charge readCharge (next reply) rest
      | _ => ∀ reply, Charged charge readCharge (next reply) budget
  | .call (.commit shape) next, budget =>
      admissible shape ∧ Charged charge readCharge (next ()) budget
  | .call (.read _ _) next, budget =>
      ∃ rest, readCharge + rest ≤ budget ∧ ∀ value, Charged charge readCharge (next value) rest

theorem Charged.mono {ω : Type} [AddCommMonoid ω] [Preorder ω] (charge : E → ω)
    (readCharge : ω) :
    ∀ (process : PIR.Process (committed J Shape Value) A) {budget larger : ω},
      Charged absorb admissible charge readCharge process budget → budget ≤ larger →
        Charged absorb admissible charge readCharge process larger
  | .done _, _, _, _, _ => trivial
  | .halt _, _, _, _, _ => trivial
  | .call (.base operation) next, _, _, bounded, le => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Charged, absorbed] at bounded ⊢
        exact fun reply => Charged.mono charge readCharge (next reply) (bounded reply) le
      · simp only [Charged, absorbed] at bounded ⊢
        exact fun reply => Charged.mono charge readCharge (next reply) (bounded reply) le
      · simp only [Charged, absorbed] at bounded ⊢
        obtain ⟨rest, charged, after⟩ := bounded
        exact ⟨rest, charged.trans le, after⟩
      · simp only [Charged, absorbed] at bounded ⊢
        exact fun reply => Charged.mono charge readCharge (next reply) (bounded reply) le
  | .call (.commit _) next, _, _, bounded, le =>
      ⟨bounded.1, Charged.mono charge readCharge (next ()) bounded.2 le⟩
  | .call (.read _ _) next, _, _, bounded, le => by
      obtain ⟨rest, charged, after⟩ := bounded
      exact ⟨rest, charged.trans le, after⟩

/-- The walk of `Charged`: every reply continues; a commitment is admitted when its shape is
admissible; a transcript query is charged its occurrence's charge, a read `readCharge`. -/
def chargedWalk {ω : Type} [Zero ω] (charge : E → ω) (readCharge : ω) :
    Zkc.Transcript.Walk (committed J Shape Value) Unit ω where
  admits _ operation :=
    match operation with
    | .commit shape => admissible shape
    | _ => True
  charge _ operation :=
    match operation with
    | .base operation =>
        match absorb operation with
        | .query event _ => charge event
        | _ => 0
    | .commit _ => 0
    | .read _ _ => readCharge
  next _ _ _ _ := True

/-- `Charged` is the path bound of its walk. -/
theorem charged_iff {ω : Type} [AddCommMonoid ω] [Preorder ω] (charge : E → ω) (readCharge : ω) :
    ∀ (process : PIR.Process (committed J Shape Value) A) (budget : ω),
      Charged absorb admissible charge readCharge process budget ↔
        (chargedWalk absorb admissible charge readCharge).Bound process () budget
  | .done _, _ => Iff.rfl
  | .halt _, _ => Iff.rfl
  | .call (.base operation) next, budget => by
      have ih := fun reply => charged_iff charge readCharge (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [chargedWalk, true_and, forall_const]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      all_goals simp only [Charged, absorbed, zero_add]
      · exact ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩,
          fun ⟨remaining, le, bounded⟩ reply =>
            (ih reply budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) le)⟩
      · exact ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩,
          fun ⟨remaining, le, bounded⟩ reply =>
            (ih reply budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) le)⟩
      · exact ⟨fun ⟨remaining, le, bounded⟩ =>
            ⟨remaining, le, fun reply _ => (ih reply remaining).mp (bounded reply)⟩,
          fun ⟨remaining, le, bounded⟩ =>
            ⟨remaining, le, fun reply => (ih reply remaining).mpr (bounded reply ())⟩⟩
      · exact ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩,
          fun ⟨remaining, le, bounded⟩ reply =>
            (ih reply budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) le)⟩
  | .call (.commit shape) next, budget => by
      have ih := fun reply => charged_iff charge readCharge (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [Charged, chargedWalk, zero_add, forall_const]
      exact and_congr_right fun _ =>
        ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp bounded⟩,
          fun ⟨remaining, le, bounded⟩ =>
            (ih () budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded () ()) le)⟩
  | .call (.read handle position) next, budget => by
      have ih := fun reply => charged_iff charge readCharge (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [Charged, chargedWalk, true_and, forall_const]
      exact ⟨fun ⟨remaining, le, bounded⟩ =>
          ⟨remaining, le, fun reply _ => (ih reply remaining).mp (bounded reply)⟩,
        fun ⟨remaining, le, bounded⟩ =>
          ⟨remaining, le, fun reply => (ih reply remaining).mpr (bounded reply ())⟩⟩

end Charged

section Commitments

/-- The walk of `CommitBound`: one per commitment, every reply continues. -/
def commitWalk : Zkc.Transcript.Walk (committed J Shape Value) Unit ℕ where
  admits _ _ := True
  charge _ operation :=
    match operation with
    | .commit _ => 1
    | _ => 0
  next _ _ _ _ := True

/-- `CommitBound` is the path bound of its walk. -/
theorem commitBound_iff :
    ∀ (process : PIR.Process (committed J Shape Value) A) (budget : ℕ),
      CommitBound process budget ↔ (commitWalk (J := J)).Bound process () budget
  | .done _, _ => Iff.rfl
  | .halt _, _ => Iff.rfl
  | .call (.base operation) next, budget => by
      have ih := fun reply => commitBound_iff (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [CommitBound, commitWalk, true_and, zero_add, forall_const]
      exact ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩,
        fun ⟨remaining, le, bounded⟩ reply =>
          (ih reply budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) le)⟩
  | .call (.commit shape) next, budget => by
      have ih := fun reply => commitBound_iff (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [CommitBound, commitWalk, true_and, forall_const]
      exact ⟨fun ⟨positive, bounded⟩ => ⟨budget - 1, by omega, fun reply _ =>
          (ih reply (budget - 1)).mp bounded⟩,
        fun ⟨remaining, le, bounded⟩ => ⟨by omega, (ih () (budget - 1)).mpr
          (Zkc.Transcript.Walk.Bound.mono _ _ (bounded () ()) (by omega))⟩⟩
  | .call (.read handle position) next, budget => by
      have ih := fun reply => commitBound_iff (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      simp only [CommitBound, commitWalk, true_and, zero_add, forall_const]
      exact ⟨fun bounded => ⟨budget, le_rfl, fun reply _ => (ih reply budget).mp (bounded reply)⟩,
        fun ⟨remaining, le, bounded⟩ reply =>
          (ih reply budget).mpr (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) le)⟩

end Commitments

section Run
variable (absorb : Typed.Interface J E P Raw) (admissible : Shape → Prop)
  (scheme : Extractable Shape Value Query Y)

theorem worstCaseCostBound_le {α : Type} {computation : OracleComp (joint Raw Shape Y Query) α}
    {cost : CostModel (joint Raw Shape Y Query) ENNReal} {bound larger : ENNReal}
    (bounded : WorstCaseCostBound computation cost bound) (le : bound ≤ larger) :
    WorstCaseCostBound computation cost larger :=
  (worstCaseCostBound_iff_support_bound _ _ _).mpr fun z member =>
    ((worstCaseCostBound_iff_support_bound _ _ _).mp bounded z member).trans le

/-- The concrete reading charges at most a charged bound of its verifier, each transcript key the
error of its occurrence and each hash call `hashError`. -/
theorem run_costBound (error : E → ENNReal) (hashError : ENNReal) (authCalls : ℕ)
    (authenticated : ∀ shape, admissible shape → ∀ root position opening,
      IsTotalQueryBound (scheme.authenticate shape root position opening) authCalls) :
    ∀ (process : PIR.Process (committed J Shape Value) A) (budget : ENNReal),
      Charged absorb admissible error ((authCalls : ENNReal) * hashError) process budget →
      ∀ (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
        (messages : List (Message P Y)) (openings : List (Opening Value Y)),
        (∀ pair ∈ roots, admissible pair.1) →
        WorstCaseCostBound (run absorb scheme process history roots messages openings)
          ⟨jointError (Shape := Shape) (Y := Y) (Query := Query) error hashError⟩ budget
  | .done _, _, _, _, _, _, _, _ => by
      rw [run.eq_def]
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | .halt _, _, _, _, _, _, _, _ => by
      rw [run.eq_def]
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | .call (.base operation) next, budget, bounded, history, roots, messages, openings,
      rooted => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Charged, absorbed] at bounded
        rw [run.eq_def]
        simp only [absorbed]
        split
        · split
          · exact run_costBound error hashError authCalls authenticated _ budget (bounded _) _ _
              _ _ rooted
          · exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        · exact (worstCaseCostBound_pure _ _ _).mpr zero_le
      · simp only [Charged, absorbed] at bounded
        rw [run.eq_def]
        simp only [absorbed]
        exact run_costBound error hashError authCalls authenticated _ budget (bounded _) _ _ _ _
          rooted
      · simp only [Charged, absorbed] at bounded
        obtain ⟨rest, charged, after⟩ := bounded
        rw [run.eq_def]
        simp only [absorbed]
        rw [worstCaseCostBound_query_bind_iff]
        intro raw cost member
        refine le_trans (add_le_add le_rfl ?_) charged
        revert cost
        rw [← worstCaseCostBound_iff_support_bound]
        split
        · exact run_costBound error hashError authCalls authenticated _ rest (after _) _ _ _ _
            rooted
        · exact (worstCaseCostBound_pure _ _ _).mpr zero_le
      · rw [run.eq_def]
        simp only [absorbed]
        exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | .call (.commit shape) next, budget, bounded, history, roots, messages, openings, rooted => by
      rw [run.eq_def]
      simp only
      split
      · refine run_costBound error hashError authCalls authenticated _ budget bounded.2 _ _ _ _
          fun pair member => ?_
        rcases List.mem_append.mp member with old | new
        · exact rooted pair old
        · rw [List.mem_singleton] at new
          subst new
          exact bounded.1
      · exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | .call (.read handle position) next, budget, bounded, history, roots, messages, openings,
      rooted => by
      obtain ⟨rest, charged, after⟩ := bounded
      rw [run.eq_def]
      simp only
      split
      · rename_i shape root opening others found
        have member : (shape, root) ∈ roots := List.mem_of_getElem? found
        refine worstCaseCostBound_le (WorstCaseCostBound.bind
          (liftHash_costBound error hashError _ _ (authenticated shape (rooted _ member) root
            position opening)) fun accepted => ?_) charged
        cases accepted
        · exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        · exact run_costBound error hashError authCalls authenticated _ rest (after _) _ _ _ _
            rooted
      · exact (worstCaseCostBound_pure _ _ _).mpr zero_le

/-- The concrete reading makes at most a charged bound of its verifier of oracle calls, with
charge `1` per transcript query and `authCalls` per read. -/
theorem run_queryBound (authCalls : ℕ)
    (authenticated : ∀ shape, admissible shape → ∀ root position opening,
      IsTotalQueryBound (scheme.authenticate shape root position opening) authCalls) :
    ∀ (process : PIR.Process (committed J Shape Value) A) (budget : ℕ),
      Charged absorb admissible (fun _ => 1) authCalls process budget →
      ∀ (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
        (messages : List (Message P Y)) (openings : List (Opening Value Y)),
        (∀ pair ∈ roots, admissible pair.1) →
        IsTotalQueryBound (run absorb scheme process history roots messages openings) budget
  | .done _, _, _, _, _, _, _, _ => by
      rw [run.eq_def]
      trivial
  | .halt _, _, _, _, _, _, _, _ => by
      rw [run.eq_def]
      trivial
  | .call (.base operation) next, budget, bounded, history, roots, messages, openings,
      rooted => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Charged, absorbed] at bounded
        rw [run.eq_def]
        simp only [absorbed]
        split
        · split
          · exact run_queryBound authCalls authenticated _ budget (bounded _) _ _ _ _ rooted
          · trivial
        · trivial
      · simp only [Charged, absorbed] at bounded
        rw [run.eq_def]
        simp only [absorbed]
        exact run_queryBound authCalls authenticated _ budget (bounded _) _ _ _ _ rooted
      · simp only [Charged, absorbed] at bounded
        obtain ⟨rest, charged, after⟩ := bounded
        rw [run.eq_def]
        simp only [absorbed]
        rw [isTotalQueryBound_query_bind_iff]
        refine ⟨by omega, fun raw => ?_⟩
        split
        · exact (run_queryBound authCalls authenticated _ rest (after _) _ _ _ _ rooted).mono
            (by omega)
        · trivial
      · rw [run.eq_def]
        simp only [absorbed]
        trivial
  | .call (.commit shape) next, budget, bounded, history, roots, messages, openings, rooted => by
      rw [run.eq_def]
      simp only
      split
      · refine run_queryBound authCalls authenticated _ budget bounded.2 _ _ _ _
          fun pair member => ?_
        rcases List.mem_append.mp member with old | new
        · exact rooted pair old
        · rw [List.mem_singleton] at new
          subst new
          exact bounded.1
      · trivial
  | .call (.read handle position) next, budget, bounded, history, roots, messages, openings,
      rooted => by
      obtain ⟨rest, charged, after⟩ := bounded
      rw [run.eq_def]
      simp only
      split
      · rename_i shape root opening others found
        have member : (shape, root) ∈ roots := List.mem_of_getElem? found
        refine (isTotalQueryBound_bind
          (liftHash_queryBound (Raw := Raw) (Shape := Shape) _ _
            (authenticated shape (rooted _ member) root position opening))
          fun accepted => ?_).mono charged
        cases accepted
        · trivial
        · exact run_queryBound authCalls authenticated _ rest (after _) _ _ _ _ rooted
      · trivial

end Run

end ZkcSecurity.Commitment

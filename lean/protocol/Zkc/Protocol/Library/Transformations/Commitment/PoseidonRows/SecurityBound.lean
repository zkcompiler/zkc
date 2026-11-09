module

public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.RecordedPermutation

@[expose] public section

/-! Probability and request-fixed extraction for the monitored ideal lazy permutation.
Allocation attempts are free in the primitive metric. Every primitive call, including cached,
inverse and prequery calls and calls on failed paths, is counted by `PrimitiveBudget`.
No eager uniform-completion or fixed public-permutation claim is made. -/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows.Monitored

open OracleComp OracleSpec
open ZkcSecurity.Probability
open scoped ENNReal

variable {Key F : Type} {rate b : ℕ} [Zero F] [DecidableEq F] [Fintype F]

local notation "D" => Digest F rate

def isPrimitive : Command Key F rate → Prop
  | .call _ => True
  | .allocate _ _ => False

instance : DecidablePred (isPrimitive (Key := Key) (F := F) (rate := rate)) :=
  fun command ↦ by cases command <;> simp only [isPrimitive] <;> infer_instance

/-- Structural all-path primitive-call budget. Allocation attempts are not charged.
This is VCVio's predicate-targeted total-query metric, not a fresh-pair count. -/
abbrev PrimitiveBudget {α : Type} (program : OracleComp (Oracle Key F rate) α) (Q : ℕ) :=
  IsQueryBoundP program isPrimitive Q

/-- Exact counter association, independently of the bad flag or budget. -/
theorem run_call_count {α : Type} (program : OracleComp (Oracle Key F rate) α)
    (result : α × Monitor Key F rate b)
    (member : result ∈ support ((simulateQ handler program).run empty)) :
    result.2.permutation.calls = (calls result.2.history).length := by
  apply simulateQ_run_preservesInv handler
    (fun s ↦ s.permutation.calls = (calls s.history).length) (fun command s inv r rm ↦ ?_)
    program empty (by simp [empty, calls, PermutationExposure.State.empty]) result member
  cases command with
  | call q =>
    change r ∈ support ((fun x ↦ (x.1, record s q x)) <$>
      PermutationExposure.step (targets s.roots) q s.permutation) at rm
    rw [support_map] at rm
    obtain ⟨x, xm, rfl⟩ := rm
    have inc := PermutationExposure.step_calls _ _ _ x xm
    simp [record, inc, inv]
  | allocate key roots =>
    change r ∈ support (pure (register s key roots)) at rm
    simp only [support_pure] at rm
    change r = register s key roots at rm
    subst r
    unfold register
    split <;> simpa using inv

/-- The primitive budget bounds the actual counter without counting allocation attempts. -/
theorem run_calls_le {α : Type} (program : OracleComp (Oracle Key F rate) α) :
    ∀ Q (s : Monitor Key F rate b), PrimitiveBudget program Q →
      ∀ result ∈ support ((simulateQ handler program).run s),
        result.2.permutation.calls ≤ s.permutation.calls + Q := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro Q s _ result member
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact Nat.le_add_right _ _
  | query_bind command next ih =>
    intro Q s budget result member
    obtain ⟨positive, rest⟩ := (isQueryBoundP_query_bind_iff isPrimitive command next Q).mp budget
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      at member
    obtain ⟨middle, hm, hr⟩ := member
    cases command with
    | call q =>
      have pos : 0 < Q := positive.resolve_left (by simp [isPrimitive])
      have tail := ih middle.1 (Q - 1) middle.2 (by simpa [isPrimitive] using rest middle.1)
        result hr
      change middle ∈ support ((fun x ↦ (x.1, record s q x)) <$>
        PermutationExposure.step (targets s.roots) q s.permutation) at hm
      rw [support_map] at hm
      obtain ⟨x, xm, eq⟩ := hm
      have inc := PermutationExposure.step_calls _ _ _ x xm
      cases eq
      change result.2.permutation.calls ≤ (record s q x).permutation.calls + (Q - 1) at tail
      simp only [record] at tail
      omega
    | allocate key roots =>
      have tail := ih middle.1 Q middle.2 (by simpa [isPrimitive] using rest middle.1) result hr
      change middle ∈ support (pure (register s key roots)) at hm
      simp only [support_pure] at hm
      change middle = register s key roots at hm
      rw [hm, register_permutation] at tail
      exact tail

/-- Lift the existing sampler potential through record instrumentation. Allocation commands
are deterministic zero-charge steps. The fresh sampling law itself is unchanged. -/
theorem potential_step (Q : ℕ) (room : Q < (Fintype.card D) ^ 2) :
    IsPotentialStep (handler (Key := Key) (F := F) (rate := rate) (b := b))
      (fun s ↦ s.permutation.bad = true)
      (fun s ↦ PermutationExposure.charge (Fintype.card D) Q b s.permutation.calls) := by
  constructor
  · intro command s result member
    cases command with
    | call q =>
      change result ∈ support ((fun r ↦ (r.1, record s q r)) <$>
        PermutationExposure.step (targets s.roots) q s.permutation) at member
      rw [support_map] at member
      obtain ⟨r, rm, rfl⟩ := member
      exact (PermutationExposure.potential_step (targets s.roots) b Q
        (targets_bound s.roots) room).mono q s.permutation r rm
    | allocate key roots =>
      change result ∈ support (pure (register s key roots)) at member
      simp only [support_pure] at member
      change result = register s key roots at member
      subst result
      rw [register_permutation]
  · intro command s quiet
    cases command with
    | call q =>
      have localLaw := (PermutationExposure.potential_step (targets s.roots) b Q
        (targets_bound s.roots) room).step q s.permutation quiet
      rcases localLaw with ⟨a, t, law, qt⟩ | ⟨samp, upd, w, law, mass, gain⟩
      · left
        refine ⟨a, record s q (a, t), ?_, qt⟩
        change PermutationExposure.step (targets s.roots) q s.permutation = pure (a, t) at law
        change (fun r ↦ (r.1, record s q r)) <$> _ = _
        rw [law, map_pure]
      · right
        refine ⟨samp, fun a ↦ record s q (a, upd a), w, ?_, mass, gain⟩
        change PermutationExposure.step (targets s.roots) q s.permutation =
          (fun a ↦ (a, upd a)) <$> samp at law
        change (fun r ↦ (r.1, record s q r)) <$> _ = _
        rw [law, Functor.map_map]
    | allocate key roots =>
      left
      refine ⟨(register s key roots).1, (register s key roots).2, rfl, ?_⟩
      rwa [register_permutation]

/-- The actual monitored execution's bad probability, obtained from the upstream potential
engine and the finished sampler component, with a primitive-only structural budget. -/
theorem bad_probability_le {α : Type} (program : OracleComp (Oracle Key F rate) α)
    (Q : ℕ) (budget : PrimitiveBudget program Q) :
    Pr{let result ← (simulateQ (handler (b := b)) program).run empty}[
      result.2.permutation.bad = true] ≤ PermutationExposure.epsilon (Fintype.card D) Q b := by
  classical
  by_cases room : Q < (Fintype.card D) ^ 2
  · rw [PermutationExposure.epsilon, ite_eq_left room]
    apply le_min (prEvent_le_one _)
    have law := potential_step (Key := Key) (b := b) Q room
    have bound := prEvent_and_le_of_potential handler (fun s ↦ s.permutation.bad = true)
      (fun s ↦ PermutationExposure.charge (Fintype.card D) Q b s.permutation.calls)
      law.mono law.step program (PermutationExposure.charge (Fintype.card D) Q b Q)
      (PermutationExposure.charge_finite _ Q b room) empty (by simp [empty,
        PermutationExposure.State.empty])
    have same := prEvent_congr_of_support ((simulateQ (handler (b := b)) program).run empty)
      (fun r ↦ r.2.permutation.bad = true)
      (fun r ↦ r.2.permutation.bad = true ∧
        PermutationExposure.charge (Fintype.card D) Q b r.2.permutation.calls ≤
          PermutationExposure.charge (Fintype.card D) Q b Q)
      (fun r rm ↦ ⟨fun raised ↦ ⟨raised, PermutationExposure.charge_mono _ Q b (by
        simpa [empty, PermutationExposure.State.empty] using
          run_calls_le program Q empty budget r rm)⟩, And.left⟩)
    rw [same]
    simpa [empty, PermutationExposure.State.empty, PermutationExposure.charge,
      PermutationExposure.work_closed] using bound
  · rw [PermutationExposure.epsilon, ite_eq_right room]
    exact prEvent_le_one _


variable [DecidableEq Key]

/-- A concrete recorded scalar operation and the physical first allocation of its key.
There is no decoder, extraction result or probability in this predicate. -/
def OpeningRecorded (request : Request rate) (history : History Key F rate)
    (key : Key) (root : D) (index : ℕ) (row : List F) : Prop :=
  ∃ roots later e siblings,
    history = beforeFirst (some key) history ++ allocation key roots :: later ∧
    root ∈ roots ∧
    SpongeTrace (calls history) request.width.full request.width.tail e row ∧
    NodeClimb (calls history) index siblings e root ∧
    siblings.length = request.depth ∧ index < request.height

/-- A concrete finite shared-frontier reduction, with full active-leaf coverage and
ordered row coverage. This preserves repetitions, actual height and fixed flattened width. -/
def BatchRecorded (request : Request rate) (history : History Key F rate)
    (key : Key) (root : D) (positions : List ℕ) (rows : List (List F)) : Prop :=
  ∃ roots later frontier proof,
    history = beforeFirst (some key) history ++ allocation key roots :: later ∧
    root ∈ roots ∧
    BatchOpening.Reduction compression (primitiveLog (calls history))
      request.depth frontier proof root ∧
    (∀ entry ∈ frontier, ∃ e row, e.output.1 = entry.2 ∧
      SpongeTrace (calls history) request.width.full request.width.tail e row) ∧
    PrimitiveRows (calls history) request.width frontier positions rows ∧
    ∀ i ∈ positions, i < request.height

/-- The registered zero completion is fixed by the request, including for absent entries. -/
def completeCheckpoint (request : Request rate) (key : Key) (history : History Key F rate)
    (root : D) (index : ℕ) : List F :=
  (directCheckpoint request key history root index).getD (List.replicate request.width.length 0)

omit [Fintype F] in
theorem opening_agrees {request : Request rate} {history : History Key F rate}
    (good : GoodHistory history) {key : Key} {root : D} {index : ℕ} {row : List F}
    (recorded : OpeningRecorded request history key root index row) :
    directCheckpoint request key history root index = some row ∧
      completeCheckpoint request key history root index = row := by
  obtain ⟨roots, later, e, siblings, marker, registered, trace, climb, length, range⟩ := recorded
  have agreement := direct_checkpoint_opening_agrees good marker registered trace climb length range
  exact ⟨agreement, by simp [completeCheckpoint, agreement]⟩

omit [Fintype F] in
theorem batch_agrees {request : Request rate} {history : History Key F rate}
    (good : GoodHistory history) {key : Key} {root : D} {positions : List ℕ}
    {rows : List (List F)} (recorded : BatchRecorded request history key root positions rows) :
    positions.map (directCheckpoint request key history root) = rows.map some ∧
      positions.map (completeCheckpoint request key history root) = rows := by
  obtain ⟨roots, later, frontier, proof, marker, registered, reduction, coverage, traces, range⟩ :=
    recorded
  have agreement := checkpoint_batch_agrees good marker registered reduction coverage traces range
  refine ⟨agreement, ?_⟩
  have mapped := congrArg (List.map (fun row : Option (List F) ↦
    row.getD (List.replicate request.width.length 0))) agreement
  change positions.map (fun i ↦ (directCheckpoint request key history root i).getD
    (List.replicate request.width.length 0)) = rows
  simpa [List.map_map, Function.comp_def] using mapped

/-- Simultaneous disagreement with any later recorded opening or ordered batch, including
zero-completed readings. The request is a parameter of the event, fixed before execution. -/
def Disagreement (request : Request rate) (history : History Key F rate) : Prop :=
  (∃ key root index row, OpeningRecorded request history key root index row ∧
    (directCheckpoint request key history root index ≠ some row ∨
      completeCheckpoint request key history root index ≠ row)) ∨
  (∃ key root positions rows, BatchRecorded request history key root positions rows ∧
    (positions.map (directCheckpoint request key history root) ≠ rows.map some ∨
      positions.map (completeCheckpoint request key history root) ≠ rows))

/-- Failure is classified into the sampler's actually charged flag, by support association
and the deterministic extractor theorems, rather than assumed as a correspondence. -/
theorem disagreement_implies_bad {α : Type} (request : Request rate)
    (program : OracleComp (Oracle Key F rate) α) (result : α × Monitor Key F rate b)
    (member : result ∈ support ((simulateQ handler program).run empty))
    (failure : Disagreement request result.2.history) : result.2.permutation.bad = true := by
  by_contra quiet
  have good := run_goodHistory program result member (by simpa using quiet)
  rcases failure with ⟨key, root, index, row, recorded, failure⟩ |
    ⟨key, root, positions, rows, recorded, failure⟩
  · have agree := opening_agrees good recorded
    exact failure.elim (fun h ↦ h agree.1) (fun h ↦ h agree.2)
  · have agree := batch_agrees good recorded
    exact failure.elim (fun h ↦ h agree.1) (fun h ↦ h agree.2)

/-- Complete generic probability plus extraction theorem for the actual monitored lazy
partial-bijection service. `Q` counts primitive calls only. `b` is enforced by allocation
refusal. Concrete trace/reduction premises are inside the event; extraction agreement,
final-event probability, eager permutation equivalence and native refinement are not premises. -/
theorem extraction_disagreement_le {α : Type} (request : Request rate)
    (program : OracleComp (Oracle Key F rate) α) (Q : ℕ)
    (budget : PrimitiveBudget program Q) :
    Pr{let result ← (simulateQ (handler (b := b)) program).run empty}[
      Disagreement request result.2.history] ≤
      PermutationExposure.epsilon (Fintype.card D) Q b := by
  exact (prEvent_mono_of_support _ _ _ fun result member failure ↦
    disagreement_implies_bad request program result member failure).trans
      (bad_probability_le program Q budget)

/-- Private randomization may select any reply-adaptive program with the same all-path
primitive budget. The request remains fixed outside that randomization. -/
theorem randomized_extraction_disagreement_le {α : Type} (request : Request rate)
    (programs : ProbComp (OracleComp (Oracle Key F rate) α)) (Q : ℕ)
    (budget : ∀ program ∈ support programs, PrimitiveBudget program Q) :
    Pr{let result ← programs >>= fun program ↦
      (simulateQ (handler (b := b)) program).run empty}[
      Disagreement request result.2.history] ≤
      PermutationExposure.epsilon (Fintype.card D) Q b := by
  exact prEvent_bind_le_of_forall_le_of_support programs _ _ fun program member ↦
    extraction_disagreement_le request program Q (budget program member)

end ZkcSecurity.Commitment.PoseidonRows.Monitored

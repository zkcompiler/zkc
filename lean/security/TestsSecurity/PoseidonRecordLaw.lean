module

public import ZkcSecurity.Transformations.Commitment.PoseidonRows.SecurityBound
public meta import ZkcSecurity.Transformations.Commitment.PoseidonRows.SecurityBound
public meta import ZkcSecurity.Transformations.Commitment.PoseidonRows.RecordedPermutation
public meta import ZkcSecurity.Transformations.Commitment.PoseidonRows.DirectExtraction
public meta import ZkcSecurity.Transformations.Commitment.PoseidonRows.Checkpoint

@[expose] public section

/-! Kernel-checked operational controls for the monitored lazy-permutation/record seam.
All explicit fresh answers are proved to belong to the actual sampler support. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace TestsSecurity.PoseidonRecordLaw

open OracleComp OracleSpec
open ZkcSecurity.Commitment ZkcSecurity.Commitment.PoseidonRows
open ZkcSecurity.Commitment.PoseidonRows.Monitored
open ZkcSecurity.Probability
open scoped ENNReal

abbrev F := Fin 64
abbrev D := Digest F 1
abbrev M := Monitor ℕ F 1 2

def v (n : F) : D := fun _ ↦ n

def first : Exposure F 1 := ⟨true, (v 1, v 0), (v 10, v 20)⟩
def second : Exposure F 1 := ⟨true, (v 2, v 20), (v 30, v 40)⟩
def widthOne : Width 1 := ⟨0, 1, by decide, by decide⟩
def widthTwo : Width 1 := ⟨1, 1, by decide, by decide⟩
def requestOne : Request 1 := ⟨widthOne, 1, 0, by decide, by decide⟩
def requestTwo : Request 1 := ⟨widthTwo, 1, 0, by decide, by decide⟩

/-- Every available value has support in the existing finite sampler. -/
theorem draw_supported {S : Type} (available : Finset S) (nonempty : available.Nonempty)
    (x : S) (member : x ∈ available) :
    x ∈ support (PermutationExposure.draw available nonempty) := by
  rw [PermutationExposure.draw, support_map]
  refine ⟨⟨x, member⟩, ?_, rfl⟩
  let : SampleableType available := SampleableType.finsetCoe available nonempty
  exact mem_support_uniformSample available

/-- A concrete fresh insertion below really is a supported handler result. -/
theorem fresh_supported (s : M) (q : PermQuery D) (answer : State F 1)
    (fresh : ¬ s.permutation.cached q)
    (available : answer ∈ s.permutation.available q.direction) :
    (answer, record s q (answer, s.permutation.insert q answer
      (decide (PermutationExposure.FiberHit (targets s.roots s.permutation q).1
        (targets s.roots s.permutation q).2 answer)))) ∈
      support ((handler (.call q)).run s) := by
  change _ ∈ support ((fun r ↦ (r.1, record s q r)) <$>
    PermutationExposure.step (targets s.roots) q s.permutation)
  rw [PermutationExposure.step_fresh _ _ _ fresh, support_map]
  refine ⟨(answer, s.permutation.insert q answer
    (decide (PermutationExposure.FiberHit (targets s.roots s.permutation q).1
      (targets s.roots s.permutation q).2 answer))), ?_, rfl⟩
  rw [support_map]
  exact ⟨answer, draw_supported _ _ _ available, rfl⟩

/-- An explicit supported-answer witness, not a separate simulation. -/
def freshRecord (s : M) (e : Exposure F 1) : M :=
  let q : PermQuery D := ⟨if e.forward then .forward else .inverse,
    if e.forward then e.input else e.output⟩
  let answer := if e.forward then e.output else e.input
  record s q (answer, s.permutation.insert q answer
    (decide (PermutationExposure.FiberHit (targets s.roots s.permutation q).1
      (targets s.roots s.permutation q).2 answer)))

def firstPrefix : M := freshRecord empty first
def twoCalls : M := freshRecord firstPrefix second

theorem first_supported : (first.output, firstPrefix) ∈
    support ((handler (.call ⟨.forward, first.input⟩)).run (empty : M)) :=
  fresh_supported empty _ _ (by decide) (by decide)

theorem second_supported : (second.output, twoCalls) ∈
    support ((handler (.call ⟨.forward, second.input⟩)).run firstPrefix) :=
  fresh_supported firstPrefix _ _ (by decide) (by decide)

theorem two_calls_good : twoCalls.permutation.bad = false ∧
    Good (normalize (calls twoCalls.history)) := by decide

theorem two_calls_invariant : Invariant twoCalls := by
  have i1 := record_invariant (empty : M) empty_invariant ⟨.forward, first.input⟩
    (first.output, firstPrefix.permutation) (by
      rw [PermutationExposure.step_fresh _ _ _ (by decide), support_map]
      exact ⟨first.output, draw_supported _ _ _ (by decide), rfl⟩)
  have i2 := record_invariant firstPrefix i1 ⟨.forward, second.input⟩
    (second.output, twoCalls.permutation) (by
      rw [PermutationExposure.step_fresh _ _ _ (by decide), support_map]
      exact ⟨second.output, draw_supported _ _ _ (by decide), rfl⟩)
  exact i2

theorem actual_forward_goodHistory : GoodHistory twoCalls.history :=
  two_calls_invariant.2.2 two_calls_good.1

/-- Inverse birth followed by a forward cache hit is an actual mixed-direction execution. -/
def inverseFirst : Exposure F 1 := { first with forward := false }
def inversePrefix : M := freshRecord empty inverseFirst

theorem inverse_first_supported : (first.input, inversePrefix) ∈
    support ((handler (.call ⟨.inverse, first.output⟩)).run (empty : M)) :=
  fresh_supported empty _ _ (by decide) (by decide)

def forwardHit : M := record inversePrefix ⟨.forward, first.input⟩
  (first.output, inversePrefix.permutation.tick)

theorem actual_forward_cache :
    (handler (.call ⟨.forward, first.input⟩)).run inversePrefix =
      pure (first.output, forwardHit) := by
  change (fun r ↦ (r.1, record inversePrefix ⟨.forward, first.input⟩ r)) <$>
    PermutationExposure.step (targets inversePrefix.roots) _ _ = _
  rw [PermutationExposure.step_cached _ _ _ (by decide), map_pure]
  rfl

theorem cache_preserves_inverse_birth : normalize (calls forwardHit.history) = [inverseFirst] ∧
    forwardHit.permutation.calls = 2 ∧ (calls forwardHit.history).length = 2 := by decide

theorem inverse_zero_capacity_charged : inversePrefix.permutation.bad = true := by decide

/-- Duplicate roots count twice in the budget and once in the rate target set. -/
def registeredPrefix : M := (register (empty : M) 7 [v 10, v 10]).2

theorem duplicate_roots_retained : registeredPrefix.history = [allocation 7 [v 10, v 10]] ∧
    registeredPrefix.roots.entries.length = 2 ∧
    (targets registeredPrefix.roots registeredPrefix.permutation
      ⟨.forward, (v 1, v 0)⟩).1.card = 3 := by decide

theorem over_budget_refused : register registeredPrefix 8 [v 11] = (false, registeredPrefix) :=
  by
    unfold register
    rw [dite_eq_right (by decide)]

theorem allocation_costs_no_primitive : registeredPrefix.permutation.calls = 0 ∧
    calls registeredPrefix.history = [] := by decide

theorem root_before_preimage_supported : (first.output, freshRecord registeredPrefix first) ∈
    support ((handler (.call ⟨.forward, first.input⟩)).run registeredPrefix) :=
  fresh_supported registeredPrefix _ _ (by decide) (by decide)

theorem root_before_preimage_charged :
    (freshRecord registeredPrefix first).permutation.bad = true := by decide

theorem root_before_preimage_checkpoint_absent :
    directCheckpoint requestOne 7 (freshRecord registeredPrefix first).history (v 10) 0 = none :=
  by decide

theorem duplicate_root_registration_good : GoodHistory registeredPrefix.history :=
  (register_invariant (empty : M) empty_invariant 7 [v 10, v 10]).2.2 rfl

/-- An empty registration still emits a physical allocation marker. -/
theorem empty_registration_keeps_marker :
    (register registeredPrefix 8 []).1 = true ∧
    (register registeredPrefix 8 []).2.history =
      registeredPrefix.history ++ [allocation 8 []] := by decide

/-- Late capacity completion supplies an old missing predecessor while missing rate targets. -/
def suffixFirst : M := freshRecord empty second
def suffixAllocated : M := (register suffixFirst 7 [v 30]).2
def lateCompletion : M := freshRecord suffixAllocated first

theorem suffix_supported : (second.output, suffixFirst) ∈
    support ((handler (.call ⟨.forward, second.input⟩)).run (empty : M)) :=
  fresh_supported empty _ _ (by decide) (by decide)

theorem late_completion_supported : (first.output, lateCompletion) ∈
    support ((handler (.call ⟨.forward, first.input⟩)).run suffixAllocated) :=
  fresh_supported suffixAllocated _ _ (by decide) (by decide)

theorem late_capacity_only :
    first.output.1 ∉ (targets suffixAllocated.roots suffixAllocated.permutation
      ⟨.forward, first.input⟩).1 ∧
    first.output.2 ∈ (targets suffixAllocated.roots suffixAllocated.permutation
      ⟨.forward, first.input⟩).2 := by decide

theorem late_capacity_changes_table :
    directCheckpoint requestTwo 7 lateCompletion.history (v 30) 0 = none ∧
    directExtract requestTwo (normalize (calls lateCompletion.history)) (v 30) 0 =
      some [1, 2] ∧ lateCompletion.permutation.bad = true := by decide

theorem late_capacity_not_good : ¬ GoodHistory lateCompletion.history := by
  intro good
  have eq := direct_checkpoint_agrees (request := requestTwo) (root := v 30) good (by decide :
    lateCompletion.history = beforeFirst (some 7) lateCompletion.history ++
      allocation 7 [v 30] :: [primitive first]) (by simp)
  have point := congrFun eq 0
  have absent := late_capacity_changes_table.1
  have present := late_capacity_changes_table.2.1
  rw [absent, present] at point
  cases point

def completed : M := (register twoCalls 7 [v 30]).2

theorem fixed_two_block_request : directCheckpoint requestTwo 7 completed.history (v 30) 0 =
    some [1, 2] := by decide

theorem changed_width_changes_decoder :
    directCheckpoint requestOne 7 completed.history (v 30) 0 = none := by decide

theorem actual_height_excludes_padding :
    directCheckpoint requestTwo 7 completed.history (v 30) 1 = none := by decide

theorem fixed_zero_completion :
    completeCheckpoint requestTwo 7 completed.history (v 31) 0 = [0, 0] ∧
    completeCheckpoint requestTwo 7 completed.history (v 30) 0 = [1, 2] := by decide

/-- Two allocation commands, three primitive calls, with both cache directions. -/
def mixedProgram : OracleComp (Oracle ℕ F 1) (State F 1) := do
  let _ ← (Oracle ℕ F 1).query (.allocate 7 [v 30, v 30])
  let answer ← (Oracle ℕ F 1).query (.call ⟨.inverse, first.output⟩)
  let output ← (Oracle ℕ F 1).query (.call ⟨.forward, answer⟩)
  let _ ← (Oracle ℕ F 1).query (.allocate 8 [])
  (Oracle ℕ F 1).query (.call ⟨.inverse, output⟩)

theorem mixed_primitive_budget : PrimitiveBudget mixedProgram 3 := by
  simp [mixedProgram, PrimitiveBudget, isPrimitive]

theorem two_is_not_primitive_budget : ¬ PrimitiveBudget mixedProgram 2 := by
  simp [mixedProgram, PrimitiveBudget, isPrimitive]

theorem five_instrumented_commands : IsTotalQueryBound mixedProgram 5 := by
  simp [mixedProgram, IsTotalQueryBound]

theorem mixed_actual_association (result : State F 1 × M)
    (member : result ∈ support ((simulateQ handler mixedProgram).run empty)) :
    result.2.roots.entries = registered result.2.history ∧
    (registered result.2.history).length ≤ 2 ∧
    result.2.permutation.calls = (calls result.2.history).length := by
  have a := run_association mixedProgram result member
  exact ⟨a.2.1, a.2.2, run_call_count mixedProgram result member⟩

theorem actual_mixed_probability :
    Pr{let result ← (simulateQ (handler (b := 2)) mixedProgram).run empty}[
      Disagreement requestTwo result.2.history] ≤ (2112 : ENNReal) / 4093 := by
  apply (extraction_disagreement_le requestTwo mixedProgram 3 mixed_primitive_budget).trans
  have cardinal : Fintype.card D = 64 := by simp [D, Digest, F]
  rw [cardinal]
  change min 1 ((2112 : ENNReal) / 4093) ≤ _
  exact min_le_right _ _

theorem certified_bound_below_one : (2112 : ENNReal) / 4093 < 1 := by
  apply (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mpr
  norm_num


/-- The third call in the mixed example is a genuine inverse cache hit too. -/
def inverseHit : M := record forwardHit ⟨.inverse, first.output⟩
  (first.input, forwardHit.permutation.tick)

theorem actual_inverse_cache :
    (handler (.call ⟨.inverse, first.output⟩)).run forwardHit = pure (first.input, inverseHit) := by
  change (fun r ↦ (r.1, record forwardHit ⟨.inverse, first.output⟩ r)) <$>
    PermutationExposure.step (targets forwardHit.roots) _ _ = _
  rw [PermutationExposure.step_cached _ _ _ (by decide), map_pure]
  rfl

theorem all_three_calls_recorded : normalize (calls inverseHit.history) = [inverseFirst] ∧
    inverseHit.permutation.calls = 3 ∧ (calls inverseHit.history).length = 3 := by decide

/-- Inverse output zero is adversary selected; only the random input is flagged. -/
theorem inverse_selected_output_not_charged :
    ¬ PermutationExposure.FiberHit
      (targets (empty : M).roots (empty : M).permutation ⟨.inverse, (0, 0)⟩).1
      (targets (empty : M).roots (empty : M).permutation ⟨.inverse, (0, 0)⟩).2
      (v 10, v 20) := by decide

theorem completed_trace : SpongeTrace (calls completed.history) 1 1 second [1, 2] :=
  .next (previous := first) (v 2) (.single (v 1) (by decide) (by decide))
    (by decide) (by decide)

theorem concrete_opening_recorded : OpeningRecorded requestTwo completed.history 7 (v 30)
    0 [1, 2] :=
  ⟨[v 30], [], second, [], by decide, by simp, completed_trace, .nil, rfl, by decide⟩

theorem concrete_ordered_duplicate_batch : BatchRecorded requestTwo completed.history 7 (v 30)
    [0, 0] [[1, 2], [1, 2]] := by
  refine ⟨[v 30], [], [(0, v 30)], [], by decide, by simp, .root _, ?_, ?_, ?_⟩
  · intro entry member
    have equal : entry = (0, v 30) := by simpa using member
    subst entry
    exact ⟨second, [1, 2], rfl, completed_trace⟩
  · exact .cons ⟨second, by simp [second], completed_trace⟩
      (.cons ⟨second, by simp [second], completed_trace⟩ .nil)
  · intro i member
    have equal : i = 0 := by simpa using member
    subst i
    decide

theorem completed_goodHistory : GoodHistory completed.history :=
  (register_invariant twoCalls two_calls_invariant 7 [v 30]).2.2 (by decide)

theorem operational_duplicate_batch_agrees :
    [0, 0].map (directCheckpoint requestTwo 7 completed.history (v 30)) =
      [some [1, 2], some [1, 2]] ∧
    [0, 0].map (completeCheckpoint requestTwo 7 completed.history (v 30)) =
      [[1, 2], [1, 2]] :=
  batch_agrees completed_goodHistory concrete_ordered_duplicate_batch

/-- The witness history above is reachable under an actual finite OracleComp. -/
def twoBlockProgram : OracleComp (Oracle ℕ F 1) Bool := do
  let _ ← (Oracle ℕ F 1).query (.call ⟨.forward, first.input⟩)
  let _ ← (Oracle ℕ F 1).query (.call ⟨.forward, second.input⟩)
  (Oracle ℕ F 1).query (.allocate 7 [v 30])

theorem completed_supported_run : (true, completed) ∈
    support ((simulateQ handler twoBlockProgram).run (empty : M)) := by
  simp only [twoBlockProgram, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff]
  refine ⟨(first.output, firstPrefix), first_supported, (second.output, twoCalls),
    second_supported, ?_⟩
  change (true, completed) ∈ support (pure (register twoCalls 7 [v 30]))
  rw [support_pure, Set.mem_singleton_iff]
  rfl

/-- Actual successful operation premises coexist with positive support and quiet sampling. -/
theorem nonvacuous_recorded_batch :
    (true, completed) ∈ support ((simulateQ handler twoBlockProgram).run (empty : M)) ∧
    completed.permutation.bad = false ∧
    BatchRecorded requestTwo completed.history 7 (v 30) [0, 0] [[1, 2], [1, 2]] :=
  ⟨completed_supported_run, by decide, concrete_ordered_duplicate_batch⟩


/-- Quiet inverse births are permitted, including adversary-chosen output-rate collisions. -/
def safeInverse : Exposure F 1 := ⟨false, (v 1, v 5), (v 10, v 20)⟩
def safeInverseSecond : Exposure F 1 := ⟨false, (v 2, v 6), (v 10, v 40)⟩
def safeInversePrefix : M := freshRecord empty safeInverse
def safeInversePair : M := freshRecord safeInversePrefix safeInverseSecond

theorem quiet_inverse_supported : (safeInverse.input, safeInversePrefix) ∈
    support ((handler (.call ⟨.inverse, safeInverse.output⟩)).run (empty : M)) :=
  fresh_supported empty _ _ (by decide) (by decide)

theorem second_inverse_supported : (safeInverseSecond.input, safeInversePair) ∈
    support ((handler (.call ⟨.inverse, safeInverseSecond.output⟩)).run safeInversePrefix) :=
  fresh_supported safeInversePrefix _ _ (by decide) (by decide)

theorem chosen_inverse_output_collision_is_good :
    safeInversePair.permutation.bad = false ∧
    safeInverse.output.1 = safeInverseSecond.output.1 ∧
    Good (normalize (calls safeInversePair.history)) := by decide

end TestsSecurity.PoseidonRecordLaw

import Zkc.Source.Structured.CollectionRepresentation
import Zkc.Source.Structured.CollectionReferenceLaws
import Zkc.Protocols.Multilinear.Source.CollectionEncoding
import Zkc.Protocols.Multilinear.Source.CollectLaws

/-! Synthetic helper-table controls: the actual two-row domain is reused, with
a different scalar formula and a retained capture. No source-body association
is inferred from these synthetic helper names. -/

namespace Tests.CollectionRepresentation
open Zkc.Source Zkc.Source.Structured Zkc.Polynomial.Multilinear
open ZkcExamples.Structured

private def bindings : MultilinearCollectBodies.Bindings :=
  ⟨"difference", "rows", "differenceCallback", "differenceComputation"⟩

private abbrev spec := MultilinearCollectBodies.collectSpec bindings

private def table : HelperTable (assignment ℚ ℚ) closedInterface :=
  [⟨spec.bodyHelper, fun args => .done (.cons
    (args.get .here - args.get (.there .here) +
      args.get (.there (.there (.there (.there .here))))) .nil)⟩]

private theorem callback (lo hi : ℚ) (low high : List ℚ) (offset : ℚ) :
    invoke table spec.bodyHelper
      (.cons lo (.cons hi (.cons low (.cons high (.cons offset .nil))))) =
      .done (.cons (lo - hi + offset) .nil) := by
  rw [table, invoke_cons_same]
  rfl

private theorem domain (low high : List ℚ) (small : low.length < indexLimit)
    (same : low.length = high.length) :
    spec.domain.admit (carriers := uniformCarriers ℚ ℚ) (.cons low (.cons high .nil)) =
      .returned ((List.range low.length).map fun i =>
        .cons (low[i]?.getD 0) (.cons (high[i]?.getD 0) .nil)) := by
  rw [MultilinearCollectLaws.domain_admit bindings low high small same]
  congr 1
  apply List.ext_getElem
  · simp [same]
  · intro i left right
    have lo : i < low.length := by simpa using right
    have hi : i < high.length := same ▸ lo
    simp [lo, hi]

private def encode {n : Nat} (row : Table ℚ n) : List ℚ :=
  List.ofFn (fun position => row (vertex n position))

/-- Two operands, subtraction and a broadcast capture use the same direct
library API as any other arity and formula, at every admitted cube size. -/
theorem difference_encodes {n : Nat} (low high : Table ℚ n) (offset : ℚ)
    (small : 2 ^ n < indexLimit) :
    Evaluation.denoteCollect table spec
      (.cons (encode low) (.cons (encode high) (.cons offset .nil))) =
      .done (.cons (encode (fun bits => low bits - high bits + offset)) .nil) := by
  have admitted := domain (encode low) (encode high)
    (by simpa [encode] using small) (by simp [encode])
  simp only [encode, List.length_ofFn] at admitted
  exact Zkc.Protocols.Multilinear.Source.CollectionEncoding.collect table spec
    (.cons (encode low) (.cons (encode high) .nil)) (.cons offset .nil)
    (![low, high] : Fin 2 → Table ℚ n) 0
    (fun values => .cons (values 0) (.cons (values 1) .nil))
    admitted rfl
    (fun values => values 0 - values 1 + offset)
    (fun values => callback _ _ _ _ _)

private def low : Table ℚ 1 := fun bits => if bits 0 then 9 else 4
private def high : Table ℚ 1 := fun bits => if bits 0 then 2 else 7

-- Every returned element and its order, rather than merely a scalar total.
example : Evaluation.denoteCollect table spec
    (.cons (encode low) (.cons (encode high) (.cons 3 .nil))) =
      .done (.cons [0, 10] .nil) := by
  rw [difference_encodes _ _ _ (by decide +kernel)]
  norm_num [encode, low, high, List.ofFn_succ, vertex]

-- A changed aggregate is obtained from the complete returned collection.
example : (Evaluation.denoteCollect table spec
    (.cons (encode low) (.cons (encode high) (.cons 3 .nil)))).bind
      (fun result => .done ((result.get .here).sum)) = .done 10 := by
  rw [difference_encodes _ _ _ (by decide +kernel)]
  change (PIR.Process.done (encode (fun bits => low bits - high bits + 3)).sum :
    PIR.Process closedInterface ℚ) = .done 10
  congr 1
  norm_num [PIR.Process.bind, Values.get, encode, low, high, List.ofFn_succ, vertex]

-- The actual collection cannot satisfy the same-typed operand-swapped goal.
example : Evaluation.denoteCollect table spec
    (.cons (encode low) (.cons (encode high) (.cons 3 .nil))) ≠
      .done (.cons (encode (fun bits => high bits - low bits + 3)) .nil) := by
  rw [difference_encodes _ _ _ (by decide +kernel)]
  intro swapped
  have observed := congrArg
    (fun result : Values (assignment ℚ ℚ) [.vector "bls12-381.fr"] => result.get .here)
    (PIR.Process.done.inj swapped)
  change encode (fun bits => low bits - high bits + 3) =
    encode (fun bits => high bits - low bits + 3) at observed
  norm_num [encode, low, high, List.ofFn_succ, vertex] at observed

-- Zero-dimensional tables contain exactly one point.
example (a b offset : ℚ) : Evaluation.denoteCollect table spec
    (.cons (encode (n := 0) (fun _ => a))
      (.cons (encode (n := 0) (fun _ => b)) (.cons offset .nil))) =
      .done (.cons [a - b + offset] .nil) := by
  exact difference_encodes _ _ _ (by decide +kernel)

-- Empty admitted rows do not invoke even a missing callback.
example : Evaluation.denoteCollect (carriers := uniformCarriers ℚ ℚ)
    (interface := closedInterface) [] spec (.cons [] (.cons [] (.cons 5 .nil))) =
      .done (.cons [] .nil) := by
  exact Evaluation.denoteCollect_empty (carriers := uniformCarriers ℚ ℚ)
    [] spec (.cons [] (.cons [] .nil)) (.cons 5 .nil) rfl

-- Strict zip fails on either unequal-length direction, before the missing body.
example : Evaluation.denoteCollect (carriers := uniformCarriers ℚ ℚ)
    (interface := closedInterface) [] spec (.cons [4] (.cons [] (.cons 5 .nil))) =
      .halt .refused := by
  exact Evaluation.denoteCollect_admission_stop (carriers := uniformCarriers ℚ ℚ) [] spec
    (.cons [4] (.cons [] .nil)) (.cons 5 .nil) .refused rfl

example : Evaluation.denoteCollect (carriers := uniformCarriers ℚ ℚ)
    (interface := closedInterface) [] spec (.cons [] (.cons [4] (.cons 5 .nil))) =
      .halt .refused := by
  exact Evaluation.denoteCollect_admission_stop (carriers := uniformCarriers ℚ ℚ) [] spec
    (.cons [] (.cons [4] .nil)) (.cons 5 .nil) .refused rfl

private abbrev traceInterface : PIR.Signature := ⟨ℚ, fun _ => Unit⟩

private def effect (lo hi offset : ℚ) : PIR.Process traceInterface ℚ :=
  .call lo fun _ => if lo = 9 then .halt .abort else .done (lo - hi + offset)

private def effectTable : HelperTable (assignment ℚ ℚ) traceInterface :=
  [⟨spec.bodyHelper, fun args =>
    (effect (args.get .here) (args.get (.there .here))
      (args.get (.there (.there (.there (.there .here)))))).bind
        (fun value => .done (.cons value .nil))⟩]

/-- The process correspondence imposes no totality or finite-table encoding
assumption on the callback. All row arguments and the capture are retained. -/
theorem effect_correspondence (low high : List ℚ) (offset : ℚ)
    (small : low.length < indexLimit) (same : low.length = high.length) :
    Evaluation.denoteCollect effectTable spec
      (.cons low (.cons high (.cons offset .nil))) =
      ((List.range low.length).mapM (fun i =>
        effect (low[i]?.getD 0) (high[i]?.getD 0) offset)).bind
          (fun values => .done (.cons values .nil)) := by
  exact Evaluation.denoteCollect_indexed_process effectTable spec
    (.cons low (.cons high .nil)) (.cons offset .nil) (.returned low.length)
    (fun i => .cons (low[i]?.getD 0) (.cons (high[i]?.getD 0) .nil))
    (domain low high small same) rfl
    (fun i => effect (low[i]?.getD 0) (high[i]?.getD 0) offset) (by
      intro i
      rw [effectTable, invoke_cons_same]
      rfl)

-- The successful first call and the stopping second call remain visible.
-- The third row is never called and no partial collection is returned.
example : Evaluation.denoteCollect effectTable spec
    (.cons [4, 9, 99] (.cons [7, 2, 3] (.cons 3 .nil))) =
      .call 4 (fun _ => .call 9 (fun _ => .halt .abort)) := by
  rw [effect_correspondence [4, 9, 99] [7, 2, 3] 3 (by decide +kernel) rfl]
  norm_num [List.range_succ, List.mapM_cons, List.mapM_nil, effect, PIR.Process.bind]
  rfl

-- Admission precedes every callback effect, even if the first row would stop.
example : Evaluation.denoteCollect effectTable spec
    (.cons [9] (.cons [] (.cons 3 .nil))) = .halt .refused := by
  exact Evaluation.denoteCollect_indexed_process effectTable spec
    (.cons [9] (.cons [] .nil)) (.cons 3 .nil) (.stopped .refused)
    (fun _ => .cons 9 (.cons 0 .nil)) rfl rfl (fun _ => effect 9 0 3) (by
      intro i
      rw [effectTable, invoke_cons_same]
      rfl)

#print axioms Evaluation.denoteCollect_indexed_process
#print axioms Evaluation.denoteCollect_ofFn
#print axioms Zkc.Protocols.Multilinear.Source.CollectionEncoding.collect
#print axioms difference_encodes
#print axioms effect_correspondence

end Tests.CollectionRepresentation

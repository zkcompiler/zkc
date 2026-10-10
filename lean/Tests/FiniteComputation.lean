import Zkc.Semantics.FiniteComputation.Realization
import Tests.Checks

/-! Executable controls and kernel-checked counterexamples for the independent
finite-computation model. They do not execute the native compiler or runtime. -/

set_option autoImplicit false

namespace Tests.FiniteComputation

open Zkc.FiniteComputation

private def accept {α : Type} (_ : α) : Except String Bool := .ok true
private def reject {α : Type} (_ : α) : Except String Bool := .ok false
private def identity (item : Nat) : Except String Nat := .ok item
private def add (state value : Nat) : Except String Nat := .ok (state + value)
private def bodyFailure (item : Nat) : Except String Nat :=
  if item = 2 then .error "body-second" else .ok item
private def updateFailure (_state _value : Nat) : Except String Nat := .error "update-first"
private def predicateFailure (item : Nat) : Except String Bool :=
  if item = 2 then .error "predicate-second" else .ok true
private def failingDomain : Domain String := .guard (.error "inner-admission") (.elements [])
private def digits (state item : Nat) : Nat := 10 * state + item

-- Kernel proofs keep the key counterexamples independent of compiled evaluation.
example : Total.fold [2, 2, 3] (fun _ => true) id (· + ·) 0 = 7 := by decide
example : Total.fold [2, 3] (fun _ => true) id (· + ·) 0 ≠ 7 := by decide
example : Total.fold [1, 2, 3] (fun _ => true) id digits 0 = 123 := by decide
example : Total.fold [3, 2, 1] (fun _ => true) id digits 0 ≠ 123 := by decide
example : Total.fold [5, 2] (fun _ => true) id (· - ·) 10 ≠ 10 - (5 - 2) := by decide

-- Concatenation is associative but noncommutative; swapping terms changes it.
example : Total.fold ["a", "b"] (fun _ => true) id (· ++ ·) "" = "ab" := by decide
example : Total.fold ["b", "a"] (fun _ => true) id (· ++ ·) "" ≠ "ab" := by decide

-- Materialization reaches the second body; streaming first reaches the update.
example : Local.materialize [1, 2] accept bodyFailure (fun values => values.foldlM updateFailure 0) =
    .error "body-second" := by decide
example : Local.fold [1, 2] accept bodyFailure updateFailure 0 = .error "update-first" := by decide
example : Local.materialize [1, 2] accept bodyFailure (fun values => values.foldlM updateFailure 0) ≠
    Local.fold [1, 2] accept bodyFailure updateFailure 0 := by decide

-- The positive law preserves a body failure under a total update.
example (items : List Nat) :
    Local.materialize items accept bodyFailure (fun values => .ok (values.foldl (· + ·) 0)) =
      Local.fold items accept bodyFailure add 0 :=
  Local.materialize_total_step items accept bodyFailure (· + ·) 0

example (items : List Nat) :
    Local.materialize items accept identity (fun values => values.foldlM updateFailure 0) =
      Local.fold items accept identity updateFailure 0 :=
  Local.materialize_total_selection items (fun _ => true) id updateFailure 0

example (items : List Nat) :
    Local.fold items accept identity add 0 = .ok (Total.fold items (fun _ => true) id (· + ·) 0) :=
  Local.fold_total items (fun _ => true) id (· + ·) 0

-- Independent admission and dependent entry differ, even for an empty outer list.
example : (Domain.product (.elements ([] : List Nat)) failingDomain).enumerate =
    .error "inner-admission" := by decide
example : Local.nestedFold ([] : List Nat) (fun _ => failingDomain.enumerate)
    (fun (state : Nat) _ _ => .ok state) 7 = .ok 7 := rfl

-- Successful multiway zip requires even the third, ignored leaf to agree.
private def ignoredMismatch : Domain ((Nat × String) × Bool) :=
  .zip (.zip (.elements []) (.elements [])) (.elements [true])
example : Local.runFold ignoredMismatch reject (fun _ => .ok (99 : Nat)) add 0 =
    .error "finite-zip-shape" := by decide

-- All three types differ: item = Bool, result = String, state = Nat × String.
example : Total.fold [true, false, true] (fun _ => true)
    (fun b => if b then "T" else "F")
    (fun (s : Nat × String) value => (s.1 + 1, s.2 ++ value)) (0, "") = (3, "TFT") := by decide
example : Local.fold [true, false, true] (fun _ => .ok true)
    (fun b => .ok (if b then "T" else "F"))
    (fun (s : Nat × String) value => .ok (s.1 + 1, s.2 ++ value)) (0, "") = .ok (3, "TFT") := by decide

-- Consumers instantiate the admitted laws, not an unchecked truncating zip.
example : Local.runFold (.zip (.elements ([2, 3] : List Int)) (.elements [5, 7])) accept
    (fun pair => .ok (pair.1 * pair.2)) (fun state value => .ok (state + value)) 0 =
    Zkc.Algebra.FiniteVectors.dot [2, 3] [5, 7] := dot_admitted _ _ rfl (by decide)

example : Local.runFold (.zip (.elements ([(2, 1), (3, -2)] : List (Int × Int)))
      (.elements ([5, 7] : List Int))) accept
    (fun pair => .ok (pair.2 • pair.1)) (fun state value => .ok (state + value)) (0 : Int × Int) =
      .ok (sumMap (([(2, 1), (3, -2)] : List (Int × Int)).zip ([5, 7] : List Int))
        (fun pair => pair.2 • pair.1)) := msm_admitted _ _ rfl

example : sumMap (List.finRange 2) (fun i => (![5, 7] : Fin 2 → Int) i •
    sumMap (List.finRange 3) (fun j => (![![1, 2, 3], ![4, 5, 6]] : Matrix (Fin 2) (Fin 3) Int) i j •
      (![2, 3, 4] : Fin 3 → Int) j)) = 429 := by decide

example : sumMap (List.finRange 2) (fun i => (![5, 7] : Fin 2 → Int) i •
    sumMap (List.finRange 3) (fun j => (![![1, 2, 3], ![4, 5, 6]] : Matrix (Fin 2) (Fin 3) Int) i j •
      (![2, 3, 4] : Fin 3 → Int) j)) =
    sumMap (List.finRange 3) (fun j =>
      Matrix.vecMul (![5, 7] : Fin 2 → Int) (![![1, 2, 3], ![4, 5, 6]]) j • (![2, 3, 4] : Fin 3 → Int) j) :=
  matrix_contraction _ _ _

/-- Run every independent control, then report all failures together. -/
def run : IO Unit := do
  let checks ← Tests.Checks.start
  checks.holds (Total.collect [2, 2, 3] (fun _ => true) id == [2, 2, 3]) "duplicate positions survive"
  checks.holds (Total.fold [1, 2, 3] (fun _ => true) id digits 0 == 123) "ordered total state updates"
  checks.holds (Total.fold ([] : List Nat) (fun _ => true) id digits 42 == 42) "empty total initial state"
  checks.holds (sumMap ([2, 2, 3] : List Nat) id == 7) "duplicate sum"
  checks.holds (productMap ([] : List Nat) id == 1) "empty product identity"
  checks.holds (sumMap ([] : List Nat) id == 0) "empty sum identity"
  checks.holds ((Domain.zip (.elements [1, 2]) (.elements ["a", "b"])).enumerate ==
    .ok [(1, "a"), (2, "b")]) "heterogeneous strict zip"
  checks.holds ((Domain.zip (.elements ([1, 2] : List Nat)) (.elements ["a"])).enumerate ==
    .error "finite-zip-shape") "zip never truncates"
  checks.holds ((Domain.zip (.elements ([] : List Nat)) (.elements [true])).enumerate ==
    .error "finite-zip-shape") "empty zip still checks other extent"
  checks.holds ((Domain.zip (.elements [true]) (.elements ([] : List Nat))).enumerate ==
    .error "finite-zip-shape") "empty right zip still checks extent"
  checks.holds ((Domain.zip (.elements ([] : List Nat)) (.elements ([] : List Bool))).enumerate ==
    .ok []) "admitted empty zip"
  checks.holds (Local.runFold ignoredMismatch reject (fun _ => .ok 99) add 0 ==
    .error "finite-zip-shape") "unused third extent checked before filter"
  checks.holds ((Domain.zip (.guard (.error "left") (.elements ([1] : List Nat)))
    (.guard (.error "right") (.elements [true]))).enumerate == .error "left") "left admission failure first"
  checks.holds ((Domain.product (.elements ([] : List Nat)) failingDomain).enumerate ==
    .error "inner-admission") "independent empty product checks right"
  checks.holds ((Domain.product failingDomain (.elements ([] : List Nat))).enumerate ==
    .error "inner-admission") "independent empty product checks left"
  checks.holds ((Domain.product (.elements [1, 2]) (.elements ["a", "b"])).enumerate ==
    .ok [(1, "a"), (1, "b"), (2, "a"), (2, "b")]) "product lexicographic order"
  checks.holds (Local.collect [2] reject bodyFailure == .ok []) "filter skips failing body"
  checks.holds (Local.fold [2] reject bodyFailure updateFailure 7 == .ok 7) "filter also skips update"
  checks.holds (Local.collect [2] predicateFailure bodyFailure == .error "predicate-second") "predicate before body"
  checks.holds (Local.collect [2] accept bodyFailure == .error "body-second") "accepted body failure"
  checks.holds (Local.collect [3, 2, 1] (fun x => .ok (x % 2 == 1)) identity == .ok [3, 1]) "stable filter order"
  checks.holds (Local.fold [1, 2] accept bodyFailure updateFailure 0 == .error "update-first") "streaming first update failure"
  checks.holds (Local.materialize [1, 2] accept bodyFailure (fun values => values.foldlM updateFailure 0) ==
    .error "body-second") "materialization body failure precedes reducer"
  checks.holds (Local.materialize [1, 2] predicateFailure identity (fun _ => (.error "reducer" : Except String Nat)) ==
    .error "predicate-second") "materialization predicate failure precedes reducer"
  checks.holds (Local.materialize [1, 2] accept identity (fun _ => (.error "reducer" : Except String Nat)) ==
    .error "reducer") "reducer failure after successful materialization"
  checks.holds (Local.materialize ([] : List Nat) accept identity (fun _ => (.error "empty-reducer" : Except String Nat)) ==
    .error "empty-reducer") "empty materialization still calls reducer"
  checks.holds (Local.materialize [1, 2, 3] accept identity (fun values => .ok (values.length == 3)) ==
    .ok true) "ordinary reducer may inspect length and change result type"
  checks.holds (Local.fold [1, 2] accept bodyFailure add 0 == .error "body-second") "total update retains body failure"
  checks.holds (Local.fold ([] : List Nat) predicateFailure bodyFailure updateFailure 9 == .ok 9) "empty fold invokes no callbacks"
  checks.holds (Local.nestedFold ([] : List Nat) (fun _ => failingDomain.enumerate)
    (fun (s : Nat) _ _ => .ok s) 7 == .ok 7) "empty nested skips inner admission"
  checks.holds (Local.nestedFold [0, 1, 2] (fun i => .ok (List.range i))
    (fun (s : List (Nat × Nat)) i j => .ok (s ++ [(i, j)])) [] ==
      .ok [(1, 0), (2, 0), (2, 1)]) "dependent triangular traversal"
  checks.holds (Local.nestedFold [1, 1] (fun i => .ok (List.range i))
    (fun (s : Nat) _ _ => .ok (s + 1)) 0 == .ok 2) "repeated outer entries repeat inner traversal"
  checks.holds (Local.nestedFold [0, 1] (fun i => if i == 0 then .ok [0] else .error "late-inner")
    (fun (_s : Nat) _ _ => .error "first-update") 0 == .error "first-update") "unreached inner failure is not hoisted"
  checks.holds (Local.nestedFold [0, 1] (fun i => if i == 0 then .ok [0] else .error "late-inner")
    (fun (s : Nat) _ _ => .ok (s + 1)) 0 == .error "late-inner") "reached inner failure propagates"
  checks.holds (Local.runFold (.zip (.elements ([(2, 1), (3, -2)] : List (Int × Int)))
    (.elements ([5, 7] : List Int))) accept (fun pair => .ok (pair.2 • pair.1))
    (fun state value => .ok (state + value)) (0 : Int × Int) == .ok (31, -9)) "heterogeneous module MSM"
  checks.holds (Local.runFold (.zip (.elements ([2, 3] : List Int)) (.elements [5, 7])) accept
    (fun pair => .ok (pair.1 * pair.2)) (fun state value => .ok (state + value)) 0 == .ok 31) "dot consumer"
  checks.holds ((Domain.guard (.ok ()) (.elements ([1, 1] : List Nat))).enumerate == .ok [1, 1])
    "successful guard preserves duplicates"
  checks.holds (Total.fold ["a", "b"] (fun _ => true) id (· ++ ·) "" !=
    Total.fold ["b", "a"] (fun _ => true) id (· ++ ·) "") "noncommutative order matters"
  checks.holds (sumMap (List.finRange 2) (fun i => (![5, 7] : Fin 2 → Int) i •
    sumMap (List.finRange 3) (fun j => (![![1, 2, 3], ![4, 5, 6]] : Matrix (Fin 2) (Fin 3) Int) i j •
      (![2, 3, 4] : Fin 3 → Int) j)) == 429) "matrix contraction value"
  checks.finish "finite computation controls"

#eval run

end Tests.FiniteComputation

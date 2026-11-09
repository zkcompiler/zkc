module

public import Zkc.Protocol.Library.Transformations.Commitment.BatchOpening
public import Zkc.Protocol.Library.Transformations.Commitment.TableLog
public import Zkc.Program.Execution
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! # A binary, single-table pruned verification operation

This independent operation interprets the cap-zero, arity-two, single-table walk described in
`docs/spec/domains/oracles.md` and implemented by the pinned Plonky3 0.8.0 adapter. It is not a
proof of Rust execution. In particular, a realization must associate the direct boundary cursor
here with `restore_paths` and the native lead-path buffers. Hash queries are actual `OracleComp`
queries: shared nodes are queried once, and no scalar paths are replayed to obtain a certificate.

The row carrier and its width/codec predicate are fixed by the application. Decode exhaustion is
an explicit boundary input, distinct from malformed authentication and invalid verifier requests.
There is no artificial hash budget, random-oracle assumption, or probability framework here.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.BatchVerification

open OracleComp OracleSpec BatchOpening

variable {Row Query Y : Type}

/-- Merge one parent before continuing with the remaining groups in this layer. -/
def join (model : LeafHashing Row Query Y) (p : ℕ) (left right : Y)
    (next : OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y))) :
    OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y)) := do
  let up ← (liftM ((Query →ₒ Y).query (model.node left right)) : OracleComp (Query →ₒ Y) Y)
  let result ← next
  pure (result.map fun result ↦ ((p, up) :: result.1, result.2))

/-- Process ascending binary groups and consume boundary siblings in child order.
Sortedness is an invariant proved by the caller, rather than an extra runtime refusal policy. -/
def layer (model : LeafHashing Row Query Y) :
    Frontier Y → List Y → OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y))
  | [], proof => pure (some ([], proof))
  | (index, label) :: rest, proof =>
      let p := index / 2
      let recurse := layer model rest
      if index % 2 = 0 then
        match rest with
        | (next, sibling) :: tail =>
            if next = index + 1 then
              join model p label sibling (layer model tail proof)
            else
              match proof with
              | [] => pure none
              | sibling :: remaining =>
                  join model p label sibling (recurse remaining)
        | [] =>
            match proof with
            | [] => pure none
            | sibling :: remaining =>
                join model p label sibling (recurse remaining)
      else
        match proof with
        | [] => pure none
        | sibling :: remaining =>
            join model p sibling label (recurse remaining)
termination_by structural frontier _ => frontier

/-- Run exactly the verifier-derived number of compression layers, then require one cap root
and complete proof consumption. Failure is an authentication Boolean, never a stopped process. -/
def reduce [DecidableEq Y] (model : LeafHashing Row Query Y) :
    ℕ → Frontier Y → List Y → Y → OracleComp (Query →ₒ Y) Bool
  | 0, frontier, proof, root => pure (frontier == [(0, root)] && proof.isEmpty)
  | depth + 1, frontier, proof, root => do
      match ← layer model frontier proof with
      | none => pure false
      | some (above, remaining) => reduce model depth above remaining root

/-- Hash each representative row exactly once in ascending distinct position order. -/
def hashRows (model : LeafHashing Row Query Y) :
    List (ℕ × Row) → OracleComp (Query →ₒ Y) (Frontier Y)
  | [] => pure []
  | (index, row) :: rest => do
      let label ← (liftM ((Query →ₒ Y).query (model.leaf row)) : OracleComp (Query →ₒ Y) Y)
      let tail ← hashRows model rest
      pure ((index, label) :: tail)

private theorem join_eval (model : LeafHashing Row Query Y) (answer : Query → Y)
    (p : ℕ) (left right : Y)
    (next : OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y))) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (join model p left right next) =
      (evalWithAnswerFn (QueryImpl.ofFn answer) next).map
        (fun result ↦ ((p, answer (model.node left right)) :: result.1, result.2)) := by
  simp only [join, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, evalWithAnswerFn_pure]

private theorem join_log (model : LeafHashing Row Query Y) (answer : Query → Y)
    (p : ℕ) (left right : Y)
    (next : OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y))) :
    tableQueryLog (join model p left right next) answer =
      ⟨model.node left right, answer (model.node left right)⟩ :: tableQueryLog next answer := by
  simp only [join, tableQueryLog_bind, tableQueryLog_query, tableQueryLog_pure,
    List.append_nil, List.singleton_append, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]

private theorem layer_shared (model : LeafHashing Row Query Y) (p : ℕ) (left right : Y)
    (rest : Frontier Y) (proof : List Y) :
    layer model ((2 * p, left) :: (2 * p + 1, right) :: rest) proof =
      join model p left right (layer model rest proof) := by
  rw [layer.eq_def]
  dsimp only
  have even : 2 * p % 2 = 0 := by omega
  have quotient : 2 * p / 2 = p := by omega
  simp only [even, quotient, ↓reduceIte]

private theorem layer_left (model : LeafHashing Row Query Y) (p : ℕ) (left right : Y)
    (rest : Frontier Y) (proof : List Y) (after : ∀ entry ∈ rest, 2 * p + 1 < entry.1) :
    layer model ((2 * p, left) :: rest) (right :: proof) =
      join model p left right (layer model rest proof) := by
  rw [layer.eq_def]
  dsimp only
  have even : 2 * p % 2 = 0 := by omega
  have quotient : 2 * p / 2 = p := by omega
  simp only [even, quotient, ↓reduceIte]
  cases rest with
  | nil => rfl
  | cons entry rest =>
      obtain ⟨index, label⟩ := entry
      have beyond := after (index, label) List.mem_cons_self
      have separate : index ≠ 2 * p + 1 := by omega
      simp only [separate, ↓reduceIte]

private theorem layer_right (model : LeafHashing Row Query Y) (p : ℕ) (left right : Y)
    (rest : Frontier Y) (proof : List Y) :
    layer model ((2 * p + 1, right) :: rest) (left :: proof) =
      join model p left right (layer model rest proof) := by
  rw [layer.eq_def]
  dsimp only
  have odd : ¬ (2 * p + 1) % 2 = 0 := by omega
  have quotient : (2 * p + 1) / 2 = p := by omega
  simp only [odd, quotient, ↓reduceIte]

/-- Honest completeness for a layer: the certificate must use the supplied answer function.
The exact query count is one compression per output parent, independent of boundary count. -/
theorem layer_complete (model : LeafHashing Row Query Y) (answer : Query → Y)
    {log : HashLog Query Y} (consistent : ∀ entry ∈ log, answer entry.1 = entry.2)
    {below above : Frontier Y} {proof tail : List Y}
    (certificate : Layer model log below proof above tail) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (layer model below proof) = some (above, tail) ∧
      (tableQueryLog (layer model below proof) answer).length = above.length := by
  induction certificate with
  | nil => simp only [layer, evalWithAnswerFn_pure, tableQueryLog_pure, List.length_nil,
      and_self]
  | shared after call next ih =>
      rw [layer_shared model]
      have response := consistent _ call
      exact ⟨by simp only [join_eval, ih.1, Option.map_some, response],
        by simp only [join_log, List.length_cons, ih.2]⟩
  | left after call next ih =>
      rw [layer_left model _ _ _ _ _ after]
      have response := consistent _ call
      exact ⟨by simp only [join_eval, ih.1, Option.map_some, response],
        by simp only [join_log, List.length_cons, ih.2]⟩
  | right after call next ih =>
      rw [layer_right model]
      have response := consistent _ call
      exact ⟨by simp only [join_eval, ih.1, Option.map_some, response],
        by simp only [join_log, List.length_cons, ih.2]⟩

/-- Number of parent compressions visited by the verifier-owned frontier schedule. -/
def compressionCount : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | depth + 1, indices =>
      (layout indices).1.length + compressionCount depth (layout indices).1

/-- Answer-consistent recorded reductions execute successfully and preserve the entire grouped
loop count. This is completeness relative to explicit rows/proof, not a native producer proof. -/
theorem reduce_complete [DecidableEq Y] (model : LeafHashing Row Query Y) (answer : Query → Y)
    {log : HashLog Query Y} (consistent : ∀ entry ∈ log, answer entry.1 = entry.2)
    {depth : ℕ} {frontier : Frontier Y} {proof : List Y} {root : Y}
    (certificate : Reduction model log depth frontier proof root) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (reduce model depth frontier proof root) = true ∧
      (tableQueryLog (reduce model depth frontier proof root) answer).length =
        compressionCount depth (frontier.map Prod.fst) := by
  induction certificate with
  | root => simp [reduce, compressionCount]
  | step layer next ih =>
      obtain ⟨result, count⟩ := layer_complete model answer consistent layer
      obtain ⟨positions, _⟩ := layer.layout_eq
      constructor
      · simp only [reduce, evalWithAnswerFn_bind, result, ih.1]
      · simp only [reduce, tableQueryLog_bind, result, List.length_append, count,
          compressionCount, positions, List.length_map, ih.2]

private theorem layer_parent_origin {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (certificate : Layer model log below proof above tail) :
    ∀ entry ∈ above, ∃ child ∈ below, entry.1 = child.1 / 2 := by
  induction certificate with
  | nil => simp
  | @shared p left right up rest above proof tail after call next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨(2 * p, left), by simp, by simp⟩
      · obtain ⟨child, childMem, same⟩ := ih entry later
        exact ⟨child, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ childMem), same⟩
  | @left p left right up rest above proof tail after call next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨(2 * p, left), by simp, by simp⟩
      · obtain ⟨child, childMem, same⟩ := ih entry later
        exact ⟨child, List.mem_cons_of_mem _ childMem, same⟩
  | @right p left right up rest above proof tail after call next ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨(2 * p + 1, right), by simp, by dsimp; omega⟩
      · obtain ⟨child, childMem, same⟩ := ih entry later
        exact ⟨child, List.mem_cons_of_mem _ childMem, same⟩

private theorem layer_parents_after {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y} {p : ℕ}
    (certificate : Layer model log below proof above tail)
    (after : ∀ entry ∈ below, 2 * p + 1 < entry.1) : ∀ entry ∈ above, p < entry.1 := by
  intro entry member
  obtain ⟨child, childMem, same⟩ := layer_parent_origin certificate entry member
  have bound := after child childMem
  omega

/-- Parent groups remain strictly ordered, independent of all hash responses. -/
theorem layer_sorted {model : LeafHashing Row Query Y} {log : HashLog Query Y}
    {below above : Frontier Y} {proof tail : List Y}
    (certificate : Layer model log below proof above tail) :
    (above.map Prod.fst).SortedLT := by
  suffices above.Pairwise (fun first second ↦ first.1 < second.1) by
    exact (List.pairwise_map.mpr this).sortedLT
  induction certificate with
  | nil => exact .nil
  | shared after call next ih => exact .cons (layer_parents_after next after) ih
  | left after call next ih => exact .cons (layer_parents_after next after) ih
  | right after call next ih => exact .cons (layer_parents_after next after) ih

private theorem join_recorded (model : LeafHashing Row Query Y) (answer : Query → Y)
    (log : HashLog Query Y) (p : ℕ) (left right : Y)
    (next : OracleComp (Query →ₒ Y) (Option (Frontier Y × List Y)))
    {above : Frontier Y} {tail : List Y}
    (recorded : ∀ entry ∈ tableQueryLog (join model p left right next) answer, entry ∈ log)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer) (join model p left right next) =
      some (above, tail)) :
    ∃ rest, above = (p, answer (model.node left right)) :: rest ∧
      (⟨model.node left right, answer (model.node left right)⟩ : (_ : Query) × Y) ∈ log ∧
      (∀ entry ∈ tableQueryLog next answer, entry ∈ log) ∧
      evalWithAnswerFn (QueryImpl.ofFn answer) next = some (rest, tail) := by
  simp only [join, tableQueryLog_bind, tableQueryLog_query, tableQueryLog_pure,
    List.singleton_append,
    List.append_nil, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
    QueryImpl.ofFn_apply, evalWithAnswerFn_pure] at recorded accepted
  cases result : evalWithAnswerFn (QueryImpl.ofFn answer) next with
  | none => simp [result] at accepted
  | some value =>
      obtain ⟨rest, remaining⟩ := value
      simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact ⟨rest, rfl, recorded _ List.mem_cons_self,
        fun entry member ↦ recorded entry (List.mem_cons_of_mem _ member), rfl⟩

/-- A successful layer constructs its certificate from its own actual queries, or from any
joint record containing those queries. Arbitrary answer functions, including collisions, work. -/
theorem layer_sound (model : LeafHashing Row Query Y) (answer : Query → Y)
    (log : HashLog Query Y) :
    ∀ (frontier : Frontier Y) (proof : List Y) {above : Frontier Y} {tail : List Y},
      (frontier.map Prod.fst).SortedLT →
      (∀ entry ∈ tableQueryLog (layer model frontier proof) answer, entry ∈ log) →
      evalWithAnswerFn (QueryImpl.ofFn answer) (layer model frontier proof) = some (above, tail) →
      Layer model log frontier proof above tail
  | [], proof, above, tail, sorted, recorded, accepted => by
      simp only [layer, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .nil proof
  | (index, label) :: rest, proof, above, tail, sorted, recorded, accepted => by
      have order : ((index, label) :: rest).Pairwise
          (fun first second ↦ first.1 < second.1) := List.pairwise_map.mp sorted.pairwise
      have restSorted : (rest.map Prod.fst).SortedLT :=
        (List.pairwise_map.mpr order.tail).sortedLT
      have later : ∀ {entry}, entry ∈ rest → index < entry.1 :=
        fun member ↦ List.rel_of_pairwise_cons order member
      rw [layer.eq_def] at recorded accepted
      dsimp only at recorded accepted
      split at accepted
      next even =>
        simp only [even, ↓reduceIte] at recorded
        have indexEq : index = 2 * (index / 2) := by omega
        cases rest with
        | nil =>
            cases proof with
            | nil => simp at accepted
            | cons sibling remaining =>
                simp only at recorded accepted
                obtain ⟨upper, rfl, call, calls, result⟩ :=
                  join_recorded model answer log _ _ _ _ recorded accepted
                simpa only [← indexEq] using
                  (Layer.left (p := index / 2) (by simp) call
                    (layer_sound model answer log [] remaining restSorted calls result))
        | cons entry rest =>
            obtain ⟨next, sibling⟩ := entry
            have tailSorted : (rest.map Prod.fst).SortedLT :=
              (List.pairwise_map.mpr order.tail.tail).sortedLT
            simp only at recorded accepted
            split at accepted
            next adjacent =>
              simp only [adjacent, ↓reduceIte] at recorded
              have after : ∀ entry ∈ rest, 2 * (index / 2) + 1 < entry.1 := by
                intro entry member
                have bound := List.rel_of_pairwise_cons order.tail member
                dsimp only at bound
                omega
              obtain ⟨upper, rfl, call, calls, result⟩ :=
                join_recorded model answer log _ _ _ _ recorded accepted
              subst next
              simpa only [← indexEq] using
                (Layer.shared (p := index / 2) after call
                  (layer_sound model answer log rest proof tailSorted calls result))
            next separate =>
              simp only [separate, ↓reduceIte] at recorded
              have after : ∀ entry ∈ (next, sibling) :: rest,
                  2 * (index / 2) + 1 < entry.1 := by
                intro entry member
                have bound := later member
                rcases List.mem_cons.mp member with rfl | inRest
                · dsimp only at bound ⊢; omega
                · have beyond := List.rel_of_pairwise_cons order.tail inRest
                  have first := later List.mem_cons_self
                  dsimp only at bound beyond first
                  omega
              cases proof with
              | nil => simp at accepted
              | cons boundary remaining =>
                  simp only at recorded accepted
                  obtain ⟨upper, rfl, call, calls, result⟩ :=
                    join_recorded model answer log _ _ _ _ recorded accepted
                  simpa only [← indexEq] using
                    (Layer.left (p := index / 2) after call
                      (layer_sound model answer log ((next, sibling) :: rest) remaining
                        restSorted calls result))
      next odd =>
        simp only [odd, ↓reduceIte] at recorded
        have after : ∀ entry ∈ rest, 2 * (index / 2) + 1 < entry.1 := by
          intro entry member
          have bound := later member
          omega
        cases proof with
        | nil => simp at accepted
        | cons sibling remaining =>
            simp only at recorded accepted
            obtain ⟨upper, rfl, call, calls, result⟩ :=
              join_recorded model answer log _ _ _ _ recorded accepted
            have indexEq : index = 2 * (index / 2) + 1 := by omega
            simpa only [← indexEq] using
              (Layer.right (p := index / 2) after call
                (layer_sound model answer log rest remaining restSorted calls result))

/-- Success of the compression loop yields the existing reduction relation without replaying
paths or postulating any recorded hash answers. -/
theorem reduce_sound [DecidableEq Y] (model : LeafHashing Row Query Y) (answer : Query → Y)
    (log : HashLog Query Y) :
    ∀ (depth : ℕ) (frontier : Frontier Y) (proof : List Y) (root : Y),
      (frontier.map Prod.fst).SortedLT →
      (∀ entry ∈ tableQueryLog (reduce model depth frontier proof root) answer, entry ∈ log) →
      evalWithAnswerFn (QueryImpl.ofFn answer) (reduce model depth frontier proof root) = true →
      Reduction model log depth frontier proof root
  | 0, frontier, proof, root, sorted, recorded, accepted => by
      simp only [reduce, evalWithAnswerFn_pure, Bool.and_eq_true, beq_iff_eq,
        List.isEmpty_iff] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .root root
  | depth + 1, frontier, proof, root, sorted, recorded, accepted => by
      simp only [reduce, tableQueryLog_bind, evalWithAnswerFn_bind] at recorded accepted
      cases result : evalWithAnswerFn (QueryImpl.ofFn answer) (layer model frontier proof) with
      | none => simp [result] at accepted
      | some pair =>
          obtain ⟨above, tail⟩ := pair
          simp only [result] at recorded accepted
          have certificate := layer_sound model answer log frontier proof sorted
            (fun entry member ↦ recorded entry (List.mem_append_left _ member)) result
          exact .step certificate (reduce_sound model answer log depth above tail root
            (layer_sorted certificate)
            (fun entry member ↦ recorded entry (List.mem_append_right _ member)) accepted)

/-- Verifier-owned sorted unique positions. -/
def unique (positions : List ℕ) : List ℕ := positions.dedup.insertionSort (· ≤ ·)

theorem unique_mem {index : ℕ} {positions : List ℕ} :
    index ∈ unique positions ↔ index ∈ positions := by simp [unique]

theorem unique_sorted (positions : List ℕ) : (unique positions).SortedLT :=
  List.sortedLE_insertionSort.sortedLT_of_nodup
    ((List.perm_insertionSort (· ≤ ·) positions.dedup).nodup_iff.mpr (List.nodup_dedup _))

/-- First occurrence supplies the row; every duplicate is compared with it before hashing. -/
def representative (pairs : List (ℕ × Row)) (index : ℕ) : Option (ℕ × Row) :=
  pairs.find? (fun pair ↦ pair.1 == index)

/-- A pure representative selection. Failure cannot occur after length and duplicate admission. -/
def select (pairs : List (ℕ × Row)) : List ℕ → Option (List (ℕ × Row))
  | [] => some []
  | index :: rest => do
      let pair ← representative pairs index
      let tail ← select pairs rest
      pure (pair :: tail)

/-- Exact ordered leaf responses, including repeated identical queries at different positions. -/
theorem hashRows_eval (model : LeafHashing Row Query Y) (answer : Query → Y)
    (pairs : List (ℕ × Row)) :
    evalWithAnswerFn (QueryImpl.ofFn answer) (hashRows model pairs) =
      pairs.map (fun pair ↦ (pair.1, answer (model.leaf pair.2))) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨index, row⟩ := pair
      simp only [hashRows, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_pure, ih, List.map_cons]

/-- Exact actual leaf-call history; in particular its length is the representative count. -/
theorem hashRows_log (model : LeafHashing Row Query Y) (answer : Query → Y)
    (pairs : List (ℕ × Row)) :
    tableQueryLog (hashRows model pairs) answer =
      pairs.map (fun pair ↦
        (⟨model.leaf pair.2, answer (model.leaf pair.2)⟩ : (_ : Query) × Y)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨index, row⟩ := pair
      simp only [hashRows, tableQueryLog_bind, tableQueryLog_query, tableQueryLog_pure,
        List.append_nil, List.singleton_append, ih, List.map_cons]

/-- Selection retains precisely the verifier's indices and chooses only original row pairs. -/
theorem select_sound {pairs : List (ℕ × Row)} :
    ∀ (indices : List ℕ) {selected : List (ℕ × Row)}, select pairs indices = some selected →
      selected.map Prod.fst = indices ∧ ∀ pair ∈ selected, pair ∈ pairs
  | [], selected, result => by
      simp only [select, Option.some.injEq] at result
      subst selected
      exact ⟨rfl, by simp⟩
  | index :: rest, selected, result => by
      simp only [select] at result
      cases found : representative pairs index with
      | none => simp [found] at result
      | some pair =>
          cases chosen : select pairs rest with
          | none => simp [found, chosen] at result
          | some tail =>
              simp [found, chosen] at result
              subst selected
              have member := List.mem_of_find?_eq_some found
              have same : pair.1 = index := by
                simpa only [beq_iff_eq] using (List.find?_some found)
              obtain ⟨indices, members⟩ := select_sound rest chosen
              refine ⟨by simp [same, indices], ?_⟩
              intro entry entryMem
              rcases List.mem_cons.mp entryMem with rfl | later
              · exact member
              · exact members entry later

/-- If a duplicate equals its first representative, selecting its index retains that exact row. -/
theorem select_covers [DecidableEq Row] {pairs : List (ℕ × Row)}
    (duplicates : ∀ pair ∈ pairs, representative pairs pair.1 = some pair) :
    ∀ (indices : List ℕ) {selected : List (ℕ × Row)}, select pairs indices = some selected →
      ∀ pair ∈ pairs, pair.1 ∈ indices → pair ∈ selected
  | [], selected, result, pair, member, indexMem => by simp at indexMem
  | index :: rest, selected, result, pair, member, indexMem => by
      simp only [select] at result
      cases found : representative pairs index with
      | none => simp [found] at result
      | some first =>
          cases chosen : select pairs rest with
          | none => simp [found, chosen] at result
          | some tail =>
              simp [found, chosen] at result
              subst selected
              rcases List.mem_cons.mp indexMem with same | later
              · have equal := duplicates pair member
                rw [same, found] at equal
                exact List.mem_cons.mpr (Or.inl (Option.some.inj equal).symm)
              · exact List.mem_cons_of_mem _
                  (select_covers duplicates rest chosen pair member later)

/-- Every original ordered occurrence is represented by an actual recorded leaf query. -/
theorem hashRows_recorded (model : LeafHashing Row Query Y) (answer : Query → Y)
    (log : HashLog Query Y) (selected : List (ℕ × Row)) (positions : List ℕ) (rows : List Row)
    (lengths : positions.length = rows.length)
    (covered : ∀ pair ∈ positions.zip rows, pair ∈ selected)
    (recorded : ∀ entry ∈ tableQueryLog (hashRows model selected) answer, entry ∈ log) :
    RowsRecorded model log (evalWithAnswerFn (QueryImpl.ofFn answer) (hashRows model selected))
      positions rows := by
  rw [hashRows_eval]
  apply List.forall₂_iff_zip.mpr
  refine ⟨lengths, ?_⟩
  intro index row member
  have selectedMem := covered (index, row) member
  refine ⟨answer (model.leaf row), List.mem_map.mpr ⟨(index, row), selectedMem, rfl⟩, ?_⟩
  apply recorded
  rw [hashRows_log]
  exact List.mem_map.mpr ⟨(index, row), selectedMem, rfl⟩

/-- Canonical digest decoding is an application boundary, including owned decode reservation.
Malformed bytes and reservation failure must not be identified. -/
inductive Decoding (Y : Type) where
  | invalid
  | exhausted
  | decoded (root : Y) (proof : List Y)
  deriving DecidableEq, Repr

/-- The native shape gate uses checked machine multiplication, an element ceiling, and height
at most `2^24`. `wordMax` fixes the selected native machine's `usize` range. -/
def ValidShape (wordMax elementLimit width height : ℕ) : Prop :=
  0 < width ∧ 0 < height ∧ height ≤ 2 ^ 24 ∧ width * height ≤ wordMax ∧
    width * height ≤ elementLimit
  deriving Decidable

/-- Independent intended operation at the decoded row boundary. `validRow` fixes application
width and codec meaning; it must not depend on attacker-chosen proof metadata. Admission order
matches the adapter: requests, row count, decoding, duplicates, proof count, widths, hashes.
Only decoding storage is modelled as exhaustion; upstream unchecked allocations are a separate
native realization/resource obligation. -/
def verify [DecidableEq Row] [DecidableEq Y] (model : LeafHashing Row Query Y)
    (validRow : ℕ → Row → Bool) (wordMax elementLimit width height : ℕ)
    (positions : List ℕ) (rows : List Row) (decoding : Decoding Y) :
    OracleComp (Query →ₒ Y) (PIR.Outcome Bool) :=
  if ¬ ValidShape wordMax elementLimit width height ∨ positions = [] ∨
      ¬ ∀ index ∈ positions, index < height then pure (.stopped .refused)
  else if positions.length ≠ rows.length ∨ wordMax < positions.length * width then
    pure (.returned false)
  else match decoding with
  | .invalid => pure (.returned false)
  | .exhausted => pure (.stopped .exhausted)
  | .decoded root proof =>
      let pairs := positions.zip rows
      if ¬ pairs.all (fun pair ↦ representative pairs pair.1 == some pair) then
        pure (.returned false)
      else if proof.length ≠ proofCount (Nat.clog 2 height) (unique positions) then
        pure (.returned false)
      else match select pairs (unique positions) with
      | none => pure (.returned false)
      | some selected =>
          if ¬ selected.all (fun pair ↦ validRow width pair.2) then pure (.returned false)
          else do
            let frontier ← hashRows model selected
            let accepted ← reduce model (Nat.clog 2 height) frontier proof root
            pure (.returned accepted)

/-- Request refusal is independent of all authentication data and makes no hash calls. -/
theorem verify_refused [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (decoding : Decoding Y)
    (invalid : ¬ ValidShape wordMax elementLimit width height ∨ positions = [] ∨
      ¬ ∀ index ∈ positions, index < height) :
    verify model validRow wordMax elementLimit width height positions rows decoding =
      pure (.stopped .refused) := by
  unfold verify
  rw [ite_eq_left invalid]

/-- After request and row framing admission, failure to reserve decode storage stops execution.
No hash query occurs and the failure is not represented by an authentication Boolean. -/
theorem verify_exhausted [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (shape : ValidShape wordMax elementLimit width height) (nonempty : positions ≠ [])
    (bounds : ∀ index ∈ positions, index < height) (lengths : positions.length = rows.length)
    (capacity : positions.length * width ≤ wordMax) :
    verify model validRow wordMax elementLimit width height positions rows .exhausted =
      pure (.stopped .exhausted) := by
  unfold verify
  rw [ite_eq_right (by tauto), ite_eq_right (by omega)]

/-- Successful authentication requires successful decoding, even though request and framing
failures can precede decoding. This retains the complete operation outcome distinction. -/
theorem verify_success_decodes [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (decoding : Decoding Y)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows decoding) =
        .returned true) : ∃ root proof, decoding = .decoded root proof := by
  cases decoding with
  | invalid =>
      unfold verify at accepted
      split at accepted
      · simp at accepted
      · split at accepted <;> simp at accepted
  | exhausted =>
      unfold verify at accepted
      split at accepted
      · simp at accepted
      · split at accepted <;> simp at accepted
  | decoded root proof => exact ⟨root, proof, rfl⟩

/-- All native admission facts and both batch premises follow from this operation's successful
call. The record is the operation's actual full history, with no fabricated leaf or path calls.
This theorem makes no source/native correspondence or cryptographic assumption. -/
theorem verify_success [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (root : Y) (proof : List Y)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true) :
    ValidShape wordMax elementLimit width height ∧ positions ≠ [] ∧
      (∀ index ∈ positions, index < height) ∧ positions.length = rows.length ∧
      positions.length * width ≤ wordMax ∧
      ∃ frontier,
        frontier.map Prod.fst = unique positions ∧
        Reduction model
          (tableQueryLog (verify model validRow wordMax elementLimit width height positions rows
            (.decoded root proof)) answer)
          (Nat.clog 2 height) frontier proof root ∧
        RowsRecorded model
          (tableQueryLog (verify model validRow wordMax elementLimit width height positions rows
            (.decoded root proof)) answer) frontier positions rows ∧
        (∀ pair ∈ positions.zip rows, validRow width pair.2 = true) ∧
        (tableQueryLog (verify model validRow wordMax elementLimit width height positions rows
          (.decoded root proof)) answer).length =
          (unique positions).length + compressionCount (Nat.clog 2 height) (unique positions) := by
  let operation := verify model validRow wordMax elementLimit width height positions rows
    (.decoded root proof)
  let log := tableQueryLog operation answer
  have history : log = tableQueryLog operation answer := rfl
  have recorded : ∀ entry ∈ tableQueryLog operation answer, entry ∈ log := fun _ member ↦ member
  change evalWithAnswerFn (QueryImpl.ofFn answer) operation = .returned true at accepted
  dsimp only [operation, verify] at accepted recorded history
  split at accepted
  next invalid => simp at accepted
  next admitted =>
    have admission : ValidShape wordMax elementLimit width height ∧ positions ≠ [] ∧
        ∀ index ∈ positions, index < height := by tauto
    refine ⟨admission.1, admission.2.1, admission.2.2, ?_⟩
    simp only [admitted, ↓reduceIte] at recorded history
    split at accepted
    next wrongLength => simp at accepted
    next lengths =>
      have lengthEq : positions.length = rows.length := by omega
      refine ⟨lengthEq, by omega, ?_⟩
      simp only [lengths, ↓reduceIte] at recorded history
      split at accepted
      next inconsistent => simp at accepted
      next duplicates =>
        simp only [duplicates, ↓reduceIte] at recorded history
        have duplicateEq : ∀ pair ∈ positions.zip rows,
            representative (positions.zip rows) pair.1 = some pair := by
          simpa only [Bool.not_eq_true, Bool.not_false, List.all_eq_true, beq_iff_eq] using
            (show ((positions.zip rows).all
              (fun pair ↦ representative (positions.zip rows) pair.1 == some pair)) = true by
              simpa using duplicates)
        split at accepted
        next wrongProof => simp at accepted
        next proofLength =>
          simp only [proofLength, ↓reduceIte] at recorded history
          cases chosen : select (positions.zip rows) (unique positions) with
          | none => simp [chosen] at accepted
          | some selected =>
              simp only [chosen] at recorded history accepted
              split at accepted
              next invalidRows => simp at accepted
              next validRows =>
                simp only [validRows, ↓reduceIte, tableQueryLog_bind, evalWithAnswerFn_bind,
                  tableQueryLog_pure, List.append_nil, evalWithAnswerFn_pure]
                  at recorded history accepted
                have leafCalls : ∀ entry ∈ tableQueryLog (hashRows model selected) answer,
                    entry ∈ log := fun entry member ↦ recorded entry
                      (List.mem_append_left _ member)
                have parentCalls : ∀ entry ∈ tableQueryLog (reduce model (Nat.clog 2 height)
                    (evalWithAnswerFn (QueryImpl.ofFn answer) (hashRows model selected)) proof root)
                    answer, entry ∈ log := fun entry member ↦ recorded entry
                      (List.mem_append_right _ member)
                have sorted : ((evalWithAnswerFn (QueryImpl.ofFn answer)
                    (hashRows model selected)).map Prod.fst).SortedLT := by
                  rw [hashRows_eval, List.map_map]
                  change (selected.map Prod.fst).SortedLT
                  rw [(select_sound (unique positions) chosen).1]
                  exact unique_sorted positions
                have covered : ∀ pair ∈ positions.zip rows, pair ∈ selected := by
                  intro pair member
                  exact select_covers duplicateEq (unique positions) chosen pair member
                    (unique_mem.mpr (List.of_mem_zip member).1)
                have widths : ∀ pair ∈ selected, validRow width pair.2 = true := by
                  simpa only [List.all_eq_true] using
                    (show (selected.all (fun pair ↦ validRow width pair.2)) = true by
                      simpa using validRows)
                refine ⟨evalWithAnswerFn (QueryImpl.ofFn answer) (hashRows model selected), ?_,
                  reduce_sound model answer log _ _ _ _ sorted parentCalls ?_,
                  hashRows_recorded model answer log selected positions rows lengthEq covered
                    leafCalls, (fun pair member ↦ widths pair (covered pair member)), ?_⟩
                · rw [hashRows_eval, List.map_map]
                  exact (select_sound (unique positions) chosen).1
                · exact PIR.Outcome.returned.inj accepted
                · have reduction := reduce_sound model answer log _ _ _ _ sorted parentCalls
                    (PIR.Outcome.returned.inj accepted)
                  have consistent : ∀ entry ∈ log, answer entry.1 = entry.2 := by
                    intro entry member
                    have same := tableQueryLog_consistent answer operation entry member
                    exact (congrArg Sigma.snd same).symm
                  have count := (reduce_complete model answer consistent reduction).2
                  change log.length = _
                  rw [history, List.length_append, hashRows_log, List.length_map, count]
                  rw [hashRows_eval, List.map_map]
                  have indices := (select_sound (unique positions) chosen).1
                  have length := congrArg List.length indices
                  simp only [List.length_map] at length
                  change selected.length + compressionCount (Nat.clog 2 height)
                    (selected.map Prod.fst) = _
                  rw [indices, length]

/-- Extraction/collision is inherited from the batch theorem, with precisely the successful
operation's history. This deterministic corollary adds no hash security assumption. -/
theorem verify_agrees_or_collision [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (root : Y) (proof : List Y)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verify model validRow wordMax elementLimit width height positions rows
        (.decoded root proof)) = .returned true) :
    let log := tableQueryLog (verify model validRow wordMax elementLimit width height positions rows
      (.decoded root proof)) answer
    positions.map (model.extract log (Nat.clog 2 height) root) = rows.map some ∨ Collision log := by
  obtain ⟨_, _, _, _, _, frontier, _, reduction, recorded, _⟩ :=
    verify_success model validRow answer wordMax elementLimit width height positions rows root proof
      accepted
  exact batch_agrees_or_collision reduction recorded

/-- Entry point for an application's fixed row framing. `none` means that the native flat
row-count gate failed; `some rows` carries exactly its width-sized chunks in original order.
The frame result is pure and introduces no allocation outcome of its own. In particular, do
not feed malformed raw rows directly to `verify` and then interpret its decode boundary.
The source/realization association must prove the selected codec's flat-count/chunking facts. -/
def verifyFramed [DecidableEq Row] [DecidableEq Y] (model : LeafHashing Row Query Y)
    (validRow : ℕ → Row → Bool) (wordMax elementLimit width height : ℕ)
    (positions : List ℕ) (framedRows : Option (List Row)) (decoding : Decoding Y) :
    OracleComp (Query →ₒ Y) (PIR.Outcome Bool) :=
  if ¬ ValidShape wordMax elementLimit width height ∨ positions = [] ∨
      ¬ ∀ index ∈ positions, index < height then pure (.stopped .refused)
  else match framedRows with
  | none => pure (.returned false)
  | some rows => verify model validRow wordMax elementLimit width height positions rows decoding

/-- Successful framing adds no calls and changes no operation outcome. -/
theorem verifyFramed_some [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ) (rows : List Row)
    (decoding : Decoding Y) :
    verifyFramed model validRow wordMax elementLimit width height positions (some rows) decoding =
      verify model validRow wordMax elementLimit width height positions rows decoding := by
  unfold verifyFramed
  split
  · rename_i invalid
    exact (verify_refused model validRow wordMax elementLimit width height positions rows decoding
      invalid).symm
  · rfl

/-- Success at the framing entry point yields both existing batch premises over the entry
point's actual history. Framing failure and decode failure are independently excluded. -/
theorem verifyFramed_success [DecidableEq Row] [DecidableEq Y]
    (model : LeafHashing Row Query Y) (validRow : ℕ → Row → Bool) (answer : Query → Y)
    (wordMax elementLimit width height : ℕ) (positions : List ℕ)
    (framedRows : Option (List Row)) (decoding : Decoding Y)
    (accepted : evalWithAnswerFn (QueryImpl.ofFn answer)
      (verifyFramed model validRow wordMax elementLimit width height positions framedRows
        decoding) =
        .returned true) :
    ∃ rows root proof frontier,
      framedRows = some rows ∧ decoding = .decoded root proof ∧
      frontier.map Prod.fst = unique positions ∧
      Reduction model (tableQueryLog
        (verifyFramed model validRow wordMax elementLimit width height positions framedRows
          decoding)
        answer) (Nat.clog 2 height) frontier proof root ∧
      RowsRecorded model (tableQueryLog
        (verifyFramed model validRow wordMax elementLimit width height positions framedRows
          decoding)
        answer) frontier positions rows := by
  cases framedRows with
  | none =>
      unfold verifyFramed at accepted
      split at accepted <;> simp at accepted
  | some rows =>
      rw [verifyFramed_some] at accepted ⊢
      obtain ⟨root, proof, rfl⟩ := verify_success_decodes model validRow answer wordMax elementLimit
        width height positions rows decoding accepted
      obtain ⟨_, _, _, _, _, frontier, indices, reduction, recorded, _⟩ :=
        verify_success model validRow answer wordMax elementLimit width height positions rows
          root proof accepted
      exact ⟨rows, root, proof, frontier, rfl, rfl, indices, reduction, recorded⟩

end ZkcSecurity.Commitment.BatchVerification

module

public import ZkcSecurity.HashChain.Provider
public import ZkcSecurity.VCVio.Deferral

@[expose] public section

/-! The simulated experiment is the translated experiment.

The simulated experiment of `ZkcSecurity.HashChain.Simulator` samples lazily: a
private answer when a call is first answered privately, a history cell when a
counter block first reads it. The translated experiment of `chainSimulator`
samples ahead: the private tape before the adversary runs, and the whole answer
at a history key when the history oracle is first asked there. The two have the
same law (`simulatedExperiment_eq_translated`).

The comparison fills a lazy state ahead (`fillAll`, `fillHistory`): the unread
tape entries are uniform, and the unread cells of each history key with some
read cell are a uniform row of a table indexed by the key's position among the
read keys (`completed`). Each step then commutes with the fill
(`ZkcSecurity.VCVio.Deferral.evalSPMF_simulateQ_fill`), because resampling one
cell of a uniform table with an independent uniform value keeps it uniform:

- a fresh private answer is the next unread tape entry (`private_commute`);
- a fresh cell of a key with read cells is the cell of that key's row
  (`completed_recordHistory_touched`);
- a fresh cell of a key without read cells reads a fresh answer of the history
  oracle (`completed_recordHistory_untouched`).
-/

set_option autoImplicit false
set_option linter.deprecated false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.VCVio.Deferral

section Uniform

/-- Resampling one cell of one row of a uniform table of rows keeps it uniform. -/
theorem evalSPMF_uniform_update_row {S α : Type} [SampleableType S] {slots width : ℕ}
    (slot : Fin slots) (block : Fin width)
    (continuation : (Fin slots → Fin width → S) → ProbComp α) :
    𝒮[($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation (Function.update rows slot (Function.update (rows slot) block value))] =
      𝒮[($ᵗ (Fin slots → Fin width → S)) >>= continuation] := by
  have expand : ∀ value : S,
      𝒮[($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
          continuation (Function.update rows slot (Function.update (rows slot) block value))] =
        𝒮[($ᵗ (Fin width → S)) >>= fun row => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
          continuation (Function.update rows slot (Function.update row block value))] := by
    intro value
    rw [← evalSPMF_uniform_update slot fun rows =>
      continuation (Function.update rows slot (Function.update (rows slot) block value))]
    simp only [Function.update_idem, Function.update_self]
  rw [evalSPMF_bind, funext fun value => expand value, ← evalSPMF_bind,
    evalSPMF_uniform_update block fun row => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
      continuation (Function.update rows slot row),
    evalSPMF_uniform_update slot continuation]

end Uniform

section Fill
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  {width : ℕ}

/-- The row of a slot, or the default row past the last slot. -/
def rowAt {slots : ℕ} (rows : Fin slots → Fin width → S) (slot : ℕ) : Fin width → S :=
  if below : slot < slots then rows ⟨slot, below⟩ else fun _ => default

/-- The history answers a lazy state determines, completed by rows: a key with
read cells answers its read cells and, elsewhere, the row of its position among
the read keys; a key without read cells has no answer. -/
def completed (tables : Simulated E S X width) {slots : ℕ} (rows : Fin slots → Fin width → S) :
    (OracleSpec.ofFn (Raw E S width)).QueryCache :=
  QueryCache.ofFn fun key =>
    if key ∈ tables.touched then
      some fun block => (tables.history (key, block)).getD
        (rowAt rows (tables.touched.idxOf key) block)
    else none

/-- Every key with a read cell is among the read keys. -/
def Organized (tables : Simulated E S X width) : Prop :=
  ∀ key block, tables.history (key, block) ≠ none → key ∈ tables.touched

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
theorem rowAt_update {slots : ℕ} (rows : Fin slots → Fin width → S) {slot : ℕ}
    (below : slot < slots) (row : Fin width → S) (other : ℕ) :
    rowAt (Function.update rows ⟨slot, below⟩ row) other =
      if other = slot then row else rowAt rows other := by
  unfold rowAt
  split_ifs with otherBelow same same
  · subst same
    simp
  · rw [Function.update_of_ne (fun equal => same (congrArg Fin.val equal))]
  · exact absurd (same ▸ below) otherBelow
  · rfl

omit [DecidableEq S] [DecidableEq X] in
/-- A fresh cell of a key with read cells is the cell of that key's row. -/
theorem completed_recordHistory_touched {tables : Simulated E S X width} {key : List E}
    (touched : key ∈ tables.touched) {block : Fin width}
    (fresh : tables.history (key, block) = none) {slots : ℕ}
    (below : tables.touched.idxOf key < slots) (rows : Fin slots → Fin width → S) (value : S) :
    completed (tables.recordHistory width key block value) rows =
      completed tables (Function.update rows ⟨_, below⟩
        (Function.update (rows ⟨_, below⟩) block value)) := by
  apply QueryCache.ext
  intro other
  simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, if_pos touched]
  split_ifs with member
  · congr 1
    funext other_block
    rw [rowAt_update]
    by_cases same : other = key
    · subst same
      rw [if_pos rfl]
      by_cases sameBlock : other_block = block
      · subst sameBlock
        simp [fresh]
      · rw [Function.update_of_ne (by simp [sameBlock]), Function.update_of_ne sameBlock]
        simp [rowAt, below]
    · have slots_differ : tables.touched.idxOf other ≠ tables.touched.idxOf key :=
        fun equal => same ((List.idxOf_inj member).mp equal)
      rw [if_neg slots_differ, Function.update_of_ne (by simp [same])]
  · rfl

omit [DecidableEq S] [DecidableEq X] in
/-- The first cell of a key without read cells makes it the next read key, at the
next slot. -/
theorem completed_recordHistory_untouched {tables : Simulated E S X width}
    (organized : Organized tables) {key : List E} (untouched : key ∉ tables.touched)
    {block : Fin width} {slots : ℕ} (below : tables.touched.length < slots)
    (rows : Fin slots → Fin width → S) (value : S) :
    completed (tables.recordHistory width key block value) rows =
      (completed tables rows).cacheQuery key
        (Function.update (rows ⟨_, below⟩) block value) := by
  have noCells : ∀ other_block, tables.history (key, other_block) = none := by
    intro other_block
    by_contra present
    exact untouched (organized key other_block present)
  apply QueryCache.ext
  intro other
  by_cases same : other = key
  · subst same
    simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, if_neg untouched,
      QueryCache.cacheQuery_self, List.mem_append, List.mem_singleton, or_true, if_true,
      List.idxOf_append_of_notMem untouched]
    congr 1
    funext other_block
    by_cases sameBlock : other_block = block
    · subst sameBlock
      simp
    · rw [Function.update_of_ne (by simp [sameBlock]), Function.update_of_ne sameBlock,
        noCells]
      simp [rowAt, below]
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, if_neg untouched,
      List.mem_append, List.mem_singleton, same, or_false]
    split_ifs with member
    · congr 1
      funext other_block
      rw [List.idxOf_append_of_mem member, Function.update_of_ne (by simp [same])]
    · rfl

omit [DecidableEq S] [DecidableEq X] in
/-- The slot after the read keys is no key's row. -/
theorem completed_update_unused (tables : Simulated E S X width) {slots : ℕ}
    (below : tables.touched.length < slots) (rows : Fin slots → Fin width → S)
    (row : Fin width → S) :
    completed tables (Function.update rows ⟨_, below⟩ row) = completed tables rows := by
  apply QueryCache.ext
  intro other
  simp only [completed, QueryCache.ofFn_apply]
  split_ifs with member
  · congr 1
    funext other_block
    rw [rowAt_update, if_neg (Nat.ne_of_lt (List.idxOf_lt_length_of_mem member))]
  · rfl

end Fill

section Laws
variable {E S X α : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width slots : ℕ}

omit [DecidableEq S] [DecidableEq X] in
/-- Reading a fresh cell of a key with read cells from the filled rows has the
law of sampling the cell and filling afterwards. -/
theorem touched_law {tables : Simulated E S X width} {key : List E}
    (touched : key ∈ tables.touched) {block : Fin width}
    (fresh : tables.history (key, block) = none) (below : tables.touched.idxOf key < slots)
    (continuation : S → (OracleSpec.ofFn (Raw E S width)).QueryCache → ProbComp α) :
    𝒮[($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation (rowAt rows (tables.touched.idxOf key) block) (completed tables rows)] =
      𝒮[($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)] := by
  rw [← evalSPMF_uniform_update_row ⟨_, below⟩ block fun rows =>
    continuation (rowAt rows (tables.touched.idxOf key) block) (completed tables rows)]
  congr 2
  funext value
  congr 1
  funext rows
  rw [completed_recordHistory_touched touched fresh below, rowAt_update, if_pos rfl,
    Function.update_self]

omit [DecidableEq S] [DecidableEq X] in
/-- Reading a fresh answer of the history oracle at a key without read cells has
the law of sampling the key's first cell and filling afterwards. -/
theorem untouched_law {tables : Simulated E S X width} (organized : Organized tables)
    {key : List E} (untouched : key ∉ tables.touched) {block : Fin width}
    (below : tables.touched.length < slots)
    (continuation : S → (OracleSpec.ofFn (Raw E S width)).QueryCache → ProbComp α) :
    𝒮[($ᵗ (Fin slots → Fin width → S)) >>= fun rows => ($ᵗ (Fin width → S)) >>= fun answer =>
        continuation (answer block) ((completed tables rows).cacheQuery key answer)] =
      𝒮[($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)] := by
  let slot : Fin slots := ⟨_, below⟩
  let reading : (Fin slots → Fin width → S) → ProbComp α := fun rows =>
    continuation (rows slot block) ((completed tables rows).cacheQuery key (rows slot))
  have right : 𝒮[($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)] =
      𝒮[($ᵗ (Fin slots → Fin width → S)) >>= reading] := by
    rw [← evalSPMF_uniform_update_row slot block reading]
    congr 2
    funext value
    congr 1
    funext rows
    simp only [reading, Function.update_self,
      completed_recordHistory_untouched organized untouched below]
    rw [completed_update_unused tables below]
  rw [right, evalSPMF_uniform_swap, ← evalSPMF_uniform_update slot reading]
  congr 2
  funext answer
  congr 1
  funext rows
  simp only [reading, Function.update_self]
  rw [completed_update_unused tables below]

end Laws

end ZkcSecurity.HashChain

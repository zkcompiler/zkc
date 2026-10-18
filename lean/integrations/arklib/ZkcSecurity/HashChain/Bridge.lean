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

section Programs
variable {S : Type} {n : Type → Type} [Monad n] [LawfulMonad n]

/-- The counter blocks of one answer as oracle calls. -/
abbrev BlockSpec (S : Type) (width : ℕ) : OracleSpec (Fin width) := OracleSpec.ofFn fun _ => S

/-- Read the counter blocks `blockOf 0, …, blockOf (count - 1)`. -/
def readBlocks {width : ℕ} (count : ℕ) (blockOf : Fin count → Fin width) :
    OracleComp (BlockSpec S width) (Fin count → S) :=
  collect count fun index => liftM ((BlockSpec S width).query (blockOf index))

theorem simulateQ_readBlocks {width : ℕ} (impl : QueryImpl (BlockSpec S width) n) :
    ∀ (count : ℕ) (blockOf : Fin count → Fin width),
      simulateQ impl (readBlocks count blockOf) = collect count fun index => impl (blockOf index)
  | 0, _ => by simp [readBlocks, collect]
  | count + 1, blockOf => by
      have tail := simulateQ_readBlocks impl count fun index => blockOf index.succ
      simp only [readBlocks] at tail
      simp only [readBlocks, collect, simulateQ_bind, simulateQ_pure, simulateQ_spec_query, tail]

theorem readBlocks_queryBound {width : ℕ} :
    ∀ (count : ℕ) (blockOf : Fin count → Fin width),
      IsTotalQueryBound (readBlocks (S := S) count blockOf) count
  | 0, _ => trivial
  | count + 1, blockOf => by
      simp only [readBlocks, collect]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun head => ?_⟩
      have tail := isTotalQueryBound_bind (ob := fun tail : Fin count → S =>
        (pure (Fin.cons head tail) : OracleComp (BlockSpec S width) (Fin (count + 1) → S)))
        (n₂ := 0) (readBlocks_queryBound count fun index => blockOf index.succ) fun _ => trivial
      simpa [readBlocks] using tail

variable {I : PIR.Signature} {E P A : Type} {R : List E → Type}

/-- The typed transform with the history oracle, simulated, is the transform with
the simulated oracle. -/
theorem simulateQ_transform (absorb : Typed.Interface I E P R)
    (impl : QueryImpl (OracleSpec.ofFn R) n) :
    ∀ (process : PIR.Proc I A) (history : List E) (proof : List P),
      simulateQ impl (Typed.transform absorb Typed.answer process history proof) =
        Typed.transform absorb (fun key => impl key) process history proof := by
  intro process
  induction process with
  | done value => intro history proof; simp [Typed.transform]
  | halt stop => intro history proof; simp [Typed.transform]
  | call operation next ih =>
      intro history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil =>
            rw [Typed.transform_receive_nil absorb _ absorbed,
              Typed.transform_receive_nil absorb _ absorbed]
            simp
        | cons message rest =>
            rw [Typed.transform_receive absorb _ absorbed, Typed.transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => simp
            | some value => exact ih value _ _
      · rw [Typed.transform_send absorb _ absorbed, Typed.transform_send absorb _ absorbed]
        exact ih value _ _
      · rw [Typed.transform_query absorb _ absorbed, Typed.transform_query absorb _ absorbed,
          simulateQ_bind, Typed.answer, simulateQ_spec_query]
        refine bind_congr fun raw => ?_
        cases decode history raw with
        | none => simp
        | some value => exact ih value _ _
      · rw [Typed.transform_refuse absorb _ absorbed, Typed.transform_refuse absorb _ absorbed]
        simp

end Programs

section HistoryOracle
variable {E S : Type} [DecidableEq E] [SampleableType S] {width : ℕ}

/-- One counter block of the history oracle's answer at a key. -/
def oracleBlock (key : List E) (block : Fin width) :
    StateT (OracleSpec.ofFn (Raw E S width)).QueryCache ProbComp S :=
  (fun answer => answer block) <$> randomOracle (spec := OracleSpec.ofFn (Raw E S width)) key

theorem collect_oracleBlock_cached {key : List E} {cache : (OracleSpec.ofFn (Raw E S width)).QueryCache}
    {answer : Fin width → S} (cached : cache key = some answer) :
    ∀ (count : ℕ) (blockOf : Fin count → Fin width),
      (collect count fun index => oracleBlock key (blockOf index)).run cache =
        pure (fun index => answer (blockOf index), cache)
  | 0, _ => by
      simp only [collect, StateT.run_pure]
      congr 2
      funext index
      exact index.elim0
  | count + 1, blockOf => by
      have tail := collect_oracleBlock_cached cached count fun index => blockOf index.succ
      simp only [oracleBlock] at tail
      simp only [collect, StateT.run_bind, oracleBlock, StateT.run_map, randomOracle.run_eq,
        cached, map_pure, pure_bind, StateT.run_pure, tail]
      congr 2
      funext index
      cases index using Fin.cases <;> rfl

/-- Reading every counter block of a key reads the history oracle's answer there. -/
theorem collect_oracleBlock (positive : 0 < width) (key : List E)
    (cache : (OracleSpec.ofFn (Raw E S width)).QueryCache) :
    (collect width fun block => oracleBlock key block).run cache =
      (randomOracle (spec := OracleSpec.ofFn (Raw E S width)) key).run cache := by
  rw [randomOracle.run_eq]
  cases cached : cache key with
  | some answer =>
      rw [collect_oracleBlock_cached cached width fun block => block]
  | none =>
      obtain ⟨count, rfl⟩ : ∃ count, width = count + 1 := ⟨width - 1, by omega⟩
      simp only [collect, StateT.run_bind, oracleBlock, StateT.run_map, randomOracle.run_eq,
        cached, map_bind, map_pure, bind_assoc, pure_bind]
      refine bind_congr fun answer => ?_
      have tail := collect_oracleBlock_cached (key := key) (answer := answer)
        (cache := cache.cacheQuery key answer) (by simp) count fun index => index.succ
      simp only [oracleBlock] at tail
      simp only [tail, pure_bind, StateT.run_pure]
      congr 2
      exact Fin.cons_self_tail answer

end HistoryOracle

section VerifierPhase
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width : ℕ}

/-- The history answers of a lazy state, filled with uniform rows. -/
def fillHistory (slots : ℕ) (tables : Simulated E S X width) :
    ProbComp (OracleSpec.ofFn (Raw E S width)).QueryCache :=
  ($ᵗ (Fin slots → Fin width → S)) >>= fun rows => pure (completed tables rows)

omit [DecidableEq S] [DecidableEq X] [SampleableType S] in
theorem completed_apply_touched {tables : Simulated E S X width} {key : List E}
    (touched : key ∈ tables.touched) {slots : ℕ} (rows : Fin slots → Fin width → S) :
    completed tables rows key = some fun block =>
      (tables.history (key, block)).getD (rowAt rows (tables.touched.idxOf key) block) := by
  simp [completed, touched]

omit [DecidableEq S] [DecidableEq X] [SampleableType S] in
theorem completed_apply_untouched {tables : Simulated E S X width} {key : List E}
    (untouched : key ∉ tables.touched) {slots : ℕ} (rows : Fin slots → Fin width → S) :
    completed tables rows key = none := by
  simp [completed, untouched]

omit [DecidableEq S] [DecidableEq X] in
/-- One counter block: filling then reading the history oracle has the law of
reading the lazy cell then filling. -/
theorem block_commute {slots : ℕ} (key : List E) (block : Fin width)
    (tables : Simulated E S X width) (organized : Organized tables)
    (room : key ∉ tables.touched → tables.touched.length < slots)
    (slotRoom : key ∈ tables.touched → tables.touched.idxOf key < slots) :
    𝒮[fillHistory slots tables >>= fun cache => (oracleBlock key block).run cache] =
      𝒮[(historyBlock width key block).run tables >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillHistory slots step.2] := by
  simp only [fillHistory, oracleBlock, StateT.run_map, randomOracle.run_eq, bind_assoc, pure_bind]
  cases cell : tables.history (key, block) with
  | some value =>
      have touched := organized key block (by simp [cell])
      rw [historyBlock_run_some cell]
      simp only [completed_apply_touched touched, cell, Option.getD_some, map_pure, pure_bind,
        map_bind]
  | none =>
      rw [historyBlock_run_none cell]
      by_cases touched : key ∈ tables.touched
      · simp only [completed_apply_touched touched, cell, Option.getD_none, map_pure, bind_assoc,
          pure_bind, map_bind]
        exact touched_law touched cell (slotRoom touched) fun value cache => pure (value, cache)
      · simp only [completed_apply_untouched touched, map_bind, map_pure, bind_assoc, pure_bind]
        exact untouched_law organized touched (room touched) fun value cache => pure (value, cache)

omit [DecidableEq S] [DecidableEq X] [Inhabited S] [SampleableType S] in
theorem Organized.recordHistory {tables : Simulated E S X width} (organized : Organized tables)
    (key : List E) (block : Fin width) (value : S) :
    Organized (tables.recordHistory width key block value) := by
  intro other otherBlock present
  simp only [Simulated.recordHistory] at present ⊢
  by_cases same : (other, otherBlock) = (key, block)
  · obtain ⟨rfl, -⟩ := Prod.mk.inj same
    split_ifs with member
    · exact member
    · simp
  · rw [Function.update_of_ne same] at present
    have old := organized other otherBlock present
    split_ifs
    · exact old
    · simp [old]

omit [DecidableEq S] [DecidableEq X] [Inhabited S] in
theorem historyBlock_support (key : List E) (block : Fin width) (tables : Simulated E S X width) :
    ∀ step ∈ support ((historyBlock width key block).run tables),
      step.2 = tables ∨ step.2 = tables.recordHistory width key block step.1 := by
  intro step member
  cases cell : tables.history (key, block) with
  | some value =>
      rw [historyBlock_run_some cell] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      exact Or.inl (by rw [member])
  | none =>
      rw [historyBlock_run_none cell] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨value, -, rfl⟩ := member
      exact Or.inr rfl

omit [DecidableEq S] [DecidableEq X] [Inhabited S] [SampleableType S] in
theorem touched_recordHistory (tables : Simulated E S X width) (key : List E) (block : Fin width)
    (value : S) :
    (tables.recordHistory width key block value).touched =
      if key ∈ tables.touched then tables.touched else tables.touched ++ [key] := rfl

omit [DecidableEq S] [DecidableEq X] in
/-- Reading every counter block of a key: filling then asking the history oracle
has the law of reading the lazy cells then filling. -/
theorem answer_commute (positive : 0 < width) {slots : ℕ} (key : List E)
    (tables : Simulated E S X width) (organized : Organized tables)
    (room : tables.touched.length < slots) :
    𝒮[fillHistory slots tables >>= fun cache =>
        (randomOracle (spec := OracleSpec.ofFn (Raw E S width)) key).run cache] =
      𝒮[(historyAnswer width key).run tables >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillHistory slots step.2] := by
  let Inv : ℕ → Simulated E S X width → Prop := fun _ current =>
    Organized current ∧ (key ∉ current.touched → current.touched.length < slots) ∧
      (key ∈ current.touched → current.touched.idxOf key < slots)
  have filled := evalSPMF_simulateQ_fill (spec := BlockSpec S width)
    (fun block => historyBlock width key block) (fun block => oracleBlock key block)
    (fillHistory slots) Inv
    (fun _ block current inv => block_commute key block current inv.1 inv.2.1 inv.2.2)
    (fun _ block current inv step member => by
      obtain ⟨organized', room', slotRoom'⟩ := inv
      rcases historyBlock_support key block current step member with same | recorded
      · rw [same]; exact ⟨organized', room', slotRoom'⟩
      · rw [recorded]
        refine ⟨organized'.recordHistory key block step.1, fun absent => ?_, fun _ => ?_⟩
        · rw [touched_recordHistory] at absent
          split_ifs at absent with member <;> simp_all
        · rw [touched_recordHistory]
          split_ifs with member
          · exact slotRoom' member
          · rw [List.idxOf_append_of_notMem member]
            simpa using room' member)
    (readBlocks width fun block => block) width tables (readBlocks_queryBound width _)
    ⟨organized, fun _ => room,
      fun member => (List.idxOf_lt_length_of_mem member).trans room⟩
  rw [simulateQ_readBlocks, simulateQ_readBlocks] at filled
  simp only [← collect_oracleBlock positive key]
  exact filled

omit [DecidableEq S] [DecidableEq X] [Inhabited S] in
/-- Reading the counter blocks of a key keeps the read keys organized and adds at
most that key. -/
theorem collect_historyBlock_support (key : List E) :
    ∀ (count : ℕ) (blockOf : Fin count → Fin width) (tables : Simulated E S X width),
      Organized tables →
      ∀ step ∈ support ((collect count fun index => historyBlock width key (blockOf index)).run
          tables),
        Organized step.2 ∧ (step.2.touched = tables.touched ∨
          (key ∉ tables.touched ∧ step.2.touched = tables.touched ++ [key]))
  | 0, _, tables, organized => by
      intro step member
      simp only [collect, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨organized, Or.inl rfl⟩
  | count + 1, blockOf, tables, organized => by
      intro step member
      simp only [collect, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at member
      obtain ⟨first, firstMember, rest, restMember, rfl⟩ := member
      have firstFacts : Organized first.2 ∧ (first.2.touched = tables.touched ∨
          (key ∉ tables.touched ∧ first.2.touched = tables.touched ++ [key])) := by
        rcases historyBlock_support key (blockOf 0) tables first firstMember with same | recorded
        · rw [same]; exact ⟨organized, Or.inl rfl⟩
        · rw [recorded, touched_recordHistory]
          refine ⟨organized.recordHistory key (blockOf 0) first.1, ?_⟩
          split_ifs with member
          · exact Or.inl rfl
          · exact Or.inr ⟨member, rfl⟩
      obtain ⟨restOrganized, restTouched⟩ := collect_historyBlock_support key count
        (fun index => blockOf index.succ) first.2 firstFacts.1 rest restMember
      refine ⟨restOrganized, ?_⟩
      rcases firstFacts.2 with firstSame | ⟨absent, firstAppended⟩ <;>
        rcases restTouched with restSame | ⟨restAbsent, restAppended⟩
      · exact Or.inl (restSame.trans firstSame)
      · exact Or.inr ⟨firstSame ▸ restAbsent, by rw [restAppended, firstSame]⟩
      · exact Or.inr ⟨absent, by rw [restSame, firstAppended]⟩
      · exact absurd (by rw [firstAppended]; simp) restAbsent

omit [DecidableEq S] [DecidableEq X] in
/-- Filling, then dropping the fill, is the identity in law. -/
theorem fillHistory_drop {slots : ℕ} (tables : Simulated E S X width) {α : Type}
    (computation : ProbComp α) :
    𝒮[fillHistory slots tables >>= fun _ => computation] = 𝒮[computation] := by
  simp only [fillHistory, bind_assoc, pure_bind]
  exact evalSPMF_uniform_drop computation

variable {I : PIR.Signature} {P A : Type}

omit [DecidableEq S] [DecidableEq X] in
/-- The typed transform over the history oracle, from the filled history answers,
has the law of the typed transform over the lazy history cells. -/
theorem verifier_eq (positive : 0 < width) (absorb : Typed.Interface I E P (Raw E S width))
    (process : PIR.Proc I A) (history : List E) (proof : List P) {queries : ℕ}
    (bounded : Typed.QueryBound absorb process queries) {slots : ℕ}
    (tables : Simulated E S X width) (organized : Organized tables)
    (room : tables.touched.length + queries ≤ slots) :
    𝒮[fillHistory slots tables >>= fun cache =>
        (simulateQ randomOracle (Typed.transform absorb Typed.answer process history proof)).run'
          cache] =
      𝒮[(Typed.transform absorb (historyAnswer width) process history proof).run' tables] := by
  let Inv : ℕ → Simulated E S X width → Prop := fun remaining current =>
    Organized current ∧ current.touched.length + remaining ≤ slots
  have filled := evalSPMF_simulateQ_fill (spec := OracleSpec.ofFn (Raw E S width))
    (fun key => historyAnswer width key) randomOracle (fillHistory slots) Inv
    (fun _ key current inv => answer_commute positive key current inv.1 (by omega))
    (fun remaining key current inv step member => by
      obtain ⟨organized', room'⟩ := inv
      obtain ⟨stepOrganized, stepTouched⟩ := collect_historyBlock_support key width
        (fun block => block) current organized' step member
      refine ⟨stepOrganized, ?_⟩
      rcases stepTouched with same | ⟨-, appended⟩
      · rw [same]; omega
      · rw [appended, List.length_append, List.length_singleton]; omega)
    (Typed.transform absorb Typed.answer process history proof) queries tables
    (Typed.transform_queryBound absorb process queries history proof bounded) ⟨organized, room⟩
  rw [simulateQ_transform absorb (fun key => historyAnswer width key)] at filled
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]
  rw [← bind_assoc, evalSPMF_bind, filled, ← evalSPMF_bind, bind_assoc]
  refine evalSPMF_bind_congr fun step _ => ?_
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact fillHistory_drop step.2 _

end VerifierPhase


end ZkcSecurity.HashChain

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

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.VCVio.Deferral

section Uniform

/-- Resampling one cell of one row of a uniform table of rows keeps it uniform. -/
theorem evalSPMF_uniform_update_row {S α : Type} [SampleableType S] {slots width : ℕ}
    (slot : Fin slots) (block : Fin width)
    (continuation : (Fin slots → Fin width → S) → ProbComp α) :
    (($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation (Function.update rows slot (Function.update (rows slot) block value))) =ᵈ (($ᵗ (Fin slots → Fin width → S)) >>= continuation) := by
  have expand : ∀ value : S,
      (($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
          continuation (Function.update rows slot (Function.update (rows slot) block value))) =ᵈ (($ᵗ (Fin width → S)) >>= fun row => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
          continuation (Function.update rows slot (Function.update row block value))) := by
    intro value
    simpa only [Function.update_idem, Function.update_self] using
      (evalSPMF_uniform_update slot fun rows =>
        continuation (Function.update rows slot (Function.update (rows slot) block value))).symm
  exact (EvalDistEq.bind_right ($ᵗ S) expand).trans
    ((evalSPMF_uniform_update block fun row => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
      continuation (Function.update rows slot row)).trans
        (evalSPMF_uniform_update slot continuation))

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
    (OracleSpec.ofFn (Answer E S width)).QueryCache :=
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
  simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, ite_eq_left touched]
  split_ifs with member
  · congr 1
    funext other_block
    rw [rowAt_update]
    by_cases same : other = key
    · subst same
      rw [ite_eq_left rfl]
      by_cases sameBlock : other_block = block
      · subst sameBlock
        simp [fresh]
      · rw [Function.update_of_ne (by simp [sameBlock]), Function.update_of_ne sameBlock]
        simp [rowAt, below]
    · have slots_differ : tables.touched.idxOf other ≠ tables.touched.idxOf key :=
        fun equal => same ((List.idxOf_inj member).mp equal)
      rw [ite_eq_right slots_differ, Function.update_of_ne (by simp [same])]
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
    simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, ite_eq_right untouched,
      QueryCache.cacheQuery_self, List.mem_append, List.mem_singleton, or_true, ite_true,
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
    simp only [completed, QueryCache.ofFn_apply, Simulated.recordHistory, ite_eq_right untouched,
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
    rw [rowAt_update, ite_eq_right (Nat.ne_of_lt (List.idxOf_lt_length_of_mem member))]
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
    (continuation : S → (OracleSpec.ofFn (Answer E S width)).QueryCache → ProbComp α) :
    (($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation (rowAt rows (tables.touched.idxOf key) block) (completed tables rows)) =ᵈ (($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)) := by
  refine (evalSPMF_uniform_update_row ⟨_, below⟩ block fun rows =>
    continuation (rowAt rows (tables.touched.idxOf key) block) (completed tables rows)).symm.trans ?_
  refine EvalDistEq.bind_right _ fun value => EvalDistEq.bind_right _ fun rows => ?_
  rw [completed_recordHistory_touched touched fresh below, rowAt_update, ite_eq_left rfl,
    Function.update_self]

omit [DecidableEq S] [DecidableEq X] in
/-- Reading a fresh answer of the history oracle at a key without read cells has
the law of sampling the key's first cell and filling afterwards. -/
theorem untouched_law {tables : Simulated E S X width} (organized : Organized tables)
    {key : List E} (untouched : key ∉ tables.touched) {block : Fin width}
    (below : tables.touched.length < slots)
    (continuation : S → (OracleSpec.ofFn (Answer E S width)).QueryCache → ProbComp α) :
    (($ᵗ (Fin slots → Fin width → S)) >>= fun rows => ($ᵗ (Fin width → S)) >>= fun answer =>
        continuation (answer block) ((completed tables rows).cacheQuery key answer)) =ᵈ (($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)) := by
  let slot : Fin slots := ⟨_, below⟩
  let reading : (Fin slots → Fin width → S) → ProbComp α := fun rows =>
    continuation (rows slot block) ((completed tables rows).cacheQuery key (rows slot))
  have right : (($ᵗ S) >>= fun value => ($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
        continuation value (completed (tables.recordHistory width key block value) rows)) =ᵈ (($ᵗ (Fin slots → Fin width → S)) >>= reading) := by
    refine EvalDistEq.trans ?_ (evalSPMF_uniform_update_row slot block reading)
    refine EvalDistEq.bind_right _ fun value => EvalDistEq.bind_right _ fun rows => ?_
    simp only [reading, Function.update_self,
      completed_recordHistory_untouched organized untouched below]
    rw [completed_update_unused tables below]
  refine (evalSPMF_uniform_swap _).trans
    (EvalDistEq.trans ?_ ((evalSPMF_uniform_update slot reading).trans right.symm))
  refine EvalDistEq.bind_right _ fun answer => EvalDistEq.bind_right _ fun rows => ?_
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

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} {R : List E → Type}
  [Typed.ReadsByOccurrence R Raw]

/-- The typed transform with the history oracle, simulated, is the transform with
the simulated oracle, read by occurrence. -/
theorem simulateQ_transform (absorb : Typed.Interface I E P Raw)
    (impl : QueryImpl (OracleSpec.ofFn R) n) :
    ∀ (process : PIR.Process I A) (history : List E) (proof : List P),
      simulateQ impl (Typed.transform absorb Typed.ask process history proof) =
        Typed.transform absorb (fun preceding event =>
          Typed.ReadsByOccurrence.read preceding event <$> impl (preceding ++ [event]))
          process history proof := by
  intro process
  induction process with
  | done value => intro history proof; simp
  | halt stop => intro history proof; simp
  | call operation next ih =>
      intro history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil =>
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed,
              Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            simp
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed,
              Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => simp
            | some value => exact ih value _ _
      · rw [Zkc.Transcript.transform_send absorb _ absorbed,
          Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value _ _
      · rw [Zkc.Transcript.transform_query absorb _ absorbed,
          Zkc.Transcript.transform_query absorb _ absorbed, Typed.ask_bind, bind_map_left,
          simulateQ_bind, Typed.answer, simulateQ_spec_query]
        refine bind_congr fun raw => ?_
        cases decode (Typed.ReadsByOccurrence.read history event raw) with
        | none => simp
        | some value => exact ih value _ _
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed,
          Zkc.Transcript.transform_refuse absorb _ absorbed]
        simp

end Programs

section HistoryOracle
variable {E S : Type} [DecidableEq E] [SampleableType S] {width : ℕ}

/-- One counter block of the history oracle's answer at a key. -/
def oracleBlock (key : List E) (block : Fin width) :
    StateT (OracleSpec.ofFn (Answer E S width)).QueryCache ProbComp S :=
  (fun answer => answer block) <$> randomOracle (spec := OracleSpec.ofFn (Answer E S width)) key

theorem collect_oracleBlock_cached {key : List E} {cache : (OracleSpec.ofFn (Answer E S width)).QueryCache}
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
    (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) :
    (collect width fun block => oracleBlock key block).run cache =
      (randomOracle (spec := OracleSpec.ofFn (Answer E S width)) key).run cache := by
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
    ProbComp (OracleSpec.ofFn (Answer E S width)).QueryCache :=
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
    (fillHistory slots tables >>= fun cache => (oracleBlock key block).run cache) =ᵈ ((historyBlock width key block).run tables >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillHistory slots step.2) := by
  simp only [fillHistory, oracleBlock, StateT.run_map, randomOracle.run_eq, bind_assoc, pure_bind]
  cases cell : tables.history (key, block) with
  | some value =>
      have touched := organized key block (by simp [cell])
      rw [historyBlock_run_some cell]
      simp only [completed_apply_touched touched, cell, Option.getD_some, map_pure, pure_bind,
        map_bind]
      rfl
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
    (fillHistory slots tables >>= fun cache =>
        (randomOracle (spec := OracleSpec.ofFn (Answer E S width)) key).run cache) =ᵈ ((historyAnswer width key).run tables >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillHistory slots step.2) := by
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
    (fillHistory slots tables >>= fun _ => computation) =ᵈ computation := by
  simp only [fillHistory, bind_assoc, pure_bind]
  exact evalSPMF_uniform_drop computation

variable {I : PIR.Signature} {P A : Type}

omit [DecidableEq S] [DecidableEq X] in
/-- The typed transform over the history oracle, from the filled history answers,
has the law of the typed transform over the lazy history cells. -/
theorem verifier_eq (positive : 0 < width) (absorb : Typed.Interface I E P (Raw E S width))
    (process : PIR.Process I A) (history : List E) (proof : List P) {queries : ℕ}
    (bounded : Typed.QueryBound absorb process queries) {slots : ℕ}
    (tables : Simulated E S X width) (organized : Organized tables)
    (room : tables.touched.length + queries ≤ slots) :
    (fillHistory slots tables >>= fun cache =>
        (simulateQ randomOracle (Typed.transform absorb Typed.ask process history proof)).run'
          cache) =ᵈ ((Typed.transform absorb (historyAsk width) process history proof).run' tables) := by
  let Inv : ℕ → Simulated E S X width → Prop := fun remaining current =>
    Organized current ∧ current.touched.length + remaining ≤ slots
  have filled := evalSPMF_simulateQ_fill (spec := OracleSpec.ofFn (Answer E S width))
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
    (Typed.transform absorb Typed.ask process history proof) queries tables
    (Typed.transform_queryBound absorb process queries history proof bounded) ⟨organized, room⟩
  rw [simulateQ_transform (R := Answer E S width) absorb
    (fun key => historyAnswer (X := X) width key)] at filled
  have asked : (fun (preceding : List E) (event : E) =>
      Typed.ReadsByOccurrence.read (R := Answer E S width) (Raw := Raw E S width) preceding event <$>
        historyAnswer (X := X) width (preceding ++ [event])) = historyAsk width := by
    funext preceding event
    exact id_map _
  rw [asked] at filled
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]
  rw [← bind_assoc]
  refine (filled.bind_left (fun step => pure step.1)).trans ?_
  rw [bind_assoc]
  refine EvalDistEq.bind_right _ fun step => ?_
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact fillHistory_drop step.2 _

end VerifierPhase

section AdversaryPhase
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width length : ℕ}

/-- The hash-chain simulator's state a lazy state determines, with the unread tape
entries and the history answers given. -/
def completedWith (tables : Simulated E S X width) (suffix : Fin length → S)
    (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) : ChainState E S X width length where
  tape index := if below : index.val < tables.consumed.length then tables.consumed[index.val]
    else suffix index
  position := tables.consumed.length
  answers := tables.aux
  reached := tables.reached
  recorded key := cache key

/-- The lazy state filled ahead: uniform rows for the history answers and a
uniform tape after the consumed entries. -/
def fillAll (slots : ℕ) (tables : Simulated E S X width) :
    ProbComp (ChainState E S X width length × (OracleSpec.ofFn (Answer E S width)).QueryCache) :=
  ($ᵗ (Fin slots → Fin width → S)) >>= fun rows => ($ᵗ (Fin length → S)) >>= fun suffix =>
    pure (completedWith tables suffix (completed tables rows), completed tables rows)

/-- The hash-chain simulator against the lazy history oracle, as one simulation. -/
def flatSimulator (width length : ℕ) :
    QueryImpl (Primitive E S X)
      (StateT (ChainState E S X width length × (OracleSpec.ofFn (Answer E S width)).QueryCache)
        ProbComp) :=
  flatten (chainSimulator width length).handle randomOracle

end AdversaryPhase

section FlatSteps
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width length : ℕ}

theorem flat_run_private {state : ChainState E S X width length}
    {cache : (OracleSpec.ofFn (Answer E S width)).QueryCache} {input : Input E S X}
    (outside : chainAttempt width state.reached input = none) :
    (flatSimulator width length input).run (state, cache) =
      pure ((state.respond input).1, ((state.respond input).2, cache)) := by
  simp only [flatSimulator, flatten, StateT.run_mk]
  rw [(chainSimulator width length).handle_private (state := state) (query := input) outside]
  simp

theorem flat_run_recorded {state : ChainState E S X width length}
    {cache : (OracleSpec.ofFn (Answer E S width)).QueryCache} {input : Input E S X} {key : List E}
    (belongs : chainAttempt width state.reached input = some key) {answer : Fin width → S}
    (recorded : state.recorded key = some answer) :
    (flatSimulator width length input).run (state, cache) =
      pure (chainShared width input answer, (state, cache)) := by
  simp only [flatSimulator, flatten, StateT.run_mk]
  rw [(chainSimulator width length).handle_recorded (state := state) (query := input)
    (key := key) (ideal := answer) belongs recorded]
  simp

theorem flat_run_fresh {state : ChainState E S X width length}
    {cache : (OracleSpec.ofFn (Answer E S width)).QueryCache} {input : Input E S X} {key : List E}
    (belongs : chainAttempt width state.reached input = some key)
    (recorded : state.recorded key = none) :
    (flatSimulator width length input).run (state, cache) =
      (randomOracle (spec := OracleSpec.ofFn (Answer E S width)) key).run cache >>= fun step =>
        pure (chainShared width input step.1,
          ({ state with recorded := Function.update state.recorded key (some step.1) }, step.2)) := by
  simp only [flatSimulator, flatten, StateT.run_mk]
  rw [(chainSimulator width length).handle_fresh (state := state) (query := input) (key := key)
    belongs recorded]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  rfl

end FlatSteps

section AdversaryCommute
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width length : ℕ}

/-- The simulator's state after its next private answer, read from the tape. -/
def afterPrivate (tables : Simulated E S X width) (input : Input E S X) (suffix : Fin length → S)
    (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) (answer : S) :
    ChainState E S X width length :=
  { completedWith tables suffix cache with
    position := tables.consumed.length + 1
    answers := Function.update tables.aux input (some answer)
    reached := noteReached tables.reached input answer }

omit [SampleableType S] in
theorem respond_completedWith_fresh {tables : Simulated E S X width} {input : Input E S X}
    (fresh : tables.aux input = none) (room : tables.consumed.length < length)
    (suffix : Fin length → S) (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) :
    (completedWith tables suffix cache).respond input =
      (suffix ⟨_, room⟩, afterPrivate tables input suffix cache (suffix ⟨_, room⟩)) := by
  have read : tapeAt (completedWith tables suffix cache).tape tables.consumed.length =
      suffix ⟨_, room⟩ := by
    simp [tapeAt, completedWith, room]
  simp only [ChainState.respond]
  rw [show (completedWith tables suffix cache).answers input = none from fresh]
  rw [show (completedWith tables suffix cache).position = tables.consumed.length from rfl, read]
  rfl

omit [Inhabited S] [SampleableType S] in
theorem completedWith_recordAux (tables : Simulated E S X width) (input : Input E S X)
    (room : tables.consumed.length < length) (suffix : Fin length → S)
    (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) (answer : S) :
    completedWith (tables.recordAux width input answer) suffix cache =
      afterPrivate tables input (Function.update suffix ⟨_, room⟩ answer) cache answer := by
  simp only [completedWith, afterPrivate, Simulated.recordAux, List.length_append,
    List.length_singleton, ChainState.mk.injEq, and_true]
  funext index
  by_cases before : index.val < tables.consumed.length
  · have alsoBefore : index.val < tables.consumed.length + 1 := by omega
    simp [before, alsoBefore, List.getElem_append_left before]
  · by_cases at_ : index.val = tables.consumed.length
    · have same : index = ⟨_, room⟩ := Fin.ext at_
      subst same
      simp
    · have after : ¬ index.val < tables.consumed.length + 1 := by omega
      have different : index ≠ ⟨_, room⟩ := fun equal => at_ (congrArg Fin.val equal)
      simp [before, after, Function.update_of_ne different]

omit [DecidableEq S] [DecidableEq X] [Inhabited S] [SampleableType S] in
theorem completedWith_cacheQuery (tables : Simulated E S X width) (suffix : Fin length → S)
    (cache : (OracleSpec.ofFn (Answer E S width)).QueryCache) (key : List E)
    (answer : Fin width → S) :
    ({ completedWith tables suffix cache with
        recorded := Function.update (completedWith tables suffix cache).recorded key
          (some answer) } : ChainState E S X width length) =
      completedWith tables suffix (cache.cacheQuery key answer) := by
  simp only [completedWith, ChainState.mk.injEq, true_and]
  funext other
  by_cases same : other = key
  · subst same
    simp
  · rw [Function.update_of_ne same, QueryCache.cacheQuery_of_ne _ _ same]

/-- One primitive call of the adversary: filling then running the hash-chain
simulator has the law of running the lazy simulator then filling. -/
theorem adversary_commute {slots : ℕ} (input : Input E S X) (tables : Simulated E S X width)
    (organized : Organized tables) (tapeRoom : tables.consumed.length < length)
    (slotRoom : tables.touched.length < slots) :
    (fillAll (length := length) slots tables >>= fun filled =>
        (flatSimulator width length input).run filled) =ᵈ ((simulator width input).run tables >>= fun step =>
        (fun filled => (step.1, filled)) <$> fillAll slots step.2) := by
  by_cases routed : ∃ state event block history, input = .request state event block ∧
      tables.reached state = some history ∧ block < width
  · obtain ⟨state, event, block, history, rfl, recorded, below⟩ := routed
    rw [simulator_run_routed tables recorded event below]
    have belongs : ∀ (suffix : Fin length → S) cache,
        chainAttempt width (completedWith tables suffix cache).reached
          (.request state event block : Input E S X) = some (history ++ [event]) := by
      intro _ _
      simp [chainAttempt, completedWith, recorded, below]
    cases cell : tables.history (history ++ [event], ⟨block, below⟩) with
    | some value =>
        have touched := organized (history ++ [event]) ⟨block, below⟩ (by rw [cell]; simp)
        rw [historyBlock_run_some cell, pure_bind]
        simp only [fillAll, bind_assoc, pure_bind, map_bind, map_pure]
        refine EvalDistEq.bind_right _ fun rows => EvalDistEq.bind_right _ fun suffix => ?_
        rw [flat_run_recorded (belongs _ _)
          (show (completedWith tables suffix (completed tables rows)).recorded (history ++ [event]) =
            _ from completed_apply_touched touched rows)]
        simp [chainShared, below, cell]
    | none =>
        rw [historyBlock_run_none cell]
        simp only [fillAll, bind_assoc, pure_bind, map_bind, map_pure]
        by_cases touched : history ++ [event] ∈ tables.touched
        · have lhs : ∀ (rows : Fin slots → Fin width → S) (suffix : Fin length → S),
              (flatSimulator width length (.request state event block)).run
                  (completedWith tables suffix (completed tables rows), completed tables rows) =
                pure (rowAt rows (tables.touched.idxOf (history ++ [event])) ⟨block, below⟩,
                  (completedWith tables suffix (completed tables rows), completed tables rows)) := by
            intro rows suffix
            rw [flat_run_recorded (belongs _ _)
              (show (completedWith tables suffix (completed tables rows)).recorded
                (history ++ [event]) = _ from completed_apply_touched touched rows)]
            simp [chainShared, below, cell]
          simp only [lhs]
          exact touched_law touched cell
            ((List.idxOf_lt_length_of_mem touched).trans slotRoom)
            fun value cache => ($ᵗ (Fin length → S)) >>= fun suffix =>
              pure (value, (completedWith tables suffix cache, cache))
        · have lhs : ∀ (rows : Fin slots → Fin width → S) (suffix : Fin length → S),
              (flatSimulator width length (.request state event block)).run
                  (completedWith tables suffix (completed tables rows), completed tables rows) =
                ($ᵗ (Fin width → S)) >>= fun answer =>
                  pure (answer ⟨block, below⟩,
                    (completedWith tables suffix ((completed tables rows).cacheQuery
                      (history ++ [event]) answer),
                      (completed tables rows).cacheQuery (history ++ [event]) answer)) := by
            intro rows suffix
            rw [flat_run_fresh (belongs _ _)
              (show (completedWith tables suffix (completed tables rows)).recorded
                (history ++ [event]) = none from completed_apply_untouched touched rows),
              randomOracle.run_eq, completed_apply_untouched touched rows]
            simp only [bind_assoc, pure_bind, chainShared, below, ↓reduceDIte]
            refine bind_congr fun answer => ?_
            rw [completedWith_cacheQuery]
          simp only [lhs]
          refine (EvalDistEq.bind_right _ fun rows => evalSPMF_uniform_swap fun suffix answer =>
            (pure (answer ⟨block, below⟩,
              (completedWith tables suffix ((completed tables rows).cacheQuery
                (history ++ [event]) answer),
                (completed tables rows).cacheQuery (history ++ [event]) answer)) :
              ProbComp _)).trans ?_
          exact untouched_law organized touched slotRoom
            fun value cache => ($ᵗ (Fin length → S)) >>= fun suffix =>
              pure (value, (completedWith tables suffix cache, cache))
  · have outside : ∀ (suffix : Fin length → S) cache,
        chainAttempt width (completedWith tables suffix cache).reached input = none := by
      intro _ _
      cases input with
      | request state event block =>
          simp only [chainAttempt, completedWith]
          split_ifs with below
          · cases recorded : tables.reached state with
            | none => rfl
            | some history => exact absurd ⟨state, event, block, history, rfl, recorded, below⟩ routed
          · rfl
      | bind => rfl
      | absorb => rfl
      | other => rfl
    have unrouted : ∀ state event block history, input = .request state event block →
        tables.reached state = some history → width ≤ block := by
      rintro state event block history rfl recorded
      by_contra below
      exact routed ⟨state, event, block, history, rfl, recorded, by omega⟩
    rw [simulator_run_unrouted tables unrouted]
    cases cachedAux : tables.aux input with
    | some value =>
        rw [auxCell_run_some cachedAux, pure_bind]
        simp only [fillAll, bind_assoc, pure_bind, map_bind, map_pure]
        refine EvalDistEq.bind_right _ fun rows => EvalDistEq.bind_right _ fun suffix => ?_
        rw [flat_run_private (outside _ _)]
        simp [ChainState.respond, completedWith, cachedAux]
    | none =>
        rw [auxCell_run_none cachedAux]
        simp only [fillAll, bind_assoc, pure_bind, map_bind, map_pure]
        have lhs : ∀ (rows : Fin slots → Fin width → S) (suffix : Fin length → S),
            (flatSimulator width length input).run
                (completedWith tables suffix (completed tables rows), completed tables rows) =
              pure (suffix ⟨_, tapeRoom⟩, (afterPrivate tables input suffix
                (completed tables rows) (suffix ⟨_, tapeRoom⟩), completed tables rows)) := by
          intro rows suffix
          rw [flat_run_private (outside _ _), respond_completedWith_fresh cachedAux tapeRoom]
        simp only [lhs]
        have recordAuxCompleted : ∀ (value : S) (rows : Fin slots → Fin width → S),
            completed (tables.recordAux width input value) rows = completed tables rows :=
          fun _ _ => rfl
        simp only [recordAuxCompleted, completedWith_recordAux tables input tapeRoom]
        symm
        refine (evalSPMF_uniform_swap (A := S) _).trans ?_
        refine EvalDistEq.bind_right _ fun rows => ?_
        simpa only [Function.update_self] using
          (evalSPMF_uniform_update ⟨_, tapeRoom⟩ fun suffix =>
            (pure (suffix ⟨_, tapeRoom⟩, (afterPrivate tables input suffix (completed tables rows)
              (suffix ⟨_, tapeRoom⟩), completed tables rows)) : ProbComp _))

omit [Inhabited S] in
theorem auxCell_support (input : Input E S X) (tables : Simulated E S X width) :
    ∀ step ∈ support ((auxCell width input).run tables),
      step.2 = tables ∨ step.2 = tables.recordAux width input step.1 := by
  intro step member
  cases cached : tables.aux input with
  | some value =>
      rw [auxCell_run_some cached] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      exact Or.inl (by rw [member])
  | none =>
      rw [auxCell_run_none cached] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨value, -, rfl⟩ := member
      exact Or.inr rfl

omit [Inhabited S] in
/-- One lazy simulator step keeps the read keys organized and reads at most one
private answer and at most one new history key. -/
theorem simulator_step_support (input : Input E S X) (tables : Simulated E S X width)
    (organized : Organized tables) :
    ∀ step ∈ support ((simulator width input).run tables),
      Organized step.2 ∧ step.2.consumed.length ≤ tables.consumed.length + 1 ∧
        step.2.touched.length ≤ tables.touched.length + 1 := by
  intro step member
  by_cases routed : ∃ state event block history, input = .request state event block ∧
      tables.reached state = some history ∧ block < width
  · obtain ⟨state, event, block, history, rfl, recorded, below⟩ := routed
    rw [simulator_run_routed tables recorded event below] at member
    rcases historyBlock_support _ _ tables step member with same | updated
    · rw [same]; exact ⟨organized, by omega, by omega⟩
    · rw [updated]
      refine ⟨organized.recordHistory _ _ _, by simp [Simulated.recordHistory], ?_⟩
      rw [touched_recordHistory]
      split_ifs <;> simp
  · have unrouted : ∀ state event block history, input = .request state event block →
        tables.reached state = some history → width ≤ block := by
      rintro state event block history rfl recorded
      by_contra below
      exact routed ⟨state, event, block, history, rfl, recorded, by omega⟩
    rw [simulator_run_unrouted tables unrouted] at member
    rcases auxCell_support input tables step member with same | updated
    · rw [same]; exact ⟨organized, by omega, by omega⟩
    · rw [updated]
      exact ⟨fun key block present => organized key block present,
        by simp [Simulated.recordAux], by simp [Simulated.recordAux]⟩

/-- The lazy simulator's run of an adversary within its query bound, filled, has the
law of the hash-chain simulator's run from the filled state. -/
theorem adversary_eq {slots : ℕ} {α : Type} (adversary : OracleComp (Primitive E S X) α)
    {calls : ℕ} (bounded : IsTotalQueryBound adversary calls) (tables : Simulated E S X width)
    (organized : Organized tables) (tapeRoom : tables.consumed.length + calls ≤ length)
    (slotRoom : tables.touched.length + calls ≤ slots) :
    (fillAll (length := length) slots tables >>= fun filled =>
        (simulateQ (flatSimulator width length) adversary).run filled) =ᵈ ((simulateQ (simulator width) adversary).run tables >>= fun result =>
        (fun filled => (result.1, filled)) <$> fillAll slots result.2) :=
  evalSPMF_simulateQ_fill (simulator width) (flatSimulator width length) (fillAll slots)
    (fun remaining current => Organized current ∧ current.consumed.length + remaining ≤ length ∧
      current.touched.length + remaining ≤ slots)
    (fun _ input current inv => adversary_commute input current inv.1 (by omega) (by omega))
    (fun remaining input current inv step member => by
      obtain ⟨stepOrganized, consumed, touched⟩ :=
        simulator_step_support input current inv.1 step member
      exact ⟨stepOrganized, by omega, by omega⟩)
    adversary calls tables bounded ⟨organized, tapeRoom, slotRoom⟩

end AdversaryCommute

section Experiments
variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]
  [SampleableType S] {width : ℕ} {I : PIR.Signature} {P A Stmt : Type}

omit [DecidableEq S] [DecidableEq X] [SampleableType S] in
theorem completed_empty {slots : ℕ} (rows : Fin slots → Fin width → S) :
    completed (Simulated.empty width : Simulated E S X width) rows = ∅ := by
  apply QueryCache.ext
  intro key
  simp [completed, Simulated.empty]

omit [SampleableType S] in
theorem completedWith_empty {length : ℕ} (suffix : Fin length → S) :
    completedWith (Simulated.empty width : Simulated E S X width) suffix ∅ =
      (chainSimulator width length).start suffix := by
  simp only [completedWith, Simulated.empty, List.length_nil, Nat.not_lt_zero, ↓reduceDIte]
  rfl

/-- The simulated experiment has the law of the translated experiment: the
adversary against the hash-chain simulator with a uniform private tape, then the
typed transform, over one lazily sampled history oracle. -/
theorem simulatedExperiment_eq_translated (positive : 0 < width)
    (absorb : Typed.Interface I E P (Raw E S width)) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) {queries : ℕ}
    (queryBounded : ∀ statement, Typed.QueryBound absorb (validator statement) queries)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) :
    simulatedExperiment width absorb validator initial adversary =ᵈ (($ᵗ (Fin calls → S)) >>= fun tape =>
        (simulateQ randomOracle (Typed.experiment absorb validator initial
          ((chainSimulator width calls).translate adversary tape))).run' ∅) := by
  have right : ∀ tape : Fin calls → S,
      (simulateQ randomOracle (Typed.experiment absorb validator initial
          ((chainSimulator width calls).translate adversary tape))).run' ∅ =
        (simulateQ (flatSimulator width calls) adversary).run
            ((chainSimulator width calls).start tape, ∅) >>= fun result =>
          (fun outcome => (result.1.1, outcome)) <$>
            (simulateQ randomOracle (Typed.transform absorb Typed.ask (validator result.1.1)
              (initial result.1.1) result.1.2)).run' result.2.2 := by
    intro tape
    simp only [Typed.experiment, Provider.Simulator.translate, StateT.run'_eq, simulateQ_bind,
      simulateQ_map, StateT.run_bind, StateT.run_map]
    rw [simulateQ_flatten]
    simp only [flatSimulator, map_bind, bind_map_left, Functor.map_map]
  let slots := calls + queries
  let finish : (Stmt × List P) × (ChainState E S X width calls ×
      (OracleSpec.ofFn (Answer E S width)).QueryCache) → ProbComp (Stmt × (PIR.Outcome A × List P)) :=
    fun result => (fun outcome => (result.1.1, outcome)) <$>
      (simulateQ randomOracle (Typed.transform absorb Typed.ask (validator result.1.1)
        (initial result.1.1) result.1.2)).run' result.2.2
  have filled : (($ᵗ (Fin calls → S)) >>= fun tape =>
        (simulateQ randomOracle (Typed.experiment absorb validator initial
          ((chainSimulator width calls).translate adversary tape))).run' ∅) =ᵈ ((fillAll (length := calls) slots (Simulated.empty width : Simulated E S X width) >>=
          fun state => (simulateQ (flatSimulator width calls) adversary).run state) >>= finish) := by
    simp only [right, fillAll, completed_empty, completedWith_empty, bind_assoc, pure_bind]
    exact (evalSPMF_uniform_drop _).symm
  symm
  refine filled.trans (((adversary_eq adversary bounded (Simulated.empty width)
    (fun _ _ absent => absurd rfl absent) (by simp [Simulated.empty])
    (by simp [Simulated.empty, slots])).bind_left finish).trans ?_)
  rw [bind_assoc]
  simp only [simulatedExperiment]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun started member => ?_
  obtain ⟨left, -, organized, room⟩ := support_simulateQ_invariant (simulator width)
    (fun remaining current => Organized current ∧ current.touched.length + remaining ≤ calls)
    (fun remaining input current inv step stepMember => by
      obtain ⟨stepOrganized, -, touched⟩ :=
        simulator_step_support input current inv.1 step stepMember
      exact ⟨stepOrganized, by omega⟩)
    adversary calls (Simulated.empty width) bounded
    ⟨fun _ _ absent => absurd rfl absent, by simp [Simulated.empty]⟩ started member
  have verified := verifier_eq positive absorb (validator started.1.1) (initial started.1.1)
    started.1.2 (queryBounded started.1.1) started.2 organized
    (show started.2.touched.length + queries ≤ slots by omega)
  simp only [map_bind, finish, fillAll, bind_assoc, map_pure, pure_bind]
  refine (EvalDistEq.bind_right _ fun rows => evalSPMF_uniform_drop _).trans ?_
  have regroup : (($ᵗ (Fin slots → Fin width → S)) >>= fun rows =>
      (fun outcome => (started.1.1, outcome)) <$>
        (simulateQ randomOracle (Typed.transform absorb Typed.ask (validator started.1.1)
          (initial started.1.1) started.1.2)).run' (completed started.2 rows)) =
      (fun outcome => (started.1.1, outcome)) <$> (fillHistory slots started.2 >>= fun cache =>
        (simulateQ randomOracle (Typed.transform absorb Typed.ask (validator started.1.1)
          (initial started.1.1) started.1.2)).run' cache) := by
    simp only [fillHistory, bind_assoc, pure_bind, map_bind]
  rw [regroup]
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    verified.map (fun outcome => (started.1.1, outcome))

end Experiments

end ZkcSecurity.HashChain

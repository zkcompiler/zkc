module

public import Zkc.Core.Facts.Body.Statements

@[expose] public section

/-!
Proofs of the statements of part 1 of the seam (`Seam/Values.lean`), with the lemmas about
readings, sharing, selections, `placed` and `Values.apply` that the later parts use, the lemmas
about lists, and how often a count says a loop runs (`Count.Is.mono`, `Count.Is.unique`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Readings grow -/

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}

mutual
  /-- A reading is kept when the table grows and more leaves get values. -/
  theorem Reads.mono {table table' : Table Raw} {ρ ρ' : Leaves Val} (sub : table.Le table')
      (le : ρ.Le ρ') : ∀ {id : Ident} {v : Val}, Reads Run truth table ρ id v →
        Reads Run truth table' ρ' id v
    | _, _, .leaf valued => .leaf (le _ _ valued)
    | _, _, .app known form position read ran result =>
        .app (sub _ known) form position (ReadsAll.mono sub le read) ran result
    | _, _, .select known form decided holds read =>
        .select (sub _ known) form (Reads.mono sub le decided) holds (Reads.mono sub le read)
  /-- Readings in order are kept when the table grows and more leaves get values. -/
  theorem ReadsAll.mono {table table' : Table Raw} {ρ ρ' : Leaves Val} (sub : table.Le table')
      (le : ρ.Le ρ') : ∀ {ids : List Ident} {vs : List Val}, ReadsAll Run truth table ρ ids vs →
        ReadsAll Run truth table' ρ' ids vs
    | _, _, .nil => .nil
    | _, _, .cons first others => .cons (Reads.mono sub le first) (ReadsAll.mono sub le others)
end

end

/-- **A reading is kept when the table grows and more leaves get values.** -/
theorem readsMono {Raw Val : Type} : ReadsMonoStatement (Raw := Raw) (Val := Val) :=
  fun _ _ _ _ _ _ sub le _ _ read => Reads.mono sub le read

/-! ## Readings are functional -/

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}

/-- A selection's value is at the start of its entry: an entry of a selection has a value. -/
theorem Table.WF.select_pos {table : Table Raw} (wf : table.WF) {e : Entry Raw} (known : e ∈ table)
    {condition first second : Ident} (form : e.form = .select condition first second) :
    0 < e.count := by
  rw [wf.selections e condition first second known form]
  exact Nat.zero_lt_one

/-- **An identifier reads one value**, for written operations that give one list of results and a
table whose values are apart. By induction on the first reading: two readings of a value of the
table are by the same entry, since the values of entries are apart and a selection has one value. -/
theorem Reads.functionalOn
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {table : Table Raw} (wf : table.WF) {ρ : Leaves Val} :
    ∀ {id : Ident} {x y : Val}, Reads Run truth table ρ id x → Reads Run truth table ρ id y →
      x = y := by
  intro id x y first
  revert y
  refine Reads.rec (motive_1 := fun id x _ => ∀ {y}, Reads Run truth table ρ id y → x = y)
    (motive_2 := fun ids xs _ => ∀ {ys}, ReadsAll Run truth table ρ ids ys → xs = ys)
    ?leaf ?app ?select ?nil ?cons first
  case leaf =>
    intro n x valued y second
    cases second with
    | leaf valued' => rw [valued] at valued'; exact Option.some.inj valued'
  case app =>
    intro e written args j operands results x known form position _ ran result same y second
    generalize hid : Ident.val (e.lo + j) = id at second
    cases second with
    | leaf _ => cases hid
    | app known' form' position' read' ran' result' =>
        injection hid with hid
        obtain rfl := wf.apart _ _ known known' _ _ position position' hid
        obtain rfl := Nat.add_left_cancel hid
        rw [form] at form'
        injection form' with sameWritten sameArgs
        subst sameWritten sameArgs
        obtain rfl := same read'
        obtain rfl := functional _ _ _ _ ran ran'
        rw [result] at result'
        exact Option.some.inj result'
    | select known' form' _ _ _ =>
        injection hid with hid
        obtain rfl := wf.apart _ _ known known' _ _ position (wf.select_pos known' form')
          (hid.trans (Nat.add_zero _).symm)
        rw [form] at form'
        cases form'
  case select =>
    intro e condition first second chosen which x known form _ holds _ sameDecided sameRead y other
    generalize hid : Ident.val e.lo = id at other
    cases other with
    | leaf _ => cases hid
    | app known' form' position' _ _ _ =>
        injection hid with hid
        obtain rfl := wf.apart _ _ known known' _ _ (wf.select_pos known form) position'
          ((Nat.add_zero _).trans hid)
        rw [form] at form'
        cases form'
    | select known' form' decided' holds' read' =>
        injection hid with hid
        obtain rfl := wf.apart _ _ known known' 0 0 (wf.select_pos known form)
          (wf.select_pos known' form') (congrArg (· + 0) hid)
        rw [form] at form'
        injection form' with sameCondition sameFirst sameSecond
        subst sameCondition sameFirst sameSecond
        obtain rfl := sameDecided decided'
        rw [holds] at holds'
        obtain rfl := Option.some.inj holds'
        exact sameRead read'
  case nil =>
    intro ys second
    cases second
    rfl
  case cons =>
    intro id ids x xs _ _ sameFirst sameOthers ys second
    cases second with
    | cons first' others' => rw [sameFirst first', sameOthers others']

/-- The allocator carries the slot invariant used to reconcile two readings. -/
theorem Reads.functional
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {v : Values Raw} (wf : v.WF) {ρ : Leaves Val} {id : Ident} {x y : Val}
    (first : Reads Run truth v.table ρ id x) (second : Reads Run truth v.table ρ id y) : x = y :=
  Reads.functionalOn functional wf.slots first second

/-- Identifiers read one list of values. -/
theorem ReadsAll.functional
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {v : Values Raw} (wf : v.WF) {ρ : Leaves Val} :
    ∀ {ids : List Ident} {xs ys : List Val}, ReadsAll Run truth v.table ρ ids xs →
      ReadsAll Run truth v.table ρ ids ys → xs = ys
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons first others, .cons first' others' => by
      rw [Reads.functional functional wf first first', ReadsAll.functional functional wf others others']

end

/-- **An identifier reads one value.** -/
theorem readsFunctional {Raw Val : Type} : ReadsFunctionalStatement (Raw := Raw) (Val := Val) :=
  fun _ _ functional _ wf _ _ _ _ first second => Reads.functional functional wf first second

/-! ## The table grows -/

section
variable {Raw : Type}

theorem Table.Le.refl (tbl : Table Raw) : tbl.Le tbl := fun _ m => m

theorem Table.Le.trans {a b c : Table Raw} (first : a.Le b) (second : b.Le c) : a.Le c :=
  fun e m => second e (first e m)

/-- The entries of a table with an entry made: that entry and the table's. -/
theorem Table.mem_add {tbl : Table Raw} {e x : Entry Raw} : x ∈ tbl.add e ↔ x = e ∨ x ∈ tbl :=
  List.mem_cons

theorem Table.le_add (tbl : Table Raw) (e : Entry Raw) : tbl.Le (tbl.add e) :=
  fun _ m => Table.mem_add.mpr (Or.inr m)

theorem Table.self_mem_add (tbl : Table Raw) (e : Entry Raw) : e ∈ tbl.add e :=
  Table.mem_add.mpr (Or.inl rfl)

/-- The values grew: the table has the entries of before, its values are well formed, and the
next value is not lower. -/
def Values.Grew (v v' : Values Raw) : Prop := v.table.Le v'.table ∧ v'.WF ∧ v.next ≤ v'.next

theorem Values.Grew.refl {v : Values Raw} (wf : v.WF) : Values.Grew v v :=
  ⟨Table.Le.refl _, wf, Nat.le_refl _⟩

theorem Values.Grew.trans {a b c : Values Raw} (first : Values.Grew a b) (second : Values.Grew b c) :
    Values.Grew a c :=
  ⟨first.1.trans second.1, second.2.1, Nat.le_trans first.2.2 second.2.2⟩

/-- A value of an entry of a table whose values are well formed is below the next value. -/
theorem Values.WF.lt_next {v : Values Raw} (wf : v.WF) {e : Entry Raw} (known : e ∈ v.table)
    {j : Nat} (position : j < e.count) : e.lo + j < v.next :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left position _) (wf.below e known)

/-- The values with an entry made at the next value are well formed, when a selection has one
value. -/
theorem Values.WF.add {v : Values Raw} (wf : v.WF) (form : Form Raw) (count : Nat)
    (selection : ∀ condition first second, form = .select condition first second → count = 1) :
    Values.WF ⟨v.table.add ⟨form, v.next, count⟩, v.next + count⟩ := by
  refine ⟨fun e m => ?_, fun e e' m m' j j' position position' same => ?_,
    fun e condition first second m form' => ?_⟩
  · rcases Table.mem_add.mp m with rfl | m
    · exact Nat.le_refl _
    · exact Nat.le_trans (wf.below e m) (Nat.le_add_right _ _)
  · rcases Table.mem_add.mp m with rfl | m <;> rcases Table.mem_add.mp m' with rfl | m'
    · rfl
    · exact absurd same (Nat.ne_of_gt (Nat.lt_of_lt_of_le (wf.lt_next m' position')
        (Nat.le_add_right _ _)))
    · exact absurd same (Nat.ne_of_lt (Nat.lt_of_lt_of_le (wf.lt_next m position)
        (Nat.le_add_right _ _)))
    · exact wf.slots.apart e e' m m' j j' position position' same
  · rcases Table.mem_add.mp m with rfl | m
    · exact selection condition first second form'
    · exact wf.slots.selections e condition first second m form'

end

/-! ## Finding a form -/

section
variable {Raw : Type} [DecidableEq Raw]

/-- The entry found among entries, with a form and a number of values, is among them. -/
theorem findIn_spec {form : Form Raw} {count lo : Nat} :
    ∀ {es : List (Entry Raw)}, findIn form count es = some lo → ⟨form, lo, count⟩ ∈ es
  | [], found => nomatch found
  | e :: es, found => by
      simp only [findIn] at found
      split at found
      · next same =>
          cases found
          obtain ⟨sameCount, sameForm⟩ := Bool.and_eq_true_iff.mp same
          obtain sameCount := beq_iff_eq.mp sameCount
          obtain sameForm := (Form.matches_iff ..).mp sameForm
          cases e
          cases sameCount
          cases sameForm
          exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (findIn_spec found)

/-- The entry found with a form and a number of values is in the table. -/
theorem Table.find_spec {tbl : Table Raw} {form : Form Raw} {count lo : Nat}
    (found : tbl.find form count = some lo) : (⟨form, lo, count⟩ : Entry Raw) ∈ tbl :=
  tbl.search_spec (probe := findIn form count) (P := fun lo => (⟨form, lo, count⟩ : Entry Raw) ∈ tbl)
    (fun b e m => b.forms e (BitTree.mem_of_find _ _ _ _ m))
    (fun _ sub hit => sub _ (findIn_spec hit)) found

/-- Sharing a form found in the table returns its entry and changes nothing. -/
theorem Values.share_found {form : Form Raw} {count lo : Nat} {v : Values Raw}
    (found : v.table.find form count = some lo) :
    v.share form count = (⟨form, lo, count⟩, v) := by
  simp only [Values.share, found]

/-- Sharing a form not in the table makes its entry at the next value. -/
theorem Values.share_new {form : Form Raw} {count : Nat} {v : Values Raw}
    (found : v.table.find form count = none) :
    v.share form count =
      (⟨form, v.next, count⟩, ⟨v.table.add ⟨form, v.next, count⟩, v.next + count⟩) := by
  simp only [Values.share, found]

/-- Sharing makes the values grow, when a selection has one value. -/
theorem Values.share_grew (form : Form Raw) (count : Nat) {v : Values Raw} (wf : v.WF)
    (selection : ∀ condition first second, form = .select condition first second → count = 1) :
    Values.Grew v (v.share form count).2 := by
  cases found : v.table.find form count with
  | some lo => rw [Values.share_found found]; exact Values.Grew.refl wf
  | none =>
      rw [Values.share_new found]
      exact ⟨Table.le_add _ _, wf.add form count selection, Nat.le_add_right _ _⟩

/-- The entry that sharing returns has the form and the number of values asked, and is in the
table after sharing. -/
theorem Values.share_entry (form : Form Raw) (count : Nat) (v : Values Raw) :
    (v.share form count).1.form = form ∧ (v.share form count).1.count = count ∧
      (v.share form count).1 ∈ (v.share form count).2.table := by
  cases found : v.table.find form count with
  | some lo =>
      rw [Values.share_found found]
      exact ⟨rfl, rfl, Table.find_spec found⟩
  | none =>
      rw [Values.share_new found]
      exact ⟨rfl, rfl, Table.self_mem_add _ _⟩

end

/-- **Sharing keeps the table's entries and its well-formedness**, and gives values below the
next. -/
theorem shareGrows {Raw : Type} : ShareGrowsStatement (Raw := Raw) :=
  fun form count _ wf selection => Values.share_grew form count wf selection

/-! ## Shared values read -/

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}

/-- Consecutive values read, position by position, as many values. -/
theorem ReadsAll.vals {table : Table Raw} {ρ : Leaves Val} :
    ∀ (count lo : Nat) (results : List Val), results.length = count →
      (∀ j x, j < count → results[j]? = some x → Reads Run truth table ρ (.val (lo + j)) x) →
      ReadsAll Run truth table ρ (Ident.vals lo count) results
  | 0, _, [], _, _ => .nil
  | count + 1, lo, x :: results, length, each =>
      .cons (each 0 x (Nat.zero_lt_succ _) rfl)
        (ReadsAll.vals count (lo + 1) results (Nat.succ.inj length) fun j y below at_ => by
          have read := each (j + 1) y (Nat.succ_lt_succ below) at_
          rwa [← Nat.add_assoc, Nat.add_right_comm lo j 1] at read)

/-- The values of an entry of the table read what its written operation gives on what its
operands read. -/
theorem ReadsAll.entry {table : Table Raw} {ρ : Leaves Val} {e : Entry Raw} {written : Raw}
    {args : List Ident} {operands results : List Val} (known : e ∈ table)
    (form : e.form = .app written args) (read : ReadsAll Run truth table ρ args operands)
    (ran : Run written operands results) (length : results.length = e.count) :
    ReadsAll Run truth table ρ (Ident.vals e.lo e.count) results :=
  ReadsAll.vals _ _ _ length fun _ _ below at_ => .app known form below read ran at_

variable [DecidableEq Raw]

/-- **The values of a shared application read what the written operation gives** on what the
operands read, whether its entry was found or made. -/
theorem Values.share_reads {written : Raw} {args : List Ident} {count : Nat} {v : Values Raw}
    {ρ : Leaves Val} {operands results : List Val}
    (read : ReadsAll Run truth v.table ρ args operands) (ran : Run written operands results)
    (length : results.length = count) :
    ReadsAll Run truth (v.share (.app written args) count).2.table ρ
      (v.share (.app written args) count).1.ids results := by
  obtain ⟨form, sameCount, known⟩ := Values.share_entry (.app written args) count v
  have grew : v.table.Le (v.share (.app written args) count).2.table := by
    cases found : v.table.find (.app written args) count with
    | some lo => rw [Values.share_found found]; exact Table.Le.refl _
    | none => rw [Values.share_new found]; exact Table.le_add _ _
  exact ReadsAll.entry known form (ReadsAll.mono grew (fun _ _ h => h) read) ran
    (length.trans sameCount.symm)

/-- **What a choice gives at a position reads what the region that ran returned there.** -/
theorem Values.select_reads {condition first second : Ident} {v : Values Raw} {ρ : Leaves Val}
    {chosen : Val} {which : Bool} {x : Val}
    (decided : Reads Run truth v.table ρ condition chosen) (holds : truth chosen = some which)
    (read : Reads Run truth v.table ρ (if which then first else second) x) :
    Reads Run truth (v.select condition first second).2.table ρ
      (v.select condition first second).1 x := by
  unfold Values.select
  split
  · next same =>
      subst same
      cases which <;> exact read
  · cases found : v.table.find (.select condition first second) 1 with
    | some lo =>
        simp only [Values.share_found found]
        exact .select (Table.find_spec found) rfl decided holds read
    | none =>
        simp only [Values.share_new found]
        exact .select (Table.self_mem_add _ _) rfl
          (Reads.mono (Table.le_add _ _) (fun _ _ h => h) decided) holds
          (Reads.mono (Table.le_add _ _) (fun _ _ h => h) read)

end

/-- **The entry of a shared application is in the table, and its values read what the written
operation gives.** -/
theorem shareReads {Raw Val : Type} : ShareReadsStatement (Raw := Raw) (Val := Val) :=
  fun _ _ written args count v _ _ _ read ran length =>
    ⟨(Values.share_entry (.app written args) count v).2.2, Values.share_reads read ran length⟩

/-- **What a choice gives reads what the region that ran returned.** -/
theorem selectReads {Raw Val : Type} : SelectReadsStatement (Raw := Raw) (Val := Val) :=
  fun _ _ _ _ _ _ _ _ _ _ decided holds read => Values.select_reads decided holds read

/-! ## Selections, `placed` and `Values.apply` -/

section
variable {Raw : Type} [DecidableEq Raw]

/-- Sharing keeps the table's entries. -/
theorem Values.share_table_le (form : Form Raw) (count : Nat) (v : Values Raw) :
    v.table.Le (v.share form count).2.table := by
  cases found : v.table.find form count with
  | some lo => rw [Values.share_found found]; exact Table.Le.refl _
  | none => rw [Values.share_new found]; exact Table.le_add _ _

/-- What a choice gives at one position keeps the table's entries. -/
theorem Values.select_table_le (condition first second : Ident) (v : Values Raw) :
    v.table.Le (v.select condition first second).2.table := by
  unfold Values.select
  split
  · exact Table.Le.refl _
  · exact Values.share_table_le _ 1 v

/-- What a choice gives at every position keeps the table's entries. -/
theorem Values.selectAll_table_le (condition : Ident) :
    ∀ (firsts seconds : List Ident) (v : Values Raw),
      v.table.Le (Values.selectAll condition firsts seconds v).2.table
  | first :: firsts, second :: seconds, v =>
      (Values.select_table_le condition first second v).trans
        (Values.selectAll_table_le condition firsts seconds _)
  | [], _, _ => Table.Le.refl _
  | _ :: _, [], _ => Table.Le.refl _

/-- What a choice gives at one position makes the values grow. -/
theorem Values.select_grew (condition first second : Ident) {v : Values Raw} (wf : v.WF) :
    Values.Grew v (v.select condition first second).2 := by
  unfold Values.select
  split
  · exact Values.Grew.refl wf
  · exact Values.share_grew _ 1 wf fun _ _ _ _ => rfl

/-- What a choice gives at every position makes the values grow. -/
theorem Values.selectAll_grew (condition : Ident) :
    ∀ (firsts seconds : List Ident) {v : Values Raw}, v.WF →
      Values.Grew v (Values.selectAll condition firsts seconds v).2
  | first :: firsts, second :: seconds, v, wf => by
      have one := Values.select_grew condition first second wf
      exact one.trans (Values.selectAll_grew condition firsts seconds one.2.1)
  | [], _, _, wf => Values.Grew.refl wf
  | _ :: _, [], _, wf => Values.Grew.refl wf

/-- What a choice gives at every position is as many identifiers as both regions return. -/
theorem Values.selectAll_length (condition : Ident) :
    ∀ (firsts seconds : List Ident) (v : Values Raw), firsts.length = seconds.length →
      (Values.selectAll condition firsts seconds v).1.length = firsts.length
  | _ :: firsts, _ :: seconds, _, same =>
      congrArg (· + 1) (Values.selectAll_length condition firsts seconds _ (Nat.succ.inj same))
  | [], _, _, _ => rfl
  | _ :: _, [], _, same => nomatch same

/-- Applying a written operation makes the values grow. -/
theorem Values.apply_grew (commutes : Raw → Bool) (written : Raw) (args : List Ident) (count : Nat)
    {v : Values Raw} (wf : v.WF) : Values.Grew v (v.apply commutes written args count).2 :=
  Values.share_grew _ count wf fun _ _ _ same => nomatch same

/-- The operands of a written operation, in the order of the table: as they are, or the two of
an operation that commutes exchanged. -/
theorem placed_cases (commutes : Bool) :
    ∀ args : List Ident, placed commutes args = args ∨
      (commutes = true ∧ ∃ first second, args = [first, second] ∧
        placed commutes args = [second, first])
  | [] => .inl rfl
  | [_] => .inl rfl
  | [first, second] => by
      by_cases exchange : commutes = true ∧ second.key < first.key
      · exact .inr ⟨exchange.1, first, second, rfl, ite_eq_left exchange⟩
      · exact .inl (ite_eq_right exchange)
  | _ :: _ :: _ :: _ => .inl rfl

end

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}

/-- **The operands placed in the order of the table read values on which the written operation
gives the same**, for an operation that gives the same on its two operands exchanged when it
commutes. -/
theorem placed_reads {table : Table Raw} {ρ : Leaves Val} {written : Raw} {commutes : Bool}
    (swap : commutes = true → ∀ a b results, Run written [a, b] results →
      Run written [b, a] results)
    {args : List Ident} {operands results : List Val}
    (read : ReadsAll Run truth table ρ args operands) (ran : Run written operands results) :
    ∃ operands', ReadsAll Run truth table ρ (placed commutes args) operands' ∧
      Run written operands' results := by
  rcases placed_cases commutes args with same | ⟨exchanges, first, second, rfl, same⟩
  · rw [same]
    exact ⟨operands, read, ran⟩
  · rw [same]
    cases read with
    | cons readFirst others =>
        cases others with
        | cons readSecond none =>
            cases none
            exact ⟨_, .cons readSecond (.cons readFirst .nil), swap exchanges _ _ _ ran⟩

variable [DecidableEq Raw]

/-- **The values of a written operation applied to operands read what it gives** on what the
operands read. -/
theorem Values.apply_reads (commutes : Raw → Bool) {written : Raw} {args : List Ident}
    {count : Nat} {v : Values Raw} {ρ : Leaves Val} {operands results : List Val}
    (swap : commutes written = true → ∀ a b results, Run written [a, b] results →
      Run written [b, a] results)
    (read : ReadsAll Run truth v.table ρ args operands) (ran : Run written operands results)
    (length : results.length = count) :
    ReadsAll Run truth (v.apply commutes written args count).2.table ρ
      (v.apply commutes written args count).1.ids results := by
  obtain ⟨operands', read', ran'⟩ := placed_reads swap read ran
  exact Values.share_reads read' ran' length

/-- **What a choice gives at every position reads what the region that ran returned**, when the
condition reads its truth and both regions return as many identifiers. -/
theorem Values.selectAll_reads {condition : Ident} {ρ : Leaves Val} {chosen : Val} {which : Bool} :
    ∀ (firsts seconds : List Ident) {v : Values Raw} {xs : List Val},
      firsts.length = seconds.length →
      Reads Run truth v.table ρ condition chosen → truth chosen = some which →
      ReadsAll Run truth v.table ρ (if which then firsts else seconds) xs →
      ReadsAll Run truth (Values.selectAll condition firsts seconds v).2.table ρ
        (Values.selectAll condition firsts seconds v).1 xs
  | first :: firsts, second :: seconds, v, xs, same, decided, holds, read => by
      have grew := Values.select_table_le condition first second v
      have split : ∃ x xs', xs = x :: xs' ∧
          Reads Run truth v.table ρ (if which then first else second) x ∧
          ReadsAll Run truth v.table ρ (if which then firsts else seconds) xs' := by
        cases which with
        | true =>
            cases read with
            | cons one others => exact ⟨_, _, rfl, one, others⟩
        | false =>
            cases read with
            | cons one others => exact ⟨_, _, rfl, one, others⟩
      obtain ⟨x, xs', rfl, one, others⟩ := split
      have head := Values.select_reads decided holds one
      have tail := Values.selectAll_reads firsts seconds (v := (v.select condition first second).2)
        (Nat.succ.inj same) (Reads.mono grew (fun _ _ h => h) decided) holds
        (ReadsAll.mono grew (fun _ _ h => h) others)
      refine .cons ?_ tail
      exact Reads.mono (Values.selectAll_table_le condition firsts seconds _) (fun _ _ h => h) head
  | [], [], v, xs, _, _, _, read => by
      cases which <;> cases read <;> exact .nil
  | [], _ :: _, _, _, same, _, _, _ => nomatch same
  | _ :: _, [], _, _, same, _, _, _ => nomatch same

end

/-! ## Readings in order -/

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}
  {table : Table Raw} {ρ : Leaves Val}

/-- Identifiers read in order as many values as they are. -/
theorem ReadsAll.length : ∀ {ids : List Ident} {vs : List Val},
    ReadsAll Run truth table ρ ids vs → ids.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ others => congrArg (· + 1) (ReadsAll.length others)

/-- The identifier at a position reads the value at that position. -/
theorem ReadsAll.get : ∀ {ids : List Ident} {vs : List Val} {i : Nat} {id : Ident},
    ReadsAll Run truth table ρ ids vs → ids[i]? = some id →
      ∃ x, vs[i]? = some x ∧ Reads Run truth table ρ id x
  | _ :: _, _ :: _, 0, _, .cons first _, at_ => by
      cases at_
      exact ⟨_, rfl, first⟩
  | _ :: _, _ :: _, _ + 1, _, .cons _ others, at_ => by
      have later := ReadsAll.get others at_
      exact later

/-- Readings in order, one list after another. -/
theorem ReadsAll.append : ∀ {ids ids' : List Ident} {vs vs' : List Val},
    ReadsAll Run truth table ρ ids vs → ReadsAll Run truth table ρ ids' vs' →
      ReadsAll Run truth table ρ (ids ++ ids') (vs ++ vs')
  | _, _, _, _, .nil, rest => rest
  | _, _, _, _, .cons first others, rest => .cons first (ReadsAll.append others rest)

/-- The value at a position of consecutive values. -/
theorem Ident.vals_getElem? : ∀ (lo count j : Nat), j < count →
    (Ident.vals lo count)[j]? = some (.val (lo + j))
  | _, _ + 1, 0, _ => rfl
  | lo, count + 1, j + 1, below => by
      have later := Ident.vals_getElem? (lo + 1) count j (Nat.lt_of_succ_lt_succ below)
      rw [Nat.add_right_comm] at later
      exact later

/-- The value at a position of consecutive leaves. -/
theorem Ident.leaves_getElem? : ∀ (lo count j : Nat), j < count →
    (Ident.leaves lo count)[j]? = some (.leaf (lo + j))
  | _, _ + 1, 0, _ => rfl
  | lo, count + 1, j + 1, below => by
      have later := Ident.leaves_getElem? (lo + 1) count j (Nat.lt_of_succ_lt_succ below)
      rw [Nat.add_right_comm] at later
      exact later

theorem Ident.vals_length (lo count : Nat) : (Ident.vals lo count).length = count := by
  simp only [Ident.vals, List.length_map, List.length_range']

theorem Ident.leaves_length (lo count : Nat) : (Ident.leaves lo count).length = count := by
  simp only [Ident.leaves, List.length_map, List.length_range']

/-- Every consecutive value reads, when they read values in order. -/
theorem ReadsAll.vals_each {lo count : Nat} {results : List Val}
    (read : ReadsAll Run truth table ρ (Ident.vals lo count) results) :
    ∀ j, j < count → ∃ x, Reads Run truth table ρ (.val (lo + j)) x := by
  intro j below
  obtain ⟨x, _, one⟩ := read.get (Ident.vals_getElem? lo count j below)
  exact ⟨x, one⟩

end

/-! ## Lists -/

section
variable {D : Dialect} {Raw : Type}

/-- A list followed by another, taken as long as the first, is the first. -/
theorem take_append_length {α : Type} : ∀ (l₁ l₂ : List α) (n : Nat), l₁.length = n →
    (l₁ ++ l₂).take n = l₁
  | [], _, _, rfl => rfl
  | a :: l₁, l₂, _, rfl => congrArg (a :: ·) (take_append_length l₁ l₂ l₁.length rfl)

/-- Readings in order, of the first identifiers. -/
theorem ReadsAll.take {Val : Type} {Run : Raw → List Val → List Val → Prop}
    {truth : Val → Option Bool} {table : Table Raw} {ρ : Leaves Val} :
    ∀ (n : Nat) {ids : List Ident} {vs : List Val}, ReadsAll Run truth table ρ ids vs →
      ReadsAll Run truth table ρ (ids.take n) (vs.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons first others => .cons first (ReadsAll.take n others)

/-- Values with their types have the types of their list. -/
theorem dyns_map_fst (sem : Semantics D) :
    ∀ {items : List D.Ty} (values : HList sem.Val items), (sem.dyns values).map Sigma.fst = items
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (_ :: ·) (dyns_map_fst sem rest)

/-- The first of the values of a list that is two lists, with their types, are the values of the
first list. -/
theorem dyns_take_split (sem : Semantics D) {carried each : List D.Ty}
    (out : HList sem.Val (carried ++ each)) :
    (sem.dyns out).take carried.length = sem.dyns (HList.split carried out).1 := by
  rw [sem.dyns_split out]
  exact take_append_length _ _ _ (sem.dyns_length _)

end

/-! ## How often a count says a loop runs -/

section
variable {D : Dialect} {Raw : Type}

/-- How often a count says a loop runs is read over every table with the entries, from more
leaves. -/
theorem Count.Is.mono {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {w : D.Who} {table table' : Table Raw} {ρ ρ' : Leaves sem.Dyn}
    (sub : table.Le table') (le : ρ.Le ρ') :
    ∀ {times : Count D w} {count : Nat}, times.Is sem Run R table ρ count →
      times.Is sem Run R table' ρ' count
  | .fixed _, _, is => is
  | .value _ _, _, ⟨v, read, is⟩ => ⟨v, Reads.mono sub le read, is⟩

/-- A count says one number of iterations, when every identifier reads one value. -/
theorem Count.Is.unique {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn}
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {v : Values Raw} (wf : v.WF) {ρ : Leaves sem.Dyn} {w : D.Who} :
    ∀ {times : Count D w} {count count' : Nat}, times.Is sem Run R v.table ρ count →
      times.Is sem Run R v.table ρ count' → count = count'
  | .fixed _, _, _, is, is' => is.trans is'.symm
  | .value _ _, _, _, ⟨_, read, is⟩, ⟨_, read', is'⟩ => by
      rw [is, is', sem.dyn_inj (Reads.functional functional wf read read')]

end

section
variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF)

include functional slots in
theorem Asks.Sound.numberAt_reads {asks : Asks} (external : asks.Sound Run R table ρ)
    {id v} (read : Reads Run R.bool table ρ id v) :
    ∃ w, Reads Run R.bool table ρ (asks.numberAt id) w ∧ R.nat w = R.nat v := by
  cases found : asks.numberSource id with
  | none => exact ⟨v, by simpa [Asks.numberAt, found] using read, rfl⟩
  | some _ =>
    obtain ⟨x,w,rx,rw',same⟩ := external.numberSource _ _ found
    cases Reads.functionalOn functional slots read rx
    exact ⟨w, by simpa [Asks.numberAt, found] using rw', same.symm⟩

include functional slots in
theorem Asks.Sound.upperAt {asks : Asks} (external : asks.Sound Run R table ρ) {id n}
    (found : asks.upperAt id = some n) : ∃ v k, Reads Run R.bool table ρ id v ∧ R.nat v = some k ∧ k ≤ n := by
  rcases Asks.upperAt_source found with direct | ⟨a,alias,bound⟩
  · exact external.upper _ _ direct
  · obtain ⟨x,y,rx,ry,same⟩ := external.numberSource _ _ alias
    obtain ⟨v,k,rv,num,le⟩ := external.upper _ _ bound
    cases Reads.functionalOn functional slots ry rv
    exact ⟨x,k,rx,same.trans num,le⟩

end

end Zkc.Core.BodyAnalysis

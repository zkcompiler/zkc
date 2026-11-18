module

public import Zkc.Core.Program.BitTree
public import Zkc.Core.Program.Stepped

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 1: identifiers, the table, readings.

An identifier is a leaf or a value, in two spaces (`Ident`). The table holds applications of
shared operations, each with the positions of its results, and selections (`Form`, `Entry`,
`Table`); it only grows. Only leaves have values of their own (`Leaves`); what any identifier
is worth is read from the leaves through the table (`Reads`): a leaf reads its value, a result
of an application reads what the written operation gives on what its operands read, and a
selection reads what the chosen one of its two operands reads. A selection is lazy: the
operand that is not chosen need not read.

Definitions are given in full. What is to be proved of them is stated as propositions
(`…Statement`), which this file only type-checks.
-/

namespace Zkc.Core.BodyAnalysis

variable {Raw α : Type}

open FactCheck (factDepth mixNumbers applicationKey)

/-! ## Identifiers -/

/-- An identifier: a leaf (an input, a result of an operation kept in order, what an iteration
gives) or a value (a result of an entry of the table). The two are numbered apart. -/
inductive Ident where
  | leaf (number : Nat)
  | val (number : Nat)
deriving DecidableEq, Repr

/-- A number for an identifier, different for different identifiers: by it the table places an
entry, and the operands of an operation that commutes are put in one order. -/
def Ident.key : Ident → Nat
  | .leaf n => 2 * n
  | .val n => 2 * n + 1

theorem Ident.key_injective : ∀ {a b : Ident}, a.key = b.key → a = b
  | .leaf _, .leaf _, h => by simp only [Ident.key] at h; rw [Nat.eq_of_mul_eq_mul_left (by decide) h]
  | .val _, .val _, h => by
      simp only [Ident.key, Nat.add_right_cancel_iff] at h
      rw [Nat.eq_of_mul_eq_mul_left (by decide) h]
  | .leaf a, .val b, h => by
      simp only [Ident.key] at h
      exact absurd (congrArg (· % 2) h) (by simp [Nat.mul_mod_right])
  | .val a, .leaf b, h => by
      simp only [Ident.key] at h
      exact absurd (congrArg (· % 2) h) (by simp [Nat.mul_mod_right])

/-- Consecutive values. -/
def Ident.vals (lo count : Nat) : List Ident := (List.range' lo count).map Ident.val

/-- Consecutive leaves. -/
def Ident.leaves (lo count : Nat) : List Ident := (List.range' lo count).map Ident.leaf

/-! ## The table -/

/-- What an entry of the table says its values are: a written operation applied to operand
identifiers, in their order; or the selection, by a condition, of one of two identifiers. -/
inductive Form (Raw : Type) where
  | app (written : Raw) (args : List Ident)
  | select (condition first second : Ident)
deriving DecidableEq

/-- An entry of the table: a form and its values, `lo` to `lo + count - 1`. An application has
one value for each result, by position; a selection has one. -/
structure Entry (Raw : Type) where
  form : Form Raw
  lo : Nat
  count : Nat

section
variable {Raw : Type}

/-- The identifiers of an entry: its values, `lo` to `lo + count - 1`. -/
def Entry.ids (e : Entry Raw) : List Ident := Ident.vals e.lo e.count

/-- Where the table places a form, to find it. -/
def Form.key (place : Raw → Nat) : Form Raw → Nat
  | .app written args => applicationKey (place written) (args.map Ident.key)
  | .select condition first second => mixNumbers 0 [condition.key, first.key, second.key]

/-- Places an entry at each of the numbers. -/
def placeAll (e : Entry Raw) : List Nat → BitTree (Entry Raw) → BitTree (Entry Raw)
  | [], t => t
  | n :: ns, t => placeAll e ns (t.insert factDepth n e)

theorem mem_placeAll (e : Entry Raw) : ∀ (ns : List Nat) (t : BitTree (Entry Raw)) (x : Entry Raw),
    x ∈ placeAll e ns t → x ∈ t ∨ x = e
  | [], _, _, m => Or.inl m
  | n :: ns, t, x, m => by
      rcases mem_placeAll e ns _ x m with m | same
      · exact BitTree.mem_insert _ _ _ _ x m
      · exact Or.inr same

end

/-- Both indexes contain only members of the authoritative, newest-first entry list. -/
structure EntryBuckets (Raw : Type) (entries : List (Entry Raw)) where
  initial : List (Entry Raw)
  initial_mem : ∀ e, e ∈ initial → e ∈ entries
  byForm : BitTree (Entry Raw)
  byValue : BitTree (Entry Raw)
  forms : ∀ e, e ∈ byForm → e ∈ entries
  values : ∀ e, e ∈ byValue → e ∈ entries

def EntryBuckets.start (es : List (Entry Raw)) : EntryBuckets Raw es :=
  ⟨es, fun _ => id, .leaf [], .leaf [], fun e m => (BitTree.not_mem_empty e m).elim,
    fun e m => (BitTree.not_mem_empty e m).elim⟩

def EntryBuckets.add {es : List (Entry Raw)} (b : EntryBuckets Raw es)
    (place : Raw → Nat) (e : Entry Raw) : EntryBuckets Raw (e :: es) where
  initial := b.initial
  initial_mem x m := List.mem_cons_of_mem _ (b.initial_mem x m)
  byForm := b.byForm.insert factDepth (e.form.key place) e
  byValue := placeAll e (List.range' e.lo e.count) b.byValue
  forms x m := by
    rcases BitTree.mem_insert _ _ _ _ x m with m | rfl
    · exact List.mem_cons_of_mem _ (b.forms x m)
    · exact List.mem_cons_self
  values x m := by
    rcases mem_placeAll e _ _ x m with m | rfl
    · exact List.mem_cons_of_mem _ (b.values x m)
    · exact List.mem_cons_self

inductive EntryIndex (Raw : Type) (entries : List (Entry Raw)) where
  | flat (remaining : Nat)
  | indexed (buckets : EntryBuckets Raw entries)

/-- Scan the existing entries while their number and their total result arity fit in one
index path's depth. Charging at least one unit per entry also covers zero-result operations.
The initial segment stays flat. Later entries go into the indexes and shadow that segment,
so a table that just exceeds the budget never has to reinsert its history. -/
def EntryIndex.add {es : List (Entry Raw)} (place : Raw → Nat) (e : Entry Raw) :
    EntryIndex Raw es → EntryIndex Raw (e :: es)
  | .flat remaining =>
    let charge := max 1 e.count
    if charge ≤ remaining then .flat (remaining - charge)
    else .indexed ((EntryBuckets.start es).add place e)
  | .indexed b => .indexed (b.add place e)

structure Table (Raw : Type) where
  place : Raw → Nat
  entries : List (Entry Raw)
  index : EntryIndex Raw entries

instance {Raw : Type} : Membership (Entry Raw) (Table Raw) := ⟨fun t e => e ∈ t.entries⟩

section
variable {Raw : Type}

/-- The table without entries. -/
def Table.empty (place : Raw → Nat) : Table Raw := ⟨place, [], .flat factDepth⟩

/-- The table with an entry made. -/
def Table.add (e : Entry Raw) (tbl : Table Raw) : Table Raw :=
  ⟨tbl.place, e :: tbl.entries, tbl.index.add tbl.place e⟩

/-- Search the newest bucket first. The bounded initial segment is shared by both indexes. -/
@[inline] def Table.search (tbl : Table Raw) (probe : List (Entry Raw) → Option α)
    (bucket : EntryBuckets Raw tbl.entries → List (Entry Raw)) : Option α :=
  match tbl.index with
  | .flat _ => probe tbl.entries
  | .indexed b => (probe (bucket b)).orElse fun _ => probe b.initial

theorem Table.search_spec (tbl : Table Raw) {probe : List (Entry Raw) → Option α}
    {bucket : EntryBuckets Raw tbl.entries → List (Entry Raw)} {answer : α} {P : α → Prop}
    (valid : ∀ b e, e ∈ bucket b → e ∈ tbl)
    (found : ∀ es, (∀ e, e ∈ es → e ∈ tbl) → probe es = some answer → P answer)
    (hit : tbl.search probe bucket = some answer) : P answer := by
  unfold search at hit
  split at hit
  · exact found _ (fun _ => id) hit
  · next b _ =>
    cases first : probe (bucket b) with
    | some a => exact found _ (valid b) (first.trans (by simpa [first] using hit))
    | none => exact found _ b.initial_mem (by simpa [first] using hit)

/-- Check operand IDs before invoking the dialect's potentially structural equality on raw ops. -/
def Form.matches [DecidableEq Raw] : Form Raw → Form Raw → Bool
  | .app op xs, .app other ys => xs == ys && decide (op = other)
  | .select c x y, .select d u v => c == d && x == u && y == v
  | _, _ => false

theorem Form.matches_iff [DecidableEq Raw] (a b : Form Raw) : a.matches b = true ↔ a = b := by
  cases a <;> cases b <;> simp [Form.matches, and_comm, and_assoc]

/-- The first value of the entry, among entries, with the form and the number of values. -/
def findIn [DecidableEq Raw] (form : Form Raw) (count : Nat) : List (Entry Raw) → Option Nat
  | [] => none
  | e :: es => if e.count == count && e.form.matches form then some e.lo else findIn form count es

/-- The first value of the entry with the form and the number of values: among the entries
placed where the form is. -/
def Table.find [DecidableEq Raw] (form : Form Raw) (count : Nat) (tbl : Table Raw) : Option Nat :=
  tbl.search (findIn form count) fun b => b.byForm.find factDepth (form.key tbl.place)

/-- The entry, among entries, that gives the value of a number. -/
def entryIn (n : Nat) : List (Entry Raw) → Option (Entry Raw)
  | [] => none
  | e :: es => if e.lo ≤ n ∧ n < e.lo + e.count then some e else entryIn n es

/-- The entry that gives the value of a number: among the entries placed at it. -/
def Table.entryOf (n : Nat) (tbl : Table Raw) : Option (Entry Raw) :=
  tbl.search (entryIn n) fun b => b.byValue.find factDepth n

/-- The form of an identifier, with the position of the identifier among the entry's values:
nothing for a leaf. It is how a domain reads an identifier. -/
def Table.formOf (tbl : Table Raw) : Ident → Option (Form Raw × Nat)
  | .leaf _ => none
  | .val n => (tbl.entryOf n).map fun e => (e.form, n - e.lo)

/-- One table has the entries of another. -/
def Table.Le (tbl tbl' : Table Raw) : Prop := ∀ e, e ∈ tbl → e ∈ tbl'

end

/-! ## Sharing -/

/-- The table and the number of the next value. -/
structure Values (Raw : Type) where
  table : Table Raw
  next : Nat

section
variable {Raw : Type}

/-- The entry that gives the values of a form, with the values after: the first entry with it,
found, or a new one, made at the next value. The values of the form are the entry's identifiers
(`Entry.ids`). -/
def Values.share [DecidableEq Raw] (form : Form Raw) (count : Nat) (v : Values Raw) :
    Entry Raw × Values Raw :=
  match v.table.find form count with
  | some lo => (⟨form, lo, count⟩, v)
  | none => (⟨form, v.next, count⟩, ⟨v.table.add ⟨form, v.next, count⟩, v.next + count⟩)

/-- The operands of a written operation in the order in which the table places its
applications: two operands of an operation that commutes with the smaller first, and every
other list as it is. -/
def placed (commutes : Bool) : List Ident → List Ident
  | [first, second] => if commutes = true ∧ second.key < first.key then [second, first] else [first, second]
  | others => others

/-- The entry that gives the values of a written operation applied to operands, with the values
after. -/
def Values.apply [DecidableEq Raw] (commutes : Raw → Bool) (written : Raw) (args : List Ident)
    (count : Nat) (v : Values Raw) : Entry Raw × Values Raw :=
  v.share (.app written (placed (commutes written) args)) count

/-- What a choice gives at one position: the common identifier when both regions return the
same one, and otherwise the selection of one of the two by the condition, the value of its
entry. -/
def Values.select [DecidableEq Raw] (condition first second : Ident) (v : Values Raw) :
    Ident × Values Raw :=
  if first = second then (first, v)
  else
    let made := v.share (.select condition first second) 1
    (.val made.1.lo, made.2)

/-- What a choice gives at every position. -/
def Values.selectAll [DecidableEq Raw] (condition : Ident) :
    List Ident → List Ident → Values Raw → List Ident × Values Raw
  | first :: firsts, second :: seconds, v =>
      let one := v.select condition first second
      let others := Values.selectAll condition firsts seconds one.2
      (one.1 :: others.1, others.2)
  | _, _, v => ([], v)

end

/-! ## Readings -/

/-- The values of the leaves. -/
abbrev Leaves (Val : Type) : Type := Nat → Option Val

/-- More leaves have values, and those that had one keep it. -/
def Leaves.Le {Val : Type} (ρ ρ' : Leaves Val) : Prop := ∀ n v, ρ n = some v → ρ' n = some v

section
variable {Raw Val : Type} (Run : Raw → List Val → List Val → Prop) (truth : Val → Option Bool)
  (table : Table Raw)

mutual
  /-- What an identifier is worth, from the values of the leaves: a leaf has its value; a value
  of an application has what the written operation gives on what the operands read, at its
  position; a selection has what the chosen operand reads. -/
  inductive Reads (ρ : Leaves Val) : Ident → Val → Prop where
    | leaf {n : Nat} {v : Val} (valued : ρ n = some v) : Reads ρ (.leaf n) v
    | app {e : Entry Raw} {written : Raw} {args : List Ident} {j : Nat} {operands results : List Val}
        {v : Val} (known : e ∈ table) (form : e.form = .app written args) (position : j < e.count)
        (read : ReadsAll ρ args operands) (ran : Run written operands results)
        (result : results[j]? = some v) : Reads ρ (.val (e.lo + j)) v
    | select {e : Entry Raw} {condition first second : Ident} {chosen : Val} {which : Bool} {v : Val}
        (known : e ∈ table) (form : e.form = .select condition first second)
        (decided : Reads ρ condition chosen) (holds : truth chosen = some which)
        (read : Reads ρ (if which then first else second) v) : Reads ρ (.val e.lo) v
  /-- What identifiers are worth, in order. -/
  inductive ReadsAll (ρ : Leaves Val) : List Ident → List Val → Prop where
    | nil : ReadsAll ρ [] []
    | cons {id : Ident} {ids : List Ident} {v : Val} {vs : List Val} (first : Reads ρ id v)
        (others : ReadsAll ρ ids vs) : ReadsAll ρ (id :: ids) (v :: vs)
end

end

/-! ## What is to be proved of them -/

section
variable {Raw Val : Type}

/-- Result slots of distinct entries are disjoint, and every selection occupies exactly one slot. -/
structure Table.WF (table : Table Raw) : Prop where
  apart : ∀ e e', e ∈ table → e' ∈ table → ∀ j j', j < e.count → j' < e'.count →
    e.lo + j = e'.lo + j' → e = e'
  selections : ∀ e condition first second, e ∈ table → e.form = .select condition first second →
    e.count = 1

/-- Allocation additionally keeps every occupied result slot below the next free position. -/
structure Values.WF (v : Values Raw) : Prop where
  below : ∀ e, e ∈ v.table → e.lo + e.count ≤ v.next
  slots : v.table.WF

/-- A reading is kept when the table grows and more leaves get values. -/
def ReadsMonoStatement : Prop :=
  ∀ (Run : Raw → List Val → List Val → Prop) (truth : Val → Option Bool) (table table' : Table Raw)
    (ρ ρ' : Leaves Val), table.Le table' → ρ.Le ρ' →
    ∀ id v, Reads Run truth table ρ id v → Reads Run truth table' ρ' id v

/-- An identifier reads one value: for written operations that give one list of results, and a
table whose values are apart. No condition is asked of the leaves: leaves and values are two
spaces. -/
def ReadsFunctionalStatement : Prop :=
  ∀ (Run : Raw → List Val → List Val → Prop) (truth : Val → Option Bool),
    (∀ raw operands results results', Run raw operands results → Run raw operands results' →
      results = results') →
    ∀ (v : Values Raw), v.WF → ∀ (ρ : Leaves Val) id x y,
      Reads Run truth v.table ρ id x → Reads Run truth v.table ρ id y → x = y

/-- Sharing keeps the table's entries and its well-formedness, and gives values below the next. -/
def ShareGrowsStatement : Prop :=
  ∀ [DecidableEq Raw] (form : Form Raw) (count : Nat) (v : Values Raw), v.WF →
    (∀ condition first second, form = .select condition first second → count = 1) →
    v.table.Le (v.share form count).2.table ∧ (v.share form count).2.WF ∧
      v.next ≤ (v.share form count).2.next

/-- The entry of a shared application is in the table after sharing, and its values read what
the written operation gives on what the operands read, whether it was found or made. Nothing is
asked of the entry but that the operands read: there is nothing to fill. -/
def ShareReadsStatement : Prop :=
  ∀ [DecidableEq Raw] (Run : Raw → List Val → List Val → Prop) (truth : Val → Option Bool)
    (written : Raw) (args : List Ident) (count : Nat) (v : Values Raw) (ρ : Leaves Val)
    (operands results : List Val),
    ReadsAll Run truth v.table ρ args operands → Run written operands results →
    results.length = count →
    (v.share (.app written args) count).1 ∈ (v.share (.app written args) count).2.table ∧
      ReadsAll Run truth (v.share (.app written args) count).2.table ρ
        (v.share (.app written args) count).1.ids results

/-- What a choice gives reads what the region that ran returned: the first when the condition
reads true, the second when it reads false. Only that one need read. -/
def SelectReadsStatement : Prop :=
  ∀ [DecidableEq Raw] (Run : Raw → List Val → List Val → Prop) (truth : Val → Option Bool)
    (condition first second : Ident) (v : Values Raw) (ρ : Leaves Val) (chosen : Val)
    (which : Bool) (x : Val),
    Reads Run truth v.table ρ condition chosen → truth chosen = some which →
    Reads Run truth v.table ρ (if which then first else second) x →
    Reads Run truth (v.select condition first second).2.table ρ
      (v.select condition first second).1 x

end

end Zkc.Core.BodyAnalysis

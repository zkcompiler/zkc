module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.BitTree
public import Zkc.Core.Program.Refusal

@[expose] public section

/-!
The table of applications, the state that carries it, and the identifiers of the names in scope.

A value has an identifier that is never reused. An application of a written operation to operand
identifiers has the result identifiers that the table gives it: those of the first application
of the same operation to the same identifiers, in their order, or new ones (`share`). The table
is never scoped: an entry says what a result is, not that it was computed. A lookup in the table
reads the leaf of a tree placed by a number computed from the number given for the written
operation and from its operands' identifiers, and the entry of an identifier the leaf placed by
that identifier (`Program/BitTree.lean`): a list, read as a list; nothing else depends on that.

The state (`St`) carries the table, the next identifier, and the refusals and the bounds of
loops that the analysis finds. The identifiers of the names in scope are a map from names
to identifiers (`Ctx Nat`): where a term binds names to its context, the same names are bound to
the new identifiers, a later name hiding an earlier one as in the context (`bindIds`).

The value form of a term (`Value/Skeleton.lean`) and the walk of the analysis that builds it
(`Facts/Walk.lean`) are built on this table; its declarations are in the namespace `FactCheck`.
-/

namespace Zkc.Core

namespace FactCheck

/-! ## The table -/

/-- An entry of the table: a written operation applied to operand identifiers, in their order,
and the identifiers of its results, `lo` to `lo + count - 1`. -/
structure Entry (Raw : Type) where
  written : Raw
  args : List Nat
  lo : Nat
  count : Nat

/-- The depth of the trees of the table, here, and of what the analysis knows (`Known`,
`Facts/State.lean`): numbers that agree on these low bits share a leaf. -/
abbrev factDepth : Nat := 12

section
variable {Raw : Type}

/-- A number computed from naturals in order, from a number to start with, each multiplying
what came before by Knuth's multiplicative constant. -/
def mixNumbers (start : Nat) (ns : List Nat) : Nat :=
  ns.foldl (fun key n => key * 2654435761 + n + 1) start

/-- Where the table places an application, to find it: a number computed from the number that
the dialect gives for its written operation and from all of its operands' identifiers, in order,
so that applications that share their operands, or have none, fall in different leaves when
their written operations differ. -/
def applicationKey (written : Nat) (args : List Nat) : Nat := mixNumbers written args

/-- Places an entry at each of the identifiers. -/
def placeAll (e : Entry Raw) : List Nat → BitTree (Entry Raw) → BitTree (Entry Raw)
  | [], t => t
  | id :: ids, t => placeAll e ids (t.insert factDepth id e)

theorem mem_placeAll (e : Entry Raw) : ∀ (ids : List Nat) (t : BitTree (Entry Raw)) (x : Entry Raw),
    x ∈ placeAll e ids t → x ∈ t ∨ x = e
  | [], _, _, m => Or.inl m
  | id :: ids, t, x, m => by
      rcases mem_placeAll e ids _ x m with m | same
      · exact BitTree.mem_insert _ _ _ _ x m
      · exact Or.inr same

end

/-- The table: its entries, the latest first, and the same entries placed by the number that
`place` gives for their written operation and by their operands' identifiers
(`applicationKey`), to find an application, and by each of their results' identifiers, to find
what gives an identifier. The walk reads only the placed entries; every placed entry is an
entry. -/
structure Table (Raw : Type) where
  place : Raw → Nat
  entries : List (Entry Raw)
  byApplication : BitTree (Entry Raw)
  byResult : BitTree (Entry Raw)
  applications : ∀ e, e ∈ byApplication → e ∈ entries
  results : ∀ e, e ∈ byResult → e ∈ entries

instance {Raw : Type} : Membership (Entry Raw) (Table Raw) := ⟨fun t e => e ∈ t.entries⟩

section
variable {Raw : Type}

/-- The table without entries, which places applications by the number that `place` gives for
their written operation. -/
def Table.empty (place : Raw → Nat) : Table Raw :=
  ⟨place, [], .leaf [], .leaf [], fun e m => (BitTree.not_mem_empty e m).elim,
    fun e m => (BitTree.not_mem_empty e m).elim⟩

/-- The table with an entry made. -/
def Table.add (e : Entry Raw) (tbl : Table Raw) : Table Raw where
  place := tbl.place
  entries := e :: tbl.entries
  byApplication :=
    tbl.byApplication.insert factDepth (applicationKey (tbl.place e.written) e.args) e
  byResult := placeAll e (List.range' e.lo e.count) tbl.byResult
  applications x m := by
    rcases BitTree.mem_insert _ _ _ _ x m with m | same
    · exact List.mem_cons_of_mem _ (tbl.applications x m)
    · rw [same]; exact List.mem_cons_self
  results x m := by
    rcases mem_placeAll e _ _ x m with m | same
    · exact List.mem_cons_of_mem _ (tbl.results x m)
    · rw [same]; exact List.mem_cons_self

/-- The first result of the entry, among entries, of the written operation applied to the
operands, with the number of results: compared by its operands first. -/
def findIn [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat) :
    List (Entry Raw) → Option Nat
  | [] => none
  | e :: es =>
      if e.args = args ∧ e.count = count ∧ e.written = written then some e.lo
      else findIn written args count es

/-- The first result of the entry of the written operation applied to the operands, with the
number of results: among the entries placed where the operands are. -/
def Table.find [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat)
    (tbl : Table Raw) : Option Nat :=
  findIn written args count
    (tbl.byApplication.find factDepth (applicationKey (tbl.place written) args))

/-- The entry, among entries, that gives an identifier. -/
def entryIn (id : Nat) : List (Entry Raw) → Option (Entry Raw)
  | [] => none
  | e :: es => if e.lo ≤ id ∧ id < e.lo + e.count then some e else entryIn id es

/-- The entry that gives an identifier: among the entries placed at it. -/
def Table.entryOf (id : Nat) (tbl : Table Raw) : Option (Entry Raw) :=
  entryIn id (tbl.byResult.find factDepth id)

theorem findIn_spec [DecidableEq Raw] {w : Raw} {args : List Nat} {count lo : Nat} :
    ∀ {es : List (Entry Raw)}, findIn w args count es = some lo →
      ∃ e, e ∈ es ∧ e.written = w ∧ e.args = args ∧ e.count = count ∧ e.lo = lo
  | [], h => by simp [findIn] at h
  | e :: es, h => by
      simp only [findIn] at h
      split at h
      · next hr =>
          cases h
          exact ⟨e, List.mem_cons_self, hr.2.2, hr.1, hr.2.1, rfl⟩
      · obtain ⟨e', m, r⟩ := findIn_spec h
        exact ⟨e', List.mem_cons_of_mem _ m, r⟩

theorem Table.find_spec [DecidableEq Raw] {w : Raw} {args : List Nat} {count lo : Nat}
    {tbl : Table Raw} (h : tbl.find w args count = some lo) :
    ∃ e, e ∈ tbl ∧ e.written = w ∧ e.args = args ∧ e.count = count ∧ e.lo = lo := by
  obtain ⟨e, m, r⟩ := findIn_spec h
  exact ⟨e, tbl.applications e (BitTree.mem_of_find _ _ _ e m), r⟩

theorem entryIn_spec {id : Nat} : ∀ {es : List (Entry Raw)} {e : Entry Raw},
    entryIn id es = some e → e ∈ es ∧ e.lo ≤ id ∧ id < e.lo + e.count
  | [], _, h => by simp [entryIn] at h
  | e' :: es, e, h => by
      simp only [entryIn] at h
      split at h
      · next hr =>
          cases h
          exact ⟨List.mem_cons_self, hr⟩
      · obtain ⟨m, r⟩ := entryIn_spec h
        exact ⟨List.mem_cons_of_mem _ m, r⟩

theorem Table.entryOf_spec {id : Nat} {tbl : Table Raw} {e : Entry Raw}
    (h : tbl.entryOf id = some e) : e ∈ tbl ∧ e.lo ≤ id ∧ id < e.lo + e.count := by
  obtain ⟨m, r⟩ := entryIn_spec h
  exact ⟨tbl.results e (BitTree.mem_of_find _ _ _ e m), r⟩

end

/-! ## The state -/

/-- What the walk carries through every region: the table, the next identifier, the refusals
and the bounds of loops found so far (the latest first). -/
structure St (T Raw : Type) where
  table : Table Raw
  next : Nat
  refusals : List (Refusal T Raw)
  bounds : List (Place × Nat)

section
variable {T Raw : Type}

/-- New identifiers. -/
def fresh (count : Nat) (st : St T Raw) : List Nat × St T Raw :=
  (List.range' st.next count, { st with next := st.next + count })

/-- The results of the written operation applied to the operands: those of the first such
application, or new ones with an entry. -/
def share [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat) (st : St T Raw) :
    List Nat × St T Raw :=
  match st.table.find written args count with
  | some lo => (List.range' lo count, st)
  | none =>
      (List.range' st.next count,
        { st with table := st.table.add ⟨written, args, st.next, count⟩,
                  next := st.next + count })

end

/-! ## The identifiers of the names in scope -/

/-- The identifier of a name in scope. In the walk every name in scope has one (`InScope`,
`Value/Valuation.lean`), so the `0` of a name without one is never read. -/
def idOf (ids : Ctx Nat) (name : Name) : Nat := (ids.find? name).getD 0

/-- The identifiers of variables. -/
def idsOf {α : Type} {Γ : Ctx α} (ids : Ctx Nat) : {items : List α} → HList (Var Γ) items →
    List Nat
  | [], .nil => []
  | _ :: _, .cons x rest => idOf ids x.name :: idsOf ids rest

/-- The identifiers of the names in scope with the names of a binding bound to identifiers, in
order, as `Ctx.extend` binds them to their types: a later name hides an earlier one. The walk
gives as many identifiers as names (`fresh`, `FactCheck.share_length`); names left without one
would stay as they were. -/
def bindIds {α : Type} (ids : Ctx Nat) : {types : List α} → Names types → List Nat → Ctx Nat
  | [], .nil, _ => ids
  | _ :: _, .cons name rest, i :: is => bindIds (ids.insert name i) rest is
  | _ :: _, .cons _ _, [] => ids

end FactCheck

end Zkc.Core

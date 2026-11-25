module

public import Zkc.Core.Program.Links
public import Zkc.Subject.Coverage.Pending
public import Zkc.Vocabulary.Project

@[expose] public section

namespace Zkc.Subject.Coverage
open Zkc.Core Zkc.Vocabulary.Project

/-- Definition keys used by the body, including calls inside nested regions. -/
@[inline] def callees {V : Core.Vocabulary} : Definition V → List Key
  | .fn _ _ _ _ _ _ body _ => body.operations.filterMap fun
      | .call k => some k
      | _ => none
  | .protocol _ _ _ _ body => body.operations.filterMap fun
      | .apply k _ | .compute _ (.call k) => some k
      | _ => none

/-- The keys still required from earlier definitions, and the definitions already found. -/
structure Reach (V : Core.Vocabulary) where
  pending : Pending
  definitions : List (Definition V)

/-- Keep a requested body and replace every pending use of its key with its dependencies. -/
@[inline] def visit {V : Core.Vocabulary} (d : Definition V) (s : Reach V) : Reach V :=
  if s.pending.contains d.key then
    ⟨(callees d).foldl Pending.insert (s.pending.discharge d.key), d :: s.definitions⟩
  else s

def entries (root relation : Key) : Pending :=
  (Pending.empty.insert root).insert relation

/-- Admitted definitions follow their dependencies. Discharge a key when its body is
visited, then request that body's callees from the remaining prefix. -/
def reach {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) : Reach V :=
  p.definitions.foldr visit ⟨entries root relation, []⟩

/-- A path from either entry along stored function calls and protocol applications. -/
inductive Reachable {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) : Key → Prop
  | root : Reachable p root relation root
  | relation : Reachable p root relation relation
  | call {d k} : d ∈ p.definitions → Reachable p root relation d.key → k ∈ callees d →
      Reachable p root relation k

private def accounted {V : Core.Vocabulary} (s : Reach V) (k : Key) : Prop :=
  s.pending.contains k = true ∨ k ∈ s.definitions.map Definition.key

private theorem visit_keeps {V : Core.Vocabulary} (s : Reach V) (d : Definition V) (k : Key)
    (h : accounted s k) : accounted (visit d s) k := by
  unfold visit
  split
  next hit =>
    rcases h with h | h
    · by_cases eq : k = d.key
      · exact Or.inr (by simp [eq])
      · exact Or.inl ((Pending.contains_fold_insert ..).mpr <| Or.inr <|
          (s.pending.contains_discharge _ _ hit).mpr ⟨eq, h⟩)
    · exact Or.inr (List.mem_cons_of_mem _ h)
  · exact h

private theorem reach_spec {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) :
    let s := reach p root relation
    s.definitions ⊆ p.definitions ∧ accounted s root ∧ accounted s relation ∧
      ∀ d ∈ s.definitions, ∀ k ∈ callees d, accounted s k := by
  obtain ⟨ds⟩ := p
  unfold reach
  induction ds with
  | nil => simp [accounted, entries]
  | cons d ds ih =>
    simp only [List.foldr_cons]
    generalize ds.foldr visit (Reach.mk (entries root relation) []) = s at ih ⊢
    obtain ⟨sub, hr, hg, hc⟩ := ih
    refine ⟨?_, visit_keeps s d _ hr, visit_keeps s d _ hg, ?_⟩
    · unfold visit
      split
      · exact List.cons_subset_cons _ sub
      · exact List.Subset.trans sub (List.subset_cons_self ..)
    · intro e he k hk
      by_cases hit : s.pending.contains d.key = true
      · simp [visit, hit] at he
        rcases he with rfl | tail
        · apply Or.inl
          simp only [visit, hit, ↓reduceIte]
          exact (Pending.contains_fold_insert ..).mpr (.inl hk)
        · exact visit_keeps s d k (hc e tail k hk)
      · simp [visit, hit] at he
        exact visit_keeps s d k (hc e he k hk)

/-- Every selected body has a path, even in a program with an unresolved call. -/
theorem reachable_of_selected {V : Core.Vocabulary} {p : NamedProgram V} {root relation : Key}
    {d : Definition V} (selected : d ∈ (reach p root relation).definitions) :
    Reachable p root relation d.key := by
  let paths (s : Reach V) :=
    (∀ k, s.pending.contains k = true → Reachable p root relation k) ∧
    (∀ e ∈ s.definitions, Reachable p root relation e.key)
  have walk (ds : List (Definition V)) (sub : ds ⊆ p.definitions) :
      paths (ds.foldr visit ⟨entries root relation, []⟩) := by
    induction ds with
    | nil =>
      constructor
      · intro k hk
        simp [entries] at hk
        rcases hk with rfl | rfl
        · exact .relation
        · exact .root
      · simp
    | cons e ds ih =>
      have ⟨pending, kept⟩ := ih (List.Subset.trans (List.subset_cons_self ..) sub)
      simp only [List.foldr_cons]
      unfold visit
      split
      next hit =>
        constructor
        · intro k hk
          rcases (Pending.contains_fold_insert ..).mp hk with edge | rest
          · exact .call (sub (List.mem_cons_self ..)) (pending _ hit) edge
          · exact pending _ ((Pending.contains_discharge _ _ _ hit).mp rest).2
        · intro body member
          rcases List.mem_cons.mp member with rfl | old
          · exact pending _ hit
          · exact kept _ old
      · exact ⟨pending, kept⟩
  exact (walk _ (List.Subset.refl _)).2 _ selected

abbrev Nominal := Sum Zkc.Vocabulary.TypeKey Parameter
abbrev Row := Sum Zkc.Vocabulary.RowKey PrimitiveName

mutual
  /-- The first nominal sort in a type without a standard interpretation. -/
  def missingSort : LinkedType → Option Nominal
    | .nominal (.inl (.field .bls12381Fr)) | .nominal (.inl (.nonzero .bls12381Fr))
      | .nominal (.inl (.group .g1)) => none
    | .nominal k => some k
    | .seq t _ => missingSort t
    | .tuple ts | .record _ _ ts | .variant _ ts => missingSorts ts
    | .bool | .nat | .fin _ => none
  def missingSorts : Tys Nominal → Option Nominal
    | .nil => none
    | .cons t ts => missingSort t <|> missingSorts ts
end

/-- The formal library proves that this predicate agrees with its semantic row table. -/
def interpreted : Row → Bool
  | .inl (.group .scale (.group .g1)) => true
  | .inl (.group .add (.group .g1)) => true
  | .inl (.group .equal (.group .g1)) => true
  | .inl (.field .add .bls12381Fr .all) => true
  | .inl (.field .sub .bls12381Fr .all) => true
  | .inl (.field .mul .bls12381Fr .all) => true
  | .inl (.field .neg .bls12381Fr .all) => true
  | .inl (.field .equal .bls12381Fr .all) => true
  | .inl (.field .nonzero .bls12381Fr .all) => true
  | .inl (.field .isNonzero .bls12381Fr .all) => true
  | .inl (.field .inverse .bls12381Fr .nonzero) => true
  | .inl (.field .fromNonzero .bls12381Fr .nonzero) => true
  | .inl (.seq .add (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .sub (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .scale (.atom (.field .bls12381Fr)) (some _)) => true
  | .inl (.seq .sum (.atom (.field .bls12381Fr)) _) => true
  | .inl (.seq .equal (.atom (.field .bls12381Fr)) _) => true
  | _ => false

def positionSampled : Zkc.Vocabulary.Ty → LinkedType → Bool
  | .fin (n + 1), .fin m => m == n + 1
  | _, _ => false

def sampledType : Zkc.Vocabulary.Ty → LinkedType → Bool
  | .nominal (.field .bls12381Fr), .nominal (.inl (.field .bls12381Fr)) => true
  | .seq (.nominal (.field .bls12381Fr)) (some n),
      .seq (.nominal (.inl (.field .bls12381Fr))) (some m) => m == n
  | t, result => positionSampled t result

@[inline] def localSort {b : Bindings} : LocalRaw b.vocabulary → Option Nominal
  | .owned _ ts _ => ts.findSome? missingSort
  | .literal t _ => missingSort t
  | .row _ | .call _ => none

@[inline] def definitionSort {b : Bindings} : Definition b.vocabulary → Option Nominal
  | .fn _ ins outs _ _ _ body _ =>
    (ins ++ outs).findSome? missingSort <|> body.operations.findSome? (localSort (b := b))
  | .protocol _ _ ins outs body =>
    (ins ++ outs).findSome? (fun port => missingSort port.ty) <|> body.operations.findSome? fun
      | .compute _ op => localSort (b := b) op
      | .event _ t => missingSort t
      | _ => none

inductive Missing where
  | definition (key : Key)
  | sort (key : Nominal)
  | row (key : Row)
  | law (key : Zkc.Vocabulary.LawKey) (result : LinkedType)

/-- The first unsupported row, law or sort of the selected definitions. -/
def missingMeaning {b : Bindings} (defs : List (Definition b.vocabulary)) : Option Missing := do
  let reached : NamedProgram b.vocabulary := ⟨defs⟩
  if let some k := reached.rows.find? (!interpreted ·) then return .row k
  if let some (.uniform t, result) := reached.laws.find? (fun (.uniform t, result) => !sampledType t result)
  then return .law (.uniform t) result
  return .sort (← defs.findSome? (definitionSort (b := b)))

/-- Read both entry points from the same program. An outstanding key has no body in
the required prefix. Diagnose an unsupported operation before its types. -/
def missing {b : Bindings} (p : NamedProgram b.vocabulary) (root relation : Key) : Option Missing :=
  let s := reach p root relation
  match s.pending.remaining with
  | some k => some (.definition k)
  | none => missingMeaning s.definitions

/-- Both entry points have stored bodies, and each retained body has all its callees. -/
structure Closed {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key)
    (defs : List (Definition V)) : Prop where
  stored : defs ⊆ p.definitions
  root_mem : root ∈ defs.map Definition.key
  relation_mem : relation ∈ defs.map Definition.key
  callees_mem : ∀ d ∈ defs, ∀ k ∈ callees d, k ∈ defs.map Definition.key

/-- With unambiguous keys, a closed selection contains the stored body at every call path. -/
theorem Closed.mem_of_reachable {V : Core.Vocabulary} {p : NamedProgram V} {root relation : Key}
    {defs : List (Definition V)} (closed : Closed p root relation defs)
    (unique : ∀ d ∈ p.definitions, ∀ e ∈ p.definitions, d.key = e.key → d = e)
    {d : Definition V} (stored : d ∈ p.definitions) (path : Reachable p root relation d.key) :
    d ∈ defs := by
  have body {e : Definition V} (he : e ∈ p.definitions) (key : e.key ∈ defs.map Definition.key) :
      e ∈ defs := by
    obtain ⟨found, mem, eq⟩ := List.mem_map.mp key
    exact unique found (closed.stored mem) e he eq ▸ mem
  have keys {k : Key} (h : Reachable p root relation k) : k ∈ defs.map Definition.key := by
    induction h with
    | root => exact closed.root_mem
    | relation => exact closed.relation_mem
    | call he _ edge ih => exact closed.callees_mem _ (body he ih) _ edge
  exact body stored (keys path)

private theorem remaining_none {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) : (reach p root relation).pending.remaining = none := by
  unfold missing at ok
  dsimp only at ok
  split at ok
  · contradiction
  · assumption

theorem closed_of_missing {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) :
    Closed p root relation (reach p root relation).definitions := by
  have ⟨sub, hr, hg, hc⟩ := reach_spec p root relation
  have clear := (reach p root relation).pending.contains_of_remaining_none (remaining_none ok)
  simp only [accounted, clear, Bool.false_eq_true, false_or] at hr hg hc
  exact ⟨sub, hr, hg, hc⟩

/-- For covered entries with unique keys, the walk selects exactly the stored bodies
reachable from the root or the relation. -/
theorem selected_iff_reachable {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none)
    (unique : ∀ d ∈ p.definitions, ∀ e ∈ p.definitions, d.key = e.key → d = e)
    {d : Definition b.vocabulary} (stored : d ∈ p.definitions) :
    d ∈ (reach p root relation).definitions ↔ Reachable p root relation d.key :=
  ⟨reachable_of_selected, (closed_of_missing ok).mem_of_reachable unique stored⟩

theorem interpreted_of_missing {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) :
    ∀ k ∈ (NamedProgram.mk (reach p root relation).definitions).rows, interpreted k = true := by
  have done := remaining_none ok
  unfold missing at ok
  dsimp only at ok
  simp only [done] at ok
  let defs := (reach p root relation).definitions
  change missingMeaning defs = none at ok
  have absent : (NamedProgram.mk defs).rows.find? (!interpreted ·) = none := by
    cases found : (NamedProgram.mk defs).rows.find? (!interpreted ·) with
    | none => rfl
    | some k => simp [missingMeaning, found] at ok
  intro k member
  simpa using List.find?_eq_none.mp absent k member

end Zkc.Subject.Coverage

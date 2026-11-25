module

public import Zkc.Core.Program.Links
public import Zkc.Vocabulary.Project

@[expose] public section

namespace Zkc.Subject.Coverage
open Zkc.Core Zkc.Vocabulary.Project

/-- Definition keys used by the body, including calls inside nested regions. -/
def callees {V : Core.Vocabulary} : Definition V → List Key
  | .fn _ _ _ _ _ _ body _ => body.operations.filterMap fun
      | .call k => some k
      | _ => none
  | .protocol _ _ _ _ body => body.operations.filterMap fun
      | .apply k _ | .compute _ (.call k) => some k
      | _ => none

/-- The keys still required from earlier definitions, and the definitions already found. -/
structure Reach (V : Core.Vocabulary) where
  pending : List Key
  definitions : List (Definition V)

/-- Keep a requested body and replace every pending use of its key with its dependencies. -/
def visit {V : Core.Vocabulary} (d : Definition V) (s : Reach V) : Reach V :=
  if d.key ∈ s.pending then
    ⟨callees d ++ s.pending.filter (· != d.key), d :: s.definitions⟩
  else s

/-- Admitted definitions follow their dependencies. Discharge a key when its body is
visited, then request that body's callees from the remaining prefix. -/
def reach {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) : Reach V :=
  p.definitions.foldr visit ⟨[root, relation], []⟩

/-- A path from either entry along stored function calls and protocol applications. -/
inductive Reachable {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) : Key → Prop
  | root : Reachable p root relation root
  | relation : Reachable p root relation relation
  | call {d k} : d ∈ p.definitions → Reachable p root relation d.key → k ∈ callees d →
      Reachable p root relation k

private def accounted {V : Core.Vocabulary} (s : Reach V) (k : Key) : Prop :=
  k ∈ s.pending ∨ k ∈ s.definitions.map Definition.key

private theorem visit_keeps {V : Core.Vocabulary} (s : Reach V) (d : Definition V) (k : Key)
    (h : accounted s k) : accounted (visit d s) k := by
  unfold visit
  split
  · rcases h with h | h
    · by_cases eq : k = d.key
      · exact Or.inr (by simp [eq])
      · exact Or.inl (List.mem_append_right _ (List.mem_filter.mpr ⟨h, by simpa using eq⟩))
    · exact Or.inr (List.mem_cons_of_mem _ h)
  · exact h

private theorem reach_spec {V : Core.Vocabulary} (p : NamedProgram V) (root relation : Key) :
    let s := reach p root relation
    s.definitions ⊆ p.definitions ∧ accounted s root ∧ accounted s relation ∧
      ∀ d ∈ s.definitions, ∀ k ∈ callees d, accounted s k := by
  obtain ⟨ds⟩ := p
  unfold reach
  induction ds with
  | nil => simp [accounted]
  | cons d ds ih =>
    simp only [List.foldr_cons]
    generalize ds.foldr visit (Reach.mk [root, relation] []) = s at ih ⊢
    obtain ⟨sub, hr, hg, hc⟩ := ih
    refine ⟨?_, visit_keeps s d _ hr, visit_keeps s d _ hg, ?_⟩
    · unfold visit
      split
      · exact List.cons_subset_cons _ sub
      · exact List.Subset.trans sub (List.subset_cons_self ..)
    · intro e he k hk
      by_cases hit : d.key ∈ s.pending
      · simp [visit, hit] at he
        rcases he with rfl | tail
        · apply Or.inl
          simp only [visit, hit, ↓reduceIte]
          exact List.mem_append_left _ hk
        · exact visit_keeps s d k (hc e tail k hk)
      · simp [visit, hit] at he
        exact visit_keeps s d k (hc e he k hk)

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

def localSort {b : Bindings} : LocalRaw b.vocabulary → Option Nominal
  | .owned _ ts _ => ts.findSome? missingSort
  | .literal t _ => missingSort t
  | .row _ | .call _ => none

def definitionSort {b : Bindings} : Definition b.vocabulary → Option Nominal
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
  match s.pending with
  | k :: _ => some (.definition k)
  | [] => missingMeaning s.definitions

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

private theorem pending_nil {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) : (reach p root relation).pending = [] := by
  unfold missing at ok
  dsimp only at ok
  split at ok
  · contradiction
  · assumption

theorem closed_of_missing {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) :
    Closed p root relation (reach p root relation).definitions := by
  have ⟨sub, hr, hg, hc⟩ := reach_spec p root relation
  simp only [accounted, pending_nil ok, List.not_mem_nil, false_or] at hr hg hc
  exact ⟨sub, hr, hg, hc⟩

theorem interpreted_of_missing {b : Bindings} {p : NamedProgram b.vocabulary} {root relation : Key}
    (ok : missing p root relation = none) :
    ∀ k ∈ (NamedProgram.mk (reach p root relation).definitions).rows, interpreted k = true := by
  have done := pending_nil ok
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

module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Verifier

@[expose] public section

/-! Dependent oracle composition for cached scalar trees and arbitrary other requests.
Every primitive occurrence makes a logical macro query. The lazy macro oracle owns the shared
cache, including verifier accesses; unqueried coordinates are never conditionally resampled.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open OracleComp OracleSpec MeasureTheory
noncomputable section
@[reducible] local instance dependentSampler {D : Type} [Fintype D] {T : D → Type}
    [∀ d, SampleableType (T d)] : SampleableType ((d : D) → T d) := by
  let : ∀ d, Fintype (T d) := fun d ↦ Fintype.ofFinite (T d)
  exact SampleableType.piOfFintype T
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α

/-- A finite cover of an adaptive dependent oracle computation. The cover ranges over every
reply branch and may contain additional independent cells. -/
theorem eager_cover {D C α : Type} {R : D → Type} {T : C → Type}
    [Fintype C] [∀ d, SampleableType (R d)] [∀ c, SampleableType (T c)]
    (program : OracleComp (ofFn R) α) (keys : Finset D)
    (covered : AllQueriesSatisfy program (· ∈ keys))
    (cell : keys → C) (distinct : Function.Injective cell)
    (read : (key : keys) → T (cell key) ≃ R key.val)
    (answers : ((c : C) → T c) → (d : D) → R d)
    (agrees : ∀ table key, answers table key.val = read key (table (cell key))) :
    (simulateQ randomOracle program).run' ∅ =ᵈ
      (do let table ← $ᵗ ((c : C) → T c)
          pure (evalWithAnswerFn (QueryImpl.ofFn (answers table)) program)) := by
  let : MeasurableSpace α := ⊤
  let : DecidableEq keys := fun a b ↦ a.instDecidableEq b
  let keysMap : ZkcSecurity.Oracle.Renaming (fun key : keys ↦ R key.val) T :=
    { cell := fun key ↦ some (cell key)
      injective := fun a b target ha hb ↦ distinct (Option.some.inj (ha.trans hb.symm))
      read := fun key target hit ↦ by
        obtain rfl := Option.some.inj hit
        exact read key
      single := fun _ impossible ↦ by cases impossible }
  let restricted := restrictQueries keys program covered
  have empty : restrictCache keys (∅ : (ofFn R).QueryCache) = ∅ := by ext key; rfl
  have law := keysMap.evalDistEq_translate restricted
  have restriction := randomOracle_restrictQueries keys program covered
    (∅ : (ofFn R).QueryCache)
  rw [empty] at restriction
  rw [← restriction]
  apply law.symm.trans
  apply EvalDistEq.of_evalDist_eq
  rw [evalDist_simulateQ_randomOracle_run'_eq_completeTable]
  simp only [completeTable_empty]
  apply evalDist_bind_congr
  intro table
  rw [keysMap.evalWithAnswerFn_translate]
  have assignment : keysMap.pullback table = fun key : keys ↦ answers table key.val := by
    funext key
    rw [ZkcSecurity.Oracle.Renaming.pullback_some keysMap table rfl]
    exact (agrees table key).symm
  rw [assignment, evalWithAnswerFn_restrictQueries]

variable {Root Coord Raw Other : Type} {R : Other → Type}

/-- The non-scalar summand has its own dependent answer range, unchanged. -/
abbrev primitiveRange : (Root × Coord) ⊕ Other → Type
  | .inl _ => Raw
  | .inr key => R key

abbrev macroRange : Root ⊕ Other → Type
  | .inl _ => Coord → Raw
  | .inr key => R key

/-- Each scalar occurrence asks its full tree, and every other request asks its original cell.
Repeated logical calls remain visible even when the shared lazy cache supplies the answer. -/
def ask : (key : (Root × Coord) ⊕ Other) →
    OracleComp (ofFn (@macroRange Root Coord Raw Other R))
      (primitiveRange (Raw := Raw) (R := R) key)
  | .inl (root, coordinate) => do
      let tree ← (ofFn (@macroRange Root Coord Raw Other R)).query (.inl root)
      pure (tree coordinate)
  | .inr key => liftM ((ofFn (@macroRange Root Coord Raw Other R)).query (.inr key))

def translate {α : Type} (program : OracleComp
    (ofFn (@primitiveRange Root Coord Raw Other R)) α) :
    OracleComp (ofFn (@macroRange Root Coord Raw Other R)) α := simulateQ ask program

def flatten (table : (key : Root ⊕ Other) → macroRange (Coord := Coord) (Raw := Raw) (R := R) key) :
    (key : (Root × Coord) ⊕ Other) → primitiveRange (Raw := Raw) (R := R) key
  | .inl (root, coordinate) => table (.inl root) coordinate
  | .inr key => table (.inr key)

theorem translate_table {α : Type} (program : OracleComp
    (ofFn (@primitiveRange Root Coord Raw Other R)) α)
    (table : (key : Root ⊕ Other) → macroRange (Coord := Coord) (Raw := Raw) (R := R) key) :
    evalWithAnswerFn (QueryImpl.ofFn table) (translate program) =
      evalWithAnswerFn (QueryImpl.ofFn (flatten table)) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind key next ih =>
    cases key with
    | inl pair =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask, evalWithAnswerFn_bind]
      exact ih _
    | inr key =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask, evalWithAnswerFn_bind]
      exact ih _

/-- Currying only the scalar summand is a bijection of complete dependent answer tables. -/
def tableEquiv :
    ((key : Root ⊕ Other) → macroRange (Coord := Coord) (Raw := Raw) (R := R) key) ≃
      ((key : (Root × Coord) ⊕ Other) → primitiveRange (Raw := Raw) (R := R) key) where
  toFun := flatten
  invFun table := fun key ↦ match key with
    | .inl root => fun coordinate ↦ table (.inl (root, coordinate))
    | .inr key => table (.inr key)
  left_inv table := by funext key; cases key <;> rfl
  right_inv table := by funext key; cases key <;> rfl

/-- Every occurrence, including every other request and every repeat, retains its cost. -/
theorem translate_budget {α : Type} (program : OracleComp
    (ofFn (@primitiveRange Root Coord Raw Other R)) α) (budget : Nat)
    (bounded : IsTotalQueryBound program budget) :
    IsTotalQueryBound (translate program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => exact bounded
  | query_bind key next ih =>
    obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
    cases key with
    | inl pair =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask, bind_assoc]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨positive, fun tree ↦ ih _ _ (rest _)⟩
    | inr key =>
      simp only [translate, simulateQ_bind, simulateQ_spec_query, ask]
      exact isTotalQueryBound_query_bind_iff.mpr
        ⟨positive, fun reply ↦ ih _ _ (rest reply)⟩

/-- The macro cell of a primitive occurrence; other requests retain their exact identity. -/
def rootOf : (Root × Coord) ⊕ Other → Root ⊕ Other
  | .inl (root, _) => .inl root
  | .inr key => .inr key

def fiber : Root ⊕ Other → Type
  | .inl _ => Coord
  | .inr _ => Unit

instance fiberFintype [Fintype Coord] (key : Root ⊕ Other) : Fintype (fiber (Coord := Coord) key) := by
  cases key with
  | inl _ => exact inferInstanceAs (Fintype Coord)
  | inr _ => exact inferInstanceAs (Fintype Unit)

def coordinate : (key : (Root × Coord) ⊕ Other) → fiber (Coord := Coord) (rootOf key)
  | .inl (_, coordinate) => coordinate
  | .inr _ => ()

def ungroup (cell : (key : Root ⊕ Other) × fiber (Coord := Coord) key) :
    (Root × Coord) ⊕ Other :=
  match cell with
  | ⟨.inl root, coordinate⟩ => .inl (root, coordinate)
  | ⟨.inr key, _⟩ => .inr key

theorem ungroup_coordinate (key : (Root × Coord) ⊕ Other) :
    ungroup ⟨rootOf key, coordinate key⟩ = key := by cases key <;> rfl

/-- A finite macro cover is saturated by every scalar coordinate, before any tree is exposed. -/
def cells (keys : Finset (Root ⊕ Other)) := (key : keys) × fiber (Coord := Coord) key.val

instance cellsFintype [Fintype Coord] (keys : Finset (Root ⊕ Other)) :
    Fintype (cells (Coord := Coord) keys) := inferInstanceAs (Fintype (Sigma _))

def cellRange (keys : Finset (Root ⊕ Other)) (cell : cells (Coord := Coord) keys) : Type :=
  primitiveRange (Raw := Raw) (R := R) (ungroup ⟨cell.1.val, cell.2⟩)

/-- Dependent table bijection: scalar cells curry to trees, and other ranges stay unchanged. -/
def coveredTableEquiv (keys : Finset (Root ⊕ Other)) :
    ((key : keys) → macroRange (Coord := Coord) (Raw := Raw) (R := R) key.val) ≃
      ((cell : cells (Coord := Coord) keys) → cellRange (Raw := Raw) (R := R) keys cell) where
  toFun table cell := by
    rcases cell with ⟨⟨key, member⟩, c⟩
    cases key with
    | inl root => exact table ⟨.inl root, member⟩ c
    | inr key => exact table ⟨.inr key, member⟩
  invFun table key := by
    rcases key with ⟨key, member⟩
    cases key with
    | inl root => exact fun c ↦ table ⟨⟨.inl root, member⟩, c⟩
    | inr key => exact table ⟨⟨.inr key, member⟩, ()⟩
  left_inv table := by funext ⟨key, member⟩; cases key <;> rfl
  right_inv table := by
    funext ⟨⟨key, member⟩, c⟩
    cases key with
    | inl root => rfl
    | inr key => cases c; rfl

variable [Fintype Coord] [SampleableType Raw] [∀ key, SampleableType (R key)]

@[reducible] local instance primitiveSampler (key : (Root × Coord) ⊕ Other) :
    SampleableType (primitiveRange (Raw := Raw) (R := R) key) := by
  cases key with
  | inl _ => exact inferInstanceAs (SampleableType Raw)
  | inr key => exact inferInstanceAs (SampleableType (R key))
@[reducible] local instance macroSampler (key : Root ⊕ Other) :
    SampleableType (macroRange (Coord := Coord) (Raw := Raw) (R := R) key) := by
  cases key with
  | inl _ => exact inferInstanceAs (SampleableType (Coord → Raw))
  | inr key => exact inferInstanceAs (SampleableType (R key))
local instance coveredCellSampler (keys : Finset (Root ⊕ Other))
    (cell : cells (Coord := Coord) keys) :
    SampleableType (cellRange (Raw := Raw) (R := R) keys cell) := primitiveSampler _

/-- Joint adaptive simulation for the full heterogeneous oracle. There is no restriction on
which scalar coordinates, other request ranges, or query order the adversary selects. -/
theorem adaptive_exact {α : Type}
    (program : OracleComp (ofFn (@primitiveRange Root Coord Raw Other R)) α) :
    (simulateQ randomOracle program).run' ∅ =ᵈ
      (simulateQ randomOracle (translate program)).run' ∅ := by
  let : MeasurableSpace α := ⊤
  let keys := (possibleQueryKeys program).image rootOf
  have covered := allQueriesSatisfy_possibleQueryKeys program
  have macroCovered : AllQueriesSatisfy (translate program) (· ∈ keys) := by
    have localCover (p : OracleComp (ofFn (@primitiveRange Root Coord Raw Other R)) α)
        (h : AllQueriesSatisfy p (fun key ↦ rootOf key ∈ keys)) :
        AllQueriesSatisfy (translate p) (· ∈ keys) := by
      induction p using OracleComp.inductionOn with
      | pure value => exact allQueriesSatisfy_pure value _
      | query_bind key next ih =>
        obtain ⟨member, rest⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
        cases key with
        | inl pair =>
          simp only [translate, simulateQ_bind, simulateQ_spec_query, ask, bind_assoc]
          exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr
            ⟨member, fun tree ↦ ih _ (rest _)⟩
        | inr key =>
          simp only [translate, simulateQ_bind, simulateQ_spec_query, ask]
          exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr
            ⟨member, fun reply ↦ ih _ (rest reply)⟩
    exact localCover program (covered.mono fun key member ↦
      Finset.mem_image.mpr ⟨key, member, rfl⟩)
  let cell : possibleQueryKeys program → cells (Coord := Coord) keys := fun key ↦
    ⟨⟨rootOf key.val, Finset.mem_image.mpr ⟨key.val, key.property, rfl⟩⟩, coordinate key.val⟩
  have distinct : Function.Injective cell := by
    intro first second same
    apply Subtype.ext
    have decoded := congrArg (fun c : cells (Coord := Coord) keys ↦
      ungroup ⟨c.1.val, c.2⟩) same
    simpa only [cell, ungroup_coordinate] using decoded
  let read (key : possibleQueryKeys program) :
      cellRange (Raw := Raw) (R := R) keys (cell key) ≃
        primitiveRange (Raw := Raw) (R := R) key.val :=
    Equiv.cast (congrArg (primitiveRange (Raw := Raw) (R := R)) (ungroup_coordinate key.val))
  let answers := fun table ↦ flatten (extendTable keys
    ((coveredTableEquiv (Coord := Coord) (Raw := Raw) (R := R) keys).symm table))
  have agrees : ∀ table key, answers table key.val = read key (table (cell key)) := by
    intro table ⟨key, member⟩
    have included : rootOf key ∈ keys := Finset.mem_image.mpr ⟨key, member, rfl⟩
    cases key with
    | inl pair =>
      simp only [rootOf] at included
      simp [answers, flatten, extendTable, included, read, cell, rootOf, coordinate,
        coveredTableEquiv, Equiv.cast, ungroup_coordinate, ungroup]
    | inr key =>
      simp only [rootOf] at included
      simp [answers, flatten, extendTable, included, read, cell, rootOf, coordinate,
        coveredTableEquiv, Equiv.cast, ungroup_coordinate, ungroup]
  have primitive := eager_cover program (possibleQueryKeys program) covered cell distinct
    read answers agrees
  have grouped := eager_cover (translate program) keys macroCovered id Function.injective_id
    (fun _ ↦ Equiv.refl _) (extendTable keys)
    (fun table key ↦ extendTable_subtype keys table key)
  apply primitive.trans
  apply EvalDistEq.trans _ grouped.symm
  let equivalence := coveredTableEquiv (Coord := Coord) (Raw := Raw) (R := R) keys
  have uniform := SampleableType.map_uniformSample_evalDistEq_of_bijective
    equivalence.bijective
  have transported := uniform.bind_left fun table ↦
    pure (evalWithAnswerFn (QueryImpl.ofFn (answers table)) program)
  rw [bind_map_left] at transported
  apply transported.symm.trans
  simp only [answers, equivalence, Equiv.symm_apply_apply, translate_table]
  rfl

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition

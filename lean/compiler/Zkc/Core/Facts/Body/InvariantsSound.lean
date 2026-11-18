module

public import Zkc.Core.Facts.Body.EnteringSound

@[expose] public section

/-!
What the walk of a loop does with its invariants and the index's operations: the value that a
written operation of the rules gives (`indexValue`) and deciding and learning invariants
(`decideInvariants`, `learnInvariants`) grow the state; the positions of an invariant read the
values of its names, the index and the carried values (`PositionsRead.invariant`); the index's
value reads what its operation gives (`indexValue_sound`); deciding invariants that refuses nothing
gives that they hold (`InvariantsHold`, `decideInvariants_sound`); and learning invariants that hold
keeps what the domain's state means (`learnInvariants_sound`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## The state grows -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw)

/-- Entering a computed index grows the value table. -/
theorem indexValue_entered (expression : Option (Expr Raw)) (args : List Ident) (s : State Raw)
    (k : cfg.domain.State) (wf : s.values.WF) :
    State.Entered s (indexValue cfg expression args s k).2.1 := by
  cases expression with
  | none => exact State.Entered.refl wf
  | some e =>
    cases entered : enterExpr cfg (args.map some) e s.values k with
    | none => simpa [indexValue, entered] using State.Entered.refl (s := s) wf
    | some x =>
      obtain ⟨id, values, known⟩ := x
      simpa [indexValue, entered] using
        State.Entered.values (s := s) (enterExpr_grew cfg (args.map some) e wf entered)

/-- Deciding invariants grows the state. -/
theorem decideInvariants_entered (site : AnnotationSite) (kept : Bool) (ids : Ctx Ident)
    (index : Option Ident) (carried : List Ident) :
    ∀ (invariants : List (List Name × List (Expr Raw))) (s : State Raw) (k : cfg.domain.State),
      s.values.WF →
        State.Entered s (decideInvariants cfg site kept ids index carried invariants s k).1
  | [], _, _, wf => State.Entered.refl wf
  | (uses, assertions) :: rest, s, k, wf => by
      have one := decideAt_entered cfg (site.place cfg) (.invariant site (.invariant uses assertions) kept)
        (invariantPositions ids uses index carried) assertions s k wf
      exact one.trans (decideInvariants_entered site kept ids index carried rest _ _ one.wf)

/-- Learning invariants grows the state. -/
theorem learnInvariants_entered (ids : Ctx Ident) (index : Option Ident) (carried : List Ident) :
    ∀ (invariants : List (List Name × List (Expr Raw))) (s : State Raw) (k : cfg.domain.State),
      s.values.WF → State.Entered s (learnInvariants cfg ids index carried invariants s k).1
  | [], _, _, wf => State.Entered.refl wf
  | (uses, assertions) :: rest, s, k, wf => by
      have one := learnAt_entered cfg (invariantPositions ids uses index carried) assertions s k wf
      exact one.trans (learnInvariants_entered ids index carried rest _ _ one.wf)

end

/-! ## The positions of an invariant -/

section
variable {D : Dialect} {Raw : Type}

/-- An invariant of the annotations at a key is an annotation at the key. -/
theorem mem_invariantsAt {notes : Annotations Raw} {key : AnnotationSite} {uses : List Name}
    {assertions : List (Expr Raw)} (m : (uses, assertions) ∈ notes.invariantsAt key) :
    Annotation.invariant uses assertions ∈ notes.at_ key := by
  obtain ⟨a, inA, eq⟩ := List.mem_filterMap.mp m
  cases a with
  | invariant uses' assertions' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨rfl, rfl⟩ := eq
      exact inA
  | step _ _ => cases eq
  | fact _ _ => cases eq

/-- The positions of an invariant whose names have identifiers. -/
theorem invariantPositions_some {ids : Ctx Ident} {uses : List Name} {found : List Ident}
    (h : uses.mapM ids.find? = some found) (index : Option Ident) (carried : List Ident) :
    invariantPositions ids uses index carried =
      some (found.map some ++ index :: carried.map some) := by
  simp only [invariantPositions, namesAt, h, Option.map_some]

/-- An invariant with a name without an identifier has no positions. -/
theorem invariantPositions_none {ids : Ctx Ident} {uses : List Name}
    (h : uses.mapM ids.find? = none) (index : Option Ident) (carried : List Ident) :
    invariantPositions ids uses index carried = none := by
  simp only [invariantPositions, namesAt, h, Option.map_none]

end

section
variable {D : Dialect} {Raw : Type} (σ : Setting D Raw)

/-- The positions of an invariant read the values of its names, the index and the carried
values. -/
theorem PositionsRead.invariant {table : Table Raw} {ρ : Leaves σ.sem.Dyn} {found : List Ident}
    {vs : List σ.sem.Dyn} {index : Option Ident} {indexValue : σ.sem.Dyn} {carriedIds : List Ident}
    {carriedValues : List σ.sem.Dyn} (names : ReadsAll σ.Runs σ.R.bool table ρ found vs)
    (indexRead : ∀ id, index = some id → Reads σ.Runs σ.R.bool table ρ id indexValue)
    (carriedRead : ReadsAll σ.Runs σ.R.bool table ρ carriedIds carriedValues) :
    PositionsRead σ table ρ (found.map some ++ index :: carriedIds.map some)
      (vs ++ indexValue :: carriedValues) :=
  (PositionsRead.of_readsAll names).append
    ((PositionsRead.of_readsAll carriedRead).cons indexRead)
    (by rw [List.length_map, names.length])

/-- The invariants hold of the values of the names that each lists, the index and the carried
values given. -/
def InvariantsHold {Γ : Ctx D.Ty} (env : Env σ.sem.Val Γ)
    (invariants : List (List Name × List (Expr Raw))) (index : σ.sem.Dyn)
    (carried : List σ.sem.Dyn) : Prop :=
  ∀ uses assertions, (uses, assertions) ∈ invariants → ∀ vs,
    valuesOfNames σ.sem env uses = some vs → ∀ a, a ∈ assertions →
      a.Holds σ.Runs σ.R (vs ++ index :: carried)

end

/-! ## Deciding and learning invariants are sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) (laws : σ.Lawful)

include laws in
/-- A dialect-supplied index expression yields the index justified by its denotation. -/
theorem indexValue_sound {expression : Option (Expr Raw)} {args : List Ident} {s : State Raw}
    {k : σ.cfg.domain.State} {ρ : Leaves σ.sem.Dyn} {operands : List σ.sem.Dyn} {result : σ.sem.Dyn}
    (wf : s.values.WF) (means : σ.domain.Means k s.values.table ρ)
    (read : ReadsAll σ.Runs σ.R.bool s.values.table ρ args operands)
    (denotes : ∀ e, expression = some e → e.Denotes σ.Runs operands result) :
    let made := indexValue σ.cfg expression args s k
    σ.domain.Means made.2.2 made.2.1.values.table ρ ∧
      ∀ id, made.1 = some id → Reads σ.Runs σ.R.bool made.2.1.values.table ρ id result := by
  cases expression with
  | none => exact ⟨means, fun _ h => nomatch h⟩
  | some e =>
    cases entered : enterExpr σ.cfg (args.map some) e s.values k with
    | none => simp [indexValue, entered, means]
    | some x =>
      obtain ⟨id, values, known⟩ := x
      obtain ⟨held, one⟩ := enterExpr_sound σ laws.rules e means wf (PositionsRead.of_readsAll read)
        (denotes e rfl) entered
      simpa [indexValue, entered] using And.intro held one

include laws in
/-- **Deciding an invariant that refuses nothing gives that its assertions hold** of the values of
its names, the index and the carried values, when the positions read them and the assertions are
defined at their types; and what the domain's state means is kept. -/
theorem decideAt_invariant_sound (place : Place) (concern : Concern Raw) {Γ : Ctx D.Ty}
    {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident} {env : Env σ.sem.Val Γ} {index : Option Ident}
    {carriedIds : List Ident} {w : D.Who} {carried : List D.Ty} {indexValue : σ.sem.Dyn}
    {carriedValues : List σ.sem.Dyn} (valid : ∀ n v, ρ n = some v → σ.Valid v)
    (indexType : indexValue.1 = D.index w) (indexValid : σ.Valid indexValue)
    (carriedTypes : carriedValues.map Sigma.fst = carried)
    (carriedValid : ∀ v, v ∈ carriedValues → σ.Valid v)
    (uses : List Name) (assertions : List (Expr Raw)) (s : State Raw) (k : σ.cfg.domain.State)
    (scope : Scope σ.sem σ.Runs σ.R ρ ids env s) (means : σ.domain.Means k s.values.table ρ)
    (indexRead : ∀ id, index = some id → Reads σ.Runs σ.R.bool s.values.table ρ id indexValue)
    (carriedRead : ReadsAll σ.Runs σ.R.bool s.values.table ρ carriedIds carriedValues)
    (defined : ∀ τs, typesOf Γ uses = some τs → ∀ a, a ∈ assertions →
      Expr.Defined σ (τs ++ D.index w :: carried) a)
    (unchanged : (decideAt σ.cfg place concern (invariantPositions ids uses index carriedIds)
      assertions s k).1.refusals = s.refusals) :
    σ.domain.Means (decideAt σ.cfg place concern (invariantPositions ids uses index carriedIds)
        assertions s k).2
      (decideAt σ.cfg place concern (invariantPositions ids uses index carriedIds)
        assertions s k).1.values.table ρ ∧
      ∀ vs, valuesOfNames σ.sem env uses = some vs → ∀ a, a ∈ assertions →
        a.Holds σ.Runs σ.R (vs ++ indexValue :: carriedValues) := by
  cases found : uses.mapM ids.find? with
  | none =>
      rw [invariantPositions_none found] at unchanged ⊢
      simp only [decideAt] at unchanged ⊢
      rw [σ.alive means] at unchanged
      have empty := refuseAll_refuses place concern assertions 0 s scope.wf unchanged
      subst empty
      exact ⟨means, fun _ _ _ m => nomatch m⟩
  | some found' =>
      obtain ⟨vs, values, types, reads⟩ := scope.names_read uses found' found
      rw [invariantPositions_some found] at unchanged ⊢
      simp only [decideAt] at unchanged ⊢
      have allValid : ∀ v, v ∈ vs ++ indexValue :: carriedValues → σ.Valid v := by
        intro v m
        rcases List.mem_append.mp m with m | m
        · exact ReadsAll.valid valid reads v m
        · rcases List.mem_cons.mp m with rfl | m
          · exact indexValid
          · exact carriedValid v m
      have typesEq : (vs ++ indexValue :: carriedValues).map Sigma.fst =
          vs.map Sigma.fst ++ D.index w :: carried := by
        rw [List.map_append, List.map_cons, indexType, carriedTypes]
      obtain ⟨means', holds⟩ := decideAll_sound σ laws.rules place concern assertions 0 s k means
        scope.wf (PositionsRead.invariant σ reads indexRead carriedRead)
        (fun a m => Expr.Defined.at_values (by rw [typesEq]; exact defined _ types a m) allValid)
        unchanged
      refine ⟨means', fun vs' values' a m => ?_⟩
      rw [values] at values'
      cases values'
      exact holds a m

include laws in
/-- **Learning an invariant that holds keeps what the domain's state means.** -/
theorem learnAt_invariant_sound {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {index : Option Ident} {carriedIds : List Ident}
    {indexValue : σ.sem.Dyn} {carriedValues : List σ.sem.Dyn} (uses : List Name)
    (assertions : List (Expr Raw)) (s : State Raw) (k : σ.cfg.domain.State)
    (scope : Scope σ.sem σ.Runs σ.R ρ ids env s) (means : σ.domain.Means k s.values.table ρ)
    (indexRead : ∀ id, index = some id → Reads σ.Runs σ.R.bool s.values.table ρ id indexValue)
    (carriedRead : ReadsAll σ.Runs σ.R.bool s.values.table ρ carriedIds carriedValues)
    (holds : ∀ vs, valuesOfNames σ.sem env uses = some vs → ∀ a, a ∈ assertions →
      a.Holds σ.Runs σ.R (vs ++ indexValue :: carriedValues)) :
    σ.domain.Means (learnAt σ.cfg (invariantPositions ids uses index carriedIds) assertions s k).2
      (learnAt σ.cfg (invariantPositions ids uses index carriedIds) assertions s k).1.values.table
        ρ := by
  cases found : uses.mapM ids.find? with
  | none =>
      rw [invariantPositions_none found]
      exact means
  | some found' =>
      obtain ⟨vs, values, -, reads⟩ := scope.names_read uses found' found
      rw [invariantPositions_some found]
      exact learnAll_sound σ laws.rules assertions s k means scope.wf
        (PositionsRead.invariant σ reads indexRead carriedRead) (holds vs values)

include laws in
/-- **Deciding invariants that refuses nothing gives that they hold**, and what the domain's state
means is kept. -/
theorem decideInvariants_sound (site : AnnotationSite) (kept : Bool) {Γ : Ctx D.Ty}
    {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident} {env : Env σ.sem.Val Γ} {index : Option Ident}
    {carriedIds : List Ident} {w : D.Who} {carried : List D.Ty} {indexValue : σ.sem.Dyn}
    {carriedValues : List σ.sem.Dyn} (valid : ∀ n v, ρ n = some v → σ.Valid v)
    (indexType : indexValue.1 = D.index w) (indexValid : σ.Valid indexValue)
    (carriedTypes : carriedValues.map Sigma.fst = carried)
    (carriedValid : ∀ v, v ∈ carriedValues → σ.Valid v) :
    ∀ (invariants : List (List Name × List (Expr Raw))) (s : State Raw) (k : σ.cfg.domain.State),
      Scope σ.sem σ.Runs σ.R ρ ids env s → σ.domain.Means k s.values.table ρ →
      (∀ id, index = some id → Reads σ.Runs σ.R.bool s.values.table ρ id indexValue) →
      ReadsAll σ.Runs σ.R.bool s.values.table ρ carriedIds carriedValues →
      (∀ uses assertions, (uses, assertions) ∈ invariants → ∀ τs, typesOf Γ uses = some τs →
        ∀ a, a ∈ assertions → Expr.Defined σ (τs ++ D.index w :: carried) a) →
      (decideInvariants σ.cfg site kept ids index carriedIds invariants s k).1.refusals =
        s.refusals →
      σ.domain.Means (decideInvariants σ.cfg site kept ids index carriedIds invariants s k).2
          (decideInvariants σ.cfg site kept ids index carriedIds invariants s k).1.values.table
          ρ ∧
        InvariantsHold σ env invariants indexValue carriedValues
  | [], _, _, _, means, _, _, _, _ => ⟨means, fun _ _ m => nomatch m⟩
  | (uses, assertions) :: rest, s, k, scope, means, indexRead, carriedRead, defined, unchanged => by
      have decided := decideAt_entered σ.cfg (site.place σ.cfg) (.invariant site (.invariant uses assertions) kept)
        (invariantPositions ids uses index carriedIds) assertions s k scope.wf
      have restEntered := decideInvariants_entered σ.cfg site kept ids index carriedIds rest _
        (decideAt σ.cfg (site.place σ.cfg) (.invariant site (.invariant uses assertions) kept)
          (invariantPositions ids uses index carriedIds) assertions s k).2 decided.wf
      obtain ⟨first, second⟩ := State.Entered.unchanged decided restEntered unchanged
      obtain ⟨means₁, holds₁⟩ := decideAt_invariant_sound σ laws (site.place σ.cfg) _ valid indexType indexValid
        carriedTypes carriedValid uses assertions s k scope means indexRead carriedRead
        (defined uses assertions List.mem_cons_self) first
      obtain ⟨means₂, holds₂⟩ := decideInvariants_sound site kept valid indexType indexValid
        carriedTypes carriedValid rest _ _ (scope.grow decided.1 (Nat.le_of_eq decided.2.1.symm))
        means₁ (fun id h => Reads.mono decided.1.1 (fun _ _ h => h) (indexRead id h))
        (ReadsAll.mono decided.1.1 (fun _ _ h => h) carriedRead)
        (fun uses' assertions' m => defined uses' assertions' (List.mem_cons_of_mem _ m)) second
      refine ⟨means₂, fun uses' assertions' m => ?_⟩
      rcases List.mem_cons.mp m with same | m
      · cases same
        exact holds₁
      · exact holds₂ uses' assertions' m

include laws in
/-- **Learning invariants that hold keeps what the domain's state means.** -/
theorem learnInvariants_sound {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {index : Option Ident} {carriedIds : List Ident}
    {indexValue : σ.sem.Dyn} {carriedValues : List σ.sem.Dyn} :
    ∀ (invariants : List (List Name × List (Expr Raw))) (s : State Raw) (k : σ.cfg.domain.State),
      Scope σ.sem σ.Runs σ.R ρ ids env s → σ.domain.Means k s.values.table ρ →
      (∀ id, index = some id → Reads σ.Runs σ.R.bool s.values.table ρ id indexValue) →
      ReadsAll σ.Runs σ.R.bool s.values.table ρ carriedIds carriedValues →
      InvariantsHold σ env invariants indexValue carriedValues →
      σ.domain.Means (learnInvariants σ.cfg ids index carriedIds invariants s k).2
        (learnInvariants σ.cfg ids index carriedIds invariants s k).1.values.table ρ
  | [], _, _, _, means, _, _, _ => means
  | (uses, assertions) :: rest, s, k, scope, means, indexRead, carriedRead, holds => by
      have learned := learnAt_entered σ.cfg (invariantPositions ids uses index carriedIds)
        assertions s k scope.wf
      have means₁ := learnAt_invariant_sound σ laws uses assertions s k scope means indexRead
        carriedRead (holds uses assertions List.mem_cons_self)
      exact learnInvariants_sound rest _ _ (scope.grow learned.1 (Nat.le_of_eq learned.2.1.symm))
        means₁ (fun id h => Reads.mono learned.1.1 (fun _ _ h => h) (indexRead id h))
        (ReadsAll.mono learned.1.1 (fun _ _ h => h) carriedRead)
        (fun uses' assertions' m => holds uses' assertions' (List.mem_cons_of_mem _ m))

end

#print axioms indexValue_sound
#print axioms decideInvariants_sound
#print axioms learnInvariants_sound

end Zkc.Core.BodyAnalysis

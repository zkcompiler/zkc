module

public import Zkc.Core.Facts.Body.ValueLaws

@[expose] public section

/-!
What entering, deciding and learning assertions do, and the annotations at the entry of an
instruction: the state grows and stays well formed (`State.Entered`, with no domain and no law);
an entered assertion that names a value reads it (`enterExpr_sound`); a decision that refuses
nothing gives that the assertions hold (`decideAll_sound`); learning assertions that hold keeps
what the domain's state means (`learnAll_sound`); and the annotations at an instruction keep the
invariant of the walk when they refuse nothing (`atEntry_inv`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Refusals are only added -/

/-- A list with something before an element and a list is not the list. -/
theorem List.append_cons_ne_self {α : Type} (new : List α) (a : α) (l : List α) :
    new ++ a :: l ≠ l := by
  intro same
  have lengths := congrArg List.length same
  rw [List.length_append, List.length_cons] at lengths
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _)) lengths

/-- When two additions of refusals add nothing in all, the first adds nothing. -/
theorem refusals_first {α : Type} {l₀ l₁ l₂ new₁ new₂ : List α} (first : l₁ = new₁ ++ l₀)
    (second : l₂ = new₂ ++ l₁) (none : l₂ = l₀) : l₁ = l₀ := by
  rw [first] at second ⊢
  rw [none, ← List.append_assoc] at second
  have empty : new₂ ++ new₁ = [] :=
    List.append_cancel_right (as := new₂ ++ new₁) (bs := l₀) (cs := []) second.symm
  rw [(List.append_eq_nil_iff.mp empty).2, List.nil_append]

/-- When two additions of refusals add nothing in all, the second adds nothing. -/
theorem refusals_second {α : Type} {l₀ l₁ l₂ new₁ new₂ : List α} (first : l₁ = new₁ ++ l₀)
    (second : l₂ = new₂ ++ l₁) (none : l₂ = l₀) : l₂ = l₁ := by
  rw [refusals_first first second none, none]

section
variable {D : Dialect} {Raw : Type}

/-! ## The state grows -/

/-- What entering, deciding and learning assertions do to the state of the walk: the values grow,
the leaf counter and the bounds stay, and refusals are added before those that were there. -/
def State.Entered (s s' : State Raw) : Prop :=
  Values.Grew s.values s'.values ∧ s'.leaves = s.leaves ∧ s'.bounds = s.bounds ∧
    ∃ new, s'.refusals = new ++ s.refusals

theorem State.Entered.refl {s : State Raw} (wf : s.values.WF) : State.Entered s s :=
  ⟨Values.Grew.refl wf, rfl, rfl, [], rfl⟩

theorem State.Entered.trans {a b c : State Raw} (first : State.Entered a b)
    (second : State.Entered b c) : State.Entered a c := by
  obtain ⟨grew, leaves, bounds, new, refusals⟩ := first
  obtain ⟨grew', leaves', bounds', new', refusals'⟩ := second
  exact ⟨grew.trans grew', leaves'.trans leaves, bounds'.trans bounds, new' ++ new,
    by rw [refusals', refusals, List.append_assoc]⟩

theorem State.Entered.wf {s s' : State Raw} (entered : State.Entered s s') : s'.values.WF :=
  entered.1.2.1

theorem State.Entered.refuse {s : State Raw} (wf : s.values.WF) (refusal : Refusal Raw) :
    State.Entered s (s.refuse refusal) :=
  ⟨Values.Grew.refl wf, rfl, rfl, [refusal], rfl⟩

theorem State.Entered.values {s : State Raw} {v : Values Raw} (grew : Values.Grew s.values v) :
    State.Entered s { s with values := v } :=
  ⟨grew, rfl, rfl, [], rfl⟩

/-- A refusal and what is added after it are not nothing added. -/
theorem State.Entered.refused {s s' : State Raw} {refusal : Refusal Raw}
    (entered : State.Entered (s.refuse refusal) s') : s'.refusals ≠ s.refusals := by
  obtain ⟨-, -, -, new, refusals⟩ := entered
  rw [refusals]
  exact List.append_cons_ne_self new refusal s.refusals

variable [DecidableEq Raw]

omit [DecidableEq Raw] in
/-- A state with a refusal before a list, and what is added after it, do not have that list of
refusals. -/
theorem State.Entered.refusedFrom {t s' : State Raw} {refusal : Refusal Raw}
    {l : List (Refusal Raw)} (entered : State.Entered t s') (head : t.refusals = refusal :: l) :
    s'.refusals ≠ l := by
  obtain ⟨-, -, -, new, refusals⟩ := entered
  rw [refusals, head]
  exact List.append_cons_ne_self new refusal l

/-- What the domain is told of an application is the application shared in the table. -/
theorem Config.apply_values (cfg : Config D Raw) (written : Raw) (args : List Ident) (count : Nat)
    (v : Values Raw) (k : cfg.domain.State) :
    (cfg.apply written args count v k).1 = (v.apply cfg.rules.commutes written args count).1.ids ∧
      (cfg.apply written args count v k).2.1 = (v.apply cfg.rules.commutes written args count).2 :=
  ⟨rfl, rfl⟩

/-- The single-port operation projects exactly the same shared entry and transfer. -/
theorem Config.applyPort_eq (cfg : Config D Raw) (op : Raw) (args : List Ident) (count port : Nat)
    (v : Values Raw) (k : cfg.domain.State) :
    cfg.applyPort op args count port v k =
      (cfg.apply op args count v k).1[port]?.map
        (fun id => (id, (cfg.apply op args count v k).2)) := by
  unfold Config.applyPort Config.apply
  cases v.apply cfg.rules.commutes op args count with
  | mk e next =>
    by_cases h : port < e.count
    · simp [h, Entry.ids, Ident.vals]
    · simp [h, Entry.ids, Ident.vals]

theorem enterExpr_apply_eq (cfg : Config D Raw) (positions : List (Option Ident))
    (op : Raw) (es : Exprs Raw) (port : Nat) (v : Values Raw) (k : cfg.domain.State) :
    enterExpr cfg positions (.apply op es port) v k =
      if cfg.rules.assertable op then
        match enterExprs cfg positions es v k with
        | some (args, v', k') =>
          let made := cfg.apply op args (cfg.rules.results op) v' k'
          made.1[port]?.map fun id => (id, made.2.1, made.2.2)
        | none => none
      else none := by
  simp only [enterExpr, cfg.rules.assertionArity_eq]
  cases h : cfg.rules.assertable op <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases enterExprs cfg positions es v k with
  | none => rfl
  | some triple => obtain ⟨_, _, _⟩ := triple; apply Config.applyPort_eq

mutual
  /-- Entering an assertion makes the values grow. -/
  theorem enterExpr_grew (cfg : Config D Raw) (positions : List (Option Ident)) :
      ∀ (a : Expr Raw) {v : Values Raw} {k : cfg.domain.State} {id : Ident} {v' : Values Raw}
        {k' : cfg.domain.State}, v.WF → enterExpr cfg positions a v k = some (id, v', k') →
        Values.Grew v v'
    | .arg _, _, _, _, _, _, wf, entered => by
        simp only [enterExpr] at entered
        split at entered
        · cases entered
          exact Values.Grew.refl wf
        · cases entered
    | .apply written operands result, _, _, _, _, _, wf, entered => by
        simp only [enterExpr_apply_eq] at entered
        split at entered
        · split at entered
          · next args v₁ k₁ inner =>
              have first := enterExprs_grew cfg positions operands wf inner
              have second := Values.apply_grew cfg.rules.commutes written args
                (cfg.rules.results written) first.2.1
              obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp entered
              simp only [Prod.mk.injEq] at same
              obtain ⟨-, rfl, -⟩ := same
              exact first.trans second
          · cases entered
        · cases entered
  /-- Entering assertions in order makes the values grow. -/
  theorem enterExprs_grew (cfg : Config D Raw) (positions : List (Option Ident)) :
      ∀ (as : Exprs Raw) {v : Values Raw} {k : cfg.domain.State} {ids : List Ident}
        {v' : Values Raw} {k' : cfg.domain.State}, v.WF →
        enterExprs cfg positions as v k = some (ids, v', k') → Values.Grew v v'
    | .nil, _, _, _, _, _, wf, entered => by
        simp only [enterExprs, Option.some.injEq, Prod.mk.injEq] at entered
        obtain ⟨-, rfl, -⟩ := entered
        exact Values.Grew.refl wf
    | .cons first others, _, _, _, _, _, wf, entered => by
        simp only [enterExprs] at entered
        split at entered
        · next id₁ v₁ k₁ inner =>
            have one := enterExpr_grew cfg positions first wf inner
            obtain ⟨⟨ids₂, v₂, k₂⟩, rest, same⟩ := Option.map_eq_some_iff.mp entered
            simp only [Prod.mk.injEq] at same
            obtain ⟨-, rfl, -⟩ := same
            exact one.trans (enterExprs_grew cfg positions others one.2.1 rest)
        · cases entered
end

/-- Deciding assertions grows the state. -/
theorem decideWith_entered {A : Type} (project : A → Expr Raw) (bound : A → Option (Expr Raw)) (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : List (Option Ident)) :
    ∀ (assertions : List A) (index : Nat) (s : State Raw) (k : cfg.domain.State),
      s.values.WF → State.Entered s (decideWith project bound cfg place concern positions index assertions s k).1
  | [], _, _, _, wf => State.Entered.refl wf
  | assertion :: rest, index, s, k, wf => by
      cases entered : enterExpr cfg positions (project assertion) s.values k with
      | none =>
          simp only [decideWith, entered]
          split
          · exact decideWith_entered project bound cfg place concern positions rest (index + 1) s k wf
          · exact (State.Entered.refuse wf _).trans
              (decideWith_entered project bound cfg place concern positions rest (index + 1) _ k wf)
      | some found =>
          obtain ⟨id, v, k'⟩ := found
          have grew := State.Entered.values (s := s) (enterExpr_grew cfg positions (project assertion) wf entered)
          simp only [decideWith, entered]
          split
          · exact grew.trans (decideWith_entered project bound cfg place concern positions rest _ _ k' grew.wf)
          · exact grew.trans (decideWith_entered project bound cfg place concern positions rest _ _ k' grew.wf)
          · exact (grew.trans (State.Entered.refuse grew.wf _)).trans
              (decideWith_entered project bound cfg place concern positions rest _ _ k' grew.wf)
          · exact (grew.trans (State.Entered.refuse grew.wf _)).trans
              (decideWith_entered project bound cfg place concern positions rest _ _ k' grew.wf)

theorem decideAll_entered (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : List (Option Ident)) :
    ∀ (assertions : List (Expr Raw)) (index : Nat) (s : State Raw) (k : cfg.domain.State),
      s.values.WF → State.Entered s (decideAll cfg place concern positions index assertions s k).1 :=
  decideWith_entered id (fun _ => none) cfg place concern positions

theorem decideClauses_entered (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : List (Option Ident)) :
    ∀ (assertions : List (ContractClause Raw)) (index : Nat) (s : State Raw) (k : cfg.domain.State),
      s.values.WF → State.Entered s (decideClauses cfg place concern positions index assertions s k).1 :=
  decideWith_entered ContractClause.assertion ContractClause.staticBound cfg place concern positions

/-- Learning assertions grows the state. -/
theorem learnAll_entered (cfg : Config D Raw) (positions : List (Option Ident)) :
    ∀ (assertions : List (Expr Raw)) (s : State Raw) (k : cfg.domain.State),
      s.values.WF → State.Entered s (learnAll cfg positions assertions s k).1
  | [], _, _, wf => State.Entered.refl wf
  | assertion :: rest, s, k, wf => by
      cases entered : enterExpr cfg positions assertion s.values k with
      | none =>
          simp only [learnAll, entered]
          exact learnAll_entered cfg positions rest s k wf
      | some found =>
          obtain ⟨id, v, k'⟩ := found
          have grew := State.Entered.values (s := s) (enterExpr_grew cfg positions assertion wf entered)
          simp only [learnAll, entered]
          exact grew.trans (learnAll_entered cfg positions rest _ _ grew.wf)

omit [DecidableEq Raw] in
/-- Refusing assertions that cannot be entered grows the state. -/
theorem refuseAll_entered (place : Place) (concern : Concern Raw) (dead : Bool) :
    ∀ (assertions : List (Expr Raw)) (index : Nat) (s : State Raw), s.values.WF →
      State.Entered s (refuseAll place concern dead index assertions s)
  | [], _, _, wf => State.Entered.refl wf
  | assertion :: rest, index, s, wf => by
      simp only [refuseAll]
      split
      · exact refuseAll_entered place concern dead rest (index + 1) s wf
      · exact (State.Entered.refuse wf _).trans
          (refuseAll_entered place concern dead rest (index + 1) _ wf)

omit [DecidableEq Raw] in
/-- Refusing assertions that cannot be entered, outside a dead state, refuses each. -/
theorem refuseAll_refuses (place : Place) (concern : Concern Raw) :
    ∀ (assertions : List (Expr Raw)) (index : Nat) (s : State Raw), s.values.WF →
      (refuseAll place concern false index assertions s).refusals = s.refusals → assertions = []
  | [], _, _, _, _ => rfl
  | _ :: rest, index, s, wf, unchanged => by
      simp only [refuseAll] at unchanged
      exact absurd unchanged (State.Entered.refused
        (refuseAll_entered place concern false rest (index + 1) _ (State.Entered.refuse wf _).wf))

/-- Deciding the assertions of an annotation grows the state. -/
theorem decideAt_entered (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : Option (List (Option Ident))) (assertions : List (Expr Raw)) (s : State Raw)
    (k : cfg.domain.State) (wf : s.values.WF) :
    State.Entered s (decideAt cfg place concern positions assertions s k).1 := by
  cases positions with
  | some positions => exact decideAll_entered cfg place concern positions assertions 0 s k wf
  | none => exact refuseAll_entered place concern _ assertions 0 s wf

/-- Learning the assertions of an annotation grows the state. -/
theorem learnAt_entered (cfg : Config D Raw) (positions : Option (List (Option Ident)))
    (assertions : List (Expr Raw)) (s : State Raw) (k : cfg.domain.State) (wf : s.values.WF) :
    State.Entered s (learnAt cfg positions assertions s k).1 := by
  cases positions with
  | some positions => exact learnAll_entered cfg positions assertions s k wf
  | none => exact State.Entered.refl wf

/-- The annotations at an instruction grow the state. -/
theorem annotate_entered (cfg : Config D Raw) (site : AnnotationSite) (ids : Ctx Ident) :
    ∀ (notes : List (Annotation Raw)) (s : State Raw) (k : cfg.domain.State), s.values.WF →
      State.Entered s (annotate cfg site ids notes s k).1
  | [], _, _, wf => State.Entered.refl wf
  | .invariant _ _ :: rest, s, k, wf => annotate_entered cfg site ids rest s k wf
  | .step lemma names :: rest, s, k, wf => by
      simp only [annotate]
      split
      · next l _ =>
          have decided := decideAt_entered cfg (site.place cfg) (.premise site (.step lemma names))
            (namesAt ids names) l.premises s k wf
          have learned := learnAt_entered cfg (namesAt ids names) [l.conclusion] _
            (decideAt cfg (site.place cfg) (.premise site (.step lemma names)) (namesAt ids names) l.premises s k).2
            decided.wf
          exact (decided.trans learned).trans (annotate_entered cfg site ids rest _ _ learned.wf)
      · split
        · exact annotate_entered cfg site ids rest s k wf
        · exact (State.Entered.refuse wf _).trans
            (annotate_entered cfg site ids rest _ k (State.Entered.refuse wf _).wf)
  | .fact uses assertion :: rest, s, k, wf => by
      simp only [annotate]
      have learned := learnAt_entered cfg (namesAt ids uses) [assertion] s k wf
      exact learned.trans (annotate_entered cfg site ids rest _ _ learned.wf)

/-- The annotations at the entry of an instruction grow the state. -/
theorem atEntry_entered (cfg : Config D Raw) (notes : Annotations Raw) (site : AnnotationSite)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) (wf : s.values.WF) :
    State.Entered s (atEntry cfg notes site ids s k).1 :=
  annotate_entered cfg _ ids _ s k wf

end

/-! ## Values that read are valid; positions -/

section
variable {D : Dialect} {Raw : Type}

/-- Through the relation of written operations on valid values, from leaves whose values are valid,
every value read is valid. -/
theorem Reads.valid {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {Valid : sem.Dyn → Prop} {truth : sem.Dyn → Option Bool} {table : Table Raw}
    {ρ : Leaves sem.Dyn} (leaves : ∀ n v, ρ n = some v → Valid v) :
    ∀ {id : Ident} {v : sem.Dyn}, Reads (ValidRun sem Run Valid) truth table ρ id v → Valid v
  | _, _, .leaf valued => leaves _ _ valued
  | _, _, .app _ _ _ _ ran result => ran.2.2 _ (List.mem_of_getElem? result)
  | _, _, .select _ _ _ _ read => Reads.valid leaves read

/-- Values read in order through the relation on valid values, from valid leaves, are valid. -/
theorem ReadsAll.valid {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {Valid : sem.Dyn → Prop} {truth : sem.Dyn → Option Bool} {table : Table Raw}
    {ρ : Leaves sem.Dyn} (leaves : ∀ n v, ρ n = some v → Valid v) :
    ∀ {ids : List Ident} {vs : List sem.Dyn}, ReadsAll (ValidRun sem Run Valid) truth table ρ ids vs →
      ∀ v, v ∈ vs → Valid v
  | _, _, .nil, _, m => nomatch m
  | _, _, .cons first others, v, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact Reads.valid leaves first
      · exact ReadsAll.valid leaves others v m

/-- The identifiers at positions read the values at the same positions. -/
def PositionsRead (σ : Setting D Raw) (table : Table Raw) (ρ : Leaves σ.sem.Dyn)
    (positions : List (Option Ident)) (args : List σ.sem.Dyn) : Prop :=
  ∀ (i : Nat) (id : Ident), positions[i]? = some (some id) →
    ∃ x, args[i]? = some x ∧ Reads σ.Runs σ.R.bool table ρ id x

/-- Positions that read keep reading when the table grows and more leaves get values. -/
theorem PositionsRead.mono {σ : Setting D Raw} {table table' : Table Raw}
    {ρ ρ' : Leaves σ.sem.Dyn} {positions : List (Option Ident)} {args : List σ.sem.Dyn}
    (read : PositionsRead σ table ρ positions args) (sub : table.Le table') (le : ρ.Le ρ') :
    PositionsRead σ table' ρ' positions args := by
  intro i id at_
  obtain ⟨x, found, one⟩ := read i id at_
  exact ⟨x, found, Reads.mono sub le one⟩

/-- Identifiers that read values in order, as positions, read them. -/
theorem PositionsRead.of_readsAll {σ : Setting D Raw} {table : Table Raw} {ρ : Leaves σ.sem.Dyn}
    {ids : List Ident} {args : List σ.sem.Dyn}
    (read : ReadsAll σ.Runs σ.R.bool table ρ ids args) :
    PositionsRead σ table ρ (ids.map some) args := by
  intro i id at_
  rw [List.getElem?_map] at at_
  cases found : ids[i]? with
  | none => rw [found] at at_; cases at_
  | some id' =>
      rw [found] at at_
      cases at_
      exact read.get found

/-- Positions that read, followed by positions that read: as many values as positions first. -/
theorem PositionsRead.append {σ : Setting D Raw} {table : Table Raw} {ρ : Leaves σ.sem.Dyn}
    {ps ps' : List (Option Ident)} {args args' : List σ.sem.Dyn}
    (first : PositionsRead σ table ρ ps args) (second : PositionsRead σ table ρ ps' args')
    (length : ps.length = args.length) : PositionsRead σ table ρ (ps ++ ps') (args ++ args') := by
  intro i id at_
  rcases Nat.lt_or_ge i ps.length with lt | ge
  · rw [List.getElem?_append_left lt] at at_
    obtain ⟨x, found, read⟩ := first i id at_
    exact ⟨x, by rw [List.getElem?_append_left (length ▸ lt)]; exact found, read⟩
  · rw [List.getElem?_append_right ge] at at_
    obtain ⟨x, found, read⟩ := second _ id at_
    refine ⟨x, ?_, read⟩
    rw [List.getElem?_append_right (length ▸ ge), ← length]
    exact found

/-- A position that reads its value, followed by positions that read. -/
theorem PositionsRead.cons {σ : Setting D Raw} {table : Table Raw} {ρ : Leaves σ.sem.Dyn} {p : Option Ident}
    {ps : List (Option Ident)} {a : σ.sem.Dyn} {args : List σ.sem.Dyn}
    (head : ∀ id, p = some id → Reads σ.Runs σ.R.bool table ρ id a)
    (tail : PositionsRead σ table ρ ps args) : PositionsRead σ table ρ (p :: ps) (a :: args) := by
  intro i id at_
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
      exact ⟨a, rfl, head id at_⟩
  | succ i =>
      simp only [List.getElem?_cons_succ] at at_ ⊢
      exact tail i id at_

/-- Nobody's answers are sound. -/
theorem Asks.nobody_sound {Val : Type} (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (table : Table Raw) (ρ : Leaves Val) : Asks.nobody.Sound Run R table ρ :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => nomatch h⟩

/-- A state that means something is not dead. -/
theorem Setting.alive (σ : Setting D Raw) {k : σ.cfg.domain.State} {table : Table Raw}
    {ρ : Leaves σ.sem.Dyn} (means : σ.domain.Means k table ρ) : σ.cfg.domain.dead k = false := by
  cases dead : σ.cfg.domain.dead k with
  | false => rfl
  | true => exact absurd means (σ.domain.dead dead)

/-- On valid values, a written operation that commutes gives the same on its two operands
exchanged. -/
theorem Setting.runs_swap (σ : Setting D Raw)
    (rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined) (written : Raw) :
    σ.cfg.rules.commutes written = true → ∀ a b results, σ.Runs written [a, b] results →
      σ.Runs written [b, a] results := by
  intro commutes a b results ran
  refine ⟨rules.commutative written commutes a b results ran.1, fun v m => ?_, ran.2.2⟩
  rcases List.mem_cons.mp m with rfl | m
  · exact ran.2.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases List.mem_cons.mp m with rfl | m
    · exact ran.2.1 _ List.mem_cons_self
    · cases m

end

/-! ## Entering is sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)
  (rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined)

include rules in
/-- **A written operation applied to operands that read**, shared and the domain told: the values
read what it gives, and what the domain's state means is kept. -/
theorem Config.apply_sound {written : Raw} {ids : List Ident} {count : Nat} {v : Values Raw}
    {k : σ.cfg.domain.State} {ρ : Leaves σ.sem.Dyn} {operands results : List σ.sem.Dyn}
    (wf : v.WF) (means : σ.domain.Means k v.table ρ) (read : ReadsAll σ.Runs σ.R.bool v.table ρ ids operands)
    (ran : σ.Runs written operands results) (length : results.length = count) :
    σ.domain.Means (σ.cfg.apply written ids count v k).2.2
        (σ.cfg.apply written ids count v k).2.1.table ρ ∧
      ReadsAll σ.Runs σ.R.bool (σ.cfg.apply written ids count v k).2.1.table ρ
        (σ.cfg.apply written ids count v k).1 results := by
  obtain ⟨operands', read', ran'⟩ := placed_reads (σ.runs_swap rules written) read ran
  have values := Values.share_reads read' ran' length
  have known := (Values.share_entry (.app written (placed (σ.cfg.rules.commutes written) ids))
    count v).2.2
  have grew := Values.share_table_le (.app written (placed (σ.cfg.rules.commutes written) ids)) count v
  have slots := (Values.apply_grew σ.cfg.rules.commutes written ids count wf).2.1.slots
  exact ⟨σ.domain.transfer slots (Asks.nobody_sound _ _ _ _)
    (σ.domain.mono grew (fun _ _ h => h) means) known values.vals_each, values⟩

set_option linter.unusedSectionVars false in
include rules in
mutual
  /-- **An entered assertion that names a value reads it**, and what the domain's state means is
  kept: from positions that read the values of the positions. -/
  theorem enterExpr_sound {positions : List (Option Ident)} {args : List σ.sem.Dyn}
      {ρ : Leaves σ.sem.Dyn} :
      ∀ (a : Expr Raw) {v : Values Raw} {k : σ.cfg.domain.State} {x : σ.sem.Dyn} {id : Ident}
        {v' : Values Raw} {k' : σ.cfg.domain.State},
        σ.domain.Means k v.table ρ → v.WF → PositionsRead σ v.table ρ positions args →
        Expr.Denotes σ.Runs args a x → enterExpr σ.cfg positions a v k = some (id, v', k') →
        σ.domain.Means k' v'.table ρ ∧ Reads σ.Runs σ.R.bool v'.table ρ id x
    | .arg _, _, _, _, _, _, _, means, _, positionsRead, denotes, entered => by
        simp only [enterExpr] at entered
        split at entered
        · next id₀ at_ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at entered
            obtain ⟨rfl, rfl, rfl⟩ := entered
            cases denotes with
            | arg found =>
                obtain ⟨x', found', one⟩ := positionsRead _ _ at_
                rw [found] at found'
                cases found'
                exact ⟨means, one⟩
        · cases entered
    | .apply written operands result, _, _, _, _, _, _, means, wf, positionsRead, denotes,
        entered => by
        simp only [enterExpr_apply_eq] at entered
        split at entered
        · split at entered
          · next ids v₁ k₁ inner =>
              cases denotes with
              | apply named ran picked =>
                  obtain ⟨means₁, read₁⟩ :=
                    enterExprs_sound operands means wf positionsRead named inner
                  have length := (rules.keeps _ _ _ ran.1 ran.2.1).2
                  obtain ⟨means₂, values⟩ := Config.apply_sound σ rules
                    (enterExprs_grew σ.cfg positions operands wf inner).2.1 means₁ read₁ ran length
                  obtain ⟨id₀, at_, same⟩ := Option.map_eq_some_iff.mp entered
                  simp only [Prod.mk.injEq] at same
                  obtain ⟨rfl, rfl, rfl⟩ := same
                  obtain ⟨x', picked', one⟩ := values.get at_
                  rw [picked] at picked'
                  cases picked'
                  exact ⟨means₂, one⟩
          · cases entered
        · cases entered
  /-- Entered assertions in order read the values that they name, and what the domain's state
  means is kept. -/
  theorem enterExprs_sound {positions : List (Option Ident)} {args : List σ.sem.Dyn}
      {ρ : Leaves σ.sem.Dyn} :
      ∀ (as : Exprs Raw) {v : Values Raw} {k : σ.cfg.domain.State} {xs : List σ.sem.Dyn}
        {ids : List Ident} {v' : Values Raw} {k' : σ.cfg.domain.State},
        σ.domain.Means k v.table ρ → v.WF → PositionsRead σ v.table ρ positions args →
        Exprs.Denote σ.Runs args as xs → enterExprs σ.cfg positions as v k = some (ids, v', k') →
        σ.domain.Means k' v'.table ρ ∧ ReadsAll σ.Runs σ.R.bool v'.table ρ ids xs
    | .nil, _, _, _, _, _, _, means, _, _, denotes, entered => by
        simp only [enterExprs, Option.some.injEq, Prod.mk.injEq] at entered
        obtain ⟨rfl, rfl, rfl⟩ := entered
        cases denotes
        exact ⟨means, .nil⟩
    | .cons first others, _, _, _, _, _, _, means, wf, positionsRead, denotes, entered => by
        simp only [enterExprs] at entered
        split at entered
        · next id₁ v₁ k₁ inner =>
            cases denotes with
            | cons one rest =>
                obtain ⟨means₁, read₁⟩ := enterExpr_sound first means wf positionsRead one inner
                have grew₁ := enterExpr_grew σ.cfg positions first wf inner
                obtain ⟨⟨ids₂, v₂, k₂⟩, inner₂, same⟩ := Option.map_eq_some_iff.mp entered
                simp only [Prod.mk.injEq] at same
                obtain ⟨rfl, rfl, rfl⟩ := same
                obtain ⟨means₂, read₂⟩ := enterExprs_sound others means₁ grew₁.2.1
                  (positionsRead.mono grew₁.1 (fun _ _ h => h)) rest inner₂
                have grew₂ := enterExprs_grew σ.cfg positions others grew₁.2.1 inner₂
                exact ⟨means₂, .cons (Reads.mono grew₂.1 (fun _ _ h => h) read₁) read₂⟩
        · cases entered
end

end

/-! ## Deciding and learning are sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)
  (rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined)

private theorem clauseTruth_true {cfg : Config D Raw} {pos demand v k i}
    (checked : clauseTruth cfg pos demand v k i = some true) : cfg.domain.truth Asks.nobody v.table k i = some true := by
  cases truth : cfg.domain.truth Asks.nobody v.table k i with
  | none => simp [clauseTruth, truth] at checked
  | some b => cases b <;> simp_all [clauseTruth]

include rules in
/-- **A decision that refuses nothing gives that the assertions hold**, for assertions that name a
value of the positions' values; and what the domain's state means is kept. -/
theorem decideWith_sound {A : Type} (project : A → Expr Raw) (bound : A → Option (Expr Raw)) (place : Place) (concern : Concern Raw) {positions : List (Option Ident)}
    {args : List σ.sem.Dyn} {ρ : Leaves σ.sem.Dyn} :
    ∀ (assertions : List A) (index : Nat) (s : State Raw) (k : σ.cfg.domain.State),
      σ.domain.Means k s.values.table ρ → s.values.WF →
      PositionsRead σ s.values.table ρ positions args →
      (∀ a, a ∈ assertions → ∃ x, Expr.Denotes σ.Runs args (project a) x) →
      (decideWith project bound σ.cfg place concern positions index assertions s k).1.refusals = s.refusals →
      σ.domain.Means (decideWith project bound σ.cfg place concern positions index assertions s k).2
          (decideWith project bound σ.cfg place concern positions index assertions s k).1.values.table ρ ∧
        ∀ a, a ∈ assertions → (project a).Holds σ.Runs σ.R args
  | [], _, _, _, means, _, _, _, _ => ⟨means, fun _ m => nomatch m⟩
  | assertion :: rest, index, s, k, means, wf, positionsRead, defined, unchanged => by
      have alive := σ.alive means
      obtain ⟨x, denotes⟩ := defined assertion List.mem_cons_self
      cases entered : enterExpr σ.cfg positions (project assertion) s.values k with
      | none =>
          simp only [decideWith, entered, alive, Bool.false_eq_true, ↓reduceIte] at unchanged
          exact absurd unchanged (State.Entered.refused
            (decideWith_entered project bound σ.cfg place concern positions rest _ _ k
              (State.Entered.refuse wf _).wf))
      | some found =>
          obtain ⟨id, v, k'⟩ := found
          obtain ⟨means', one⟩ := enterExpr_sound σ rules (project assertion) means wf positionsRead denotes
            entered
          have grew := State.Entered.values (s := s) (enterExpr_grew σ.cfg positions (project assertion) wf entered)
          have alive' := σ.alive means'
          cases truth : clauseTruth σ.cfg positions (bound assertion) v k' id with
          | none =>
              simp only [decideWith, entered, alive', truth] at unchanged
              exact absurd unchanged (State.Entered.refusedFrom
                (decideWith_entered project bound σ.cfg place concern positions rest _ _ k'
                  (State.Entered.refuse grew.wf _).wf) rfl)
          | some b =>
              cases b with
              | false =>
                  simp only [decideWith, entered, alive', truth] at unchanged
                  exact absurd unchanged (State.Entered.refusedFrom
                    (decideWith_entered project bound σ.cfg place concern positions rest _ _ k'
                      (State.Entered.refuse grew.wf _).wf) rfl)
              | true =>
                  simp only [decideWith, entered, alive', truth] at unchanged ⊢
                  have holds := σ.domain.truth grew.wf.slots (Asks.nobody_sound _ _ _ _) means' one (clauseTruth_true truth)
                  obtain ⟨means'', others⟩ := decideWith_sound project bound place concern rest (index + 1)
                    { s with values := v } k' means' grew.wf
                    (positionsRead.mono grew.1.1 (fun _ _ h => h))
                    (fun a m => defined a (List.mem_cons_of_mem _ m)) unchanged
                  refine ⟨means'', fun a m => ?_⟩
                  rcases List.mem_cons.mp m with rfl | m
                  · exact ⟨x, denotes, holds⟩
                  · exact others a m

include rules in
theorem decideAll_sound (place : Place) (concern : Concern Raw) {positions : List (Option Ident)}
    {args : List σ.sem.Dyn} {ρ : Leaves σ.sem.Dyn} :
    ∀ (assertions : List (Expr Raw)) (index : Nat) (s : State Raw) (k : σ.cfg.domain.State),
      σ.domain.Means k s.values.table ρ → s.values.WF →
      PositionsRead σ s.values.table ρ positions args →
      (∀ a, a ∈ assertions → ∃ x, Expr.Denotes σ.Runs args a x) →
      (decideAll σ.cfg place concern positions index assertions s k).1.refusals = s.refusals →
      σ.domain.Means (decideAll σ.cfg place concern positions index assertions s k).2
          (decideAll σ.cfg place concern positions index assertions s k).1.values.table ρ ∧
        ∀ a, a ∈ assertions → a.Holds σ.Runs σ.R args :=
  decideWith_sound σ rules id (fun _ => none) place concern

include rules in
theorem decideClauses_sound (place : Place) (concern : Concern Raw) {positions : List (Option Ident)}
    {args : List σ.sem.Dyn} {ρ : Leaves σ.sem.Dyn} (cs : List (ContractClause Raw)) (index : Nat)
    (s : State Raw) (k : σ.cfg.domain.State) (means : σ.domain.Means k s.values.table ρ) (wf : s.values.WF)
    (reads : PositionsRead σ s.values.table ρ positions args)
    (defined : ∀ a ∈ cs.map ContractClause.assertion, ∃ x, Expr.Denotes σ.Runs args a x)
    (ok : (decideClauses σ.cfg place concern positions index cs s k).1.refusals = s.refusals) :
    let result := decideClauses σ.cfg place concern positions index cs s k
    σ.domain.Means result.2 result.1.values.table ρ ∧ ∀ a ∈ cs.map ContractClause.assertion, a.Holds σ.Runs σ.R args := by
  simp only [List.forall_mem_map] at defined ⊢
  exact decideWith_sound σ rules ContractClause.assertion ContractClause.staticBound place concern cs index s k means wf reads defined ok

include rules in
/-- **Learning assertions that hold keeps what the domain's state means.** -/
theorem learnAll_sound {positions : List (Option Ident)} {args : List σ.sem.Dyn}
    {ρ : Leaves σ.sem.Dyn} :
    ∀ (assertions : List (Expr Raw)) (s : State Raw) (k : σ.cfg.domain.State),
      σ.domain.Means k s.values.table ρ → s.values.WF →
      PositionsRead σ s.values.table ρ positions args →
      (∀ a, a ∈ assertions → a.Holds σ.Runs σ.R args) →
      σ.domain.Means (learnAll σ.cfg positions assertions s k).2
        (learnAll σ.cfg positions assertions s k).1.values.table ρ
  | [], _, _, means, _, _, _ => means
  | assertion :: rest, s, k, means, wf, positionsRead, holds => by
      cases entered : enterExpr σ.cfg positions assertion s.values k with
      | none =>
          simp only [learnAll, entered]
          exact learnAll_sound rest s k means wf positionsRead
            (fun a m => holds a (List.mem_cons_of_mem _ m))
      | some found =>
          obtain ⟨id, v, k'⟩ := found
          obtain ⟨x, denotes, isTrue⟩ := holds assertion List.mem_cons_self
          obtain ⟨means', one⟩ := enterExpr_sound σ rules assertion means wf positionsRead denotes
            entered
          have grew := State.Entered.values (s := s) (enterExpr_grew σ.cfg positions assertion wf entered)
          simp only [learnAll, entered]
          exact learnAll_sound rest _ _
            (σ.domain.assume grew.wf.slots (Asks.nobody_sound _ _ _ _) means' one isTrue) grew.wf
            (positionsRead.mono grew.1.1 (fun _ _ h => h))
            (fun a m => holds a (List.mem_cons_of_mem _ m))

end

/-! ## The scope and the invariant are kept -/

section
variable {D : Dialect} {Raw : Type}

/-- Of two additions of refusals that add nothing in all, each adds nothing. -/
theorem State.Entered.unchanged {s t u : State Raw} (first : State.Entered s t)
    (second : State.Entered t u) (unchanged : u.refusals = s.refusals) :
    t.refusals = s.refusals ∧ u.refusals = t.refusals := by
  obtain ⟨-, -, -, new₁, r₁⟩ := first
  obtain ⟨-, -, -, new₂, r₂⟩ := second
  exact ⟨refusals_first r₁ r₂ unchanged, refusals_second r₁ r₂ unchanged⟩

/-- The scope is kept when the values grow and the leaf counter does not go down. -/
theorem Scope.grow {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s s' : State Raw} (scope : Scope sem Run R ρ ids env s)
    (grew : Values.Grew s.values s'.values) (leaves : s.leaves ≤ s'.leaves) :
    Scope sem Run R ρ ids env s' :=
  ⟨fun n above => scope.fresh n (Nat.le_trans leaves above),
    fun τ x => by
      obtain ⟨id, found, read⟩ := scope.agree τ x
      exact ⟨id, found, Reads.mono grew.1 (fun _ _ h => h) read⟩,
    scope.bound, grew.2.1⟩

/-- The scope is kept under leaves that extend these and have no value at or above the counter. -/
theorem Scope.widen {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ ρ' : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) (le : ρ.Le ρ')
    (fresh : ∀ n, s.leaves ≤ n → ρ' n = none) : Scope sem Run R ρ' ids env s :=
  ⟨fresh, fun τ x => by
      obtain ⟨id, found, read⟩ := scope.agree τ x
      exact ⟨id, found, Reads.mono (Table.Le.refl _) le read⟩,
    scope.bound, scope.wf⟩

/-- The invariant is kept by entering, deciding and learning, with what the new domain's state
means. -/
theorem Inv.entered {σ : Setting D Raw} {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {k k' : σ.cfg.domain.State} {s s' : State Raw}
    (inv : Inv σ ρ ids env k s) (entered : State.Entered s s')
    (means : σ.domain.Means k' s'.values.table ρ) : Inv σ ρ ids env k' s' :=
  ⟨inv.toScope.grow entered.1 (Nat.le_of_eq entered.2.1.symm), inv.valid, means⟩

/-- The identifier of a variable reads its value. -/
theorem Scope.idOf_reads {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) {τ : D.Ty}
    (x : Var Γ τ) : Reads Run R.bool s.values.table ρ (idOf ids x.name) ⟨τ, env.get x⟩ := by
  obtain ⟨id, found, read⟩ := scope.agree τ x
  simp only [idOf, found, Option.getD_some]
  exact read

/-- The identifiers of variables read their values. -/
theorem Scope.idsOf_reads {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) :
    ∀ {items : List D.Ty} (xs : HList (Var Γ) items),
      ReadsAll Run R.bool s.values.table ρ (idsOf ids xs) (sem.dyns (env.all xs))
  | [], .nil => .nil
  | _ :: _, .cons x rest => .cons (scope.idOf_reads x) (scope.idsOf_reads rest)

/-- The identifiers of variables are as many as the variables. -/
theorem idsOf_length {α : Type} {Γ : Ctx α} (ids : Ctx Ident) :
    ∀ {items : List α} (xs : HList (Var Γ) items), (idsOf ids xs).length = items.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (idsOf_length ids rest)

/-! ### Names -/

/-- The value of a name in scope. -/
theorem valueOfName_of_find (sem : Semantics D) {Γ : Ctx D.Ty} (env : Env sem.Val Γ) {name : Name}
    {τ : D.Ty} (found : Γ.find? name = some τ) :
    valueOfName sem env name = some ⟨τ, env name τ found⟩ := by
  unfold valueOfName
  split
  · next τ' found' =>
      have same : τ' = τ := Option.some.inj (found'.symm.trans found)
      subst same
      rfl
  · next found' =>
      rw [found] at found'
      cases found'

/-- What a map in the option monad gives of a list with a first element. -/
theorem mapM_cons_eq_some {α β : Type} {f : α → Option β} {a : α} {as : List α} {cs : List β}
    (h : (a :: as).mapM f = some cs) :
    ∃ b bs, f a = some b ∧ as.mapM f = some bs ∧ cs = b :: bs := by
  rw [List.mapM_cons] at h
  cases first : f a with
  | none => rw [first] at h; cases h
  | some b =>
      cases others : as.mapM f with
      | none => rw [first, others] at h; cases h
      | some bs =>
          rw [first, others] at h
          cases h
          exact ⟨b, bs, rfl, rfl, rfl⟩

/-- A map in the option monad that gives a value of the first element and of the others. -/
theorem mapM_cons_of_some {α β : Type} {f : α → Option β} {a : α} {as : List α} {b : β}
    {bs : List β} (first : f a = some b) (others : as.mapM f = some bs) :
    (a :: as).mapM f = some (b :: bs) := by
  rw [List.mapM_cons, first, others]
  rfl

/-- **The names that have identifiers have values and types**, and the identifiers read the
values. -/
theorem Scope.names_read {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) :
    ∀ (names : List Name) (found : List Ident), names.mapM ids.find? = some found →
      ∃ vs, valuesOfNames sem env names = some vs ∧ typesOf Γ names = some (vs.map Sigma.fst) ∧
        ReadsAll Run R.bool s.values.table ρ found vs
  | [], found, h => by
      rw [List.mapM_nil] at h
      cases h
      exact ⟨[], rfl, rfl, .nil⟩
  | name :: names, _, h => by
      obtain ⟨id, ids', at_, rest, rfl⟩ := mapM_cons_eq_some h
      obtain ⟨τ, typed⟩ := scope.bound name id at_
      obtain ⟨id', at', read⟩ := scope.agree τ ⟨name, typed⟩
      rw [at_] at at'
      cases at'
      obtain ⟨vs, values, types, reads⟩ := scope.names_read names ids' rest
      exact ⟨⟨τ, env name τ typed⟩ :: vs,
        mapM_cons_of_some (valueOfName_of_find sem env typed) values,
        mapM_cons_of_some typed types, .cons read reads⟩

/-- Values with their types, as a list of values of their types. -/
def dynsList (sem : Semantics D) : (vs : List sem.Dyn) → HList sem.Val (vs.map Sigma.fst)
  | [] => .nil
  | v :: rest => .cons v.2 (dynsList sem rest)

/-- Values with their types, as a list of values of their types, are the same values. -/
theorem dyns_dynsList (sem : Semantics D) : ∀ vs : List sem.Dyn, sem.dyns (dynsList sem vs) = vs
  | [] => rfl
  | v :: rest => by
      show ⟨v.1, v.2⟩ :: sem.dyns (dynsList sem rest) = v :: rest
      rw [dyns_dynsList sem rest]

/-- A list of valid dynamic values realizes the argument context carried by those values. -/
theorem typedValues (sem : Semantics D) (Valid : sem.Dyn → Prop) (vs : List sem.Dyn)
    (valid : ∀ v, v ∈ vs → Valid v) :
    ArgumentsMatch (TypedValue sem Valid) vs (vs.map Sigma.fst) := by
  induction vs with
  | nil => exact .nil
  | cons v rest ih =>
      exact .cons ⟨valid v List.mem_cons_self, rfl⟩
        (ih (fun x member => valid x (List.mem_cons_of_mem _ member)))

/-- Valid intrinsic values realize their declared argument context. -/
theorem ArgumentsMatch.ofValues {sem : Semantics D} {Valid : sem.Dyn → Prop} :
    ∀ {ts} (xs : HList sem.Val ts), (∀ v, v ∈ sem.dyns xs → Valid v) →
      ArgumentsMatch (TypedValue sem Valid) (sem.dyns xs) ts
  | _, .nil, _ => .nil
  | _, .cons _ rest, valid => .cons ⟨valid _ List.mem_cons_self, rfl⟩
      (ArgumentsMatch.ofValues rest fun v h => valid v (List.mem_cons_of_mem _ h))

/-- A matching argument list is the erasure of valid values in exactly the declared context. -/
theorem ArgumentsMatch.realizes {sem : Semantics D} {Valid : sem.Dyn → Prop}
    {vs : List sem.Dyn} {types : List D.Ty} (matched : ArgumentsMatch (TypedValue sem Valid) vs types) :
    ∃ args : HList sem.Val types, sem.dyns args = vs ∧ ∀ v, v ∈ vs → Valid v := by
  induction matched with
  | nil => exact ⟨.nil, rfl, fun _ h => nomatch h⟩
  | @cons v t vs ts head _ ih =>
      obtain ⟨valid, rfl⟩ := head
      obtain ⟨args, erased, validTail⟩ := ih
      refine ⟨.cons v.2 args, congrArg (v :: ·) erased, ?_⟩
      intro x member
      rcases List.mem_cons.mp member with rfl | later
      · exact valid
      · exact validTail x later

/-- A theorem author can prove a lemma directly on intrinsically typed arguments. -/
theorem Lemma.valid_iff_typed {σ : Setting D Raw} (l : Lemma D.Ty Raw) :
    l.Valid σ.Runs σ.R (TypedValue σ.sem σ.Valid) ↔
      ∀ args : HList σ.sem.Val l.parameters, σ.AllValid args →
        (∀ p, p ∈ l.premises → p.Holds σ.Runs σ.R (σ.sem.dyns args)) →
        l.conclusion.Holds σ.Runs σ.R (σ.sem.dyns args) := by
  constructor
  · intro law args valid
    exact law _ (ArgumentsMatch.ofValues args valid)
  · intro law vs matched premises
    obtain ⟨args, rfl, valid⟩ := matched.realizes
    exact law args valid premises

/-- An assertion defined at the types of valid values names a value of them. -/
theorem Expr.Defined.at_values {σ : Setting D Raw} {vs : List σ.sem.Dyn} {a : Expr Raw}
    (defined : Expr.Defined σ (vs.map Sigma.fst) a) (valid : ∀ v, v ∈ vs → σ.Valid v) :
    ∃ x, Expr.Denotes σ.Runs vs a x := by
  have named := defined (dynsList σ.sem vs) (by rw [dyns_dynsList]; exact valid)
  rwa [dyns_dynsList] at named

end

/-! ## The annotations at an instruction -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) (laws : σ.Lawful)

include laws in
/-- **The annotations at an instruction keep the invariant when they refuse nothing**: the premises
of each stated step, defined at the types of the names it lists, are decided and hold, so the
conclusion holds by the lemma and is learned; each given fact holds and is learned. -/
theorem annotate_sound (site : AnnotationSite) {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} :
    ∀ (notes : List (Annotation Raw)) (s : State Raw) (k : σ.cfg.domain.State),
      Inv σ ρ ids env k s →
      (∀ lemma names, Annotation.step lemma names ∈ notes →
        ∃ l, σ.cfg.lemmas[lemma]? = some l ∧ typesOf Γ names = some l.parameters ∧
          ∀ premise, premise ∈ l.premises → Expr.Defined σ l.parameters premise) →
      (∀ uses assertion, Annotation.fact uses assertion ∈ notes →
        ∀ vs, valuesOfNames σ.sem env uses = some vs → assertion.Holds σ.Runs σ.R vs) →
      (annotate σ.cfg site ids notes s k).1.refusals = s.refusals →
      Inv σ ρ ids env (annotate σ.cfg site ids notes s k).2 (annotate σ.cfg site ids notes s k).1
  | [], _, _, inv, _, _, _ => inv
  | .invariant _ _ :: rest, s, k, inv, steps, facts, unchanged =>
      annotate_sound site rest s k inv
        (fun lemma names m => steps lemma names (List.mem_cons_of_mem _ m))
        (fun uses a m => facts uses a (List.mem_cons_of_mem _ m)) unchanged
  | .step lemma names :: rest, s, k, inv, steps, facts, unchanged => by
      have alive := σ.alive inv.means
      have steps' := fun lemma names m => steps lemma names (List.mem_cons_of_mem _ m)
      have facts' := fun uses a m => facts uses a (List.mem_cons_of_mem _ m)
      cases found : σ.cfg.lemmas[lemma]? with
      | none =>
          simp only [annotate, found, alive, Bool.false_eq_true, ↓reduceIte] at unchanged
          exact absurd unchanged (State.Entered.refusedFrom
            (annotate_entered σ.cfg site ids rest _ k (State.Entered.refuse inv.wf _).wf) rfl)
      | some l =>
          cases positions : namesAt ids names with
          | none =>
              simp only [annotate, found, positions, decideAt, learnAt, alive] at unchanged ⊢
              obtain ⟨first, -⟩ := State.Entered.unchanged
                (refuseAll_entered (site.place σ.cfg) (.premise site (.step lemma names)) false l.premises 0 s inv.wf)
                (annotate_entered σ.cfg site ids rest _ k
                  (refuseAll_entered (site.place σ.cfg) (.premise site (.step lemma names)) false l.premises 0 s
                    inv.wf).wf) unchanged
              have empty := refuseAll_refuses (site.place σ.cfg) _ l.premises 0 s inv.wf first
              rw [empty] at unchanged ⊢
              exact annotate_sound site rest s k inv steps' facts' unchanged
          | some ps =>
              obtain ⟨found', at_, rfl⟩ := Option.map_eq_some_iff.mp positions
              obtain ⟨vs, -, types, reads⟩ := inv.toScope.names_read names found' at_
              have valid := ReadsAll.valid inv.valid reads
              obtain ⟨declared, declaredAt, typed, premisesDefined⟩ :=
                steps lemma names List.mem_cons_self
              have same : declared = l := Option.some.inj (declaredAt.symm.trans found)
              subst declared
              have argumentTypes : vs.map Sigma.fst = l.parameters :=
                Option.some.inj (types.symm.trans typed)
              have defined : ∀ a, a ∈ l.premises → ∃ x, Expr.Denotes σ.Runs vs a x :=
                fun a m => Expr.Defined.at_values
                  (argumentTypes ▸ premisesDefined a m) valid
              simp only [annotate, found, positions, decideAt, learnAt] at unchanged ⊢
              have decidedEntered := decideAll_entered σ.cfg (site.place σ.cfg) (.premise site (.step lemma names))
                (found'.map some) l.premises 0 s k inv.wf
              have decidedSound := fun unchanged =>
                decideAll_sound σ laws.rules (site.place σ.cfg) (.premise site (.step lemma names)) l.premises 0 s k
                  inv.means inv.wf (PositionsRead.of_readsAll reads) defined unchanged
              generalize decideAll σ.cfg (site.place σ.cfg) (.premise site (.step lemma names)) (found'.map some) 0
                l.premises s k = decided at decidedEntered decidedSound unchanged ⊢
              obtain ⟨decidedState, decidedKnown⟩ := decided
              have learnedEntered := learnAll_entered σ.cfg (found'.map some) [l.conclusion]
                decidedState decidedKnown decidedEntered.wf
              have restEntered := annotate_entered σ.cfg site ids rest _
                (learnAll σ.cfg (found'.map some) [l.conclusion] decidedState decidedKnown).2
                learnedEntered.wf
              obtain ⟨first, second⟩ := State.Entered.unchanged (decidedEntered.trans learnedEntered)
                restEntered unchanged
              obtain ⟨-, third⟩ := State.Entered.unchanged decidedEntered learnedEntered first
              obtain ⟨decidedMeans, premisesHold⟩ :=
                decidedSound (third.symm.trans first)
              have conclusionHolds :=
                laws.lemmas l (List.mem_of_getElem? found) vs
                  (argumentTypes ▸ typedValues σ.sem σ.Valid vs valid) premisesHold
              have learnedMeans := learnAll_sound σ laws.rules [l.conclusion] decidedState
                decidedKnown decidedMeans decidedEntered.wf
                (PositionsRead.of_readsAll (ReadsAll.mono decidedEntered.1.1 (fun _ _ h => h) reads))
                (fun a m => by
                  rcases List.mem_cons.mp m with rfl | m
                  · exact conclusionHolds
                  · cases m)
              exact annotate_sound site rest _ _
                ((inv.entered decidedEntered decidedMeans).entered learnedEntered learnedMeans)
                steps' facts' second
  | .fact uses assertion :: rest, s, k, inv, steps, facts, unchanged => by
      have steps' := fun lemma names m => steps lemma names (List.mem_cons_of_mem _ m)
      have facts' := fun uses a m => facts uses a (List.mem_cons_of_mem _ m)
      cases positions : namesAt ids uses with
      | none =>
          simp only [annotate, positions, learnAt] at unchanged ⊢
          exact annotate_sound site rest s k inv steps' facts' unchanged
      | some ps =>
          obtain ⟨found', at_, rfl⟩ := Option.map_eq_some_iff.mp positions
          obtain ⟨vs, values, -, reads⟩ := inv.toScope.names_read uses found' at_
          have holds := facts uses assertion List.mem_cons_self vs values
          simp only [annotate, positions, learnAt] at unchanged ⊢
          have learnedEntered := learnAll_entered σ.cfg (found'.map some) [assertion] s k inv.wf
          have restEntered := annotate_entered σ.cfg site ids rest _
            (learnAll σ.cfg (found'.map some) [assertion] s k).2 learnedEntered.wf
          obtain ⟨-, second⟩ := State.Entered.unchanged learnedEntered restEntered unchanged
          have learnedMeans := learnAll_sound σ laws.rules [assertion] s k inv.means inv.wf
            (PositionsRead.of_readsAll reads)
            (fun a m => by
              rcases List.mem_cons.mp m with rfl | m
              · exact holds
              · cases m)
          exact annotate_sound site rest _ _ (inv.entered learnedEntered learnedMeans)
            steps' facts' second

include laws in
/-- **The annotations at the entry of an instruction keep the invariant** when they refuse nothing,
with the premises of its stated steps defined and its given facts holding. -/
theorem atEntry_inv {Γ : Ctx D.Ty} {mid : List D.Ty} (cursor : StaticCursor) (key : Key)
    (i : Instr D Γ mid) {path : List Frame} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {s : State Raw} {k : σ.cfg.domain.State}
    (inv : Inv σ ρ ids env k s) (steps : StepsDefinedAt σ Γ (Instr.site cursor key i)) (facts : FactsAt σ cursor key i path env)
    (unchanged : (atEntry σ.cfg σ.notes (Instr.site cursor key i) ids s k).1.refusals = s.refusals) :
    Inv σ ρ ids env (atEntry σ.cfg σ.notes (Instr.site cursor key i) ids s k).2
      (atEntry σ.cfg σ.notes (Instr.site cursor key i) ids s k).1 :=
  annotate_sound σ laws _ _ s k inv steps facts unchanged

end

#print axioms enterExpr_sound
#print axioms decideAll_sound
#print axioms learnAll_sound
#print axioms atEntry_entered
#print axioms atEntry_inv

end Zkc.Core.BodyAnalysis

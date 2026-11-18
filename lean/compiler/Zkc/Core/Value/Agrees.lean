module

public import Zkc.Core.Value.Runs

@[expose] public section

/-!
Names that agree with a table, and what a skeleton's run reads of them, for any dialect and any
semantics.

The names in scope agree with a table, a bound and a valuation (`Agrees`) when each has an
identifier below the bound that reads, from the leaves through the table, as the environment's
value. The agreement goes along a binding as the environment does, a later name hiding an earlier
one in both, and grows with the table and the valuation. How often a loop runs is what its count
on the identifiers says (`Times.count_is`); operands that read in the order written read, in the
order in which the table places an application, as values on which the written operation gives
the same results (`ValueRules.Binding.reads_order`, by the law `commutative`); and an application
that is shared has results that read as what it gives (`FactCheck.share_reads`). The walk that
builds and follows skeletons (`Facts/WalkRuns.lean`) proves that a term runs its skeleton with
these.
-/

namespace Zkc.Core

open FactCheck (Valuation Table St share fresh idOf idsOf bindIds Support)

section
variable {D : Dialect} {Raw : Type} (sem : Semantics D)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)

/-! ## Names that agree with a table -/

variable [DecidableEq Raw] (rules : ValueRules D Raw) {undefined : sem.H → Prop}

/-- The names in scope have identifiers below the next one, and each reads, from the leaves
through the table, as the environment's value. -/
def Agrees {Γ : Ctx D.Ty} (table : Table Raw) (next : Nat) (ρ : Valuation sem.Dyn)
    (ids : Ctx Nat) (env : Env sem.Val Γ) : Prop :=
  ∀ τ (x : Var Γ τ), ∃ i, ids.find? x.name = some i ∧ i < next ∧
    Reads Run table ρ i ⟨τ, env.get x⟩

section
variable {sem} {Run}
omit [DecidableEq Raw]

/-- Names that agree with a table, a bound and a valuation agree with a table with its entries,
a higher bound and a valuation with its values. -/
theorem Agrees.mono {Γ : Ctx D.Ty} {table table' : Table Raw} {next next' : Nat}
    {ρ ρ' : Valuation sem.Dyn} {ids : Ctx Nat} {env : Env sem.Val Γ}
    (agrees : Agrees sem Run table next ρ ids env) (sub : ∀ e, e ∈ table → e ∈ table')
    (le : next ≤ next') (grown : ρ.Le ρ') : Agrees sem Run table' next' ρ' ids env :=
  fun τ x => by
    obtain ⟨i, found, below, read⟩ := agrees τ x
    exact ⟨i, found, Nat.lt_of_lt_of_le below le, Reads.mono Run table sub grown read⟩

/-- A variable has an identifier below the bound, which reads as its value. -/
theorem Agrees.read {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn}
    {ids : Ctx Nat} {env : Env sem.Val Γ} (agrees : Agrees sem Run table next ρ ids env)
    {τ : D.Ty} (x : Var Γ τ) :
    idOf ids x.name < next ∧ Reads Run table ρ (idOf ids x.name) ⟨τ, env.get x⟩ := by
  obtain ⟨i, found, below, read⟩ := agrees τ x
  simp only [FactCheck.idOf, found, Option.getD_some]
  exact ⟨below, read⟩

/-- Variables read, at their identifiers, as their values. -/
theorem Agrees.readsAll {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn}
    {ids : Ctx Nat} {env : Env sem.Val Γ} (agrees : Agrees sem Run table next ρ ids env) :
    ∀ {items : List D.Ty} (xs : HList (Var Γ) items),
      ReadsAll Run table ρ (idsOf ids xs) (sem.dyns (env.all xs))
  | [], .nil => .nil
  | _ :: _, .cons x rest => .cons (agrees.read x).2 (agrees.readsAll rest)

/-- Names that agree are in scope below the bound. -/
theorem Agrees.inScope {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn}
    {ids : Ctx Nat} {env : Env sem.Val Γ} (agrees : Agrees sem Run table next ρ ids env) :
    FactCheck.InScope Γ ids next := fun name τ found => by
  obtain ⟨i, known, below, _⟩ := agrees τ ⟨name, found⟩
  exact ⟨i, known, below⟩

/-- A name bound to an identifier below the bound that reads as its value keeps the names in
agreement. -/
theorem Agrees.insert {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn}
    {ids : Ctx Nat} {env : Env sem.Val Γ} (agrees : Agrees sem Run table next ρ ids env)
    (bound : Name) {τ : D.Ty} (v : sem.Val τ) {i : Nat} (below : i < next)
    (read : Reads Run table ρ i ⟨τ, v⟩) :
    Agrees sem Run table next ρ (ids.insert bound i) (env.insert bound v) := fun σ x => by
  by_cases same : x.name = bound
  · have typed := x.typed
    rw [Ctx.find?_insert, ite_eq_left same] at typed
    obtain rfl := Option.some.inj typed
    refine ⟨i, by rw [Ctx.find?_insert, ite_eq_left same], below, ?_⟩
    rw [show (env.insert bound v).get x = v from
      eq_of_heq (Env.insert_at_bound env bound v same x.typed)]
    exact read
  · have typed : Γ.find? x.name = some σ := by
      have typed := x.typed
      rw [Ctx.find?_insert, ite_eq_right same] at typed
      exact typed
    obtain ⟨j, found, below', read'⟩ := agrees σ ⟨x.name, typed⟩
    refine ⟨j, by rw [Ctx.find?_insert, ite_eq_right same]; exact found, below', ?_⟩
    rw [show (env.insert bound v).get x = env.get ⟨x.name, typed⟩ from
      Env.insert_at_other env bound v same x.typed]
    exact read'

/-- The names of a binding bound to identifiers below the bound that read as its values keep
the names in agreement. -/
theorem Agrees.bind {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn} :
    ∀ {Γ : Ctx D.Ty} {ids : Ctx Nat} {env : Env sem.Val Γ} {types : List D.Ty}
      (names : Names types) (values : HList sem.Val types) (made : List Nat),
      Agrees sem Run table next ρ ids env → ReadsAll Run table ρ made (sem.dyns values) →
      (∀ i, i ∈ made → i < next) →
      Agrees sem Run table next ρ (bindIds ids names made) (env.extend names values)
  | _, _, _, [], .nil, .nil, _, agrees, _, _ => agrees
  | _, _, _, _ :: _, .cons name rest, .cons v vs, _ :: is, agrees, reads, below => by
      cases reads with
      | cons read reads =>
        exact Agrees.bind rest vs is (agrees.insert name v (below _ List.mem_cons_self) read) reads
          fun j m => below j (List.mem_cons_of_mem _ m)
  | _, _, _, _ :: _, .cons _ _, .cons _ _, [], _, reads, _ => by cases reads

/-- The names of a binding bound to leaves from an identifier on, set to its values in a
valuation with nothing from below them on, agree, and the valuation has nothing after them. -/
theorem Agrees.leaves {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat} {ρ : Valuation sem.Dyn}
    {ids : Ctx Nat} {env : Env sem.Val Γ} (agrees : Agrees sem Run table next ρ ids env)
    {lo : Nat} (support : Support lo ρ) {types : List D.Ty} (names : Names types)
    (values : HList sem.Val types) (results count : Nat) (length : types.length = count)
    (above : lo ≤ results) (below : results + count ≤ next) :
    Support (results + count) (ρ.setFrom results (sem.dyns values)) ∧
      Agrees sem Run table next (ρ.setFrom results (sem.dyns values))
        (bindIds ids names (List.range' results count)) (env.extend names values) := by
  subst length
  refine ⟨?_, ?_⟩
  · have support' := FactCheck.setFrom_support (support.mono above) (sem.dyns values)
    rwa [sem.dyns_length] at support'
  · have reads := ReadsAll.setFrom Run table ρ results (sem.dyns values)
    rw [sem.dyns_length] at reads
    exact Agrees.bind names values _
      (agrees.mono (fun _ known => known) (Nat.le_refl _)
        (FactCheck.setFrom_le (support.mono above) _))
      reads fun i m => by
        have := mem_range'_bounds m
        omega

/-- The inputs of a definition bound to the first identifiers, set to their values in a valuation
that has nothing else, agree over every table, and the valuation has nothing after them. -/
theorem Agrees.start {table : Table Raw} {types : List D.Ty} (inputs : Names types)
    (values : HList sem.Val types) :
    Support types.length (FactCheck.Valuation.setFrom (fun _ => none) 0 (sem.dyns values)) ∧
      Agrees sem Run table types.length
        (FactCheck.Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
        (bindIds Ctx.empty inputs (List.range types.length)) (Env.empty.extend inputs values) := by
  have empty : Agrees sem Run table types.length (fun _ => none) (Ctx.empty : Ctx Nat)
      (Env.empty : Env sem.Val Ctx.empty) := fun _ x => by
    have typed := x.typed
    rw [Ctx.find?_empty] at typed
    cases typed
  have bound := empty.leaves (lo := 0) (fun _ _ => rfl) inputs values 0 types.length rfl
    (Nat.le_refl 0) (by omega)
  rw [Nat.zero_add] at bound
  rw [List.range_eq_range']
  exact bound

/-- How often a loop runs, in an environment that agrees with the names, is what its count on
the identifiers says. -/
theorem Times.count_is {w : D.Who} {Γ : Ctx D.Ty} {table : Table Raw} {next : Nat}
    {ρ : Valuation sem.Dyn} {ids : Ctx Nat} {env : Env sem.Val Γ}
    (agrees : Agrees sem Run table next ρ ids env) :
    ∀ times : Times D w Γ, (times.count ids).Is sem Run table ρ (sem.times times env)
  | .fixed _ => rfl
  | .value count _ => ⟨env.get count, (agrees.read count).2, rfl⟩

variable {rules} in
/-- Operands that read in the order written read, in the order in which the table places an
application of a written operation, as values on which it gives the same results: the two
operands of an operation that commutes, exchanged, by the law `commutative`. -/
theorem ValueRules.Binding.reads_order (binding : rules.Binding sem Run undefined)
    {table : Table Raw} {ρ : Valuation sem.Dyn} (raw : Raw) :
    ∀ {ids : List Nat} {operands results : List sem.Dyn},
      ReadsAll Run table ρ ids operands → Run raw operands results →
      ∃ operands', ReadsAll Run table ρ (rules.order raw ids) operands' ∧
        Run raw operands' results
  | [], _, _, read, ran => ⟨_, read, ran⟩
  | [_], _, _, read, ran => ⟨_, read, ran⟩
  | [_, _], _, results, read, ran => by
      simp only [ValueRules.order]
      split
      · next exchanged =>
          cases read with
          | cons readFirst others =>
            cases others with
            | cons readSecond none =>
              cases none
              exact ⟨_, .cons readSecond (.cons readFirst .nil),
                binding.commutative raw exchanged.1 _ _ results ran⟩
      · exact ⟨_, read, ran⟩
  | _ :: _ :: _ :: _, _, _, read, ran => ⟨_, read, ran⟩

end

/-- What a loop gives, with the types, is the same with the collected types of its count on the
identifiers as with those of its count. -/
theorem Times.dyns_collected {w : D.Who} {Γ : Ctx D.Ty} {carried each : List D.Ty}
    (ids : Ctx Nat) :
    ∀ (times : Times D w Γ) (state : sem.LoopState carried each),
      sem.dyns (state.1.append (sem.collected (times.count ids).size state.2)) =
        sem.dyns (state.1.append (sem.collected times.size state.2))
  | .fixed _, _ => rfl
  | .value _ _, _ => rfl

omit [DecidableEq Raw] in
/-- A written operation applied to operands, shared, has results that read as what it gives on
the operands' values. -/
theorem FactCheck.share_reads [DecidableEq Raw] {Val : Type}
    {Run : Raw → List Val → List Val → Prop} {T : Type} (written : Raw) (args : List Nat)
    (count : Nat) (st : St T Raw) {ρ : Valuation Val} {operands results : List Val}
    (read : ReadsAll Run (share written args count st).2.table ρ args operands)
    (ran : Run written operands results) (length : results.length = count) :
    ReadsAll Run (share written args count st).2.table ρ (share written args count st).1
      results := by
  cases found : st.table.find written args count with
  | some lo =>
      simp only [share, found] at read ⊢
      obtain ⟨e, known, sameWritten, sameArgs, sameCount, sameLo⟩ := FactCheck.Table.find_spec found
      subst sameWritten sameArgs sameCount sameLo
      exact ReadsAll.results Run st.table known read ran length
  | none =>
      simp only [share, found] at read ⊢
      subst length
      exact ReadsAll.results Run _ (e := ⟨written, args, st.next, results.length⟩)
        (show _ ∈ (_ :: st.table.entries) from List.mem_cons_self) read ran rfl

end

end Zkc.Core

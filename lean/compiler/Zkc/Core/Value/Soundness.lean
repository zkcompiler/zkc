module

public import Zkc.Core.Value.Runs

@[expose] public section

/-!
The soundness of the value form and of following, for any dialect and any semantics whose
values satisfy the laws of `ValueRules.Binding`.

A term that never stops `undefined` runs its own skeleton, over the table that the skeleton is
built with (`Term.skeleton_runs`): each value of the term reads through its shared entry (the
operands of an operation that commutes, in the order of the table, by the law `commutative`:
`ValueRules.Binding.reads_order`), each leaf is set to what the term binds there, and the names
in scope read as the environment's
values (`Agrees`). A term that follows a skeleton and never stops `undefined` runs it, over the
table that following gives, when the skeleton's leaves are made in order above every value that
the run already has (`Term.follows_runs`). So two definitions of which the second follows the
skeleton of the first mean the same on every input on which neither stops `undefined`
(`followsSkeleton_sound`).
-/

namespace Zkc.Core

open FactCheck (Valuation Table St share fresh idOf idsOf bindIds Support)

section
variable {D : Dialect} {Raw : Type} (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)

/-! ## A term runs its skeleton -/

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

/-! ### The run of a term over its skeleton -/

mutual
  /-- A term that never stops `undefined` runs its own skeleton over the table that the skeleton
  is built with. -/
  theorem Term.denote_runs_skeleton (binding : rules.Binding sem Run undefined) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (st : St D.Ty Raw)
        (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn),
        Table.WF st.next st.table → Support st.next ρ →
        Agrees sem Run st.table st.next ρ ids env →
        (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
        Skel.Runs sem permitted Run (t.skeleton rules ids st).2.table path ρ
          (t.skeleton rules ids st).1 (t.denote sem path env)
    | _, _, .ret exit, _, _, _, _, _, _, _, agrees, _ => by
        simp only [Term.skeleton, Term.denote]
        exact .ret _ (agrees.readsAll exit)
    | _, _, .op (res := res) key o operands results rest, ids, st, path, env, ρ, wf, support,
        agrees, safe => by
        cases written : rules.written o with
        | some raw =>
            simp only [Term.skeleton, written]
            rcases binding.computes o raw written key path (env.all operands) with
              ⟨values, ran, run⟩ | ⟨stop, halted, bad⟩
            · simp only [Term.denote, ran, Process.bind] at safe ⊢
              obtain ⟨wf', grows, made⟩ :=
                FactCheck.share_grows raw (rules.order raw (idsOf ids operands)) res.length st wf
                  (rules.order_lt (FactCheck.idsOf_lt agrees.inScope operands))
              have agrees' := agrees.mono grows.sub grows.next (.refl ρ)
              obtain ⟨ordered, readOrdered, runOrdered⟩ :=
                binding.reads_order raw (agrees'.readsAll operands) run
              have reads := FactCheck.share_reads raw (rules.order raw (idsOf ids operands))
                res.length st readOrdered runOrdered (sem.dyns_length values)
              exact Term.denote_runs_skeleton binding rest _ _ path _ ρ wf' (support.mono
                grows.next) (Agrees.bind results values _ agrees' reads made) safe
            · simp only [Term.denote, halted, Process.bind] at safe
              exact absurd bad safe
        | none =>
            simp only [Term.skeleton, written]
            simp only [Term.denote] at safe ⊢
            obtain ⟨wf', grows, made⟩ := FactCheck.fresh_grows res.length st wf
            obtain ⟨-, grows', -⟩ := Term.skeleton_state rules rest _ _
              (FactCheck.InScope.bind results _ (agrees.inScope.mono grows.next) (by simp [fresh])
                made) wf'
            refine .effect (env.all operands)
              (ReadsAll.mono Run _ (grows.trans grows').sub (.refl ρ) (agrees.readsAll operands))
              fun returned returns => ?_
            have bound := (agrees.mono grows.sub grows.next (.refl ρ)).leaves support results
              returned st.next res.length rfl (Nat.le_refl _) (Nat.le_refl _)
            exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf' bound.1 bound.2
              (safe.of_bind_canReturn returns)
    | _, _, .guard key w c ok why rest, ids, st, path, env, ρ, wf, support, agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        obtain ⟨-, grows, -⟩ := Term.skeleton_state rules rest ids st agrees.inScope wf
        have read := Reads.mono Run _ grows.sub (.refl ρ) (agrees.read c).2
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            exact .guardHolds _ read holds
              (Term.denote_runs_skeleton binding rest ids st path env ρ wf support agrees safe)
        | false =>
            simp only [Bool.cond_false]
            exact .guardStops _ read holds
    | _, _, .choose (mid := mid) key w c ok _ onTrue onFalse results rest, ids, st, path, env, ρ,
        wf, support, agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules onTrue ids st scope wf
        obtain ⟨wf2, grows2, -⟩ := Term.skeleton_state rules onFalse ids _ (scope.mono grows1.next)
            wf1
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf2
        obtain ⟨-, grows4, -⟩ := Term.skeleton_state rules rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans (grows2.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have read := Reads.mono Run _ (grows1.trans (grows2.trans (grows3.trans grows4))).sub
          (.refl ρ) (agrees.read c).2
        have toRest := grows1.trans (grows2.trans grows3)
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            refine .chooseTrue _ read holds
              (Skel.Runs.grow sem permitted Run _ (grows2.trans (grows3.trans grows4)).sub _
                (Term.denote_runs_skeleton binding onTrue ids st path env ρ wf support agrees
                  safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
              (support.mono (grows1.trans grows2).next) results returned _ mid.length rfl
              (Nat.le_refl _) (Nat.le_refl _)
            exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
              (safe.of_bind_canReturn returns)
        | false =>
            simp only [holds, Bool.cond_false] at safe ⊢
            refine .chooseFalse _ read holds
              (Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
                (Term.denote_runs_skeleton binding onFalse ids _ path env ρ wf1
                  (support.mono grows1.next) (agrees.mono grows1.sub grows1.next (.refl ρ))
                  safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
              (support.mono (grows1.trans grows2).next) results returned _ mid.length rfl
              (Nat.le_refl _) (Nat.le_refl _)
            exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
              (safe.of_bind_canReturn returns)
    | _, _, .cases (mid := mid) key w x ok _ arms results rest, ids, st, path, env, ρ, wf, support,
        agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1, -⟩ := Arms.skeleton_state rules arms ids st scope wf
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨-, grows4, -⟩ := Term.skeleton_state rules rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans grows3).next)
            (by simp [fresh]) made) wf3
        refine .cases (env.get x)
          (Reads.mono Run _ (grows1.trans (grows3.trans grows4)).sub (.refl ρ) (agrees.read x).2)
          (SkelArms.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (Arms.denote_runs_skeleton binding arms ids st path env ρ (sem.pick ok (env.get x)) wf
              support agrees safe.of_bind))
          fun returned returns => ?_
        have bound := (agrees.mono (grows1.trans grows3).sub (grows1.trans grows3).next
          (.refl ρ)).leaves (support.mono grows1.next) results returned _ mid.length rfl
          (Nat.le_refl _) (Nat.le_refl _)
        exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
          (safe.of_bind_canReturn returns)
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, ids, st, path, env, ρ, wf, support, agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows (carried.length + 1) st wf
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules body _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows (carried.length + each.length) _ wf1
        obtain ⟨-, grows4, -⟩ := Term.skeleton_state rules rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows0.trans (grows1.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have toEnd := grows0.trans (grows1.trans (grows3.trans grows4))
        have toRest := grows0.trans (grows1.trans grows3)
        let bodyOf : Nat → HList sem.Val carried →
            Process sem.S sem.H (HList sem.Val (carried ++ each)) := fun i values =>
          body.denote sem (path ++ [.iteration key i])
            (env.extend inputs (.cons (sem.index w i) values))
        have step : sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key
            path env = sem.stepOf bodyOf := rfl
        rw [step] at safe ⊢
        refine .loop (sem.times times env)
          (Count.Is.mono sem Run _ toEnd.sub (.refl ρ) (Times.count_is agrees times))
          (env.all initial) (ReadsAll.mono Run _ toEnd.sub (.refl ρ) (agrees.readsAll initial))
          bodyOf (fun i state below returns => ?_) (fun final returns => ?_)
        · have bound := (agrees.mono grows0.sub grows0.next (.refl ρ)).leaves support inputs
            (.cons (sem.index w i) state.1) st.next (carried.length + 1) rfl (Nat.le_refl _)
            (Nat.le_refl _)
          have safeStep := Process.Every.iterate_step i _ 0 _ state below safe.of_bind returns
          rw [Nat.zero_add] at safeStep
          exact Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (Term.denote_runs_skeleton binding body _ _ _ _ _ wf0 bound.1 bound.2
              safeStep.of_bind)
        · rw [Times.dyns_collected sem ids times final]
          have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
            (support.mono (grows0.trans grows1).next) results
            (final.1.append (sem.collected times.size final.2)) _ (carried.length + each.length)
            (by simp) (Nat.le_refl _) (Nat.le_refl _)
          exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
            (safe.of_bind_canReturn returns)
    | _, _, .block (mid := mid) key number body results rest, ids, st, path, env, ρ, wf, support,
        agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules body ids st scope wf
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨-, grows4, -⟩ := Term.skeleton_state rules rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows1.trans grows3).next)
            (by simp [fresh]) made) wf3
        refine .block (Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (Term.denote_runs_skeleton binding body ids st _ env ρ wf support agrees safe.of_bind))
          fun returned returns => ?_
        have bound := (agrees.mono (grows1.trans grows3).sub (grows1.trans grows3).next
          (.refl ρ)).leaves (support.mono grows1.next) results returned _ mid.length rfl
          (Nat.le_refl _) (Nat.le_refl _)
        exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
          (safe.of_bind_canReturn returns)
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, st, path, env, ρ, wf,
        support, agrees, safe => by
        simp only [Term.skeleton, Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows 1 st wf
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules body _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨wf3, grows3, made⟩ := FactCheck.fresh_grows mid.length _ wf1
        obtain ⟨-, grows4, -⟩ := Term.skeleton_state rules rest _ _
          (FactCheck.InScope.bind results _ (scope.mono (grows0.trans (grows1.trans grows3)).next)
            (by simp [fresh]) made) wf3
        have toRest := grows0.trans (grows1.trans grows3)
        refine .attempt (fun number => body.denote sem path (env.extend inputs (.cons number .nil)))
          (fun number began => ?_) (fun number returned began ran settled => ?_)
        · have bound := (agrees.mono grows0.sub grows0.next (.refl ρ)).leaves support inputs
            (.cons number .nil) st.next 1 rfl (Nat.le_refl _) (Nat.le_refl _)
          exact Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (Term.denote_runs_skeleton binding body _ _ path _ _ wf0 bound.1 bound.2
              (safe.of_bind_canReturn began).of_bind)
        · have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
            (support.mono (grows0.trans grows1).next) results returned _ mid.length rfl
            (Nat.le_refl _) (Nat.le_refl _)
          exact Term.denote_runs_skeleton binding rest _ _ path _ _ wf3 bound.1 bound.2
            (((safe.of_bind_canReturn began).of_bind_canReturn ran).of_bind_canReturn settled)
  /-- The arms of a term that never stop `undefined` on an alternative run their skeletons on
  it. -/
  theorem Arms.denote_runs_skeleton (binding : rules.Binding sem Run undefined) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (st : St D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn)
        (pick : Pick sem.Val payloads),
        Table.WF st.next st.table → Support st.next ρ →
        Agrees sem Run st.table st.next ρ ids env →
        (arms.denote sem path env pick).Every permitted (fun _ => True)
          (fun stop => ¬ undefined stop) →
        SkelArms.Runs sem permitted Run (arms.skeleton rules ids st).2.table path ρ
          (arms.skeleton rules ids st).1 pick (arms.denote sem path env pick)
    | _, _, _, .nil, _, _, _, _, _, pick, _, _, _, _ => nomatch pick
    | _, _, _, .cons inputs arm rest, ids, st, path, env, ρ, .here v, wf, support, agrees,
        safe => by
        simp only [Arms.skeleton, Arms.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows 1 st wf
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules arm _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        obtain ⟨-, grows2, -⟩ := Arms.skeleton_state rules rest ids _
          (scope.mono (grows0.trans grows1).next) wf1
        have bound := (agrees.mono grows0.sub grows0.next (.refl ρ)).leaves support inputs
          (.cons v .nil) st.next 1 rfl (Nat.le_refl _) (Nat.le_refl _)
        exact .here (Skel.Runs.grow sem permitted Run _ grows2.sub _
          (Term.denote_runs_skeleton binding arm _ _ path _ _ wf0 bound.1 bound.2 safe))
    | _, _, _, .cons inputs arm rest, ids, st, path, env, ρ, .there pick, wf, support, agrees,
        safe => by
        simp only [Arms.skeleton, Arms.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := FactCheck.fresh_grows 1 st wf
        obtain ⟨wf1, grows1, -⟩ := Term.skeleton_state rules arm _ _
          (FactCheck.InScope.bind inputs _ (scope.mono grows0.next) (by simp [fresh]) made0) wf0
        have toRest := grows0.trans grows1
        exact .there (Arms.denote_runs_skeleton binding rest ids _ path env ρ pick wf1
          (support.mono toRest.next) (agrees.mono toRest.sub toRest.next (.refl ρ)) safe)
end

/-- A term that never stops `undefined` runs its own skeleton, over the table that the skeleton
is built with, and the skeleton's leaves are apart from that table. -/
theorem Term.skeleton_runs (binding : rules.Binding sem Run undefined) :
    ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (st : St D.Ty Raw)
      (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn),
      Table.WF st.next st.table → Support st.next ρ →
      Agrees sem Run st.table st.next ρ ids env →
      (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
      Skel.Runs sem permitted Run (t.skeleton rules ids st).2.table path ρ
          (t.skeleton rules ids st).1 (t.denote sem path env) ∧
        (t.skeleton rules ids st).1.Apart (t.skeleton rules ids st).2.table ∧
        Table.WF (t.skeleton rules ids st).2.next (t.skeleton rules ids st).2.table ∧
        St.Grows st (t.skeleton rules ids st).2 := by
  intro Γ outs t ids st path env ρ wf support agrees safe
  obtain ⟨wf', grows, -, apart, -⟩ := Term.skeleton_state rules t ids st agrees.inScope wf
  exact ⟨Term.denote_runs_skeleton sem permitted Run rules binding t ids st path env ρ wf support
      agrees safe, apart, wf', grows⟩

/-! ### The run of a term over a skeleton that it follows -/

mutual
  /-- A term that follows a skeleton and never stops `undefined` runs it, over the table that
  following gives, when the leaves of the skeleton are made in order from a number on and the
  valuation has nothing from that number on. -/
  theorem Term.denote_runs_followed (binding : rules.Binding sem Run undefined)
      (checks : SkelRules D) (lawful : checks.Lawful) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (skel : Skel D outs) (ids : Ctx Nat)
        (st st' : St D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn)
        (lo : Nat),
        t.follows rules checks skel ids st = some st' →
        Table.WF st.next st.table → skel.Below st.next → skel.Apart st.table →
        Support lo ρ → skel.Fresh lo →
        Agrees sem Run st.table st.next ρ ids env →
        (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
        Skel.Runs sem permitted Run st'.table path ρ skel (t.denote sem path env)
    | _, _, .ret exit, skel, _, _, _, _, _, _, _, followed, _, _, _, _, _, agrees, _ => by
        cases skel
        case ret =>
          simp only [Term.follows] at followed
          split at followed
          · next same =>
              cases followed
              subst same
              simp only [Term.denote]
              exact .ret _ (agrees.readsAll exit)
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .op (res := res) key o operands results rest, skel, ids, st, st', path, env, ρ, lo,
        followed, wf, below, apart, support, inOrder, agrees, safe => by
        cases written : rules.written o with
        | some raw =>
            simp only [Term.follows, written] at followed
            rcases binding.computes o raw written key path (env.all operands) with
              ⟨values, ran, run⟩ | ⟨stop, halted, bad⟩
            · simp only [Term.denote, ran, Process.bind] at safe ⊢
              obtain ⟨wf', grows, made⟩ :=
                FactCheck.share_grows raw (rules.order raw (idsOf ids operands)) res.length st wf
                  (rules.order_lt (FactCheck.idsOf_lt agrees.inScope operands))
              have agrees' := agrees.mono grows.sub grows.next (.refl ρ)
              obtain ⟨ordered, readOrdered, runOrdered⟩ :=
                binding.reads_order raw (agrees'.readsAll operands) run
              have reads := FactCheck.share_reads raw (rules.order raw (idsOf ids operands))
                res.length st readOrdered runOrdered (sem.dyns_length values)
              exact Term.denote_runs_followed binding checks lawful rest skel _ _ st' path _ ρ lo
                followed wf' (below.mono grows.next) (Skel.Apart.grows grows skel apart below)
                support inOrder (Agrees.bind results values _ agrees' reads made) safe
            · simp only [Term.denote, halted, Process.bind] at safe
              exact absurd bad safe
        | none =>
            cases skel
            case effect ins' res' key' o' operands' results' rest' =>
              simp only [Term.follows, written] at followed
              split at followed
              · next sameIns sameRes _ _ =>
                  split at followed
                  · next decided =>
                      obtain ⟨sameOp, rfl, sameOperands⟩ := decided
                      subst sameIns sameRes sameOperands
                      obtain ⟨-, sameO⟩ := lawful o _ sameOp
                      obtain rfl := eq_of_heq (sameO.trans (cast_heq _ o'))
                      obtain ⟨-, grows, -⟩ := Term.follows_state rules checks rest rest' _ st
                        st' followed
                        (FactCheck.InScope.bind results _ agrees.inScope (by simp) fun i m => by
                          have := mem_range'_bounds m
                          have := below.1
                          omega)
                        wf below.2 apart.2
                      simp only [Term.denote] at safe ⊢
                      refine .effect (env.all operands)
                        (ReadsAll.mono Run _ grows.sub (.refl ρ) (agrees.readsAll operands))
                        fun returned returns => ?_
                      have bound := agrees.leaves support results returned results' res.length rfl
                        inOrder.1 below.1
                      exact Term.denote_runs_followed binding checks lawful rest rest' _ st st' path
                        _ _ _ followed wf below.2 apart.2 bound.1 inOrder.2 bound.2
                        (safe.of_bind_canReturn returns)
                  · cases followed
              · cases followed
            all_goals simp [Term.follows, written] at followed
    | _, _, .guard key w c ok why rest, skel, ids, st, st', path, env, ρ, lo, followed, wf, below,
        apart, support, inOrder, agrees, safe => by
        cases skel
        case guard t' key' w' condition ok' why' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameTy _ _ =>
              split at followed
              · next decided =>
                  obtain ⟨rfl, rfl, rfl⟩ := decided
                  subst sameWho sameTy
                  obtain ⟨-, grows, -⟩ := Term.follows_state rules checks rest rest' ids st
                    st' followed agrees.inScope wf below apart
                  have read := Reads.mono Run _ grows.sub (.refl ρ) (agrees.read c).2
                  simp only [Term.denote] at safe ⊢
                  cases holds : sem.holds ok (env.get c) with
                  | true =>
                      simp only [holds, Bool.cond_true] at safe ⊢
                      exact .guardHolds _ read holds
                        (Term.denote_runs_followed binding checks lawful rest rest' ids st st' path
                          env ρ lo followed wf below apart support inOrder agrees safe)
                  | false =>
                      simp only [Bool.cond_false]
                      exact .guardStops _ read holds
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .choose (mid := mid) key w c ok _ onTrue onFalse results rest, skel, ids, st, st', path,
        env, ρ, lo, followed, wf, below, apart, support, inOrder, agrees, safe => by
        cases skel
        case choose mid' t' key' w' condition ok' onTrue' onFalse' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameTy sameMid _ _ _ =>
              split at followed
              · next decided =>
                  obtain ⟨rfl, rfl⟩ := decided
                  subst sameWho sameTy sameMid
                  simp only [cast_eq] at followed
                  obtain ⟨afterTrue, followedTrue, followedAfter⟩ :=
                    Option.bind_eq_some_iff.mp followed
                  obtain ⟨afterFalse, followedFalse, followedRest⟩ :=
                    Option.bind_eq_some_iff.mp followedAfter
                  have scope := agrees.inScope
                  obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks onTrue onTrue'
                    ids st afterTrue followedTrue scope wf below.1 apart.1
                  obtain ⟨wf2, grows2, -⟩ := Term.follows_state rules checks onFalse onFalse'
                    ids afterTrue afterFalse followedFalse (scope.mono grows1.next) wf1
                    (below.2.1.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.1 below.2.1)
                  have toRest := grows1.trans grows2
                  obtain ⟨-, grows3, -⟩ := Term.follows_state rules checks rest rest' _
                    afterFalse st' followedRest
                    (FactCheck.InScope.bind results _ (scope.mono toRest.next) (by simp)
                      fun i m => by
                        have := mem_range'_bounds m
                        have := below.2.2.1
                        have := toRest.next
                        omega)
                    wf2 (below.2.2.2.mono toRest.next)
                    (Skel.Apart.grows toRest _ apart.2.2.2 below.2.2.2)
                  have read := Reads.mono Run _ (toRest.trans grows3).sub (.refl ρ) (agrees.read
                      c).2
                  simp only [Term.denote] at safe ⊢
                  cases holds : sem.holds ok (env.get c) with
                  | true =>
                      simp only [holds, Bool.cond_true] at safe ⊢
                      refine .chooseTrue _ read holds
                        (Skel.Runs.grow sem permitted Run _ (grows2.trans grows3).sub _
                          (Term.denote_runs_followed binding checks lawful onTrue onTrue' ids st
                            afterTrue path env ρ lo followedTrue wf below.1 apart.1 support
                                inOrder.1
                            agrees safe.of_bind))
                        fun returned returns => ?_
                      have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves support
                        results returned results' mid.length rfl inOrder.2.2.1
                        (Nat.le_trans below.2.2.1 toRest.next)
                      exact Term.denote_runs_followed binding checks lawful rest rest' _ afterFalse
                        st' path _ _ _ followedRest wf2 (below.2.2.2.mono toRest.next)
                        (Skel.Apart.grows toRest _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2
                        bound.2 (safe.of_bind_canReturn returns)
                  | false =>
                      simp only [holds, Bool.cond_false] at safe ⊢
                      refine .chooseFalse _ read holds
                        (Skel.Runs.grow sem permitted Run _ grows3.sub _
                          (Term.denote_runs_followed binding checks lawful onFalse onFalse' ids
                            afterTrue afterFalse path env ρ lo followedFalse wf1
                            (below.2.1.mono grows1.next)
                            (Skel.Apart.grows grows1 _ apart.2.1 below.2.1) support inOrder.2.1
                            (agrees.mono grows1.sub grows1.next (.refl ρ)) safe.of_bind))
                        fun returned returns => ?_
                      have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves support
                        results returned results' mid.length rfl inOrder.2.2.1
                        (Nat.le_trans below.2.2.1 toRest.next)
                      exact Term.denote_runs_followed binding checks lawful rest rest' _ afterFalse
                        st' path _ _ _ followedRest wf2 (below.2.2.2.mono toRest.next)
                        (Skel.Apart.grows toRest _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2
                        bound.2 (safe.of_bind_canReturn returns)
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .cases (mid := mid) key w x ok _ arms results rest, skel, ids, st, st', path, env, ρ,
        lo, followed, wf, below, apart, support, inOrder, agrees, safe => by
        cases skel
        case cases mid' t' payloads' key' w' subject ok' arms' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameTy sameMid samePayloads _ _ _ _ =>
              split at followed
              · next decided =>
                  obtain ⟨rfl, rfl⟩ := decided
                  subst sameWho sameTy sameMid samePayloads
                  simp only [cast_eq] at followed
                  obtain ⟨afterArms, followedArms, followedRest⟩ :=
                    Option.bind_eq_some_iff.mp followed
                  have scope := agrees.inScope
                  obtain ⟨wf1, grows1, -⟩ := Arms.follows_state rules checks arms arms' ids
                    st afterArms followedArms scope wf below.1 apart.1
                  obtain ⟨-, grows3, -⟩ := Term.follows_state rules checks rest rest' _
                    afterArms st' followedRest
                    (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp)
                      fun i m => by
                        have := mem_range'_bounds m
                        have := below.2.1
                        have := grows1.next
                        omega)
                    wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2)
                  simp only [Term.denote] at safe ⊢
                  refine .cases (env.get x)
                    (Reads.mono Run _ (grows1.trans grows3).sub (.refl ρ) (agrees.read x).2)
                    (SkelArms.Runs.grow sem permitted Run _ grows3.sub _
                      (Arms.denote_runs_followed binding checks lawful arms arms' ids st afterArms
                          path
                        env ρ lo (sem.pick ok (env.get x)) followedArms wf below.1 apart.1 support
                        inOrder.1 agrees safe.of_bind))
                    fun returned returns => ?_
                  have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support
                    results returned results' mid.length rfl inOrder.2.1 (Nat.le_trans below.2.1
                        grows1.next)
                  exact Term.denote_runs_followed binding checks lawful rest rest' _ afterArms st'
                    path _ _ _ followedRest wf1 (below.2.2.mono grows1.next)
                    (Skel.Apart.grows grows1 _ apart.2.2 below.2.2) bound.1 inOrder.2.2 bound.2
                    (safe.of_bind_canReturn returns)
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest,
        skel, ids, st, st', path, env, ρ, lo, followed, wf, below, apart, support, inOrder, agrees,
        safe => by
        cases skel
        case loop carried' each' key' w' times' initial' inputs' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameCarried sameEach _ _ _ =>
              split at followed
              · next decided =>
                  obtain ⟨rfl, sameTimes, sameInitial⟩ := decided
                  subst sameWho sameCarried sameEach sameInitial
                  simp only [cast_eq] at followed sameTimes
                  obtain rfl := Times.follows_eq checks ids times times' sameTimes
                  obtain ⟨afterBody, followedBody, followedRest⟩ :=
                    Option.bind_eq_some_iff.mp followed
                  have scope := agrees.inScope
                  obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks body body' _ st
                    afterBody followedBody
                    (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
                      have := mem_range'_bounds m
                      have := below.1
                      omega)
                    wf below.2.1 apart.2.1
                  obtain ⟨-, grows3, -⟩ := Term.follows_state rules checks rest rest' _
                    afterBody st' followedRest
                    (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp)
                      fun i m => by
                        have := mem_range'_bounds m
                        have := below.2.2.1
                        have := grows1.next
                        omega)
                    wf1 (below.2.2.2.mono grows1.next)
                    (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2)
                  have toEnd := grows1.trans grows3
                  simp only [Term.denote] at safe ⊢
                  let bodyOf : Nat → HList sem.Val carried →
                      Process sem.S sem.H (HList sem.Val (carried ++ each)) := fun i values =>
                    body.denote sem (path ++ [.iteration key i])
                      (env.extend inputs (.cons (sem.index w i) values))
                  have step : sem.loopStep w inputs (fun path' env' => body.denote sem path' env')
                      key path env = sem.stepOf bodyOf := rfl
                  rw [step] at safe ⊢
                  refine .loop (sem.times times env)
                    (Count.Is.mono sem Run _ toEnd.sub (.refl ρ) (Times.count_is agrees times))
                    (env.all initial)
                    (ReadsAll.mono Run _ toEnd.sub (.refl ρ) (agrees.readsAll initial))
                    bodyOf (fun i state below' returns => ?_) (fun final returns => ?_)
                  · have bound := agrees.leaves support inputs (.cons (sem.index w i) state.1)
                      inputs' (carried.length + 1) rfl inOrder.1 below.1
                    have safeStep := Process.Every.iterate_step i _ 0 _ state below' safe.of_bind
                      returns
                    rw [Nat.zero_add] at safeStep
                    exact Skel.Runs.grow sem permitted Run _ grows3.sub _
                      (Term.denote_runs_followed binding checks lawful body body' _ st afterBody _ _
                        _ _ followedBody wf below.2.1 apart.2.1 bound.1 inOrder.2.1 bound.2
                        safeStep.of_bind)
                  · rw [Times.dyns_collected sem ids times final]
                    have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support
                      results (final.1.append (sem.collected times.size final.2)) results'
                      (carried.length + each.length) (by simp) inOrder.2.2.1
                      (Nat.le_trans below.2.2.1 grows1.next)
                    exact Term.denote_runs_followed binding checks lawful rest rest' _ afterBody st'
                      path _ _ _ followedRest wf1 (below.2.2.2.mono grows1.next)
                      (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2
                      bound.2 (safe.of_bind_canReturn returns)
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .block (mid := mid) key number body results rest, skel, ids, st, st', path, env, ρ, lo,
        followed, wf, below, apart, support, inOrder, agrees, safe => by
        cases skel
        case block mid' key' number' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameMid _ =>
              split at followed
              · next decided =>
                  obtain ⟨rfl, rfl⟩ := decided
                  subst sameMid
                  simp only [cast_eq] at followed
                  obtain ⟨afterBody, followedBody, followedRest⟩ :=
                    Option.bind_eq_some_iff.mp followed
                  have scope := agrees.inScope
                  obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks body body' ids
                    st afterBody followedBody scope wf below.1 apart.1
                  obtain ⟨-, grows3, -⟩ := Term.follows_state rules checks rest rest' _
                    afterBody st' followedRest
                    (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp)
                      fun i m => by
                        have := mem_range'_bounds m
                        have := below.2.1
                        have := grows1.next
                        omega)
                    wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2)
                  simp only [Term.denote] at safe ⊢
                  refine .block (Skel.Runs.grow sem permitted Run _ grows3.sub _
                      (Term.denote_runs_followed binding checks lawful body body' ids st afterBody _
                        env ρ lo followedBody wf below.1 apart.1 support inOrder.1 agrees
                        safe.of_bind))
                    fun returned returns => ?_
                  have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support
                    results returned results' mid.length rfl inOrder.2.1 (Nat.le_trans below.2.1
                        grows1.next)
                  exact Term.denote_runs_followed binding checks lawful rest rest' _ afterBody st'
                    path _ _ _ followedRest wf1 (below.2.2.mono grows1.next)
                    (Skel.Apart.grows grows1 _ apart.2.2 below.2.2) bound.1 inOrder.2.2 bound.2
                    (safe.of_bind_canReturn returns)
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, skel, ids, st, st', path, env,
        ρ, lo, followed, wf, below, apart, support, inOrder, agrees, safe => by
        cases skel
        case attempt mid' key' w' input' body' results' rest' =>
          simp only [Term.follows] at followed
          split at followed
          · next sameWho sameMid _ _ =>
              split at followed
              · next sameKey =>
                  subst sameKey sameWho sameMid
                  simp only [cast_eq] at followed
                  obtain ⟨afterBody, followedBody, followedRest⟩ :=
                    Option.bind_eq_some_iff.mp followed
                  have scope := agrees.inScope
                  obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks body body' _ st
                    afterBody followedBody
                    (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
                      have := mem_range'_bounds m
                      have := below.1
                      omega)
                    wf below.2.1 apart.2.1
                  obtain ⟨-, grows3, -⟩ := Term.follows_state rules checks rest rest' _
                    afterBody st' followedRest
                    (FactCheck.InScope.bind results _ (scope.mono grows1.next) (by simp)
                      fun i m => by
                        have := mem_range'_bounds m
                        have := below.2.2.1
                        have := grows1.next
                        omega)
                    wf1 (below.2.2.2.mono grows1.next)
                    (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2)
                  simp only [Term.denote] at safe ⊢
                  refine .attempt
                    (fun number => body.denote sem path (env.extend inputs (.cons number .nil)))
                    (fun number began => ?_) (fun number returned began ran settled => ?_)
                  · have bound := agrees.leaves support inputs (.cons number .nil) input' 1 rfl
                      inOrder.1 below.1
                    exact Skel.Runs.grow sem permitted Run _ grows3.sub _
                      (Term.denote_runs_followed binding checks lawful body body' _ st afterBody
                        path _ _ _ followedBody wf below.2.1 apart.2.1 bound.1 inOrder.2.1 bound.2
                        (safe.of_bind_canReturn began).of_bind)
                  · have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support
                      results returned results' mid.length rfl inOrder.2.2.1
                      (Nat.le_trans below.2.2.1 grows1.next)
                    exact Term.denote_runs_followed binding checks lawful rest rest' _ afterBody st'
                      path _ _ _ followedRest wf1 (below.2.2.2.mono grows1.next)
                      (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2
                      bound.2
                      (((safe.of_bind_canReturn began).of_bind_canReturn ran).of_bind_canReturn
                        settled)
              · cases followed
          · cases followed
        all_goals simp [Term.follows] at followed
  /-- Arms that follow the arms of a skeleton and never stop `undefined` on an alternative run
  them on it. -/
  theorem Arms.denote_runs_followed (binding : rules.Binding sem Run undefined)
      (checks : SkelRules D) (lawful : checks.Lawful) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (skel : SkelArms D mid payloads) (ids : Ctx Nat) (st st' : St D.Ty Raw) (path : List Frame)
        (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn) (lo : Nat) (pick : Pick sem.Val payloads),
        arms.follows rules checks skel ids st = some st' →
        Table.WF st.next st.table → skel.Below st.next → skel.Apart st.table →
        Support lo ρ → skel.Fresh lo →
        Agrees sem Run st.table st.next ρ ids env →
        (arms.denote sem path env pick).Every permitted (fun _ => True)
          (fun stop => ¬ undefined stop) →
        SkelArms.Runs sem permitted Run st'.table path ρ skel pick
          (arms.denote sem path env pick)
    | _, _, _, .nil, .nil, _, _, _, _, _, _, _, pick, _, _, _, _, _, _, _, _ => nomatch pick
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, st, st', path, env, ρ, lo,
        .here v, followed, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [Arms.follows] at followed
        obtain ⟨afterArm, followedArm, followedRest⟩ := Option.bind_eq_some_iff.mp followed
        have scope := agrees.inScope
        obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks arm arm' _ st afterArm
          followedArm
          (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
            have := mem_range'_bounds m
            have := below.1
            omega)
          wf below.2.1 apart.2.1
        obtain ⟨-, grows2, -⟩ := Arms.follows_state rules checks rest rest' ids afterArm st'
          followedRest (scope.mono grows1.next) wf1 (below.2.2.mono grows1.next)
          (SkelArms.Apart.grows grows1 _ apart.2.2 below.2.2)
        simp only [Arms.denote] at safe ⊢
        have bound := agrees.leaves support inputs (.cons v .nil) input' 1 rfl inOrder.1 below.1
        exact .here (Skel.Runs.grow sem permitted Run _ grows2.sub _
          (Term.denote_runs_followed binding checks lawful arm arm' _ st afterArm path _ _ _
            followedArm wf below.2.1 apart.2.1 bound.1 inOrder.2.1 bound.2 safe))
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, st, st', path, env, ρ, lo,
        .there pick, followed, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [Arms.follows] at followed
        obtain ⟨afterArm, followedArm, followedRest⟩ := Option.bind_eq_some_iff.mp followed
        have scope := agrees.inScope
        obtain ⟨wf1, grows1, -⟩ := Term.follows_state rules checks arm arm' _ st afterArm
          followedArm
          (FactCheck.InScope.bind inputs _ scope (by simp) fun i m => by
            have := mem_range'_bounds m
            have := below.1
            omega)
          wf below.2.1 apart.2.1
        simp only [Arms.denote] at safe ⊢
        exact .there (Arms.denote_runs_followed binding checks lawful rest rest' ids afterArm st'
          path env ρ lo pick followedRest wf1 (below.2.2.mono grows1.next)
          (SkelArms.Apart.grows grows1 _ apart.2.2 below.2.2) support inOrder.2.2
          (agrees.mono grows1.sub grows1.next (.refl ρ)) safe)
end

/-- A term that follows a skeleton and never stops `undefined` runs it, over the table that
following gives, when the skeleton's leaves are made in order from a number on and the valuation
has no value from that number on. -/
theorem Term.follows_runs (binding : rules.Binding sem Run undefined) (checks : SkelRules D)
    (lawful : checks.Lawful) :
    ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (skel : Skel D outs) (ids : Ctx Nat)
      (st st' : St D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn)
      (lo : Nat),
      t.follows rules checks skel ids st = some st' →
      Table.WF st.next st.table → skel.Below st.next → skel.Apart st.table →
      Support lo ρ → skel.Fresh lo → Agrees sem Run st.table st.next ρ ids env →
      (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
      Skel.Runs sem permitted Run st'.table path ρ skel (t.denote sem path env) ∧
        skel.Apart st'.table ∧ Table.WF st'.next st'.table ∧ St.Grows st st' := by
  intro Γ outs t skel ids st st' path env ρ lo followed wf below apart support inOrder agrees safe
  obtain ⟨wf', grows, apart'⟩ := Term.follows_state rules checks t skel ids st st' followed
    agrees.inScope wf below apart
  exact ⟨Term.denote_runs_followed sem permitted Run rules binding checks lawful t skel ids st st'
      path env ρ lo followed wf below apart support inOrder agrees safe, apart', wf', grows⟩

/-- Two definitions of which the second follows the skeleton of the first mean the same on
every input on which neither stops `undefined`. -/
theorem followsSkeleton_sound (binding : rules.Binding sem Run undefined) (checks : SkelRules D)
    (lawful : checks.Lawful) {types outs : List D.Ty} (inputs inputs' : Names types)
    (t : Term D (Ctx.empty.extend inputs) outs) (t' : Term D (Ctx.empty.extend inputs') outs)
    (decided : followsSkeleton rules checks inputs inputs' t t' = true) (path : List Frame)
    (values : HList sem.Val types)
    (safe : (t.denote sem path (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop))
    (safe' : (t'.denote sem path (Env.empty.extend inputs' values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    Process.SameWhen permitted (t.denote sem path (Env.empty.extend inputs values))
      (t'.denote sem path (Env.empty.extend inputs' values)) := by
  simp only [followsSkeleton] at decided
  obtain ⟨st2, followed⟩ := Option.isSome_iff_exists.mp decided
  obtain ⟨support, agrees⟩ := Agrees.start (Run := Run)
    (table := (FactCheck.Table.empty rules.place : Table Raw)) inputs values
  obtain ⟨-, agrees'⟩ := Agrees.start (Run := Run)
    (table := (FactCheck.Table.empty rules.place : Table Raw)) inputs' values
  have wf : Table.WF types.length (FactCheck.Table.empty rules.place : Table Raw) := trivial
  obtain ⟨wf1, grows1, below1, apart1, inOrder1⟩ := Term.skeleton_state rules t
    (bindIds Ctx.empty inputs (List.range types.length))
    ⟨FactCheck.Table.empty rules.place, types.length, [], []⟩ agrees.inScope wf
  have runs := Term.denote_runs_skeleton sem permitted Run rules binding t _
    ⟨FactCheck.Table.empty rules.place, types.length, [], []⟩ path _ _ wf support agrees safe
  have agrees1 := agrees'.mono grows1.sub grows1.next (.refl _)
  obtain ⟨wf2, grows2, apart2⟩ := Term.follows_state rules checks t' _ _ _ st2 followed
    agrees1.inScope wf1 below1 apart1
  have runs' := Term.denote_runs_followed sem permitted Run rules binding checks lawful t' _ _ _ st2
    path _ _ types.length followed wf1 below1 apart1 support inOrder1 agrees1 safe'
  have leaves : Leaves st2.table
      (FactCheck.Valuation.setFrom (fun _ => none) 0 (sem.dyns values)) := by
    intro e known j _
    obtain ⟨_, new, entries, above⟩ := grows1.trans grows2
    have known' : e ∈ new ++ [] := by
      have known'' : e ∈ st2.table.entries := known
      rw [entries] at known''
      exact known''
    rw [List.append_nil] at known'
    have low : types.length ≤ e.lo := above e known'
    exact support _ (by omega)
  exact Skel.Runs.same sem permitted Run binding.functional wf2 _ apart2 leaves
    (Skel.Runs.grow sem permitted Run _ grows2.sub _ runs) runs'

end

end Zkc.Core

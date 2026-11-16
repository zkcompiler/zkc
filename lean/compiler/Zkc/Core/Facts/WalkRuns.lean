module

public import Zkc.Core.Facts.WalkSkeleton
public import Zkc.Core.Value.Agrees

@[expose] public section

/-!
The runs of the walk of the analysis, for any dialect and any semantics whose values satisfy the
laws of `ValueRules.Binding`: without a skeleton to follow, a term that never stops `undefined`
runs the skeleton that the walk builds, over the table that the walk gives
(`walk_runs_built`); with a skeleton to follow and no place that differs, it runs the skeleton
that it follows (`walk_runs_followed`). A value of the walk also checks its requirements, which
may enter applications in the table before the value is shared: the table only grows across it
(`valueStep_reads`).
-/

namespace Zkc.Core.Analysis.ValueSide

open FactCheck

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D)
  (definition : Key) (role : Option Role) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
  {undefined : sem.H → Prop}

/-- The results of a value read, over the table after it, as what its written operation gives on
the operands: its requirements may enter applications first, and the operands of an operation
that commutes are placed in the table's order. -/
theorem valueStep_reads (binding : rules.values.Binding sem Run undefined) (place : Place)
    (raw : Raw) (res : List D.Ty) (argIds : List Nat) (k : Known) (st : St D.Ty Raw)
    {ρ : Valuation sem.Dyn} {operands results : List sem.Dyn} (wf : Table.WF st.next st.table)
    (below : ∀ a, a ∈ argIds → a < st.next) (read : ReadsAll Run st.table ρ argIds operands)
    (ran : Run raw operands results) (length : results.length = res.length) :
    ReadsAll Run (valueStep rules place raw res argIds k st).2.2.table ρ
      (valueStep rules place raw res argIds k st).1 results := by
  obtain ⟨wf1, grows1⟩ := checkRequirements_grows rules.ops k place raw argIds
    (rules.ops.requires raw) st wf below
  obtain ⟨-, grows2, -⟩ := share_grows raw (rules.values.order raw argIds) res.length _ wf1
    (rules.values.order_lt fun a m => Nat.lt_of_lt_of_le (below a m) grows1.next)
  obtain ⟨_, readOrdered, runOrdered⟩ := binding.reads_order raw
    (ReadsAll.mono Run _ (grows1.trans grows2).sub (.refl ρ) read) ran
  exact share_reads raw (rules.values.order raw argIds) res.length _ readOrdered runOrdered length

/-! ## Without a skeleton to follow -/

mutual
  /-- Without a skeleton to follow, a term that never stops `undefined` runs the skeleton that
  the walk builds, over the table that the walk gives. -/
  theorem walk_runs_built (binding : rules.values.Binding sem Run undefined)
      (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Nat) (k : Known)
        (s : State D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn),
        Table.WF s.st.next s.st.table → Support s.st.next ρ →
        Agrees sem Run s.st.table s.st.next ρ ids env →
        (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
        Skel.Runs sem permitted Run
          (walk rules checks definition role blocks t none ids k s).state.st.table path ρ
          (walk rules checks definition role blocks t none ids k s).skel (t.denote sem path env)
    | _, _, .ret exit, _, _, _, _, _, _, _, _, agrees, _ => by
        simp only [walk, kept_none, Term.denote]
        exact .ret _ (by rw [miss_st]; exact agrees.readsAll exit)
    | _, _, .op (res := res) key o args results rest, ids, k, s, path, env, ρ, wf, support,
        agrees, safe => by
        cases written : rules.written o with
        | some raw =>
            simp only [walk, written]
            rcases binding.computes o raw written key path (env.all args) with
              ⟨values, ran, run⟩ | ⟨stop, halted, bad⟩
            · simp only [Term.denote, ran, Process.bind] at safe ⊢
              have scope := agrees.inScope
              obtain ⟨wf1, grows1, made1, -⟩ := valueStep_grows rules
                ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
                (idsOf_lt scope args)
              have reads := valueStep_reads rules sem Run binding
                ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
                (idsOf_lt scope args) (agrees.readsAll args) run (sem.dyns_length values)
              generalize valueStep rules _ raw res (idsOf ids args) k s.st = step
                at wf1 grows1 made1 reads ⊢
              exact walk_runs_built binding blocks rest _ step.2.1 { s with st := step.2.2 } path
                _ ρ wf1 (support.mono grows1.next)
                (Agrees.bind results values _ (agrees.mono grows1.sub grows1.next (.refl ρ)) reads
                  made1) safe
            · simp only [Term.denote, halted, Process.bind] at safe
              exact absurd bad safe
        | none =>
            simp only [walk, written, effectEntry_none, Option.isSome_none, miss_not_following,
              Option.map_none, leaves_none, kept_none]
            simp only [Term.denote] at safe ⊢
            obtain ⟨wf1, grows1, made1⟩ := fresh_grows res.length s.st wf
            generalize Known.enter rules _ _ = k1
            have scope1 := (agrees.inScope.mono grows1.next).bind results _ (by simp [fresh]) made1
            obtain ⟨-, grows2⟩ := walk_grows rules checks definition role blocks rest none _ k1
              { s with st := (fresh res.length s.st).2 } scope1 wf1 FollowedBelow.none
            refine .effect (env.all args)
              (ReadsAll.mono Run _ (grows1.trans grows2).sub (.refl ρ) (agrees.readsAll args))
              fun returned returns => ?_
            have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support results
              returned s.st.next res.length rfl (Nat.le_refl _) (Nat.le_refl _)
            exact walk_runs_built binding blocks rest _ k1
              { s with st := (fresh res.length s.st).2 } path _ _ wf1 bound.1 bound.2
              (safe.of_bind_canReturn returns)
    | _, _, .guard key w c ok why rest, ids, k, s, path, env, ρ, wf, support, agrees, safe => by
        simp only [walk, guardEntry_none, Option.isSome_none, miss_not_following, kept_none]
        simp only [Term.denote] at safe ⊢
        generalize assume rules.ops _ _ _ _ _ = k1
        obtain ⟨-, grows⟩ := walk_grows rules checks definition role blocks rest none ids k1 s
          agrees.inScope wf FollowedBelow.none
        have read := Reads.mono Run _ grows.sub (.refl ρ) (agrees.read c).2
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            exact .guardHolds _ read holds
              (walk_runs_built binding blocks rest ids k1 s path env ρ wf support agrees safe)
        | false =>
            simp only [Bool.cond_false]
            exact .guardStops _ read holds
    | _, _, .choose (mid := mid) key w c ok _ onTrue onFalse results rest, ids, k, s, path, env, ρ,
        wf, support, agrees, safe => by
        simp only [walk, chooseEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        generalize assume rules.ops _ _ k _ true = k1
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks onTrue none ids k1 s
          scope wf FollowedBelow.none
        have runsTrue := fun safeTrue =>
          walk_runs_built binding blocks onTrue ids k1 s path env ρ wf support agrees safeTrue
        generalize walk rules checks definition role blocks onTrue none ids k1 s = first
          at wf1 grows1 runsTrue ⊢
        generalize assume rules.ops _ _ k _ false = k2
        obtain ⟨wf2, grows2⟩ := walk_grows rules checks definition role blocks onFalse none ids k2
          first.state (scope.mono grows1.next) wf1 FollowedBelow.none
        have runsFalse := fun safeFalse =>
          walk_runs_built binding blocks onFalse ids k2 first.state path env ρ wf1
            (support.mono grows1.next) (agrees.mono grows1.sub grows1.next (.refl ρ)) safeFalse
        generalize walk rules checks definition role blocks onFalse none ids k2 first.state = second
          at wf2 grows2 runsFalse ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length second.state.st wf2
        generalize Known.enter rules _ _ = k3
        have toRest := grows1.trans (grows2.trans grows3)
        have scope3 := (scope.mono toRest.next).bind results _ (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { second.state with st := (fresh mid.length second.state.st).2 } scope3 wf3
          FollowedBelow.none
        have read := Reads.mono Run _ (toRest.trans grows4).sub (.refl ρ) (agrees.read c).2
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            refine .chooseTrue _ read holds
              (Skel.Runs.grow sem permitted Run _ (grows2.trans (grows3.trans grows4)).sub _
                (runsTrue safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
              (support.mono (grows1.trans grows2).next) results returned _ mid.length rfl
              (Nat.le_refl _) (Nat.le_refl _)
            exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
              (safe.of_bind_canReturn returns)
        | false =>
            simp only [holds, Bool.cond_false] at safe ⊢
            refine .chooseFalse _ read holds
              (Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
                (runsFalse safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
              (support.mono (grows1.trans grows2).next) results returned _ mid.length rfl
              (Nat.le_refl _) (Nat.le_refl _)
            exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
              (safe.of_bind_canReturn returns)
    | _, _, .cases (mid := mid) key w x ok _ arms results rest, ids, k, s, path, env, ρ, wf,
        support, agrees, safe => by
        simp only [walk, casesEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1⟩ := walkArms_grows rules checks definition role blocks arms none ids k
          s scope wf ArmsFollowedBelow.none
        have runsArms := walkArms_runs_built binding blocks arms ids k s path env ρ
          (sem.pick ok (env.get x)) wf support agrees safe.of_bind
        generalize walkArms rules checks definition role blocks arms none ids k s = regions
          at wf1 grows1 runsArms ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length regions.state.st wf1
        generalize Known.enter rules _ _ = k3
        have scope3 := (scope.mono (grows1.trans grows3).next).bind results _ (by simp [fresh])
          made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { regions.state with st := (fresh mid.length regions.state.st).2 } scope3 wf3
          FollowedBelow.none
        refine .cases (env.get x)
          (Reads.mono Run _ (grows1.trans (grows3.trans grows4)).sub (.refl ρ) (agrees.read x).2)
          (SkelArms.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _ runsArms)
          fun returned returns => ?_
        have bound := (agrees.mono (grows1.trans grows3).sub (grows1.trans grows3).next
          (.refl ρ)).leaves (support.mono grows1.next) results returned _ mid.length rfl
          (Nat.le_refl _) (Nat.le_refl _)
        exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
          (safe.of_bind_canReturn returns)
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, ids, k, s, path, env, ρ, wf, support, agrees, safe => by
        simp only [walk, loopEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows (carried.length + 1) s.st wf
        generalize bodyKnown rules _ _ _ _ _ _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body none _ k1
          { s with st := (fresh (carried.length + 1) s.st).2 } scope0 wf0 FollowedBelow.none
        have runsBody := fun path' env' ρ' support' agrees' safe' =>
          walk_runs_built binding blocks body
            (bindIds ids inputs (fresh (carried.length + 1) s.st).1) k1
            { s with st := (fresh (carried.length + 1) s.st).2 } path' env' ρ' wf0 support' agrees'
            safe'
        generalize walk rules checks definition role blocks body none _ k1 _ = e
          at wf1 grows1 runsBody ⊢
        obtain ⟨tableSame, nextSame, -, -⟩ :=
          recordBound_state ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound _ k ids e.state.st times = st₁ at tableSame nextSame ⊢
        obtain ⟨table₁, next₁, refusals₁, bounds₁⟩ := st₁
        simp only at tableSame nextSame
        subst tableSame nextSame
        have grows2 : St.Grows e.state.st
            ⟨e.state.st.table, e.state.st.next, refusals₁, bounds₁⟩ :=
          ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows (carried.length + each.length)
          ⟨e.state.st.table, e.state.st.next, refusals₁, bounds₁⟩ wf1
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans (grows2.trans grows3))
        have scope3 := (scope.mono toRest.next).bind results _ (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh (carried.length + each.length)
              ⟨e.state.st.table, e.state.st.next, refusals₁, bounds₁⟩).2 } scope3 wf3
          FollowedBelow.none
        have toEnd := toRest.trans grows4
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
            (.cons (sem.index w i) state.1) s.st.next (carried.length + 1) rfl (Nat.le_refl _)
            (Nat.le_refl _)
          have safeStep := Process.Every.iterate_step i _ 0 _ state below safe.of_bind returns
          rw [Nat.zero_add] at safeStep
          exact Skel.Runs.grow sem permitted Run _ (grows2.trans (grows3.trans grows4)).sub _
            (runsBody _ _ _ bound.1 bound.2 safeStep.of_bind)
        · rw [Times.dyns_collected sem ids times final]
          have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
            (support.mono (grows0.trans grows1).next) results
            (final.1.append (sem.collected times.size final.2)) _ (carried.length + each.length)
            (by simp) (Nat.le_refl _) (Nat.le_refl _)
          exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
            (safe.of_bind_canReturn returns)
    | _, _, .block (mid := mid) key number body results rest, ids, k, s, path, env, ρ, wf, support,
        agrees, safe => by
        simp only [walk, blockEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role (blocks ++ [(key, number)])
          body none ids k s scope wf FollowedBelow.none
        have runsBody := fun path' safe' =>
          walk_runs_built binding (blocks ++ [(key, number)]) body ids k s path' env ρ wf support
            agrees safe'
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body none ids k
          s = e at wf1 grows1 runsBody ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length e.state.st wf1
        generalize Known.enter rules _ _ = k3
        have scope3 := (scope.mono (grows1.trans grows3).next).bind results _ (by simp [fresh])
          made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3 FollowedBelow.none
        refine .block (Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (runsBody _ safe.of_bind))
          fun returned returns => ?_
        have bound := (agrees.mono (grows1.trans grows3).sub (grows1.trans grows3).next
          (.refl ρ)).leaves (support.mono grows1.next) results returned _ mid.length rfl
          (Nat.le_refl _) (Nat.le_refl _)
        exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
          (safe.of_bind_canReturn returns)
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, ids, k, s, path, env, ρ, wf,
        support, agrees, safe => by
        simp only [walk, attemptEntry_none, Option.isSome_none, miss_not_following,
          Option.map_none, leaves_none, kept_none]
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows 1 s.st wf
        generalize Known.enter rules (Known.addRanges k _ _) _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body none _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0 FollowedBelow.none
        have runsBody := fun env' ρ' support' agrees' safe' =>
          walk_runs_built binding blocks body (bindIds ids inputs (fresh 1 s.st).1) k1
            { s with st := (fresh 1 s.st).2 } path env' ρ' wf0 support' agrees' safe'
        generalize walk rules checks definition role blocks body none _ k1 _ = e
          at wf1 grows1 runsBody ⊢
        obtain ⟨wf3, grows3, made3⟩ := fresh_grows mid.length e.state.st wf1
        generalize Known.enter rules _ _ = k3
        have toRest := grows0.trans (grows1.trans grows3)
        have scope3 := (scope.mono toRest.next).bind results _ (by simp [fresh]) made3
        obtain ⟨-, grows4⟩ := walk_grows rules checks definition role blocks rest none _ k3
          { e.state with st := (fresh mid.length e.state.st).2 } scope3 wf3 FollowedBelow.none
        refine .attempt (fun number => body.denote sem path (env.extend inputs (.cons number .nil)))
          (fun number began => ?_) (fun number returned began ran settled => ?_)
        · have bound := (agrees.mono grows0.sub grows0.next (.refl ρ)).leaves support inputs
            (.cons number .nil) s.st.next 1 rfl (Nat.le_refl _) (Nat.le_refl _)
          exact Skel.Runs.grow sem permitted Run _ (grows3.trans grows4).sub _
            (runsBody _ _ bound.1 bound.2 (safe.of_bind_canReturn began).of_bind)
        · have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves
            (support.mono (grows0.trans grows1).next) results returned _ mid.length rfl
            (Nat.le_refl _) (Nat.le_refl _)
          exact walk_runs_built binding blocks rest _ k3 _ path _ _ wf3 bound.1 bound.2
            (((safe.of_bind_canReturn began).of_bind_canReturn ran).of_bind_canReturn settled)
  /-- Without arms to follow, the arms of a term that never stop `undefined` on an alternative
  run the arms that the walk builds, on it. -/
  theorem walkArms_runs_built (binding : rules.values.Binding sem Run undefined)
      (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) (ids : Ctx Nat)
        (k : Known) (s : State D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ)
        (ρ : Valuation sem.Dyn) (pick : Pick sem.Val payloads),
        Table.WF s.st.next s.st.table → Support s.st.next ρ →
        Agrees sem Run s.st.table s.st.next ρ ids env →
        (arms.denote sem path env pick).Every permitted (fun _ => True)
          (fun stop => ¬ undefined stop) →
        SkelArms.Runs sem permitted Run
          (walkArms rules checks definition role blocks arms none ids k s).state.st.table path ρ
          (walkArms rules checks definition role blocks arms none ids k s).skel pick
          (arms.denote sem path env pick)
    | _, _, _, .nil, _, _, _, _, _, _, pick, _, _, _, _ => nomatch pick
    | _, _, _, .cons inputs arm rest, ids, k, s, path, env, ρ, .here v, wf, support, agrees,
        safe => by
        simp only [walkArms, armEntry_none, Option.map_none, leaves_none, Option.getD_none]
        simp only [Arms.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows 1 s.st wf
        generalize Known.enter rules _ _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks arm none _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0 FollowedBelow.none
        have bound := (agrees.mono grows0.sub grows0.next (.refl ρ)).leaves support inputs
          (.cons v .nil) s.st.next 1 rfl (Nat.le_refl _) (Nat.le_refl _)
        have runsArm := walk_runs_built binding blocks arm (bindIds ids inputs (fresh 1 s.st).1) k1
          { s with st := (fresh 1 s.st).2 } path _ _ wf0 bound.1 bound.2 safe
        generalize walk rules checks definition role blocks arm none _ k1 _ = e
          at wf1 grows1 runsArm ⊢
        obtain ⟨-, grows2⟩ := walkArms_grows rules checks definition role blocks rest none ids k
          e.state (scope.mono (grows0.trans grows1).next) wf1 ArmsFollowedBelow.none
        exact .here (Skel.Runs.grow sem permitted Run _ grows2.sub _ runsArm)
    | _, _, _, .cons inputs arm rest, ids, k, s, path, env, ρ, .there pick, wf, support, agrees,
        safe => by
        simp only [walkArms, armEntry_none, Option.map_none, leaves_none, Option.getD_none]
        simp only [Arms.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf0, grows0, made0⟩ := fresh_grows 1 s.st wf
        generalize Known.enter rules _ _ = k1
        have scope0 := (scope.mono grows0.next).bind inputs _ (by simp [fresh]) made0
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks arm none _ k1
          { s with st := (fresh 1 s.st).2 } scope0 wf0 FollowedBelow.none
        generalize walk rules checks definition role blocks arm none _ k1 _ = e at wf1 grows1 ⊢
        have toRest := grows0.trans grows1
        exact .there (walkArms_runs_built binding blocks rest ids k e.state path env ρ pick wf1
          (support.mono toRest.next) (agrees.mono toRest.sub toRest.next (.refl ρ)) safe)
end

/-! ## With a skeleton to follow -/

mutual
  /-- With a skeleton to follow and no place that differs at the end, a term that never stops
  `undefined` runs the skeleton that it follows, over the table that the walk gives, when the
  leaves of the skeleton are made in order from a number on and the valuation has nothing from
  that number on. -/
  theorem walk_runs_followed (binding : rules.values.Binding sem Run undefined)
      (lawful : checks.Lawful) (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (skel : Skel D outs) (ids : Ctx Nat)
        (k : Known) (s : State D.Ty Raw) (path : List Frame) (env : Env sem.Val Γ)
        (ρ : Valuation sem.Dyn) (lo : Nat),
        (walk rules checks definition role blocks t (some skel) ids k s).state.differs = [] →
        Table.WF s.st.next s.st.table → skel.Below s.st.next → skel.Apart s.st.table →
        Support lo ρ → skel.Fresh lo →
        Agrees sem Run s.st.table s.st.next ρ ids env →
        (t.denote sem path env).Every permitted (fun _ => True) (fun stop => ¬ undefined stop) →
        Skel.Runs sem permitted Run
          (walk rules checks definition role blocks t (some skel) ids k s).state.st.table path ρ
          skel (t.denote sem path env)
    | _, _, .ret exit, skel, ids, k, s, path, env, ρ, lo, noPlace, _, _, _, _, _, agrees, _ => by
        simp only [walk] at noPlace ⊢
        have found := found_of_no_place (AddsPlaces.refl _) noPlace
        obtain rfl := Option.some.inj (retEntry_hit found)
        simp only [miss_st, Term.denote]
        exact .ret _ (agrees.readsAll exit)
    | _, _, .op (res := res) key o args results rest, skel, ids, k, s, path, env, ρ, lo, noPlace,
        wf, below, apart, support, inOrder, agrees, safe => by
        cases written : rules.written o with
        | some raw =>
            simp only [walk, written] at noPlace ⊢
            rcases binding.computes o raw written key path (env.all args) with
              ⟨values, ran, run⟩ | ⟨stop, halted, bad⟩
            · simp only [Term.denote, ran, Process.bind] at safe ⊢
              have scope := agrees.inScope
              obtain ⟨wf1, grows1, made1, -⟩ := valueStep_grows rules
                ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
                (idsOf_lt scope args)
              have reads := valueStep_reads rules sem Run binding
                ⟨definition, blocks, some key, role⟩ raw res (idsOf ids args) k s.st wf
                (idsOf_lt scope args) (agrees.readsAll args) run (sem.dyns_length values)
              generalize valueStep rules _ raw res (idsOf ids args) k s.st = step
                at wf1 grows1 made1 reads noPlace ⊢
              exact walk_runs_followed binding lawful blocks rest skel _ step.2.1
                { s with st := step.2.2 } path _ ρ lo noPlace wf1 (below.mono grows1.next)
                (Skel.Apart.grows grows1 skel apart below) support inOrder
                (Agrees.bind results values _ (agrees.mono grows1.sub grows1.next (.refl ρ)) reads
                  made1) safe
            · simp only [Term.denote, halted, Process.bind] at safe
              exact absurd bad safe
        | none =>
            simp only [walk, written] at noPlace ⊢
            generalize hhit : effectEntry checks key o (idsOf ids args) (some skel) = hit
              at noPlace ⊢
            obtain ⟨⟨r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
              refine AddsPlaces.trans ?_
                (walk_adds rules checks definition role blocks rest _ _ _ _)
              exact leaves_adds _ _ _) noPlace
            obtain ⟨o', sameOp, e⟩ := effectEntry_hit checks hhit
            obtain rfl := Option.some.inj e
            obtain ⟨-, sameO⟩ := lawful o o' sameOp
            obtain rfl := eq_of_heq sameO
            simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some]
              at noPlace ⊢
            simp only [Term.denote] at safe ⊢
            generalize Known.enter rules _ _ = k1 at noPlace ⊢
            have scope1 := agrees.inScope.bind results (List.range' r res.length) (by simp)
              fun i m => by
                have := mem_range'_bounds m
                have := below.1
                omega
            obtain ⟨-, grows⟩ := walk_grows rules checks definition role blocks rest (some rest') _
              k1 s scope1 wf (FollowedBelow.of_some below.2)
            refine .effect (env.all args)
              (ReadsAll.mono Run _ grows.sub (.refl ρ) (agrees.readsAll args))
              fun returned returns => ?_
            have bound := agrees.leaves support results returned r res.length rfl inOrder.1 below.1
            exact walk_runs_followed binding lawful blocks rest rest' _ k1 s path _ _ _ noPlace wf
              below.2 apart.2 bound.1 inOrder.2 bound.2 (safe.of_bind_canReturn returns)
    | _, _, .guard (t := t) key w c ok why rest, skel, ids, k, s, path, env, ρ, lo, noPlace, wf,
        below, apart, support, inOrder, agrees, safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : guardEntry checks (t := t) key w (idOf ids c.name) why (some skel) = hit
          at noPlace ⊢
        obtain ⟨rest', rfl⟩ : ∃ a, hit = some a := hit_of_no_place
          (walk_adds rules checks definition role blocks rest _ _ _ _) noPlace
        obtain ⟨ok', e⟩ := guardEntry_hit checks hhit
        obtain rfl := Option.some.inj e
        simp only [Option.isSome_some, miss_found] at noPlace ⊢
        generalize assume rules.ops _ _ _ _ _ = k1 at noPlace ⊢
        obtain ⟨-, grows⟩ := walk_grows rules checks definition role blocks rest (some rest') ids k1
          s agrees.inScope wf (FollowedBelow.of_some below)
        have read := Reads.mono Run _ grows.sub (.refl ρ) (agrees.read c).2
        simp only [Term.denote] at safe ⊢
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            exact .guardHolds _ read holds
              (walk_runs_followed binding lawful blocks rest rest' ids k1 s path env ρ lo noPlace wf
                below apart support inOrder agrees safe)
        | false =>
            simp only [Bool.cond_false]
            exact .guardStops _ read holds
    | _, _, .choose (mid := mid) (t := t) key w c ok _ onTrue onFalse results rest, skel, ids, k,
        s, path, env, ρ, lo, noPlace, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : chooseEntry checks (mid := mid) (t := t) key w (idOf ids c.name)
          (some skel) = hit at noPlace ⊢
        obtain ⟨⟨onTrue', onFalse', r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks onFalse _ _ _ _)
          exact walk_adds rules checks definition role blocks onTrue _ _ _ _) noPlace
        obtain ⟨ok', e⟩ := chooseEntry_hit checks hhit
        obtain rfl := Option.some.inj e
        simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        generalize assume rules.ops _ _ k _ true = k1 at noPlace ⊢
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks onTrue (some onTrue')
          ids k1 s scope wf (FollowedBelow.of_some below.1)
        have noPlaceTrue : (walk rules checks definition role blocks onTrue (some onTrue') ids k1
            s).state.differs = [] := AddsPlaces.none_before (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          exact walk_adds rules checks definition role blocks onFalse _ _ _ _) noPlace
        have runsTrue := fun safeTrue =>
          walk_runs_followed binding lawful blocks onTrue onTrue' ids k1 s path env ρ lo
            noPlaceTrue wf below.1 apart.1 support inOrder.1 agrees safeTrue
        generalize walk rules checks definition role blocks onTrue (some onTrue') ids k1 s = first
          at wf1 grows1 noPlaceTrue runsTrue noPlace ⊢
        generalize assume rules.ops _ _ k _ false = k2 at noPlace ⊢
        obtain ⟨wf2, grows2⟩ := walk_grows rules checks definition role blocks onFalse
          (some onFalse') ids k2 first.state (scope.mono grows1.next) wf1
          (FollowedBelow.of_some (below.2.1.mono grows1.next))
        have noPlaceFalse := AddsPlaces.none_before
          (walk_adds rules checks definition role blocks rest _ _ _ _) noPlace
        have runsFalse := fun safeFalse =>
          walk_runs_followed binding lawful blocks onFalse onFalse' ids k2 first.state path env ρ lo
            noPlaceFalse wf1 (below.2.1.mono grows1.next)
            (Skel.Apart.grows grows1 _ apart.2.1 below.2.1) support inOrder.2.1
            (agrees.mono grows1.sub grows1.next (.refl ρ)) safeFalse
        generalize walk rules checks definition role blocks onFalse (some onFalse') ids k2
          first.state = second at wf2 grows2 noPlaceFalse runsFalse noPlace ⊢
        generalize Known.enter rules _ _ = k3 at noPlace ⊢
        have toRest := grows1.trans grows2
        have scope3 := (scope.mono toRest.next).bind results (List.range' r mid.length) (by simp)
          fun i m => by
            have := mem_range'_bounds m
            have := below.2.2.1
            have := toRest.next
            omega
        obtain ⟨-, grows3⟩ := walk_grows rules checks definition role blocks rest (some rest') _ k3
          second.state scope3 wf2 (FollowedBelow.of_some (below.2.2.2.mono toRest.next))
        have read := Reads.mono Run _ (toRest.trans grows3).sub (.refl ρ) (agrees.read c).2
        cases holds : sem.holds ok (env.get c) with
        | true =>
            simp only [holds, Bool.cond_true] at safe ⊢
            refine .chooseTrue _ read holds
              (Skel.Runs.grow sem permitted Run _ (grows2.trans grows3).sub _
                (runsTrue safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves support results
              returned r mid.length rfl inOrder.2.2.1 (Nat.le_trans below.2.2.1 toRest.next)
            exact walk_runs_followed binding lawful blocks rest rest' _ k3 second.state path _ _ _
              noPlace wf2 (below.2.2.2.mono toRest.next)
              (Skel.Apart.grows toRest _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2 bound.2
              (safe.of_bind_canReturn returns)
        | false =>
            simp only [holds, Bool.cond_false] at safe ⊢
            refine .chooseFalse _ read holds
              (Skel.Runs.grow sem permitted Run _ grows3.sub _ (runsFalse safe.of_bind))
              fun returned returns => ?_
            have bound := (agrees.mono toRest.sub toRest.next (.refl ρ)).leaves support results
              returned r mid.length rfl inOrder.2.2.1 (Nat.le_trans below.2.2.1 toRest.next)
            exact walk_runs_followed binding lawful blocks rest rest' _ k3 second.state path _ _ _
              noPlace wf2 (below.2.2.2.mono toRest.next)
              (Skel.Apart.grows toRest _ apart.2.2.2 below.2.2.2) bound.1 inOrder.2.2.2 bound.2
              (safe.of_bind_canReturn returns)
    | _, _, .cases (mid := mid) (t := t) (payloads := payloads) key w x ok _ arms results rest,
        skel, ids, k, s, path, env, ρ, lo, noPlace, wf, below, apart, support, inOrder, agrees,
        safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w
          (idOf ids x.name) (some skel) = hit at noPlace ⊢
        obtain ⟨⟨arms', r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
          exact walkArms_adds rules checks definition role blocks arms _ _ _ _) noPlace
        obtain ⟨ok', e⟩ := casesEntry_hit checks hhit
        obtain rfl := Option.some.inj e
        simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1⟩ := walkArms_grows rules checks definition role blocks arms (some arms')
          ids k s scope wf (ArmsFollowedBelow.of_some below.1)
        have noPlaceArms := AddsPlaces.none_before
          (walk_adds rules checks definition role blocks rest _ _ _ _) noPlace
        have runsArms := walkArms_runs_followed binding lawful blocks arms arms' ids k s path env ρ
          lo (sem.pick ok (env.get x)) noPlaceArms wf below.1 apart.1 support inOrder.1 agrees
          safe.of_bind
        generalize walkArms rules checks definition role blocks arms (some arms') ids k s = regions
          at wf1 grows1 noPlaceArms runsArms noPlace ⊢
        generalize Known.enter rules _ _ = k3 at noPlace ⊢
        have scope3 := (scope.mono grows1.next).bind results (List.range' r mid.length) (by simp)
          fun i m => by
            have := mem_range'_bounds m
            have := below.2.1
            have := grows1.next
            omega
        obtain ⟨-, grows3⟩ := walk_grows rules checks definition role blocks rest (some rest') _ k3
          regions.state scope3 wf1 (FollowedBelow.of_some (below.2.2.mono grows1.next))
        refine .cases (env.get x)
          (Reads.mono Run _ (grows1.trans grows3).sub (.refl ρ) (agrees.read x).2)
          (SkelArms.Runs.grow sem permitted Run _ grows3.sub _ runsArms)
          fun returned returns => ?_
        have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support results
          returned r mid.length rfl inOrder.2.1 (Nat.le_trans below.2.1 grows1.next)
        exact walk_runs_followed binding lawful blocks rest rest' _ k3 regions.state path _ _ _
          noPlace wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2)
          bound.1 inOrder.2.2 bound.2 (safe.of_bind_canReturn returns)
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, skel, ids, k, s, path, env, ρ, lo, noPlace, wf, below, apart, support, inOrder,
        agrees, safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : loopEntry checks (carried := carried) (each := each) key w
          (fun count => times.follows checks ids count) (idsOf ids initial) (some skel) = hit
          at noPlace ⊢
        obtain ⟨⟨inputs', body', r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
          refine AddsPlaces.trans ?_ (AddsPlaces.with_st _ _)
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks body _ _ _ _)
          exact leaves_adds _ _ _) noPlace
        obtain ⟨times', sameTimes, e⟩ := loopEntry_hit checks hhit
        obtain rfl := Option.some.inj e
        obtain rfl := Times.follows_eq checks ids times times' sameTimes
        simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        generalize bodyKnown rules _ _ _ _ _ _ = k1 at noPlace ⊢
        have scope0 := scope.bind inputs (List.range' inputs' (carried.length + 1)) (by simp)
          fun i m => by
            have := mem_range'_bounds m
            have := below.1
            omega
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body (some body')
          _ k1 s scope0 wf (FollowedBelow.of_some below.2.1)
        have noPlaceBody : (walk rules checks definition role blocks body (some body')
            (bindIds ids inputs (List.range' inputs' (carried.length + 1))) k1 s).state.differs =
            [] := AddsPlaces.none_before (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          exact AddsPlaces.with_st _ _) noPlace
        have runsBody := fun path' env' ρ' support' agrees' safe' =>
          walk_runs_followed binding lawful blocks body body'
            (bindIds ids inputs (List.range' inputs' (carried.length + 1))) k1 s path' env' ρ' _
            noPlaceBody wf below.2.1 apart.2.1 support' inOrder.2.1 agrees' safe'
        generalize walk rules checks definition role blocks body (some body') _ k1 s = e
          at wf1 grows1 noPlaceBody runsBody noPlace ⊢
        obtain ⟨tableSame, nextSame, -, -⟩ :=
          recordBound_state ⟨definition, blocks, some key, role⟩ k ids e.state.st times
        generalize recordBound _ k ids e.state.st times = st₁ at tableSame nextSame noPlace ⊢
        obtain ⟨table₁, next₁, refusals₁, bounds₁⟩ := st₁
        simp only at tableSame nextSame
        subst tableSame nextSame
        have grows2 : St.Grows e.state.st
            ⟨e.state.st.table, e.state.st.next, refusals₁, bounds₁⟩ :=
          ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩
        generalize Known.enter rules _ _ = k3 at noPlace ⊢
        have scope3 := (scope.mono grows1.next).bind results
          (List.range' r (carried.length + each.length)) (by simp) fun i m => by
            have := mem_range'_bounds m
            have := below.2.2.1
            have := grows1.next
            omega
        obtain ⟨-, grows3⟩ := walk_grows rules checks definition role blocks rest (some rest') _ k3
          { e.state with st := ⟨e.state.st.table, e.state.st.next, refusals₁, bounds₁⟩ } scope3 wf1
          (FollowedBelow.of_some (below.2.2.2.mono grows1.next))
        have toEnd := grows1.trans (grows2.trans grows3)
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
          bodyOf (fun i state below' returns => ?_) (fun final returns => ?_)
        · have bound := agrees.leaves support inputs (.cons (sem.index w i) state.1) inputs'
            (carried.length + 1) rfl inOrder.1 below.1
          have safeStep := Process.Every.iterate_step i _ 0 _ state below' safe.of_bind returns
          rw [Nat.zero_add] at safeStep
          exact Skel.Runs.grow sem permitted Run _ (grows2.trans grows3).sub _
            (runsBody _ _ _ bound.1 bound.2 safeStep.of_bind)
        · rw [Times.dyns_collected sem ids times final]
          have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support results
            (final.1.append (sem.collected times.size final.2)) r (carried.length + each.length)
            (by simp) inOrder.2.2.1 (Nat.le_trans below.2.2.1 grows1.next)
          exact walk_runs_followed binding lawful blocks rest rest' _ k3 _ path _ _ _ noPlace wf1
            (below.2.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2)
            bound.1 inOrder.2.2.2 bound.2 (safe.of_bind_canReturn returns)
    | _, _, .block (mid := mid) key number body results rest, skel, ids, k, s, path, env, ρ, lo,
        noPlace, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : blockEntry checks (mid := mid) key number (some skel) = hit at noPlace ⊢
        obtain ⟨⟨body', r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
          exact walk_adds rules checks definition role (blocks ++ [(key, number)]) body _ _ _ _)
          noPlace
        obtain rfl := Option.some.inj (blockEntry_hit checks hhit)
        simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role (blocks ++ [(key, number)])
          body (some body') ids k s scope wf (FollowedBelow.of_some below.1)
        have noPlaceBody := AddsPlaces.none_before
          (walk_adds rules checks definition role blocks rest _ _ _ _) noPlace
        have runsBody := fun path' safe' =>
          walk_runs_followed binding lawful (blocks ++ [(key, number)]) body body' ids k s path' env
            ρ lo noPlaceBody wf below.1 apart.1 support inOrder.1 agrees safe'
        generalize walk rules checks definition role (blocks ++ [(key, number)]) body (some body')
          ids k s = e at wf1 grows1 noPlaceBody runsBody noPlace ⊢
        generalize Known.enter rules _ _ = k3 at noPlace ⊢
        have scope3 := (scope.mono grows1.next).bind results (List.range' r mid.length) (by simp)
          fun i m => by
            have := mem_range'_bounds m
            have := below.2.1
            have := grows1.next
            omega
        obtain ⟨-, grows3⟩ := walk_grows rules checks definition role blocks rest (some rest') _ k3
          e.state scope3 wf1 (FollowedBelow.of_some (below.2.2.mono grows1.next))
        refine .block (Skel.Runs.grow sem permitted Run _ grows3.sub _ (runsBody _ safe.of_bind))
          fun returned returns => ?_
        have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support results
          returned r mid.length rfl inOrder.2.1 (Nat.le_trans below.2.1 grows1.next)
        exact walk_runs_followed binding lawful blocks rest rest' _ k3 e.state path _ _ _ noPlace
          wf1 (below.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2 below.2.2) bound.1
          inOrder.2.2 bound.2 (safe.of_bind_canReturn returns)
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, skel, ids, k, s, path, env, ρ,
        lo, noPlace, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [walk] at noPlace ⊢
        generalize hhit : attemptEntry checks (mid := mid) key w (some skel) = hit at noPlace ⊢
        obtain ⟨⟨input', body', r, rest'⟩, rfl⟩ : ∃ a, hit = some a := hit_of_no_place (by
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks rest _ _ _ _)
          refine AddsPlaces.trans ?_ (leaves_adds _ _ _)
          refine AddsPlaces.trans ?_ (walk_adds rules checks definition role blocks body _ _ _ _)
          exact leaves_adds _ _ _) noPlace
        obtain rfl := Option.some.inj (attemptEntry_hit checks hhit)
        simp only [Option.isSome_some, miss_found, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Term.denote] at safe ⊢
        have scope := agrees.inScope
        generalize Known.enter rules (Known.addRanges k _ _) _ = k1 at noPlace ⊢
        have scope0 := scope.bind inputs (List.range' input' 1) (by simp) fun i m => by
          have := mem_range'_bounds m
          have := below.1
          omega
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks body (some body') _
          k1 s scope0 wf (FollowedBelow.of_some below.2.1)
        have noPlaceBody := AddsPlaces.none_before
          (walk_adds rules checks definition role blocks rest _ _ _ _) noPlace
        have runsBody := fun env' ρ' support' agrees' safe' =>
          walk_runs_followed binding lawful blocks body body'
            (bindIds ids inputs (List.range' input' 1)) k1 s path env' ρ' _ noPlaceBody wf below.2.1
            apart.2.1 support' inOrder.2.1 agrees' safe'
        generalize walk rules checks definition role blocks body (some body') _ k1 s = e
          at wf1 grows1 noPlaceBody runsBody noPlace ⊢
        generalize Known.enter rules _ _ = k3 at noPlace ⊢
        have scope3 := (scope.mono grows1.next).bind results (List.range' r mid.length) (by simp)
          fun i m => by
            have := mem_range'_bounds m
            have := below.2.2.1
            have := grows1.next
            omega
        obtain ⟨-, grows3⟩ := walk_grows rules checks definition role blocks rest (some rest') _ k3
          e.state scope3 wf1 (FollowedBelow.of_some (below.2.2.2.mono grows1.next))
        refine .attempt (fun number => body.denote sem path (env.extend inputs (.cons number .nil)))
          (fun number began => ?_) (fun number returned began ran settled => ?_)
        · have bound := agrees.leaves support inputs (.cons number .nil) input' 1 rfl inOrder.1
            below.1
          exact Skel.Runs.grow sem permitted Run _ grows3.sub _
            (runsBody _ _ bound.1 bound.2 (safe.of_bind_canReturn began).of_bind)
        · have bound := (agrees.mono grows1.sub grows1.next (.refl ρ)).leaves support results
            returned r mid.length rfl inOrder.2.2.1 (Nat.le_trans below.2.2.1 grows1.next)
          exact walk_runs_followed binding lawful blocks rest rest' _ k3 e.state path _ _ _ noPlace
            wf1 (below.2.2.2.mono grows1.next) (Skel.Apart.grows grows1 _ apart.2.2.2 below.2.2.2)
            bound.1 inOrder.2.2.2 bound.2
            (((safe.of_bind_canReturn began).of_bind_canReturn ran).of_bind_canReturn settled)
  /-- With arms to follow and no place that differs at the end, the arms of a term that never
  stop `undefined` on an alternative run the arms that they follow, on it. -/
  theorem walkArms_runs_followed (binding : rules.values.Binding sem Run undefined)
      (lawful : checks.Lawful) (blocks : List (Key × Nat)) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (skel : SkelArms D mid payloads) (ids : Ctx Nat) (k : Known) (s : State D.Ty Raw)
        (path : List Frame) (env : Env sem.Val Γ) (ρ : Valuation sem.Dyn) (lo : Nat)
        (pick : Pick sem.Val payloads),
        (walkArms rules checks definition role blocks arms (some skel) ids k s).state.differs =
          [] →
        Table.WF s.st.next s.st.table → skel.Below s.st.next → skel.Apart s.st.table →
        Support lo ρ → skel.Fresh lo →
        Agrees sem Run s.st.table s.st.next ρ ids env →
        (arms.denote sem path env pick).Every permitted (fun _ => True)
          (fun stop => ¬ undefined stop) →
        SkelArms.Runs sem permitted Run
          (walkArms rules checks definition role blocks arms (some skel) ids k s).state.st.table
          path ρ skel pick (arms.denote sem path env pick)
    | _, _, _, .nil, .nil, _, _, _, _, _, _, _, pick, _, _, _, _, _, _, _, _ => nomatch pick
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, k, s, path, env, ρ, lo,
        .here v, noPlace, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [walkArms, armEntry, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Arms.denote] at safe ⊢
        have scope := agrees.inScope
        generalize Known.enter rules _ _ = k1 at noPlace ⊢
        have scope0 := scope.bind inputs (List.range' input' 1) (by simp) fun i m => by
          have := mem_range'_bounds m
          have := below.1
          omega
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks arm (some arm') _ k1
          s scope0 wf (FollowedBelow.of_some below.2.1)
        have noPlaceArm := AddsPlaces.none_before
          (walkArms_adds rules checks definition role blocks rest _ _ _ _) noPlace
        have bound := agrees.leaves support inputs (.cons v .nil) input' 1 rfl inOrder.1 below.1
        have runsArm := walk_runs_followed binding lawful blocks arm arm'
          (bindIds ids inputs (List.range' input' 1)) k1 s path _ _ _ noPlaceArm wf below.2.1
          apart.2.1 bound.1 inOrder.2.1 bound.2 safe
        generalize walk rules checks definition role blocks arm (some arm') _ k1 s = e
          at wf1 grows1 runsArm noPlace ⊢
        obtain ⟨-, grows2⟩ := walkArms_grows rules checks definition role blocks rest (some rest')
          ids k e.state (scope.mono grows1.next) wf1
          (ArmsFollowedBelow.of_some (below.2.2.mono grows1.next))
        exact .here (Skel.Runs.grow sem permitted Run _ grows2.sub _ runsArm)
    | _, _, _, .cons inputs arm rest, .cons input' arm' rest', ids, k, s, path, env, ρ, lo,
        .there pick, noPlace, wf, below, apart, support, inOrder, agrees, safe => by
        simp only [walkArms, armEntry, Option.map_some, leaves_some] at noPlace ⊢
        simp only [Arms.denote] at safe ⊢
        have scope := agrees.inScope
        generalize Known.enter rules _ _ = k1 at noPlace ⊢
        have scope0 := scope.bind inputs (List.range' input' 1) (by simp) fun i m => by
          have := mem_range'_bounds m
          have := below.1
          omega
        obtain ⟨wf1, grows1⟩ := walk_grows rules checks definition role blocks arm (some arm')
          (bindIds ids inputs (List.range' input' 1)) k1 s scope0 wf
          (FollowedBelow.of_some below.2.1)
        generalize walk rules checks definition role blocks arm (some arm') _ k1 s = e
          at wf1 grows1 noPlace ⊢
        exact .there (walkArms_runs_followed binding lawful blocks rest rest' ids k e.state path env
          ρ lo pick noPlace wf1 (below.2.2.mono grows1.next)
          (SkelArms.Apart.grows grows1 _ apart.2.2 below.2.2) support inOrder.2.2
          (agrees.mono grows1.sub grows1.next (.refl ρ)) safe)
end

end

end Zkc.Core.Analysis.ValueSide

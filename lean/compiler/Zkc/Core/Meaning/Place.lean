module

public import Zkc.Core.Meaning.Stepped
public import Zkc.Core.Process.Same
public import Zkc.Core.Program.Place

@[expose] public section

/-!
Places inside a term, with their meaning.

A term in a wider context means the same on environments that agree with the narrower one
(`Term.denote_reindex`): the structural rule on contexts keeps the meaning.

A run of a term with one place left open reaches the place with a path and an environment
(`Hole.Reaches`), on permitted replies: every instruction before it returned, every guard before
it held, the regions around it are those that run, and inside the body of a loop the place is
reached once for each iteration that begins. A fact at a place is a property of every path and
environment with which a run reaches it (`Hole.Holds`); it says nothing that would allow removing
what established it.

Replacement (`Hole.fill_same`): two terms that mean the same wherever a run reaches the place
give wholes that mean the same. And the meaning of a term depends on its environment only at
the names that it reads (`Term.denote_reads`).
-/

namespace Zkc.Core

/-! ## Environments that agree with a narrower one -/

section
variable {T : Type}

/-- An environment of the wider context gives every name of the narrower one the value that the
narrower environment gives it. -/
def Env.Agrees {V : T → Type} {Γ Δ : Ctx T} (keeps : Γ.Within Δ) (wide : Env V Δ)
    (narrow : Env V Γ) : Prop :=
  ∀ name τ (found : Γ.find? name = some τ), wide name τ (keeps name τ found) = narrow name τ found

/-- Environments that agree still agree with one more name bound to the same value on both
sides. -/
theorem Env.Agrees.insert {V : T → Type} {Γ Δ : Ctx T} {keeps : Γ.Within Δ} {wide : Env V Δ}
    {narrow : Env V Γ} (agrees : Env.Agrees keeps wide narrow) (bound : Name) {τ : T} (v : V τ) :
    Env.Agrees (keeps.insert bound τ) (wide.insert bound v) (narrow.insert bound v) := by
  intro name σ found
  by_cases same : name = bound
  · exact eq_of_heq ((Env.insert_at_bound wide bound v same _).trans
      (Env.insert_at_bound narrow bound v same found).symm)
  · rw [Env.insert_at_other wide bound v same, Env.insert_at_other narrow bound v same]
    exact agrees name σ _

/-- Environments that agree still agree after a binding binds the same values on both sides. -/
theorem Env.Agrees.extend {V : T → Type} {Γ Δ : Ctx T} {keeps : Γ.Within Δ} {wide : Env V Δ}
    {narrow : Env V Γ} (agrees : Env.Agrees keeps wide narrow) :
    ∀ {types : List T} (bound : Names types) (values : HList V types),
      Env.Agrees (keeps.extend bound) (wide.extend bound values) (narrow.extend bound values) := by
  intro types bound values
  induction bound generalizing Γ Δ with
  | nil =>
      cases values
      exact agrees
  | cons name rest ih =>
      cases values with
      | cons v vs => exact ih (agrees.insert name v) vs

/-- A variable in the wider context has, in an environment that agrees, the value of the
variable in the narrower one. -/
theorem Env.Agrees.get {V : T → Type} {Γ Δ : Ctx T} {keeps : Γ.Within Δ} {wide : Env V Δ}
    {narrow : Env V Γ} (agrees : Env.Agrees keeps wide narrow) {τ : T} (x : Var Γ τ) :
    wide.get (x.reindex keeps) = narrow.get x :=
  agrees x.name τ x.typed

/-- Variables in the wider context have, in an environment that agrees, the values of the
variables in the narrower one. -/
theorem Env.Agrees.all {V : T → Type} {Γ Δ : Ctx T} {keeps : Γ.Within Δ} {wide : Env V Δ}
    {narrow : Env V Γ} (agrees : Env.Agrees keeps wide narrow) :
    ∀ {items : List T} (xs : HList (Var Γ) items),
      wide.all (HList.reindex keeps xs) = narrow.all xs
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      show HList.cons (wide.get (x.reindex keeps)) (wide.all (HList.reindex keeps rest)) =
        HList.cons (narrow.get x) (narrow.all rest)
      rw [agrees.get x, Env.Agrees.all agrees rest]

end

section
variable {D : Dialect}

/-! ## The structural rule keeps the meaning -/

mutual
  /-- A term in a wider context means the same on environments that agree. -/
  theorem Term.denote_reindex (sem : Semantics D) :
      ∀ {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (keeps : Γ.Within Δ) (t : Term D Γ outs)
        (path : List Frame) {wide : Env sem.Val Δ} {narrow : Env sem.Val Γ},
        Env.Agrees keeps wide narrow →
        (t.reindex keeps).denote sem path wide = t.denote sem path narrow
    | _, _, _, keeps, .ret exit, path, wide, narrow, agrees => by
        simp only [Term.reindex, Term.denote_ret, agrees.all]
    | _, _, _, keeps, .step key i results rest, path, wide, narrow, agrees => by
        simp only [Term.reindex, Term.denote_step, Instr.denote_reindex sem keeps key i path agrees]
        congr 1
        funext values
        exact Term.denote_reindex sem (keeps.extend results) rest path (agrees.extend results values)
  /-- Reindexing preserves the instruction process, including effects under its regions. -/
  theorem Instr.denote_reindex (sem : Semantics D) :
      ∀ {Γ Δ : Ctx D.Ty} {mid : List D.Ty} (keeps : Γ.Within Δ) (key : Key) (i : Instr D Γ mid)
        (path : List Frame) {wide : Env sem.Val Δ} {narrow : Env sem.Val Γ}, Env.Agrees keeps wide narrow →
        (i.reindex keeps).denote sem key path wide = i.denote sem key path narrow
    | _, _, _, keeps, _, .op o args, _, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_op, agrees.all]
    | _, _, _, keeps, _, .guard w c ok why, _, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_guard, agrees.get]
    | _, _, _, keeps, _, .choose _ _ _ _ t f, path, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_choose, agrees.get,
          Term.denote_reindex sem keeps t path agrees, Term.denote_reindex sem keeps f path agrees]
    | _, _, _, keeps, _, .cases _ _ _ _ arms, path, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_cases, agrees.get, Arms.denote_reindex sem keeps arms path agrees]
    | _, _, _, keeps, key, .loop w times _ initial inputs body, path, wide, narrow, agrees => by
        have step : sem.loopStep w inputs
              (fun path' env' => (body.reindex (keeps.extend inputs)).denote sem path' env') key path wide =
            sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path narrow := by
          funext i state
          simp only [Semantics.loopStep]
          rw [Term.denote_reindex sem (keeps.extend inputs) body _ (agrees.extend inputs _)]
        cases times <;> simp only [Instr.reindex] <;> erw [Instr.denote_loop, Instr.denote_loop]
        · simp only [agrees.all, step, Semantics.times]
          rfl
        · simp only [agrees.all, step, Semantics.times, agrees.get]
          rfl
    | _, _, _, keeps, _, .block _ body, _, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_block, Term.denote_reindex sem keeps body _ agrees]
    | _, _, _, keeps, _, .attempt _ _ inputs body, _, _, _, agrees => by
        simp only [Instr.reindex, Instr.denote_attempt,
          Term.denote_reindex sem (keeps.extend inputs) body _ (agrees.extend inputs _)]
  /-- The arms of a case analysis in a wider context mean the same on environments that agree. -/
  theorem Arms.denote_reindex (sem : Semantics D) :
      ∀ {Γ Δ : Ctx D.Ty} {mid payloads : List D.Ty} (keeps : Γ.Within Δ)
        (arms : Arms D Γ mid payloads) (path : List Frame) {wide : Env sem.Val Δ}
        {narrow : Env sem.Val Γ}, Env.Agrees keeps wide narrow →
        ∀ pick : Pick sem.Val payloads,
          (arms.reindex keeps).denote sem path wide pick = arms.denote sem path narrow pick
    | _, _, _, _, _, .nil, _, _, _, _, pick => nomatch pick
    | _, _, _, _, keeps, .cons inputs arm rest, path, wide, narrow, agrees, .here v => by
        simp only [Arms.reindex, Arms.denote_cons]
        exact Term.denote_reindex sem (keeps.extend inputs) arm path
          (agrees.extend inputs (.cons v .nil))
    | _, _, _, _, keeps, .cons inputs arm rest, path, wide, narrow, agrees, .there pick => by
        simp only [Arms.reindex, Arms.denote_cons]
        exact Arms.denote_reindex sem keeps rest path agrees pick
end

/-! ## Reaching a place -/

variable (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)

mutual
  /-- A run of the whole, with `filling` at the open place, from the path and the environment
  at its start reaches the place with the path and the environment `path'` and `env'`, on permitted
  replies: every instruction before the place returned, every guard before it held, the regions
  around it are those that run. Inside the body of a loop the place is reached once for each
  iteration that begins, after the iterations before it, which ran the filling. -/
  def Hole.Reaches : {Γ : Ctx D.Ty} → {outs : List D.Ty} → {Δ : Ctx D.Ty} → {mid : List D.Ty} →
      Hole D Γ outs Δ mid → Term D Δ mid → List Frame → Env sem.Val Γ → List Frame →
      Env sem.Val Δ → Prop
    | _, _, _, _, .here, _, path, env, path', env' => path' = path ∧ env' = env
    | _, _, _, _, .step key i results rest, filling, path, env, path', env' =>
        ∃ values, (i.denote sem key path env).CanReturn permitted values ∧
          rest.Reaches filling path (env.extend results values) path' env'
    | _, _, _, _, .inTrue _ _ c ok _ onTrue _ _ _, filling, path, env, path', env' =>
        sem.holds ok (env.get c) = true ∧ onTrue.Reaches filling path env path' env'
    | _, _, _, _, .inFalse _ _ c ok _ _ onFalse _ _, filling, path, env, path', env' =>
        sem.holds ok (env.get c) = false ∧ onFalse.Reaches filling path env path' env'
    | _, _, _, _, .inArm _ _ x ok _ arms _ _, filling, path, env, path', env' =>
        arms.Reaches filling path env (sem.pick ok (env.get x)) path' env'
    | _, _, _, _, .inLoop (each := each) key w times _ initial inputs body _ _, filling, path, env, path',
        env' =>
        ∃ i state, i < sem.times times env ∧
          (Process.iterate i
              (sem.loopStep w inputs (fun at_ inside => (body.fill filling).denote sem at_ inside)
                key path env)
              0 (env.all initial, HList.empties each)).CanReturn permitted state ∧
          body.Reaches filling (path ++ [.iteration key i])
            (env.extend inputs (.cons (sem.index w i) state.1)) path' env'
    | _, _, _, _, .inBlock key number body _ _, filling, path, env, path', env' =>
        body.Reaches filling (path ++ [.iteration key number]) env path' env'
    | _, _, _, _, .inAttempt key w _ inputs body _ _, filling, path, env, path', env' =>
        ∃ n, (sem.begin w key path).CanReturn permitted n ∧
          body.Reaches filling path (env.extend inputs (.cons n .nil)) path' env'
  /-- A run of a case analysis on an alternative reaches the open place of its arms. -/
  def ArmsHole.Reaches : {Γ : Ctx D.Ty} → {inner payloads : List D.Ty} → {Δ : Ctx D.Ty} →
      {mid : List D.Ty} → ArmsHole D Γ inner payloads Δ mid → Term D Δ mid → List Frame →
      Env sem.Val Γ → Pick sem.Val payloads → List Frame → Env sem.Val Δ → Prop
    | _, _, _, _, _, .first inputs arm _, filling, path, env, .here v, path', env' =>
        arm.Reaches filling path (env.extend inputs (.cons v .nil)) path' env'
    | _, _, _, _, _, .first _ _ _, _, _, _, .there _, _, _ => False
    | _, _, _, _, _, .later _ _ _, _, _, _, .here _, _, _ => False
    | _, _, _, _, _, .later _ _ rest, filling, path, env, .there p, path', env' =>
        rest.Reaches filling path env p path' env'
end

/-- Reaching the end of a prefix preserves the path and returns the reached environment. -/
theorem Prefix.return_of_reaches {outs : List D.Ty} {Γ Δ : Ctx D.Ty}
    (p : Prefix D Γ Δ) (t : Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ)
    (path' : List Frame) (env' : Env sem.Val Δ)
    (reach : p.hole.Reaches sem permitted t path env path' env') :
    path' = path ∧ (p.run sem path env).CanReturn permitted env' := by
  induction p with
  | nil =>
    obtain ⟨rfl, rfl⟩ := reach
    exact ⟨rfl, .done _⟩
  | step key i results rest ih =>
    obtain ⟨values, returned, later⟩ := reach
    obtain ⟨same, ended⟩ := ih t _ _ later
    exact ⟨same, returned.bind ended⟩

/-- A fact at a place: it holds of every path and environment with which a run reaches the
place. It says nothing that would allow removing what established it. -/
def Hole.Holds {Γ : Ctx D.Ty} {outs : List D.Ty} {Δ : Ctx D.Ty} {mid : List D.Ty}
    (hole : Hole D Γ outs Δ mid) (filling : Term D Δ mid) (path : List Frame)
    (env : Env sem.Val Γ) (fact : List Frame → Env sem.Val Δ → Prop) : Prop :=
  ∀ path' env', hole.Reaches sem permitted filling path env path' env' → fact path' env'

/-! ## Replacement -/

mutual
  /-- Replacement: two terms that mean the same wherever a run reaches the place give wholes that
  mean the same. -/
  theorem Hole.fill_same {Γ : Ctx D.Ty} {outs : List D.Ty} {Δ : Ctx D.Ty} {mid : List D.Ty}
      (hole : Hole D Γ outs Δ mid) (t t' : Term D Δ mid) (path : List Frame)
      (env : Env sem.Val Γ)
      (same : hole.Holds sem permitted t path env fun path' env' =>
        Process.SameWhen permitted (t.denote sem path' env') (t'.denote sem path' env')) :
      Process.SameWhen permitted ((hole.fill t).denote sem path env)
        ((hole.fill t').denote sem path env) :=
    match Γ, outs, Δ, mid, hole, t, t', path, env, same with
    | _, _, _, _, .here, t, t', path, env, same => same path env ⟨rfl, rfl⟩
    | _, _, _, _, .step key i results rest, t, t', path, env, same => by
        simp only [Hole.fill, Term.denote_step]
        exact Process.SameWhen.bind (.refl _) (Process.every_canReturn _) fun values returns =>
          Hole.fill_same rest t t' path _ fun path' env' reach =>
            same path' env' ⟨values, returns, reach⟩
    | _, _, _, _, .inTrue key w c ok gives onTrue onFalse results rest, t, t', path, env, same => by
        simp only [Hole.fill, Term.denote_choose]
        cases holds : sem.holds ok (env.get c) with
        | false => exact .refl _
        | true =>
            exact Process.SameWhen.bind
              (Hole.fill_same onTrue t t' path env fun path' env' reach =>
                same path' env' ⟨holds, reach⟩)
              (Process.every_true _ _) fun _ _ => .refl _
    | _, _, _, _, .inFalse key w c ok gives onTrue onFalse results rest, t, t', path, env,
        same => by
        simp only [Hole.fill, Term.denote_choose]
        cases holds : sem.holds ok (env.get c) with
        | false =>
            exact Process.SameWhen.bind
              (Hole.fill_same onFalse t t' path env fun path' env' reach =>
                same path' env' ⟨holds, reach⟩)
              (Process.every_true _ _) fun _ _ => .refl _
        | true => exact .refl _
    | _, _, _, _, .inArm key w x ok gives arms results rest, t, t', path, env, same => by
        simp only [Hole.fill, Term.denote_cases]
        exact Process.SameWhen.bind
          (ArmsHole.fill_same arms t t' path env _ fun path' env' reach => same path' env' reach)
          (Process.every_true _ _) fun _ _ => .refl _
    | _, _, _, _, .inLoop (each := each) key w times gives initial inputs body results rest, t, t',
        path, env, same => by
        simp only [Hole.fill, Term.denote_loop]
        refine Process.SameWhen.bind ?_ (Process.every_true _ _) fun _ _ => .refl _
        refine Process.SameWhen.iterate_below
          (fun i state => (Process.iterate i
            (sem.loopStep w inputs (fun at_ inside => (body.fill t).denote sem at_ inside) key
              path env) 0 (env.all initial, HList.empties each)).CanReturn permitted state)
          (sem.times times env) ?_ ?_ (sem.times times env) 0 _
          (Nat.le_of_eq (Nat.zero_add _)) (.done _)
        · intro i state below reached
          simp only [Semantics.loopStep]
          exact Process.SameWhen.bind
            (Hole.fill_same body t t' _ _ fun path' env' reach =>
              same path' env' ⟨i, state, below, reached, reach⟩)
            (Process.every_true _ _) fun _ _ => .refl _
        · intro i state _ reached
          refine Process.every_mono _ permitted (fun next returns => ?_) (fun _ h => h)
            (Process.every_canReturn _)
          refine Process.CanReturn.iterate_succ reached ?_
          rw [Nat.zero_add]
          exact returns
    | _, _, _, _, .inBlock key number body results rest, t, t', path, env, same => by
        simp only [Hole.fill, Term.denote_block]
        exact Process.SameWhen.bind
          (Hole.fill_same body t t' _ env fun path' env' reach => same path' env' reach)
          (Process.every_true _ _) fun _ _ => .refl _
    | _, _, _, _, .inAttempt key w owns inputs body results rest, t, t', path, env, same => by
        simp only [Hole.fill, Term.denote_attempt]
        exact Process.SameWhen.bind (.refl _) (Process.every_canReturn _) fun n began =>
          Process.SameWhen.bind
            (Hole.fill_same body t t' path _ fun path' env' reach =>
              same path' env' ⟨n, began, reach⟩)
            (Process.every_true _ _) fun _ _ => .refl _
  /-- Replacement in the arms of a case analysis: two terms that mean the same wherever a run on
  the alternative reaches the place give arms that mean the same on it. -/
  theorem ArmsHole.fill_same {Γ : Ctx D.Ty} {inner payloads : List D.Ty} {Δ : Ctx D.Ty}
      {mid : List D.Ty} (arms : ArmsHole D Γ inner payloads Δ mid) (t t' : Term D Δ mid)
      (path : List Frame) (env : Env sem.Val Γ) (pick : Pick sem.Val payloads)
      (same : ∀ path' env', arms.Reaches sem permitted t path env pick path' env' →
        Process.SameWhen permitted (t.denote sem path' env') (t'.denote sem path' env')) :
      Process.SameWhen permitted ((arms.fill t).denote sem path env pick)
        ((arms.fill t').denote sem path env pick) :=
    match Γ, inner, payloads, Δ, mid, arms, t, t', path, env, pick, same with
    | _, _, _, _, _, .first inputs arm rest, t, t', path, env, .here v, same => by
        simp only [ArmsHole.fill, Arms.denote_cons]
        exact Hole.fill_same arm t t' path _ fun path' env' reach => same path' env' reach
    | _, _, _, _, _, .first inputs arm rest, t, t', path, env, .there pick, same => by
        simp only [ArmsHole.fill, Arms.denote_cons]
        exact .refl _
    | _, _, _, _, _, .later inputs arm rest, t, t', path, env, .here v, same => by
        simp only [ArmsHole.fill, Arms.denote_cons]
        exact .refl _
    | _, _, _, _, _, .later inputs arm rest, t, t', path, env, .there pick, same => by
        simp only [ArmsHole.fill, Arms.denote_cons]
        exact ArmsHole.fill_same rest t t' path env pick same
end

/-! ## The names that a term reads -/

/-- How often a loop runs is the same in environments that agree at the name that it reads. -/
theorem Semantics.times_same {w : D.Who} {Γ : Ctx D.Ty} (times : Times D w Γ)
    {env env' : Env sem.Val Γ}
    (agree : ∀ name, name ∈ times.reads → ∀ τ found, env name τ found = env' name τ found) :
    sem.times times env = sem.times times env' := by
  cases times with
  | fixed n => rfl
  | value count ok =>
      show sem.count ok (env.get count) = sem.count ok (env'.get count)
      rw [Env.get_same count (agree count.name (.head _))]

mutual
  /-- The meaning of a term depends on its environment only at the names that it reads. -/
  theorem Term.denote_reads {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
      (path : List Frame) (env env' : Env sem.Val Γ)
      (agree : ∀ name, name ∈ t.reads → ∀ τ found, env name τ found = env' name τ found) :
      t.denote sem path env = t.denote sem path env' :=
    match Γ, outs, t, env, env', agree with
    | _, _, .ret exit, env, env', agree => by
        simp only [Term.denote_ret]
        rw [Env.all_same exit agree]
    | _, _, .op key o operands results rest, env, env', agree => by
        simp only [Term.denote_op]
        rw [Env.all_same operands fun name mem => agree name (List.mem_append.mpr (.inl mem))]
        congr 1
        funext values
        exact Term.denote_reads rest path _ _ (Env.extend_same values fun name mem =>
          agree name (List.mem_append.mpr (.inr mem)))
    | _, _, .guard key w c ok why rest, env, env', agree => by
        simp only [Term.denote_guard]
        rw [Env.get_same c (agree c.name (.head _)),
          Term.denote_reads rest path env env' fun name mem => agree name (.tail _ mem)]
    | _, _, .choose key w c ok gives onTrue onFalse results rest, env, env', agree => by
        simp only [Term.denote_choose]
        rw [Env.get_same c (agree c.name (.head _)),
          Term.denote_reads onTrue path env env' fun name mem =>
            agree name (.tail _ (List.mem_append.mpr (.inl mem))),
          Term.denote_reads onFalse path env env' fun name mem =>
            agree name (.tail _ (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl mem)))))]
        congr 1
        funext mids
        exact Term.denote_reads rest path _ _ (Env.extend_same mids fun name mem =>
          agree name (.tail _ (List.mem_append.mpr (.inr (List.mem_append.mpr (.inr mem))))))
    | _, _, .cases key w x ok gives arms results rest, env, env', agree => by
        simp only [Term.denote_cases]
        rw [Env.get_same x (agree x.name (.head _)),
          Arms.denote_reads arms path env env' fun name mem =>
            agree name (.tail _ (List.mem_append.mpr (.inl mem)))]
        congr 1
        funext mids
        exact Term.denote_reads rest path _ _ (Env.extend_same mids fun name mem =>
          agree name (.tail _ (List.mem_append.mpr (.inr mem))))
    | _, _, .loop key w times gives initial inputs body results rest, env, env', agree => by
        have step : sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key
              path env =
            sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env' := by
          funext i state
          simp only [Semantics.loopStep]
          rw [Term.denote_reads body _ _ _ (Env.extend_same _ fun name mem =>
            agree name (List.mem_append.mpr (.inr (List.mem_append.mpr
              (.inr (List.mem_append.mpr (.inl mem)))))))]
        simp only [Term.denote_loop]
        rw [sem.times_same times fun name mem => agree name (List.mem_append.mpr (.inl mem)),
          Env.all_same initial fun name mem =>
            agree name (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl mem)))),
          step]
        congr 1
        funext state
        exact Term.denote_reads rest path _ _ (Env.extend_same _ fun name mem =>
          agree name (List.mem_append.mpr (.inr (List.mem_append.mpr
            (.inr (List.mem_append.mpr (.inr mem)))))))
    | _, _, .block key number body results rest, env, env', agree => by
        simp only [Term.denote_block]
        rw [Term.denote_reads body _ env env' fun name mem =>
          agree name (List.mem_append.mpr (.inl mem))]
        congr 1
        funext mids
        exact Term.denote_reads rest path _ _ (Env.extend_same mids fun name mem =>
          agree name (List.mem_append.mpr (.inr mem)))
    | _, _, .attempt key w owns inputs body results rest, env, env', agree => by
        simp only [Term.denote_attempt]
        congr 1
        funext n
        rw [Term.denote_reads body path _ _ (Env.extend_same _ fun name mem =>
          agree name (List.mem_append.mpr (.inl mem)))]
        congr 1
        funext mids
        congr 1
        funext _
        exact Term.denote_reads rest path _ _ (Env.extend_same mids fun name mem =>
          agree name (List.mem_append.mpr (.inr mem)))
  /-- The meaning of the arms of a case analysis depends on the environment only at the names
  that they read. -/
  theorem Arms.denote_reads {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads) (path : List Frame) (env env' : Env sem.Val Γ)
      (agree : ∀ name, name ∈ arms.reads → ∀ τ found, env name τ found = env' name τ found)
      (pick : Pick sem.Val payloads) :
      arms.denote sem path env pick = arms.denote sem path env' pick :=
    match Γ, mid, payloads, arms, env, env', agree, pick with
    | _, _, _, .nil, _, _, _, pick => nomatch pick
    | _, _, _, .cons inputs arm rest, env, env', agree, .here v => by
        simp only [Arms.denote_cons]
        exact Term.denote_reads arm path _ _ (Env.extend_same _ fun name mem =>
          agree name (List.mem_append.mpr (.inl mem)))
    | _, _, _, .cons inputs arm rest, env, env', agree, .there pick => by
        simp only [Arms.denote_cons]
        exact Arms.denote_reads rest path env env' (fun name mem =>
          agree name (List.mem_append.mpr (.inr mem))) pick
end

end

end Zkc.Core

module

public import Zkc.Core.Program.Stepped
public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
The meaning of the term in steps, for any semantics.

What an instruction runs has a meaning of its own: `Stepped.Instr.denote sem key i` is the process
of what the instruction at the key runs, returning the values that it binds, once per kind of
instruction, and none of its clauses mentions a continuation. A step runs its instruction, binds
what it returns, and goes on: that clause of `Stepped.Term.denote` is the one place where "the rest"
appears. Three kinds of instruction return what their own process returns only after a last step:
a guard returns no value (`.done .nil`) when its condition holds, a loop turns its final state into
the values that it binds, and an attempt ends its body (`settle`) before it returns what the body
returned.

The meaning is used through its equations, each by `rfl` or by one case on a pick here: of a term
(`Stepped.Term.denote_ret`, `Stepped.Term.denote_step`), of each kind of instruction
(`Stepped.Instr.denote_op`, `_guard`, `_choose`, `_cases`, `_loop`, `_block`, `_attempt`) and of
arms (`Stepped.Arms.denote_nil`, `Stepped.Arms.denote_cons`). No proof outside this file unfolds
the mutual recursion. The translations keep the meaning (`Term.denote_toStepped`,
`Stepped.Term.denote_toTerm`).

The meaning of a prefix is in continuation-passing form (`Prefix.denote`: its steps, then what to
do in the environment that they end in); a prefix followed by a term means the prefix, then the
term (`Prefix.denote_fill`), two prefixes mean the first, then the second (`Prefix.denote_append`),
and the meaning of a prefix is a process of its own, of the environment that it ends in
(`Prefix.run`, `Prefix.denote_eq_run`), so that a prefix followed by a term is the prefix's process,
then the term (`Prefix.denote_fill_run`).
-/

namespace Zkc.Core

/-! ## The meaning -/

mutual
  /-- The process of a term in steps. -/
  def Stepped.Term.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Stepped.Term D Γ outs → List Frame → Env sem.Val Γ →
        Process sem.S sem.H (HList sem.Val outs)
    | _, _, .ret exit, _, env => .done (env.all exit)
    | _, _, .step key i results rest, path, env =>
        (Stepped.Instr.denote sem key i path env).bind fun values =>
          rest.denote sem path (env.extend results values)
  /-- The process of what an instruction at a key runs: the values that it binds. -/
  def Stepped.Instr.denote {D : Dialect} (sem : Semantics D) (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Stepped.Instr D Γ mid → List Frame → Env sem.Val Γ →
        Process sem.S sem.H (HList sem.Val mid)
    | _, _, .op o operands, path, env => sem.op key o path (env.all operands)
    | _, _, .guard w c ok why, path, env =>
        bif sem.holds ok (env.get c) then .done .nil else .halt (sem.stop w why ⟨path, key⟩)
    | _, _, .choose _ c ok _ onTrue onFalse, path, env =>
        bif sem.holds ok (env.get c) then onTrue.denote sem path env
        else onFalse.denote sem path env
    | _, _, .cases _ x ok _ arms, path, env => arms.denote sem path env (sem.pick ok (env.get x))
    | _, _, .loop (each := each) w times _ initial inputs body, path, env =>
        (Process.iterate (sem.times times env)
          (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
          0 (env.all initial, HList.empties each)).bind fun state =>
          .done (state.1.append (sem.collected times.size state.2))
    | _, _, .block number body, path, env => body.denote sem (path ++ [.iteration key number]) env
    | _, _, .attempt w _ inputs body, path, env =>
        (sem.begin w key path).bind fun n =>
          (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
            (sem.settle w key path).bind fun _ => .done mids
  /-- The process of the region of the alternative that a variant is, its payload bound to the
  name of the region's input. -/
  def Stepped.Arms.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Stepped.Arms D Γ mid payloads → List Frame →
        Env sem.Val Γ → Pick sem.Val payloads → Process sem.S sem.H (HList sem.Val mid)
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        arm.denote sem path (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, env, .there p => rest.denote sem path env p
end

section
variable {D : Dialect} (sem : Semantics D)

/-! ## The equations -/

/-- An exit gives the values of its names. -/
theorem Stepped.Term.denote_ret {Γ : Ctx D.Ty} {outs : List D.Ty} (exit : HList (Var Γ) outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Term.ret exit).denote sem path env = .done (env.all exit) :=
  rfl

/-- **A step is its instruction's process, then the rest on what it returns**, bound to the names
of the step. -/
theorem Stepped.Term.denote_step {Γ : Ctx D.Ty} {outs mid : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) (results : Names mid)
    (rest : Stepped.Term D (Γ.extend results) outs) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Term.step key i results rest).denote sem path env =
      (i.denote sem key path env).bind fun values =>
        rest.denote sem path (env.extend results values) :=
  rfl

/-- An operation runs the semantics' operation at its key on the values of its operands. -/
theorem Stepped.Instr.denote_op {Γ : Ctx D.Ty} {ins res : List D.Ty} (key : Key) (o : D.Op ins res)
    (operands : HList (Var Γ) ins) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.op o operands).denote sem key path env = sem.op key o path (env.all operands) :=
  rfl

/-- A guard returns no value when its condition holds, and stops at its occurrence when it does
not. -/
theorem Stepped.Instr.denote_guard {Γ : Ctx D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (c : Var Γ t)
    (ok : D.Condition w t) (why : Reason) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.guard w c ok why).denote sem key path env =
      bif sem.holds ok (env.get c) then .done .nil else .halt (sem.stop w why ⟨path, key⟩) :=
  rfl

/-- A choice runs the region that its condition chooses. -/
theorem Stepped.Instr.denote_choose {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (onTrue onFalse : Stepped.Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.choose w c ok gives onTrue onFalse).denote sem key path env =
      bif sem.holds ok (env.get c) then onTrue.denote sem path env
      else onFalse.denote sem path env :=
  rfl

/-- A case analysis runs its arms at the alternative that its subject is. -/
theorem Stepped.Instr.denote_cases {Γ : Ctx D.Ty} {mid payloads : List D.Ty} {t : D.Ty} (key : Key)
    (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Stepped.Arms D Γ mid payloads)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.cases w x ok gives arms).denote sem key path env =
      arms.denote sem path env (sem.pick ok (env.get x)) :=
  rfl

/-- A loop iterates its body, from its initial carried values and nothing collected, as often as
its count says, and returns the last carried values and what was collected. -/
theorem Stepped.Instr.denote_loop {Γ : Ctx D.Ty} {carried each : List D.Ty} (key : Key) (w : D.Who)
    (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Stepped.Term D (Γ.extend inputs) (carried ++ each)) (path : List Frame)
    (env : Env sem.Val Γ) :
    (Stepped.Instr.loop w times gives initial inputs body).denote sem key path env =
      (Process.iterate (sem.times times env)
        (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
        0 (env.all initial, HList.empties each)).bind fun state =>
        .done (state.1.append (sem.collected times.size state.2)) :=
  rfl

/-- A block runs its body under its frame. -/
theorem Stepped.Instr.denote_block {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (number : Nat)
    (body : Stepped.Term D Γ mid) (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.block number body).denote sem key path env =
      body.denote sem (path ++ [.iteration key number]) env :=
  rfl

/-- An attempt begins, runs its body with the number of the attempt, ends, and returns what the
body returned. -/
theorem Stepped.Instr.denote_attempt {Γ : Ctx D.Ty} {mid : List D.Ty} (key : Key) (w : D.Who)
    (owns : D.Attempt w) (inputs : Names [D.index w]) (body : Stepped.Term D (Γ.extend inputs) mid)
    (path : List Frame) (env : Env sem.Val Γ) :
    (Stepped.Instr.attempt w owns inputs body).denote sem key path env =
      (sem.begin w key path).bind fun n =>
        (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
          (sem.settle w key path).bind fun _ => .done mids :=
  rfl

/-- A case analysis without an alternative has no variant to run on: what its arms run at a pick
is any process. -/
theorem Stepped.Arms.denote_nil {Γ : Ctx D.Ty} {mid : List D.Ty} (path : List Frame)
    (env : Env sem.Val Γ) (pick : Pick sem.Val []) (p : Process sem.S sem.H (HList sem.Val mid)) :
    (Stepped.Arms.nil : Stepped.Arms D Γ mid []).denote sem path env pick = p :=
  nomatch pick

/-- The arms of a case analysis run the first arm, on its payload, at the first alternative, and
the other arms at another. -/
theorem Stepped.Arms.denote_cons {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Stepped.Term D (Γ.extend inputs) mid)
    (rest : Stepped.Arms D Γ mid payloads) (path : List Frame) (env : Env sem.Val Γ)
    (pick : Pick sem.Val (payload :: payloads)) :
    (Stepped.Arms.cons inputs arm rest).denote sem path env pick =
      match pick with
      | .here v => arm.denote sem path (env.extend inputs (.cons v .nil))
      | .there p => rest.denote sem path env p := by
  cases pick <;> rfl

/-! ## The translations keep the meaning -/

mutual
  /-- **A term in steps means what the term means.** -/
  theorem Term.denote_toStepped : ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
      (path : List Frame) (env : Env sem.Val Γ),
      t.toStepped.denote sem path env = t.denote sem path env
    | _, _, .ret _, _, _ => rfl
    | _, _, .op _ _ _ _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_op, Term.denote,
          Term.denote_toStepped rest]
    | _, _, .guard _ _ c ok _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_guard,
          Term.denote]
        cases sem.holds ok (env.get c) with
        | false => rfl
        | true => exact Term.denote_toStepped rest path env
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_choose,
          Term.denote, Term.denote_toStepped onTrue, Term.denote_toStepped onFalse,
          Term.denote_toStepped rest]
    | _, _, .cases _ _ _ _ _ arms _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_cases,
          Term.denote, Arms.denote_toStepped arms, Term.denote_toStepped rest]
    | _, _, .loop _ _ _ _ _ _ body _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_loop,
          Term.denote, Process.bind_assoc, Process.bind, Term.denote_toStepped body,
          Term.denote_toStepped rest]
    | _, _, .block _ _ body _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_block,
          Term.denote, Term.denote_toStepped body, Term.denote_toStepped rest]
    | _, _, .attempt _ _ _ _ body _ rest, path, env => by
        simp only [Term.toStepped, Stepped.Term.denote_step, Stepped.Instr.denote_attempt,
          Term.denote, Process.bind_assoc, Process.bind, Term.denote_toStepped body,
          Term.denote_toStepped rest]
  /-- Arms in steps mean what the arms mean. -/
  theorem Arms.denote_toStepped : ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads) (path : List Frame) (env : Env sem.Val Γ)
      (pick : Pick sem.Val payloads),
      arms.toStepped.denote sem path env pick = arms.denote sem path env pick
    | _, _, _, .nil, _, _, pick => nomatch pick
    | _, _, _, .cons _ arm _, path, env, .here _ => by
        simp only [Arms.toStepped, Stepped.Arms.denote_cons, Arms.denote, Term.denote_toStepped arm]
    | _, _, _, .cons _ _ rest, path, env, .there _ => by
        simp only [Arms.toStepped, Stepped.Arms.denote_cons, Arms.denote,
          Arms.denote_toStepped rest]
end

/-- **A term in steps, as a term, means what it means.** -/
theorem Stepped.Term.denote_toTerm {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Stepped.Term D Γ outs)
    (path : List Frame) (env : Env sem.Val Γ) :
    t.toTerm.denote sem path env = t.denote sem path env := by
  conv => rhs; rw [← Stepped.Term.toTerm_toStepped t]
  exact (Term.denote_toStepped sem t.toTerm path env).symm

/-! ## The meaning of a prefix -/

/-- The meaning of a prefix, in continuation-passing form: its steps, then `k` in the environment
that they end in. -/
def Prefix.denote {A : Type} : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → List Frame → Env sem.Val Γ →
    (Env sem.Val Δ → Process sem.S sem.H A) → Process sem.S sem.H A
  | _, _, .nil, _, env, k => k env
  | _, _, .step key i results rest, path, env, k =>
      (i.denote sem key path env).bind fun values =>
        rest.denote path (env.extend results values) k

/-- **A prefix followed by a term means the prefix, then the term.** -/
theorem Prefix.denote_fill {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (t : Stepped.Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ) :
    (p.fill t).denote sem path env = p.denote sem path env fun env' => t.denote sem path env' := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.fill, Stepped.Term.denote_step, Prefix.denote]
      congr 1
      funext values
      exact ih _ _

/-- Two prefixes, one after the other, mean the first, then the second. -/
theorem Prefix.denote_append {A : Type} {Γ Δ Θ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (q : Prefix D Δ Θ) (path : List Frame) (env : Env sem.Val Γ)
    (k : Env sem.Val Θ → Process sem.S sem.H A) :
    (p.append q).denote sem path env k =
      p.denote sem path env fun env' => q.denote sem path env' k := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.append, Prefix.denote]
      congr 1
      funext values
      exact ih _ _

/-- The process of a prefix on its own: the environment that it ends in. -/
def Prefix.run {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame) (env : Env sem.Val Γ) :
    Process sem.S sem.H (Env sem.Val Δ) :=
  p.denote sem path env .done

/-- The meaning of a prefix with any continuation is its process, then the continuation. -/
theorem Prefix.denote_eq_run {A : Type} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame)
    (env : Env sem.Val Γ) (k : Env sem.Val Δ → Process sem.S sem.H A) :
    p.denote sem path env k = (p.run sem path env).bind k := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.run, Prefix.denote] at ih ⊢
      rw [Process.bind_assoc]
      congr 1
      funext values
      exact ih _ _

/-- **A prefix followed by a term is the prefix's process, then the term** on the environment
that the prefix ends in. -/
theorem Prefix.denote_fill_run {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (t : Stepped.Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ) :
    (p.fill t).denote sem path env = (p.run sem path env).bind fun env' => t.denote sem path env' :=
  (p.denote_fill sem t path env).trans (p.denote_eq_run sem path env _)

end

end Zkc.Core

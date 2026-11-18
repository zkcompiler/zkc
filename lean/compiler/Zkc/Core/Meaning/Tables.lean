module

public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops

@[expose] public section

/-!
A term of a function against tables of callees.

A function that calls a replaced function is the same term run against another table of
callees. On valid values in scope, a term of a function returns valid values against callees
that keep validity (`Term.denote_valid`), and it means the same against two tables that agree on
valid inputs when one of them keeps validity (`Term.denote_tables`): every call is on valid
values, where the two tables agree. Neither needs the check of facts. One more name, or the
names of a binding, bound to valid values keep every value in scope valid (`Env.insert_valid`,
`Env.extend_valid`).
-/
namespace Zkc.Core

/-! ## A function against two tables of callees -/

section
variable {V : Vocabulary} {M : Model V}

/-- One more name bound to a valid value keeps every value in scope valid. -/
theorem Env.insert_valid {Γ : Ctx V.Ty} {env : Env M.Val Γ}
    (valid : ∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) (bound : Name) {τ : V.Ty} (v : M.Val τ)
    (valid' : M.Valid τ v) :
    ∀ σ (x : Var (Γ.insert bound τ) σ), M.Valid σ ((env.insert bound v).get x) :=
  Env.insert_preserves valid bound v valid'

/-- The names of a binding bound to valid values keep every value in scope valid. -/
theorem Env.extend_valid : ∀ {Γ : Ctx V.Ty} {env : Env M.Val Γ},
    (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
    ∀ {types : List V.Ty} (bound : Names types) (vs : HList M.Val types), vs.All M.Valid →
      ∀ τ (x : Var (Γ.extend bound) τ), M.Valid τ ((env.extend bound vs).get x) :=
  by exact @Env.extend_preserves _ _ M.Valid

/-- What a local process returns has a property when every value that it returns as `.done`
has it. -/
theorem Local.every_of_done {A : Type} {P : A → Prop} :
    ∀ {p : Local A}, (∀ a, p = .done a → P a) → p.Every (fun _ _ => True) P (fun _ => True)
  | .done a, returns => returns a rfl
  | .halt _, _ => trivial
  | .call op _, _ => nomatch op

/-- A local process followed by two continuations that are the same on every value that it
returns is one process. -/
theorem Local.bind_congr {A B : Type} {P : A → Prop} :
    ∀ {p : Local A} {f g : A → Local B}, p.Every (fun _ _ => True) P (fun _ => True) →
      (∀ a, P a → f a = g a) → p.bind f = p.bind g
  | .done a, _, _, holds, same => same a holds
  | .halt _, _, _, _, _ => rfl
  | .call op _, _, _, _, _ => nomatch op

/-- Bounded iteration of local steps that are the same on every state that satisfies an
invariant which every step keeps is one process. -/
theorem Local.iterate_congr {A : Type} (invariant : Nat → A → Prop)
    {step step' : Nat → A → Local A}
    (same : ∀ i a, invariant i a → step' i a = step i a)
    (kept : ∀ i a, invariant i a →
      (step i a).Every (fun _ _ => True) (invariant (i + 1)) (fun _ => True)) :
    ∀ (n i : Nat) (a : A), invariant i a →
      Process.iterate n step' i a = Process.iterate n step i a
  | 0, _, _, _ => rfl
  | n + 1, i, a, holds => by
      simp only [Process.iterate]
      rw [same i a holds]
      exact Local.bind_congr (kept i a holds) fun a' holds' =>
        Local.iterate_congr invariant same kept n (i + 1) a' holds'

variable {fns : List (FnHeader V)}

/-- A local operation on valid operands means the same against two tables that agree on valid
inputs: only a call reads the table. -/
theorem localOp_tables {table table' : FnTable M fns}
    (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
      table' hdr callee args = table hdr callee args) :
    ∀ {ins res : List V.Ty} (o : LocalOp V fns ins res) (args : HList M.Val ins),
      args.All M.Valid → localOp M table' o args = localOp M table o args
  | _, _, .row .., _, _ => rfl
  | _, _, .owned _, _, _ => rfl
  | _, _, .literal .., _, _ => rfl
  | _, _, .call callee, args, valid => agree _ callee args valid

variable (table : FnTable M fns)

/-- How often a loop of a function runs does not depend on the callees. -/
theorem localSem_times (table' : FnTable M fns) {Γ : Ctx V.Ty} {w : (localDialect V fns).Who}
    (times : Times (localDialect V fns) w Γ) (env : Env M.Val Γ) :
    (localSem M fns table').times times env = (localSem M fns table).times times env := by
  cases times <;> rfl

/-- What a loop of a function collects, as one value, does not depend on the callees. -/
theorem localSem_collected (table' : FnTable M fns) (size : Option Nat) :
    ∀ {each : List V.Ty} (collected : HList (fun a => List (M.Val a)) each),
      (localSem M fns table').collected size collected =
        (localSem M fns table).collected size collected
  | [], .nil => rfl
  | a :: _, .cons values rest =>
      congrArg (HList.cons ((localSem M fns table).collect size a values.reverse))
        (localSem_collected table' size rest)

/-- The state of a loop of a function is valid: its carried values, and what it collected,
as many of each type as iterations. -/
def LoopValid {carried each : List V.Ty} (i : Nat)
    (state : (localSem M fns table).LoopState carried each) : Prop :=
  state.1.All M.Valid ∧ CollectedOK (localSem M fns table) (ValidDyn M) state.2 i

mutual
  /-- **A term of a function returns valid values** on valid values in scope, against callees
  that keep validity. Every value that it binds is valid: no operation, choice, case analysis or
  loop of a function gives an invalid value from valid ones. -/
  theorem Term.denote_valid (keeps : FnTable.KeepsValidity table) :
      ∀ {Γ : Ctx V.Ty} {outs : List V.Ty} (t : Term (localDialect V fns) Γ outs)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        (t.denote (localSem M fns table) path env).Every (fun _ _ => True)
          (fun outs => outs.All M.Valid) (fun _ => True)
    | _, _, .ret exit, _, _, valid =>
        ((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
          (env_all_valid valid exit)
    | _, _, .op _ o operands results rest, path, env, valid => by
        simp only [Term.denote_op]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _
          (fun values valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results values valid')) (fun _ h => h)
          (Local.every_of_done fun values ran =>
            localOp_valid table keeps o _ values
              (((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
                (env_all_valid valid operands)) ran)
    | _, _, .guard .., path, env, valid => by
        simp only [Term.denote_guard]
        exact cond_every _ (Term.denote_valid keeps _ path env valid) trivial
    | _, _, .choose _ _ _ _ _ onTrue onFalse results rest, path, env, valid => by
        simp only [Term.denote_choose]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact cond_every _
          (Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
            (Term.denote_valid keeps onTrue path env valid))
          (Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
            (Term.denote_valid keeps onFalse path env valid))
    | _, _, .cases _ _ x ok _ arms results rest, path, env, valid => by
        simp only [Term.denote_cases]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
          (Arms.denote_valid keeps arms path env valid _ (localPick_valid ok _ (valid _ x)))
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, path, env, valid => by
        simp only [Term.denote_loop]
        apply (Process.every_bind _ _ _ _ _).mpr
        have fits : ∀ m, times.size = some m → 0 + (localSem M fns table).times times env = m := by
          intro m sized
          cases times with
          | fixed n =>
              simp only [Times.size, Option.some.injEq] at sized
              subst sized
              exact Nat.zero_add _
          | value => cases sized
        refine Process.every_mono _ _ (fun state (loopValid : LoopValid table _ state) =>
            Term.denote_valid keeps rest path _ (Env.extend_valid valid results _
              ((all_append _ _).mpr ⟨loopValid.1,
                ((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
                  (collected_valid localCollect_valid times.size fits loopValid.2)⟩)))
          (fun _ h => h)
          (Process.every_iterate _ _ _ (LoopValid table) (fun i state stateValid => ?_) _ 0 _
            ⟨((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
                (env_all_valid valid initial), collectedOK_empties each⟩)
        simp only [Semantics.loopStep]
        apply (Process.every_bind _ _ _ _ _).mpr
        refine Process.every_mono _ _ (fun out outValid => ?_) (fun _ h => h)
          (Term.denote_valid keeps body _ _ (Env.extend_valid valid inputs _
            (HList.all_cons.mpr ⟨trivial, stateValid.1⟩)))
        have parts := (all_append _ _).mp
          (by rw [split_append]; exact outValid :
            ((HList.split carried out).1.append (HList.split carried out).2).All M.Valid)
        exact ⟨parts.1, collectedOK_push stateValid.2
          (((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mpr parts.2)⟩
    | _, _, .block _ _ body results rest, path, env, valid => by
        simp only [Term.denote_block]
        apply (Process.every_bind _ _ _ _ _).mpr
        exact Process.every_mono _ _ (fun mids valid' => Term.denote_valid keeps rest path _
            (Env.extend_valid valid results mids valid')) (fun _ h => h)
          (Term.denote_valid keeps body _ env valid)
    | _, _, .attempt _ _ owns _ _ _ _, _, _, _ => nomatch owns
  /-- The arms of a case analysis of a function return valid values on valid values in scope and
  a valid payload, against callees that keep validity. -/
  theorem Arms.denote_valid (keeps : FnTable.KeepsValidity table) :
      ∀ {Γ : Ctx V.Ty} {mid payloads : List V.Ty} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        ∀ pick : Pick M.Val payloads, pick.All M.Valid →
        (arms.denote (localSem M fns table) path env pick).Every (fun _ _ => True)
          (fun outs => outs.All M.Valid) (fun _ => True)
    | _, _, _, .nil, _, _, _, pick, _ => nomatch pick
    | _, _, _, .cons inputs arm _, path, _, valid, .here v, pickValid =>
        Term.denote_valid keeps arm path _ (Env.extend_valid valid inputs (.cons v .nil)
          (HList.all_cons.mpr ⟨pickValid, trivial⟩))
    | _, _, _, .cons _ _ rest, path, env, valid, .there pick, pickValid =>
        Arms.denote_valid keeps rest path env valid pick pickValid
end

variable {table} (table' : FnTable M fns)

mutual
  /-- **A term of a function means the same against two tables of callees that agree on valid
  inputs**, on valid values in scope, when the first table keeps validity: every value that the
  term binds is valid, so every call is on valid values, where the tables agree. -/
  theorem Term.denote_tables (keeps : FnTable.KeepsValidity table)
      (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        table' hdr callee args = table hdr callee args) :
      ∀ {Γ : Ctx V.Ty} {outs : List V.Ty} (t : Term (localDialect V fns) Γ outs)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        t.denote (localSem M fns table') path env = t.denote (localSem M fns table) path env
    | _, _, .ret _, _, _, _ => rfl
    | _, _, .op _ o operands results rest, path, env, valid => by
        have operandsValid :=
          ((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
            (env_all_valid valid operands)
        simp only [Term.denote_op]
        show (localOp M table' o (env.all operands)).bind _ =
          (localOp M table o (env.all operands)).bind _
        rw [localOp_tables agree o _ operandsValid]
        exact Local.bind_congr
          (Local.every_of_done fun values ran =>
            localOp_valid table keeps o _ values operandsValid ran)
          fun values valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results values valid')
    | _, _, .guard _ _ c ok _ rest, path, env, valid => by
        simp only [Term.denote_guard]
        rw [Term.denote_tables keeps agree rest path env valid]
    | _, _, .choose _ _ c ok _ onTrue onFalse results rest, path, env, valid => by
        simp only [Term.denote_choose]
        rw [Term.denote_tables keeps agree onTrue path env valid,
          Term.denote_tables keeps agree onFalse path env valid]
        exact Local.bind_congr
          (cond_every _ (Term.denote_valid table keeps onTrue path env valid)
            (Term.denote_valid table keeps onFalse path env valid))
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .cases _ _ x ok _ arms results rest, path, env, valid => by
        simp only [Term.denote_cases]
        show (arms.denote (localSem M fns table') path env (localPick M ok (env.get x))).bind _ =
          (arms.denote (localSem M fns table) path env (localPick M ok (env.get x))).bind _
        rw [Arms.denote_tables keeps agree arms path env valid _ (localPick_valid ok _ (valid _ x))]
        exact Local.bind_congr
          (Arms.denote_valid table keeps arms path env valid _ (localPick_valid ok _ (valid _ x)))
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .loop (carried := carried) (each := each) key w times _ initial inputs body results
        rest, path, env, valid => by
        simp only [Term.denote_loop]
        have fits : ∀ m, times.size = some m → 0 + (localSem M fns table).times times env = m := by
          intro m sized
          cases times with
          | fixed n =>
              simp only [Times.size, Option.some.injEq] at sized
              subst sized
              exact Nat.zero_add _
          | value => cases sized
        have kept : ∀ i (state : (localSem M fns table).LoopState carried each),
            LoopValid table i state →
            ((localSem M fns table).loopStep w inputs (fun path' env' => body.denote
              (localSem M fns table) path' env') key path env i state).Every (fun _ _ => True)
              (LoopValid table (i + 1)) (fun _ => True) := by
          intro i state stateValid
          simp only [Semantics.loopStep]
          apply (Process.every_bind _ _ _ _ _).mpr
          refine Process.every_mono _ _ (fun out outValid => ?_) (fun _ h => h)
            (Term.denote_valid table keeps body _ _ (Env.extend_valid valid inputs _
              (HList.all_cons.mpr ⟨trivial, stateValid.1⟩)))
          have parts := (all_append _ _).mp
            (by rw [split_append]; exact outValid :
              ((HList.split carried out).1.append (HList.split carried out).2).All M.Valid)
          exact ⟨parts.1, collectedOK_push stateValid.2
            (((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mpr parts.2)⟩
        have initialValid : LoopValid table 0 (env.all initial, HList.empties each) :=
          ⟨((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
              (env_all_valid valid initial), collectedOK_empties each⟩
        have iterated := Local.iterate_congr (LoopValid table)
          (step' := (localSem M fns table').loopStep w inputs (fun path' env' => body.denote
            (localSem M fns table') path' env') key path env)
          (fun i state stateValid => by
            simp only [Semantics.loopStep]
            rw [Term.denote_tables keeps agree body _ _ (Env.extend_valid valid inputs _
              (HList.all_cons.mpr ⟨trivial, stateValid.1⟩))])
          kept ((localSem M fns table).times times env) 0 _ initialValid
        rw [localSem_times table table' times env, iterated]
        refine Local.bind_congr
          (Process.every_iterate _ _ _ (LoopValid table) kept _ 0 _ initialValid)
          fun state loopValid => ?_
        rw [localSem_collected table table' times.size state.2]
        exact Term.denote_tables keeps agree rest path _
          (Env.extend_valid valid results _ ((all_append _ _).mpr ⟨loopValid.1,
            ((localSem M fns table).dyns_valid_iff (Valid := ValidDyn M) _).mp
              (collected_valid localCollect_valid times.size fits loopValid.2)⟩))
    | _, _, .block _ _ body results rest, path, env, valid => by
        simp only [Term.denote_block]
        rw [Term.denote_tables keeps agree body _ env valid]
        exact Local.bind_congr (Term.denote_valid table keeps body _ env valid)
          fun mids valid' => Term.denote_tables keeps agree rest path _
            (Env.extend_valid valid results mids valid')
    | _, _, .attempt _ _ owns _ _ _ _, _, _, _ => nomatch owns
  /-- The arms of a case analysis of a function mean the same against two tables of callees that
  agree on valid inputs, on valid values in scope and a valid payload, when the first table keeps
  validity. -/
  theorem Arms.denote_tables (keeps : FnTable.KeepsValidity table)
      (agree : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        table' hdr callee args = table hdr callee args) :
      ∀ {Γ : Ctx V.Ty} {mid payloads : List V.Ty} (arms : Arms (localDialect V fns) Γ mid payloads)
        (path : List Frame) (env : Env M.Val Γ), (∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) →
        ∀ pick : Pick M.Val payloads, pick.All M.Valid →
        arms.denote (localSem M fns table') path env pick =
          arms.denote (localSem M fns table) path env pick
    | _, _, _, .nil, _, _, _, pick, _ => nomatch pick
    | _, _, _, .cons inputs arm _, path, _, valid, .here v, pickValid =>
        Term.denote_tables keeps agree arm path _ (Env.extend_valid valid inputs (.cons v .nil)
          (HList.all_cons.mpr ⟨pickValid, trivial⟩))
    | _, _, _, .cons _ _ rest, path, env, valid, .there pick, pickValid =>
        Arms.denote_tables keeps agree rest path env valid pick pickValid
end

end


end Zkc.Core

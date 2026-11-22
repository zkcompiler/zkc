module

public import ZkcFormal.Written.Source
public import ZkcFormal.Written.PureRows

@[expose] public section
set_option autoImplicit false

namespace ZkcFormal.Written
open Zkc.Core

variable {D : Dialect} {sem : Semantics D} {Γ : Ctx D.Ty} {mid outs : List D.Ty}
    {key : Key} {i : Instr D Γ mid} {names : Names mid} {rest : Term D (Γ.extend names) outs}
    {path : List Frame} {env : Env sem.Val Γ}
    {trace : List ((op : sem.S.Op) × sem.S.Reply op)} {Q : Prop}

/-- Reduce a projected instruction at the syntax level. Transporting the complete
predicate by this equality avoids comparing two open continuations by executing them. -/
theorem returnsTerm {source exposed : Term D Γ outs} (eq : source = exposed)
    (run : Returns (exposed.denote sem path env) trace ↔ Q) :
    Returns (source.denote sem path env) trace ↔ Q := eq.symm ▸ run

theorem afterReturn (exit : HList (Var Γ) outs) (env : Env sem.Val Γ) (path : List Frame) :
    Returns ((Term.ret exit).denote sem path env) [] := by
  rw [Term.denote_ret]
  exact returns_done _

theorem afterReturnIff (exit : HList (Var Γ) outs) (env : Env sem.Val Γ) (path : List Frame) :
    Returns ((Term.ret exit).denote sem path env) [] ↔ True := iff_true_intro (afterReturn ..)

/-- Consume one pure instruction. Its result is explicit so later instructions can reuse
the value without re-evaluating its producing instruction or traversing an old environment. -/
theorem afterValue (values : HList sem.Val mid) (step : i.denote sem key path env = .done values)
    (tail : Returns (rest.denote sem path (env.extend names values)) trace ↔ Q) :
    Returns ((Term.step key i names rest).denote sem path env) trace ↔ Q := by
  rw [returns_iff_interpret, Term.interpret_step, step]
  exact (returns_iff_interpret _ trace).symm.trans tail

/-- Consume exactly the operation and typed reply at the front of the recorded execution. -/
theorem afterReply (op : sem.S.Op) (reply : sem.S.Reply op) (bindValue : sem.S.Reply op → HList sem.Val mid)
    (step : i.denote sem key path env = .call op (fun x => .done (bindValue x)))
    (tail : Returns (rest.denote sem path (env.extend names (bindValue reply))) trace ↔ Q) :
    Returns ((Term.step key i names rest).denote sem path env) (⟨op,reply⟩ :: trace) ↔ Q := by
  rw [Term.denote_step, step]
  exact (@returns_call sem.S sem.H _ op (fun x => rest.denote sem path (env.extend names (bindValue x))) reply trace).trans tail

/-- A guard owned by this role tests its operand in the current environment and
continues with the projection of the source suffix. -/
theorem projectedGuard {V : Vocabulary} {hs : Headers V} {r : Role} {Γ : Ctx (LTy V)}
    {outs : List (LTy V)} {key : Key} {ps : List Role} {t : LTy V} {c : Var Γ t}
    {ok : (protocolDialect V hs).Condition ps t} {why : Reason}
    {rest : Term (protocolDialect V hs) Γ outs} {sem : Semantics (roleDialect V hs r)}
    {path : List Frame} {env : Env sem.Val Γ} {trace} {Q : Prop}
    (member : r ∈ ps) (test : Bool)
    (condition : sem.holds (w := ps) (t := t) ⟨ok.1, ok.2.1 r member, member⟩ (env.get c) = test)
    (tail : Returns ((project r rest).denote sem path env) trace ↔ Q) :
    Returns ((project r (Term.guard key ps c ok why rest)).denote sem path env) trace ↔ (test = true ∧ Q) := by
  rw [project.eq_3, dite_eq_left member, Term.denote_guard, condition]
  cases test <;> simp [tail]

/-- Projection erases another role's guard, even when its test reads a private operand. -/
theorem projectedGuardElsewhere {V : Vocabulary} {hs : Headers V} {r : Role} {Γ : Ctx (LTy V)}
    {outs : List (LTy V)} {key : Key} {ps : List Role} {t : LTy V} {c : Var Γ t}
    {ok : (protocolDialect V hs).Condition ps t} {why : Reason}
    {rest : Term (protocolDialect V hs) Γ outs} {sem : Semantics (roleDialect V hs r)}
    {path : List Frame} {env : Env sem.Val Γ} {trace} {Q : Prop}
    (away : r ∉ ps) (tail : Returns ((project r rest).denote sem path env) trace ↔ Q) :
    Returns ((project r (Term.guard key ps c ok why rest)).denote sem path env) trace ↔ Q := by
  rwa [project.eq_3, dite_eq_right away]

/-- A terminal decision is the special case with a returning continuation. -/
theorem afterDecision (test : Bool) (why : sem.H) (values : HList sem.Val mid)
    (step : i.denote sem key path env = (bif test then .done values else .halt why))
    (tail : Returns (rest.denote sem path (env.extend names values)) []) :
    Returns ((Term.step key i names rest).denote sem path env) [] ↔ require test = some () := by
  rw [Term.denote_step, step]
  cases test <;> simp [require, Process.bind, tail]

end ZkcFormal.Written

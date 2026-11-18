module

public import Zkc.Core.Facts.Loops
public import Zkc.Core.Meaning.Stepped

@[expose] public section

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
  (B : List (Key × Nat) → Key → Nat → Prop)

/-- An exit reaches no loop. -/
theorem Term.everyLoop_ret {Γ : Ctx D.Ty} {outs : List D.Ty} (exit : HList (Var Γ) outs)
    (path : List Frame) (blocks : List (Key × Nat)) (env : Env sem.Val Γ) :
    (Term.ret exit).EveryLoop sem permitted B path blocks env ↔ True :=
  Iff.rfl

/-- **The loops of a step** are those of its instruction, and those of the rest at every result
that the instruction can return. -/
theorem Term.everyLoop_step {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Instr D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs) (path : List Frame)
    (blocks : List (Key × Nat)) (env : Env sem.Val Γ) :
    (Term.step key i results rest).EveryLoop sem permitted B path blocks env ↔
      Instr.EveryLoop sem permitted B key i path blocks env ∧
        (i.denote sem key path env).Every permitted
          (fun values => rest.EveryLoop sem permitted B path blocks (env.extend results values))
          (fun _ => True) :=
  Iff.rfl

end

end Zkc.Core

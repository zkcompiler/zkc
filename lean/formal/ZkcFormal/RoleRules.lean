module

public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Fold

@[expose] public section
set_option autoImplicit false

/-!
Rules of the program of a role, as equations of processes.

An instruction that computes a function need not be read through the function's body: where
the value of the function on the operands is known, the step is the rest on that value.
-/

namespace Zkc.Core
variable {V : Vocabulary} {M : Model V}

/-- **The rule of a computation by its law.** A step of a role that computes a local operation
whose value on the operands is known is the rest on that value. The body of the operation is
not read. -/
theorem Term.denote_compute_role {hs : Headers V} {r : Role} {fnTable : FnTable M hs.fns}
    {rTable : RTable M hs.protocols} {Γ : Ctx (LTy V)} {outs : List (LTy V)}
    {ins res : List V.Ty} (key : Key) (R : Holders) (o : LocalOp V hs.fns ins res)
    (operands : List (LTy V)) (types : operands.map (·.ty) = ins) (mine : r ∈ R)
    (here : ∀ a, a ∈ operands → r ∈ a.holders) (args : HList (Var Γ) operands)
    (results : Names (res.map fun τ => (⟨τ, R⟩ : LTy V)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs) (path : List Frame)
    (env : Env (RV M r) Γ) (value : HList M.Val res)
    (law : localOp M fnTable o (computeArgs M types (revealAll M here (env.all args))) =
      .done value) :
    (Term.step key (.op (RoleOp.compute R o operands types mine here) args) results rest).denote
        (roleSem M r fnTable rTable) path env =
      rest.denote (roleSem M r fnTable rTable) path
        (env.extend results (hideAll M r (HList.located M R value))) := by
  rw [Term.denote_step]
  show ((liftLocal id (localOp M fnTable o _)).map _).bind _ = _
  rw [law]
  rfl

end Zkc.Core

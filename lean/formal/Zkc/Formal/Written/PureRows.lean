module

public import Zkc.Core.Meaning.Role

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written
open Core

variable {V : Vocabulary} (M : Model V)

/-- The result of any total row in the supplied model, with its complete typed signature. -/
def rowValues {ins outs : List V.Ty} (key : V.RowKey)
    (known : V.row key = some ⟨ins, outs, .pure⟩) (args : HList M.Val ins) : HList M.Val outs :=
  (M.apply key _ known args).get ((M.defined key _ known args).trans (M.total key _ known args rfl))

theorem apply_pure {ins outs : List V.Ty} (key : V.RowKey)
    (known : V.row key = some ⟨ins, outs, .pure⟩) (args : HList M.Val ins) :
    M.apply key _ known args = some (rowValues M key known args) := (Option.some_get _).symm

def firstValue {T : Type} {F : T → Type} {t ts} : HList F (t :: ts) → F t
  | .cons x _ => x

def otherValues {T : Type} {F : T → Type} {t ts} : HList F (t :: ts) → HList F ts
  | .cons _ xs => xs

/-- Expose the known output arity without reducing an abstract model application. -/
def unpackValues {T : Type} {F : T → Type} : (ts : List T) → HList F ts → HList F ts
  | [], _ => .nil
  | _ :: ts, xs => .cons (firstValue xs) (unpackValues ts (otherValues xs))

theorem unpackValues_eq {T : Type} {F : T → Type} {ts} (xs : HList F ts) :
    unpackValues ts xs = xs := by induction xs <;> simp_all [unpackValues, firstValue, otherValues]

theorem pure_instruction {hs : Headers V} {r : Role} {table : FnTable M hs.fns}
    {roles : RTable M hs.protocols} {Γ : Ctx (LTy V)} {key : Key} {owners : Holders}
    {ins outs : List V.Ty} {row : V.RowKey} {known : V.row row = some ⟨ins, outs, .pure⟩}
    {ports : List (LTy V)} {types : ports.map LTy.ty = ins} {canRead here}
    {vs : HList (Var Γ) ports} {path : List Frame} {env : Env (RV M r) Γ} :
    (Instr.op (D := roleDialect V hs r)
      (.compute owners (.row row ⟨ins, outs, .pure⟩ known) ports types canRead here) vs).denote
        (roleSem M r table roles) key path env = .done
      (hideAll M r (HList.located M owners (unpackValues outs (rowValues M row known
        (computeArgs M types (revealAll M here (env.all vs))))))) := by
  rw [unpackValues_eq, Instr.denote_op]
  change (liftLocal id (localOp M table (.row row ⟨ins, outs, .pure⟩ known) _)).map _ = _
  rw [localOp, apply_pure]
  rfl

theorem firstValue_of_apply {ins : List V.Ty} {out : V.Ty} {key : V.RowKey}
    {known : V.row key = some ⟨ins, [out], .pure⟩} {args : HList M.Val ins} {v : M.Val out}
    (law : M.apply key _ known args = some (.cons v .nil)) :
    firstValue (rowValues M key known args) = v := by
  rw [Option.some.inj ((apply_pure M key known args).symm.trans law)]
  rfl

end Zkc.Formal.Written

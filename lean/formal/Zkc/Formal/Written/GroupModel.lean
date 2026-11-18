module

public import Zkc.Formal.Written.Source

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written
open Core
def Matches (key : Standard.RowKey) (row : Zkc.Vocabulary.RowKey) : Prop := key = .inl row
instance (key : Standard.RowKey) (row : Zkc.Vocabulary.RowKey) : Decidable (Matches key row) :=
  Standard.decRowKey key (.inl row)

/-- Replace three rows with their definitions in the chosen group interpretation. All
other operations, carriers, domains and law supports are those of the supplied model. -/
def groupApply (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] (k : Standard.RowKey) (sig : RowSignature Standard.TypeKey Standard.RowKey)
    (ok : Standard.row k = some sig) (args : HList M.Val sig.ins) : Option (HList M.Val sig.outs) :=
  if h : Matches k (.group .scale (.group .g1)) then by
    unfold Matches at h
    subst k
    have eq := Option.some.inj ((show Standard.row (.inl (.group .scale (.group .g1))) = _ from rfl).symm.trans ok)
    subst sig
    match args with | .cons p (.cons x .nil) => exact some (.cons (ops.scale p x) .nil)
  else if h : Matches k (.group .add (.group .g1)) then by
    unfold Matches at h
    subst k
    have eq := Option.some.inj ((show Standard.row (.inl (.group .add (.group .g1))) = _ from rfl).symm.trans ok)
    subst sig
    match args with | .cons p (.cons q .nil) => exact some (.cons (ops.add p q) .nil)
  else if h : Matches k (.group .equal (.group .g1)) then by
    unfold Matches at h
    subst k
    have eq := Option.some.inj ((show Standard.row (.inl (.group .equal (.group .g1))) = _ from rfl).symm.trans ok)
    subst sig
    match args with | .cons p (.cons q .nil) => exact some (.cons (@decide ((p : M.Val pointTy) = q) ((inferInstance : DecidableEq (M.Val pointTy)) p q)) .nil)
  else M.apply k sig ok args

theorem groupApply_eq (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] (rows : GroupRows M ops) : groupApply M ops = M.apply := by
  funext k sig ok args
  unfold groupApply
  split <;> rename_i h
  · unfold Matches at h
    subst k
    cases ok
    match args with | .cons p (.cons q .nil) => exact (rows.scale p q).symm
  · split <;> rename_i h
    · unfold Matches at h
      subst k
      cases ok
      match args with | .cons p (.cons q .nil) => exact (rows.add p q).symm
    · split <;> rename_i h
      · unfold Matches at h
        subst k
        cases ok
        match args with | .cons p (.cons q .nil) => exact (rows.equal p q).symm
      · rfl

private theorem replaceApply_eq (M : Model Standard) (f : (k : Standard.RowKey) →
    (sig : RowSignature Standard.TypeKey Standard.RowKey) → Standard.row k = some sig →
    HList M.Val sig.ins → Option (HList M.Val sig.outs)) (h : f = M.apply) :
    ({ M with apply := f, defined := by rw [h]; exact M.defined,
              decides := by rw [h]; exact M.decides, keeps := by rw [h]; exact M.keeps } : Model Standard) = M := by
  subst f
  rfl

/-- Extensionally equal to the original Core model. Presenting its known rows in this form
allows the kernel to reduce an emitted role without unfolding arbitrary model operations. -/
def groupModel (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] (rows : GroupRows M ops) : Model Standard :=
  { M with
    apply := groupApply M ops
    defined := by rw [groupApply_eq M ops rows]; exact M.defined
    decides := by rw [groupApply_eq M ops rows]; exact M.decides
    keeps := by rw [groupApply_eq M ops rows]; exact M.keeps }

theorem groupModel_eq (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] (rows : GroupRows M ops) : groupModel M ops rows = M := by
  exact replaceApply_eq M _ (groupApply_eq M ops rows)

end Zkc.Formal.Written

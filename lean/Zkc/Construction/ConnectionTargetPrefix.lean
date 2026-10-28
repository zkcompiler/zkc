module

public import Zkc.Construction.DomainView
public import Zkc.Source.Structured.DomainModels

@[expose] public section

/-! A finite flat target prefix. Appending a continuation replaces only the
terminal empty block; it does not wrap the prefix in another sequence or add
checkpoints at an application boundary. Entries reference existing views. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionTargetPrefix
open Zkc.Source.Structured
abbrev TargetBlock := (model : DomainModel) → Domain.View.Block model.toCarriers

inductive Prefix where
  | empty
  | step (view : TargetBlock) (rest : Prefix)

def Prefix.plug (spine : Prefix) (suffix : TargetBlock) : TargetBlock :=
  match spine with
  | .empty => suffix
  | .step view rest => fun model => Domain.View.sequence (view model) (rest.plug suffix model)

def Prefix.block (spine : Prefix) : TargetBlock :=
  spine.plug (fun _ => Domain.View.empty)

/-- The exact flat instruction/checkpoint schedule, for every continuation
and environment. This equation concerns only existing target combinators. -/
theorem Prefix.plug_eq_bind (spine : Prefix) (suffix : TargetBlock) (model : Zkc.Source.Structured.DomainModel)
    (environment : Domain.Environment model.toCarriers) :
    spine.plug suffix model environment =
      (spine.block model environment).bind (suffix model) := by
  induction spine generalizing environment with
  | empty => rfl
  | step view rest ih =>
    change Domain.View.sequence (view model) (rest.plug suffix model) environment =
      (Domain.View.sequence (view model) (rest.block model) environment).bind (suffix model)
    unfold Domain.View.sequence
    apply congrArg (fun next : Unit → PIR.Process (Domain.effects model.toCarriers)
      (Domain.Environment model.toCarriers) =>
        PIR.Process.call (I := Domain.effects model.toCarriers) (.checkpoint environment) next)
    funext ignored
    rw [PIR.Process.bind_assoc]
    apply congrArg (PIR.Process.bind (view model environment))
    funext reached
    apply congrArg (fun next : Unit → PIR.Process (Domain.effects model.toCarriers)
      (Domain.Environment model.toCarriers) =>
        PIR.Process.call (I := Domain.effects model.toCarriers) (.checkpoint reached) next)
    funext ignored
    exact ih reached

end Zkc.Construction.ConnectionTargetPrefix

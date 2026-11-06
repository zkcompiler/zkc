module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.DomainEvaluation

@[expose] public section

/-! A Math branch passes its actual captures to exactly one callback. Its
source meaning supplies this fact even though general dialect operations can
inspect callback processes. Both callback bodies stay in the typed source. -/
namespace Zkc.Source.Structured

variable {model : DomainModel} {table : MeaningsOn model.toCarriers}
    {inputs outputs : List Ty} {condition : Bool} {captures : Values model.Value inputs}
    {yes no : Region dialect inputs outputs}

theorem branchAt (selected : Bool) (choice : condition = selected) {target}
    (arm : Region.Derivation (meaningOn model table) (fun op => .call op .done)
      (if selected then yes else no) captures.get target) :
    (meaningOn model table).OperationLaw (fun op => .call op .done)
      (.branch inputs outputs) (.cons condition captures)
      ((Regions.cons yes (.cons no .nil)).denote (meaningOn model table)) target := by
  apply RegionMeaning.OperationLaw.identity
  subst condition
  cases selected <;> exact arm.sound_identity

theorem branchAlternatives
    {onTrue : condition = true → PIR.Process closedInterface (Values model.Value outputs)}
    {onFalse : condition = false → PIR.Process closedInterface (Values model.Value outputs)}
    (left : ∀ selected, Region.Derivation (meaningOn model table) (fun op => .call op .done)
      yes captures.get (onTrue selected))
    (right : ∀ selected, Region.Derivation (meaningOn model table) (fun op => .call op .done)
      no captures.get (onFalse selected)) :
    (meaningOn model table).OperationLaw (fun op => .call op .done)
      (.branch inputs outputs) (.cons condition captures)
      ((Regions.cons yes (.cons no .nil)).denote (meaningOn model table))
      (if h : condition = true then onTrue h else onFalse (Bool.eq_false_iff.mpr h)) := by
  cases condition
  · exact branchAt false rfl (right rfl)
  · exact branchAt true rfl (left rfl)

end Zkc.Source.Structured

module

public import Zkc.Source.Structured.OracleValueObservations
public import Zkc.Source.Structured.DomainComponent

@[expose] public section

/-! Component calculations at the protocol value boundary. Calls enter retained Math bodies
on optional values; structural operations preserve deferred fields. Concrete demand occurs
only at a strict leaf. Closed Local calls continue to use the existing strict evaluator. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace ProtocolValue

variable {carriers : Carriers}

def embedValues : {types : List Ty} → Values carriers.Value types →
    Values (ProtocolValue carriers) types
  | _, .nil => .nil
  | type :: _, .cons value rest => .cons (ofConcrete type value) (embedValues rest)

def embedComponents : {types : List Ty} → Values (Component carriers.Value) types →
    Values (Component (ProtocolValue carriers)) types
  | _, .nil => .nil
  | type :: _, .cons value rest => .cons (value.map (ofConcrete type)) (embedComponents rest)

def concreteComponents : {types : List Ty} → Values (Component (ProtocolValue carriers)) types →
    Values (Component carriers.Value) types
  | _, .nil => .nil
  | _ :: _, .cons value rest => .cons (value.bind toConcrete) (concreteComponents rest)

@[simp] theorem concreteComponents_embedComponents {types : List Ty}
    (values : Values (Component carriers.Value) types) :
    concreteComponents (embedComponents values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value <;> simp [embedComponents, concreteComponents, toConcrete_ofConcrete, ih]

def materializeComponents {I : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers I) (self : Nat) :
    {types : List Ty} → Values (Component (ProtocolValue carriers)) types →
      PIR.Process I (Values (Component carriers.Value) types)
  | _, .nil => .done .nil
  | _ :: _, .cons none rest =>
    (materializeComponents demand self rest).bind fun values ↦ .done (.cons none values)
  | _ :: _, .cons (some value) rest =>
    (value.materializeWith demand self).bind fun value ↦
      (materializeComponents demand self rest).bind fun values ↦ .done (.cons (some value) values)

@[simp] theorem materializeComponents_embedComponents {I : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers I) (self : Nat) {types : List Ty}
    (values : Values (Component carriers.Value) types) :
    materializeComponents demand self (embedComponents values) = .done values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value <;> simp [embedComponents, materializeComponents, materializeWith_ofConcrete,
      ih, PIR.Process.bind]

end ProtocolValue

namespace ProtocolCalculation
variable {I : PIR.Signature}

abbrev Tables (carriers : Carriers) (I : PIR.Signature) :=
  HelperTable (Component (ProtocolValue carriers)) I

/-- The fallback uses the original component operation, including its differing strict-leaf
absence rules. It does not replace absent values or claim that a partial calculation is total. -/
def strict (model : DomainModel) (demand : OracleDataDemandInterpretation model.toCarriers I)
    (self : Nat) (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (op : Op) (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (noRegions : op.regions = []) :
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) op.results) :=
  let evaluate := fun values ↦
    (Evaluation.componentOperationOn model (.silent _) tables op values
      (by change Values _ op.regions; rw [noRegions]; exact .nil)).bind fun result ↦ .done (ProtocolValue.embedComponents result)
  if (RoleFamily.sequence args).isNone then
    evaluate (ProtocolValue.concreteComponents args)
  else (ProtocolValue.materializeComponents demand self args).bind evaluate

/-- The strict boundary agrees exactly on ordinary operands, including absence and an
empty result tuple. Its missing-operand branch performs no concrete-data demand. -/
theorem strict_embed (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (op : Op)
    (args : Values (Component model.Value) op.arguments) (noRegions : op.regions = []) :
    strict model demand self tables op (ProtocolValue.embedComponents args) noRegions =
      (Evaluation.componentOperationOn model (.silent _) tables op args
        (by change Values _ op.regions; rw [noRegions]; exact .nil)).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  unfold strict
  split <;> simp only [ProtocolValue.concreteComponents_embedComponents,
    ProtocolValue.materializeComponents_embedComponents, PIR.Process.bind]

/-- A finite Math fold enters the retained helper prefix on optional values. Only the
domain's actual descriptor inputs are concretized before admission; state and captures
remain structural values, even when the step ignores a deferred field. -/
def fold (model : DomainModel) (demand : OracleDataDemandInterpretation model.toCarriers I)
    (self : Nat) (helpers : Tables model.toCarriers I) (spec : FoldSpec)
    (args : Values (Component (ProtocolValue model.toCarriers)) spec.arguments) :
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) spec.state) :=
  match RoleFamily.sequence args with
  | none => .done (Values.absent _ spec.state)
  | some _ =>
    let (arguments, rest) := args.split spec.domain.inputs
    let (initial, captures) := rest.split spec.state
    (ProtocolValue.materializeComponents demand self arguments).bind fun arguments ↦
      match RoleFamily.sequence arguments with
      | none => .halt .incomplete
      | some concrete =>
        Finite.admitThen (spec.domain.admit concrete) fun items ↦
          Finite.fold (fun state item ↦
            let callbackArguments :=
              (ProtocolValue.embedComponents item.present).append
                ((ProtocolValue.embedComponents concrete.present).append captures)
            let enabled : PIR.Process I (Option Bool) :=
              if spec.predicate.isEmpty then .done (some true)
              else (invoke helpers spec.predicateHelper callbackArguments).bind
                (fun result ↦ .done ((result.get .here).bind ProtocolValue.toConcrete))
            enabled.bind fun enabled ↦ match enabled with
              | none => .halt .incomplete
              | some false => .done state
              | some true => invoke helpers spec.stepHelper (state.append callbackArguments))
            items initial

def operation (model : DomainModel) (demand : OracleDataDemandInterpretation model.toCarriers I)
    (self : Nat) (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : Tables model.toCarriers I) (op : Op)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments) :
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) op.results) :=
  match op, args with
  | .fold spec, args =>
    if spec.kind = .math then fold model demand self helpers spec args
    else strict model demand self ordinary (.fold spec) args rfl
  | .invoke helper, args =>
    if helper.kind = .math then invoke helpers helper args
    else strict model demand self ordinary (.invoke helper) args rfl
  | .makeProduct identity constructor fields, args =>
    .done (.cons ((RoleFamily.sequence args).map
      (ProtocolValue.product identity constructor fields)) .nil)
  | .getProduct _ _ _ _ field, .cons value .nil =>
    .done (.cons (value.map (fun value ↦ value.project field)) .nil)
  | .select _, .cons condition (.cons yes (.cons no .nil)) =>
    .done (.cons (do
      let condition ← condition >>= ProtocolValue.toConcrete
      let yes ← yes
      let no ← no
      pure (if condition then yes else no)) .nil)
  | .vectorLength _, .cons value .nil =>
    .done (.cons ((value.bind ProtocolValue.observedLength).map
      (ProtocolValue.ofConcrete .index)) .nil)
  | .exec (.vectorLength _), .cons value .nil =>
    match value.bind ProtocolValue.observedLength with
    | none => .halt .incomplete
    | some length => .done (.cons (some (ProtocolValue.ofConcrete .index length)) .nil)
  | op, args =>
    if noRegions : op.regions = [] then strict model demand self ordinary op args noRegions
    else .halt .refused

/-- A Math branch first checks presence of every operand. The Boolean selects a
single callback, whose captures keep their structural Oracle values. -/
def selected (model : DomainModel) {captures outputs : List Ty}
    (args : Values (Component (ProtocolValue model.toCarriers)) (.boolean :: captures))
    (yes no : RegionFunction (Component (ProtocolValue model.toCarriers)) I (captures, outputs)) :
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) outputs) :=
  match RoleFamily.sequence args with
  | none => .done (Values.absent _ outputs)
  | some (.cons condition values) =>
    match condition.toConcrete with
    | none => .halt .refused
    | some flag => (if flag then yes else no) values.present

def regionOperation (model : DomainModel)
    (demand : OracleDataDemandInterpretation model.toCarriers I) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : Tables model.toCarriers I) (op : Op) :
    Values (Component (ProtocolValue model.toCarriers)) op.arguments →
    Values (RegionFunction (Component (ProtocolValue model.toCarriers)) I) op.regions →
    PIR.Process I (Values (Component (ProtocolValue model.toCarriers)) op.results) :=
  match op with
  | .branch _ _ => fun args (.cons yes (.cons no .nil)) => selected model args yes no
  | op => fun args _ => operation model demand self ordinary helpers op args

abbrev meaning (model : DomainModel) (demand : OracleDataDemandInterpretation model.toCarriers I)
    (self : Nat) (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (helpers : Tables model.toCarriers I) : RegionMeaning dialect I where
  Value := Component (ProtocolValue model.toCarriers)
  operation := regionOperation model demand self ordinary helpers

/-- Math helpers capture their already checked prefix, never a caller-supplied meaning.
Entering a helper does not force any optional argument or nested field. -/
def extend (model : DomainModel) (demand : OracleDataDemandInterpretation model.toCarriers I)
    (self : Nat) (ordinary : Evaluation.ComponentTablesOn model.toCarriers I)
    (captured : Tables model.toCarriers I) (definition : CheckedDefinition) : Tables model.toCarriers I :=
  ⟨definition.helper, fun args ↦ definition.body.denote
    (meaning model demand self ordinary captured) args.get⟩ :: captured

end ProtocolCalculation
end Zkc.Source.Structured

module

public import Zkc.Source.Structured.ReferenceLibrary
public import Zkc.Source.Structured.CollectionRepresentation
public import Zkc.Source.Structured.DomainContract

@[expose] public section

/-! Structural reference composition for complete helper calls and ordered
collections. Curried functions describe mathematics in source operand order;
the generic layer owns heterogeneous ABI packing and captures. -/

set_option autoImplicit false
namespace Zkc.Source

@[simp] theorem Values.get_head {T : Type} {Value : T → Type} {ty : T} {types : List T}
    (value : Value ty) (rest : Values Value types) :
    (Values.cons value rest).get .here = value := rfl

@[simp] theorem Values.get_tail {T : Type} {Value : T → Type} {ty head : T}
    {types : List T} (value : Value head) (rest : Values Value types) (position : Var types ty) :
    (Values.cons value rest).get (.there position) = rest.get position := rfl

def Values.Curried {T : Type} (Value : T → Type) : List T → Type → Type
  | [], Result => Result
  | ty :: rest, Result => Value ty → Curried Value rest Result

def Values.curry {T : Type} {Value : T → Type} {Result : Type} :
    (types : List T) → (Values Value types → Result) → Curried Value types Result
  | [], function => function .nil
  | _ :: rest, function => fun value => curry rest (fun values => function (.cons value values))

namespace Structured

/-- An explicit complete dependency law in the caller's actual table. The
association to its body is supplied separately when this proposition is proved. -/
def ReferenceLaw.Realizes {model : DomainModel} {helper : Helper}
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop :=
  ∀ arguments, Structured.invoke table helper arguments = primitiveOutcome (law.reference arguments)

theorem ReferenceLaw.realizes {model : DomainModel} {helper : Helper}
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (premises : ∀ arguments, law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) arguments) :
    law.Realizes (helper := helper)
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) :=
  fun arguments => law.invoke definitions linked associated arguments (premises arguments)

/-- Install a carrier-based law into the existing uniform table using the
proved evaluator bridge. This does not normalize a whole declaration fold. -/
theorem ReferenceLaw.invokeUniform {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] {helper : Helper}
    (law : ReferenceLaw (ringModel F G) helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (arguments : Values (assignment F G) helper.inputs)
    (premises : law.Requires (closedMeanings definitions) arguments) :
    Structured.invoke (closedMeanings definitions) helper arguments =
      primitiveOutcome (law.reference arguments) := by
  rw [closedMeanings_eq_closedMeaningsOn] at premises ⊢
  exact law.invoke definitions linked associated arguments premises

theorem ReferenceLaw.realizesUniform {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] {helper : Helper}
    (law : ReferenceLaw (ringModel F G) helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (premises : ∀ arguments, law.Requires (closedMeanings definitions) arguments) :
    law.Realizes (helper := helper) (closedMeanings definitions) :=
  fun arguments => law.invokeUniform definitions linked associated arguments (premises arguments)

namespace ReferenceLibrary

def forwardDependency (model : DomainModel) {inputs : List Ty} (helper : Helper)
    (arguments : Operands inputs helper.inputs)
    (dependency : ReferenceLaw model helper.inputs helper.outputs) :
    ReferenceLaw model inputs helper.outputs where
  body := (forward model helper arguments dependency.reference).body
  Requires table _ := dependency.Realizes (helper := helper) table
  reference := (forward model helper arguments dependency.reference).reference
  valid table args premise := (forward model helper arguments dependency.reference).valid
    table args (premise _)

/-- Any admitted ordered domain and scalar formula, with every domain input
and heterogeneous capture retained. Admission failures keep their exact stop. -/
def indexedCollection (model : DomainModel) {inputs : List Ty} (spec : CollectSpec)
    (arguments : Operands inputs (spec.domain.inputs ++ spec.captures))
    (shape : Values model.Value inputs → PIR.Outcome Nat)
    (item : Values model.Value inputs → Nat → Values model.Value spec.domain.items)
    (formula : Values model.Value spec.bodyHelper.inputs → model.Value spec.collection.element)
    (absent : spec.predicate.isEmpty = true) :
    ReferenceLaw model inputs [spec.collection.type] where
  body := .letOp (.collect spec) arguments .nil
    (.ret (resultOperands [spec.collection.type] inputs))
  Requires table args :=
    let actual := Operands.eval args.get arguments
    let domain := actual.split.1
    spec.domain.admit domain = Finite.continueWith (shape args)
      (fun length => .returned ((List.range length).map (item args))) ∧
    ∀ selected : Values model.Value spec.domain.items,
      invoke table spec.bodyHelper (selected.append actual) =
      .done (.cons (formula (selected.append actual)) .nil)
  reference args :=
    let actual := Operands.eval args.get arguments
    match shape args with
    | .stopped reason => .stopped reason
    | .returned length => .returned (.cons (spec.collection.pack
        ((List.range length).map fun index => formula ((item args index).append actual))) .nil)
  valid table args premise := by
    let actual := Operands.eval args.get arguments
    have packed := Values.append_split spec.domain.inputs actual
    change (Evaluation.denoteCollect table spec actual).bind _ = _
    cases selectedShape : shape args with
    | stopped reason =>
        have collected := Evaluation.denoteCollect_admission_stop table spec
          actual.split.1 actual.split.2 reason (by
            simpa only [selectedShape, Finite.continueWith] using premise.1)
        rw [packed] at collected
        rw [collected]
        rfl
    | returned length =>
        have collected := Evaluation.denoteCollect_reference table spec
          actual.split.1 actual.split.2 (List.range length) (item args)
          (by simpa only [selectedShape, Finite.continueWith] using premise.1)
          absent (fun index => formula ((item args index).append actual)) (by
            intro index _
            simpa only [packed] using premise.2 (item args index))
        rw [packed] at collected
        rw [collected]
        simp only [PIR.Process.bind, primitiveOutcome]
        exact congrArg PIR.Process.done (eval_resultOperands model args.get _)

end ReferenceLibrary
end Structured
end Zkc.Source

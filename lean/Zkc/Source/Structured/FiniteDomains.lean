module

public import Zkc.Source.Structured.Algebra
public import Zkc.Source.Finite

@[expose] public section

/-! Typed, ordered admission of stored finite-domain constructors. Data arguments
and domain SSA references are distinct environments. Every constructor is checked
once in stored order, including unused results. This logical model does not model
native allocation, executable loop limits or provider custody. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

abbrev DomainValues (carriers : Carriers) (context : List (List Ty)) :=
  Values (fun items => List (Values carriers.Value items)) context

/-- Strict zip concatenates complete item tuples; no shortest-input truncation. -/
def zipDomainRows {carriers : Carriers} : {items : List (List Ty)} →
    DomainValues carriers items → PIR.Outcome (List (Values carriers.Value items.flatten))
  | [], .nil => .stopped .refused
  | [_], .cons rows .nil => .returned (rows.map fun row => row.append .nil)
  | _ :: _ :: _, .cons rows rest =>
      Finite.continueWith (zipDomainRows rest) fun tail =>
        if rows.length = tail.length then
          .returned ((rows.zip tail).map fun pair => pair.1.append pair.2)
        else .stopped .refused

/-- Cartesian enumeration has the last factor varying fastest. All factors have
already passed their own admission, including factors following an empty one. -/
def productDomainRows {carriers : Carriers} : {items : List (List Ty)} →
    DomainValues carriers items → List (Values carriers.Value items.flatten)
  | [], .nil => [.nil]
  | _ :: _, .cons rows rest =>
      rows.flatMap fun row => (productDomainRows rest).map fun tail => row.append tail

def DomainNode.admit {carriers : Carriers} {inputs : List Ty} {context : List (List Ty)}
    (arguments : Values carriers.Value inputs) (domains : DomainValues carriers context) :
    {items : List Ty} → DomainNode inputs context items →
      PIR.Outcome (List (Values carriers.Value items))
  | _, .elements collection container =>
      let values := collection.values (arguments.get container)
      if values.length < indexLimit then .returned (values.map fun value => .cons value .nil)
      else .stopped .exhausted
  | _, .indices collection container =>
      let values := collection.values (arguments.get container)
      if values.length < indexLimit then
        .returned ((List.range values.length).map fun index => .cons index .nil)
      else .stopped .exhausted
  | _, .range lower upper =>
      let lo := arguments.get lower
      let hi := arguments.get upper
      if lo < indexLimit ∧ hi < indexLimit then
        .returned ((List.range' lo (hi - lo)).map fun index => .cons index .nil)
      else .stopped .refused
  | _, .zip _ operands => zipDomainRows (operands.eval domains.get)
  | _, .product items operands =>
      if items.isEmpty then .stopped .refused
      else .returned (productDomainRows (operands.eval domains.get))

def DomainBody.admit {carriers : Carriers} {inputs : List Ty}
    (arguments : Values carriers.Value inputs) : {context : List (List Ty)} → {items : List Ty} →
    DomainBody inputs context items → DomainValues carriers context →
      PIR.Outcome (List (Values carriers.Value items))
  | _, _, .ret value, domains => .returned (domains.get value)
  | _, _, .letNode node next, domains =>
      Finite.continueWith (node.admit arguments domains) fun rows =>
        next.admit arguments (.cons rows domains)

def DomainSpec.admit {carriers : Carriers} (domain : DomainSpec)
    (arguments : Values carriers.Value domain.inputs) :
    PIR.Outcome (List (Values carriers.Value domain.items)) :=
  domain.body.admit arguments .nil

/-- The singleton tuple preserves the selected collection's exact order and bound. -/
theorem DomainSpec.admit_elements {carriers : Carriers} (name : String) (inputs : List Ty)
    (collection : Collection) (container : Var inputs collection.type)
    (arguments : Values carriers.Value inputs) :
    (DomainSpec.elements name inputs collection container).admit arguments =
      if (collection.values (arguments.get container)).length < indexLimit then
        .returned ((collection.values (arguments.get container)).map fun item => .cons item .nil)
      else .stopped .exhausted := by
  simp only [DomainSpec.elements, DomainSpec.admit, DomainBody.admit, DomainNode.admit]
  split <;> rfl

/-- Index enumeration retains the exact selected container and its size check. -/
theorem DomainSpec.admit_indices {carriers : Carriers} (name : String) (inputs : List Ty)
    (collection : Collection) (container : Var inputs collection.type)
    (arguments : Values carriers.Value inputs) :
    (DomainSpec.indices name inputs collection container).admit arguments =
      if (collection.values (arguments.get container)).length < indexLimit then
        .returned ((List.range (collection.values (arguments.get container)).length).map
          fun item => .cons item .nil)
      else .stopped .exhausted := by
  simp only [DomainSpec.indices, DomainSpec.admit, DomainBody.admit, DomainNode.admit]
  split <;> rfl

/-- A failed unused constructor stops the complete domain before its suffix. -/
theorem DomainBody.admit_stop {carriers : Carriers} {inputs items output : List Ty}
    {context : List (List Ty)} (node : DomainNode inputs context items)
    (next : DomainBody inputs (items :: context) output)
    (arguments : Values carriers.Value inputs) (domains : DomainValues carriers context)
    (reason : PIR.Stop) (stopped : node.admit arguments domains = .stopped reason) :
    (DomainBody.letNode node next).admit arguments domains = .stopped reason := by
  simp only [DomainBody.admit, stopped, Finite.continueWith]

end Zkc.Source.Structured

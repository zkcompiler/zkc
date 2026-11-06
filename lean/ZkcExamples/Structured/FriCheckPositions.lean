module

public import ZkcExamples.Structured.FriQueryCall
public import ZkcExamples.Structured.FriValueAssociation
public import Zkc.Source.Structured.OracleReadEffects
public import Zkc.Source.Structured.MarkedPrefix
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback
public meta import ZkcExamples.Structured.FriSourceBodies

@[expose] public section

/-! The first table read in each installed Check iteration. Its position is
looked up in the bound list at the loop ordinal. Preceding source marks and
the entire continuation are retained. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCheckPositions
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding
open OracleProtocol (concrete)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

open Zkc.Source.Structured.Bindings

checked_callback query := protocol3Body at 0

variable {model : DomainModel}

/-- Select the first receiver query from the admitted callback itself. -/
def initialSite : OracleLocation :=
  (queryBody.erase.operations.findSome? fun op ↦ match op with
    | .oracle (.query _ (some 1)) site => some site
    | _ => none).get (by decide +kernel)

def initialRequest (context : ProtocolContext) (source : OracleAnchor) (position : Nat) :
    (OracleProtocol.Interface model).Op :=
  OracleProtocol.tableQuery model (.field extension) none source position 1 1 context.roles initialSite

/-- Everything else carried into the iteration stays free. The position list
and the initial receiver handle occupy their admitted input roles. -/
structure Captures (model : DomainModel) where
  values : Value model (.vector extension)
  layers : Value model layersSort.type
  folds : Value model layersSort.type
  shift : Value model (.field extension)
  size : Value model .index
  coefficients : Value model (.vector extension)
  associate : Value model .boolean
  first : Value model (.vector extension)
  remaining : Value model .index

def iteration (context : ProtocolContext) (cap : Captures model) (xs : List Nat) (ordinal : Nat)
    (source : OracleAnchor) :=
  let inputs : Values (Value model) (.index :: (querySite.spec.state ++ querySite.spec.captures)) :=
    .cons (concrete model .index ordinal) (.cons cap.values (.cons (concrete model initialSort.type source)
      (.cons cap.layers (.cons cap.folds (.cons cap.shift (.cons cap.size (.cons cap.coefficients
        (.cons (concrete model .indices xs) (.cons cap.associate (.cons cap.first (.cons cap.remaining .nil)))))))))))
  queryBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) inputs.get

private theorem lookup (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs)
    (ordinal : Fin xs.length) :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil)) =
        .done (.cons (concrete model .index xs[ordinal.val]) .nil) := by
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper30Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) xs
      (.cons (ty := .index) ordinal.val .nil)).present) = _
  rw [OracleProtocol.owned_present,
    (FriBoundedPositions.lookupLaw model).invokeOn (helper := helper30Helper)
      unit.definitions unit.linked (by exact_body helper30Definition)
      (.cons xs (.cons ordinal.val .nil)) ⟨admitted, ordinal.isLt⟩]
  simp [FriBoundedPositions.lookupLaw,
    primitiveOutcome, PIR.Process.bind]
  rfl

/-- An associated checker compares by ordinal even when sampled positions
repeat. A wrong value stops before any later query or append. -/
def rejectsMismatch (cap : Captures model) (i : Nat)
    {context : ProtocolContext} {source : OracleAnchor} {position : Nat}
    (next : (OracleProtocol.Interface model).Reply (initialRequest context source position) →
      PIR.Process (OracleProtocol.Interface model) (Values (Value model) querySite.spec.state)) : Prop :=
  ∀ (first : List (model.Field extension)) (value : model.Field extension),
    cap.associate = concrete model .boolean true → cap.first = concrete model (.vector extension) first →
    first.length < indexLimit → ∀ inside : i < first.length, value ≠ first[i] →
      OracleProtocol.StopsAfterMarks .reject (next (.cons (concrete model (.field extension) value) .nil))

/-- All other captured values may be arbitrary. Only the initial handle and
the checked position vector determine the first table request. -/
theorem firstRead (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs)
    (ordinal : Fin xs.length) (source : OracleAnchor)
    (cap : Captures model) :
    OracleProtocol.AtMarkedCall (initialRequest context source xs[ordinal.val])
      (rejectsMismatch (context := context) (source := source) (position := xs[ordinal.val]) cap ordinal.val)
      (iteration context cap xs ordinal.val source) := by
  unfold iteration
  apply OracleProtocol.AtMarkedCall.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [3, 1]
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil))
    rw [receiver, lookup xs admitted ordinal]
  apply OracleProtocol.AtMarkedCall.mark
  apply OracleProtocol.AtMarkedCall.found
  intro first value enabled vector size inside mismatch
  apply OracleProtocol.StopsAfterMarks.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [2, 1]
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper31Helper
      (.cons cap.associate (.cons cap.first (.cons (concrete model .index ordinal.val)
        (.cons (concrete model (.field extension) value) .nil))))
    rw [receiver, enabled, vector, FriValueAssociation.installed true first ordinal.val value (fun _ ↦ ⟨size, inside⟩)]
    simp only [List.getElem?_eq_getElem inside, Option.any_some, mismatch, decide_false, ↓reduceIte]
  apply OracleProtocol.StopsAfterMarks.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [2, 1]
    change ((Participant.guard (services := services) (Value := model.Value) 1 (context.roles 1)
      ((concrete model .boolean false).bind ProtocolValue.toConcrete)).interpret
        (OracleProtocol.actions model)).bind _
    rw [receiver]
    simp [OracleProtocol.concrete, ProtocolValue.toConcrete_ofConcrete, Participant.guard,
      PIR.Process.interpret, PIR.Process.bind]
  exact OracleProtocol.StopsAfterMarks.now .reject

end ZkcExamples.Structured.FriCheckPositions

module

public import ZkcExamples.Structured.FriQueryCall
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

/-- All other captured values may be arbitrary. Only the initial handle and
the checked position vector determine the first table request. -/
theorem firstRead (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs)
    (ordinal : Fin xs.length) (source : OracleAnchor)
    (cap : Captures model) :
    OracleProtocol.AfterMarks (· = initialRequest context source xs[ordinal.val])
      (iteration context cap xs ordinal.val source) := by
  unfold iteration
  apply OracleProtocol.AfterMarks.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [2, 1]
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil))
    rw [receiver, lookup xs admitted ordinal]
  apply OracleProtocol.AfterMarks.mark
  apply OracleProtocol.AfterMarks.found
  rfl

end ZkcExamples.Structured.FriCheckPositions

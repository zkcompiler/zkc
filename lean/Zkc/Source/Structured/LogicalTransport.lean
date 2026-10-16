module

public import Zkc.Source.Structured.LogicalInstantiation

@[expose] public section

/-! Transport of logical contexts under a port repacking.

A port map sends every port of one signature to a port of another with the
same type and the same participant scope. Observations and legacy
selector-named slots move along the map; lexical binders do not move at all.
Consequently every atom over binders and observations holds on the repacked
subject exactly when it holds on the original one at the pulled-back boundary:
only the view from ports to logical objects changes, never the mathematics. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

/-- A port repacking with unchanged roles and scopes. -/
structure PortMap (source target : ProtocolSignature) where
  roles : source.roles.length = target.roles.length
  input : Renaming source.inputs target.inputs
  output : Renaming source.outputs target.outputs
  inputScope : ∀ {type : Ty} (ref : Var source.inputs type),
    target.inputScopes[(input ref).index]?.getD [] = source.inputScopes[ref.index]?.getD []
  outputScope : ∀ {type : Ty} (ref : Var source.outputs type),
    target.outputScopes[(output ref).index]?.getD [] = source.outputScopes[ref.index]?.getD []

namespace PortMap
variable {source target : ProtocolSignature} (map : PortMap source target)

def port {type : Ty} :
    BoundaryPort source.inputs source.outputs type → BoundaryPort target.inputs target.outputs type
  | .input ref => .input (map.input ref)
  | .output ref => .output (map.output ref)

def selector {type : Ty} (selector : BoundarySelector source type) : BoundarySelector target type where
  port := map.port selector.port
  role := Fin.cast map.roles selector.role
  inScope := by
    rcases selector with ⟨port, role, inScope⟩
    cases port with
    | input ref =>
      simpa only [PortMap.port, BoundaryPort.index, map.inputScope, Fin.val_cast] using inScope
    | output ref =>
      simpa only [PortMap.port, BoundaryPort.index, map.outputScope, Fin.val_cast] using inScope

/-- Read a target boundary in the source's port order. -/
def pull {Value : Ty → Type} (boundary : BoundaryValuation Value target.inputs target.outputs) :
    BoundaryValuation Value source.inputs source.outputs :=
  ⟨fun role => Environment.toValues (fun ref => (boundary.inputs role).get (map.input ref)),
   fun role => Environment.toValues (fun ref => (boundary.outputs role).get (map.output ref))⟩

theorem selector_read {Value : Ty → Type} {type : Ty} (selected : BoundarySelector source type)
    (context : ProtocolContext) (boundary : BoundaryValuation Value target.inputs target.outputs) :
    (map.selector selected).read context boundary = selected.read context (map.pull boundary) := by
  rcases selected with ⟨port, role, inScope⟩
  cases port <;>
    simp only [BoundarySelector.read, PortMap.selector, PortMap.port, pull, Environment.toValues_get,
      Fin.val_cast]

variable {V : Vocabulary} {Value : Ty → Type} {context : List (LogicalType V.Sorts)}

/-- Terms move with the ports; binders are left untouched. -/
def term : {type : LogicalType V.Sorts} → Term V Value source context type →
    Term V Value target context type
  | _, .key (.binder ref) => .key (.binder ref)
  | _, .key (.parameter selected) => .key (.parameter (map.selector selected))
  | _, .key (.witness selected) => .key (.witness (map.selector selected))
  | _, .observed selected => .observed (map.selector selected)
  | _, .supplied value => .supplied value
  | _, .unavailable => .unavailable
  | _, .view code argument => .view code (term argument)

def terms : {types : List (LogicalType V.Sorts)} → Values (Term V Value source context) types →
    Values (Term V Value target context) types
  | _, .nil => .nil
  | _, .cons first rest => .cons (map.term first) (terms rest)

def atom (atom : Atom V Value source context) : Atom V Value target context :=
  ⟨atom.predicate, map.terms atom.arguments⟩

/-- A binder is the same term before and after repacking. -/
theorem term_binder {type : LogicalType V.Sorts} (ref : Var context type) :
    map.term (Term.binder (V := V) (Value := Value) (signature := source) ref) = Term.binder ref := rfl

variable {snapshot other : Snapshot} {imported : Imported snapshot} {repacked : Imported other}
  {interpretation : Interpretation V Value}
  {owner : ContractBinding imported} {targetOwner : ContractBinding repacked}
  {invocation : InvocationCoordinate}

/-- The source subject's view of a store kept by the repacked subject. -/
def pullStore (map : PortMap owner.protocol.signature targetOwner.protocol.signature)
    (store : Store interpretation targetOwner invocation context) :
    Store interpretation owner invocation context :=
  ⟨fun key => match key with
    | .binder ref => store.get (.binder ref)
    | .parameter selected => store.get (.parameter (map.selector selected))
    | .witness selected => store.get (.witness (map.selector selected))⟩

theorem term_read (map : PortMap owner.protocol.signature targetOwner.protocol.signature)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value targetOwner.protocol.inputs targetOwner.protocol.outputs)
    (store : Store interpretation targetOwner invocation context) {type : LogicalType V.Sorts}
    (original : Term V Value owner.protocol.signature context type) :
    (map.term original).read interpretation protocolContext boundary store =
      original.read interpretation protocolContext (map.pull boundary) (map.pullStore store) := by
  induction original with
  | key slot => cases slot <;> rfl
  | observed selected => exact map.selector_read selected protocolContext boundary
  | supplied value => rfl
  | unavailable => rfl
  | view code argument ih =>
    simp only [PortMap.term, Term.read, ih]

theorem terms_read (map : PortMap owner.protocol.signature targetOwner.protocol.signature)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value targetOwner.protocol.inputs targetOwner.protocol.outputs)
    (store : Store interpretation targetOwner invocation context) {types : List (LogicalType V.Sorts)}
    (original : Values (Term V Value owner.protocol.signature context) types) :
    readTerms interpretation protocolContext boundary store (map.terms original) =
      readTerms interpretation protocolContext (map.pull boundary) (map.pullStore store) original := by
  induction original with
  | nil => rfl
  | cons first rest ih =>
    simp only [PortMap.terms, readTerms, map.term_read, ih]

/-- Transport of an atom along a port repacking: the predicate and its binders
are unchanged; only observations and legacy slot names move. -/
theorem atom_holds (map : PortMap owner.protocol.signature targetOwner.protocol.signature)
    (original : Atom V Value owner.protocol.signature context) (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value targetOwner.protocol.inputs targetOwner.protocol.outputs)
    (store : Store interpretation targetOwner invocation context) :
    (map.atom original).Holds interpretation protocolContext boundary store ↔
      original.Holds interpretation protocolContext (map.pull boundary) (map.pullStore store) := by
  unfold Atom.Holds PortMap.atom
  rw [map.terms_read]

/-- A store of binder values alone is unchanged by repacking. -/
theorem pullStore_ofValues (map : PortMap owner.protocol.signature targetOwner.protocol.signature)
    (values : Values interpretation.Denote context) {type : LogicalType V.Sorts}
    (ref : Var context type) :
    (map.pullStore (Store.ofValues (invocation := invocation) values)).get (.binder ref) =
      (Store.ofValues (owner := owner) (invocation := invocation) values).get (.binder ref) := rfl

end PortMap

end Zkc.Source.Structured.Logical

module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Program.Region.Basic
public import Zkc.Program.Interaction

@[expose] public section

/-! Types, holders, sides and models of the core language.

A value in a protocol body has one holder. For a side, a set of roles, the value of
`T @ r` is a value of `T` when `r` is in the side and the single unit value
otherwise. Membership is a `Bool`; a literal side applied to a literal role reduces
to `true` or `false`, and the family `Held` reduces with it. No optional value and no
run-time presence test occurs in a side's process.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- Core types: a structural grammar over the package's nominal types. A variant has
at least one alternative, so every type has a value when every nominal carrier has
one. Oracle handle types are part of the specified grammar and are not represented
here yet. -/
inductive Ty where
  | unit
  | bool
  | index
  | nominal (row : Nat)
  | array (element : Ty)
  | tuple (components : List Ty)
  | variant (first : Ty) (rest : List Ty)
  deriving Repr, Inhabited, BEq

mutual
  /-- Values of a type, given the carriers of the nominal rows. -/
  @[reducible] def Ty.Value (Carrier : Nat → Type) : Ty → Type
    | .unit => PUnit
    | .bool => Bool
    | .index => Nat
    | .nominal row => Carrier row
    | .array element => List (Ty.Value Carrier element)
    | .tuple components => Ty.Tuple Carrier components
    | .variant first rest => Ty.Value Carrier first ⊕ Ty.Variant Carrier rest

  /-- Records by position. -/
  @[reducible] def Ty.Tuple (Carrier : Nat → Type) : List Ty → Type
    | [] => PUnit
    | component :: rest => Ty.Value Carrier component × Ty.Tuple Carrier rest

  /-- One of the later alternatives of a variant, tagged by position. -/
  @[reducible] def Ty.Variant (Carrier : Nat → Type) : List Ty → Type
    | [] => PEmpty
    | alternative :: rest => Ty.Value Carrier alternative ⊕ Ty.Variant Carrier rest
end

/-- A located type `T @ r`: a type and its one holder. -/
structure Located where
  type : Ty
  holder : Nat
  deriving Repr, Inhabited, BEq

/-- The types of a list, all held by one role. -/
@[reducible] def Located.atRole (role : Nat) (types : List Ty) : List Located :=
  types.map fun type => ⟨type, role⟩

/-- One value of a type for each role of a list, in order. -/
@[reducible] def Located.ofRoles (type : Ty) (roles : List Nat) : List Located :=
  roles.map fun role => ⟨type, role⟩

/-- A map from a callee's roles to the caller's roles: callee role `j` runs as entry `j`. -/
abbrev RoleMap := List Nat

def RoleMap.apply (map : RoleMap) (role : Nat) : Nat := map.getD role 0

/-- A number is one of a list. -/
def occursIn (numbers : List Nat) (number : Nat) : Bool := numbers.any (Nat.beq number)

/-- No number occurs twice in the list. A role map with distinct entries is
injective: no caller role runs two callee roles. -/
def distinctNumbers : List Nat → Bool
  | [] => true
  | number :: rest => !(occursIn rest number) && distinctNumbers rest

/-- Each number is above the one before it. -/
def increasingNumbers : List Nat → Bool
  | first :: second :: rest => Nat.blt first second && increasingNumbers (second :: rest)
  | _ => true

def Located.rename (map : RoleMap) (located : Located) : Located :=
  ⟨located.type, map.apply located.holder⟩

/-- Every located type is held by one of the roles. -/
def Located.heldBy (roles : List Nat) (types : List Located) : Bool :=
  types.all fun located => occursIn roles located.holder

/-- A side: the membership of each role. -/
abbrev Side := Nat → Bool

/-- The side whose members are the set bits of a mask. -/
def Side.ofMask (mask : Nat) : Side := fun role => mask.testBit role

/-- The callee's side of an application: callee role `j` is in it when the caller
role that runs it is in the caller's side. -/
def Side.preimage (map : RoleMap) (side : Side) : Side := fun role => side (map.apply role)

/-- A value that exists only when `present` holds. -/
def Held (X : Type) : Bool → Type
  | true => X
  | false => PUnit

namespace Held

variable {X : Type}

/-- Keep a value when present; the unit value otherwise. -/
def of : (present : Bool) → X → Held X present
  | true, value => value
  | false, _ => PUnit.unit

/-- The unit value of an absent holder. -/
def absent : (present : Bool) → present = false → Held X present
  | false, _ => PUnit.unit

/-- The value of a present holder. -/
def value : (present : Bool) → present = true → Held X present → X
  | true, _, held => held

/-- Eliminate a held value: continue with it when present, otherwise with the
absence fact. -/
def elim {α : Sort _} : (present : Bool) → Held X present → (X → α) → (present = false → α) → α
  | true, held, onPresent, _ => onPresent held
  | false, _, _, onAbsent => onAbsent rfl

end Held


/-- The values of a present holder. -/
def presentValues {X : Ty → Type} : (present : Bool) → present = true →
    {types : List Ty} → Values (fun type => Held (X type) present) types → Values X types
  | true, _, _, values => values

/-- The unit values of an absent holder. -/
def absentValues {X : Ty → Type} : (types : List Ty) → Values (fun type => Held (X type) false) types
  | [] => .nil
  | _ :: rest => .cons PUnit.unit (absentValues rest)

/-- Values all held by one holder: the values when it is present, unit values
otherwise. The match is on the presence, so the values of a present holder reduce to
themselves whatever their form. -/
def holdValues {X : Ty → Type} :
    (present : Bool) → {types : List Ty} → Values X types →
      Values (fun type => Held (X type) present) types
  | true, _, values => values
  | false, types, _ => absentValues types

/-- The unit values of a holder known to be absent. -/
def absentHeldValues {X : Ty → Type} : (present : Bool) → present = false →
    (types : List Ty) → Values (fun type => Held (X type) present) types
  | false, _, types => absentValues types

/-- View values indexed by a mapped list as values indexed by the original list. -/
def unmapValues {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → Values F (items.map f) → Values (fun item => F (f item)) items
  | [], _ => .nil
  | _ :: rest, values => .cons (values.get .here) (unmapValues f rest values.tail)

/-- The inverse of `unmapValues`. -/
def remapValues {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → Values (fun item => F (f item)) items → Values F (items.map f)
  | [], _ => .nil
  | _ :: rest, values => .cons (values.get .here) (remapValues f rest values.tail)

/-- The kind of a catalogue operation row. -/
inductive OperationKind where
  | pure
  | «partial»
  | sampling
  deriving Repr, Inhabited, BEq, DecidableEq

/-- A row an operation may compute with: pure or partial, not a sampling law. -/
def OperationKind.computes : OperationKind → Bool
  | .pure | .partial => true
  | .sampling => false

/-- A row of the package's operation table: a catalogue operation instantiated at its
static arguments, with its signature and kind. Operations name a row by a variable
into the table, so their use of the row agrees with its signature and kind by typing. -/
structure OperationSignature where
  inputs : List Ty
  outputs : List Ty
  kind : OperationKind
  deriving Repr, Inhabited

/-- A pure or partial row as a model interprets it: its number and its signature. -/
structure OperationRow where
  row : Nat
  inputs : List Ty
  outputs : List Ty
  deriving Repr, Inhabited, BEq

/-- A sampling row: a law whose output distribution the inputs determine. -/
structure SamplingRow where
  row : Nat
  inputs : List Ty
  output : Ty
  deriving Repr, Inhabited, BEq

/-- The model's key of the pure or partial row that a variable into an operation
table names. -/
@[reducible] def OperationRow.of {operations : List OperationSignature} {inputs outputs : List Ty}
    {kind : OperationKind} (row : Var operations ⟨inputs, outputs, kind⟩) : OperationRow :=
  ⟨row.index, inputs, outputs⟩

/-- The sampling law that a variable into an operation table names. -/
@[reducible] def SamplingRow.of {operations : List OperationSignature} {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩) : SamplingRow :=
  ⟨law.index, inputs, output⟩

/-- The reasons a program or a model stops with. The remaining reason of `PIR.Stop`,
`incomplete`, belongs to the meaning of a side whose roles disagree on a control
value; no guard and no partial row can name it. -/
inductive Reason where
  | reject
  | abort
  | exhausted
  | refused
  deriving Repr, Inhabited, DecidableEq

/-- An authored reason as a reason of the shared process type. -/
def Reason.stop : Reason → PIR.Stop
  | .reject => .reject
  | .abort => .abort
  | .exhausted => .exhausted
  | .refused => .refused

/-- A stop reason is one of the authored reasons. `Region.stop` names a `PIR.Stop`;
residual well-formedness requires this of it. -/
def authoredStop : PIR.Stop → Bool
  | .incomplete => false
  | .reject | .abort | .exhausted | .refused => true

theorem Reason.stop_ne_incomplete (reason : Reason) : reason.stop ≠ .incomplete := by
  cases reason <;> exact PIR.Stop.noConfusion

/-- A model: carriers for the nominal types and a meaning for every pure and partial
operation row. A partial row returns its outputs or stops with an authored reason. A
sampling row needs no meaning: a side's process leaves the reply of a `draw` or
`sample` unconstrained. Statements about programs hold for an arbitrary model; laws
are hypotheses about `pure` and `partial`. -/
structure Model where
  Carrier : Nat → Type
  pure : (row : OperationRow) →
    Values (Ty.Value Carrier) row.inputs → Values (Ty.Value Carrier) row.outputs
  «partial» : (row : OperationRow) →
    Values (Ty.Value Carrier) row.inputs → Except Reason (Values (Ty.Value Carrier) row.outputs)

abbrev Model.Value (model : Model) : Ty → Type := Ty.Value model.Carrier

mutual
  /-- A value of a type, from a value of every nominal carrier. -/
  def Ty.inhabitant {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
      (type : Ty) → Ty.Value Carrier type
    | .unit => PUnit.unit
    | .bool => false
    | .index => (0 : Nat)
    | .nominal row => carrier row
    | .array _ => ([] : List _)
    | .tuple components => Ty.tupleInhabitant carrier components
    | .variant first _ => .inl (Ty.inhabitant carrier first)

  /-- A record of a value of every component. -/
  def Ty.tupleInhabitant {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
      (components : List Ty) → Ty.Tuple Carrier components
    | [] => PUnit.unit
    | component :: rest => (Ty.inhabitant carrier component, Ty.tupleInhabitant carrier rest)
end

/-- A value of every type of a list. -/
def Ty.inhabitants {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
    (types : List Ty) → Values (Ty.Value Carrier) types
  | [] => .nil
  | type :: rest => .cons (Ty.inhabitant carrier type) (Ty.inhabitants carrier rest)

/-- A model exists: one-point carriers, every pure row returning the value of each of
its output types, every partial row stopping. A statement quantified over models is
therefore not vacuous. A model interprets every row, so each of its carriers has a
value. -/
def Model.unit : Model where
  Carrier _ := PUnit
  pure row _ := Ty.inhabitants (fun _ => PUnit.unit) row.outputs
  «partial» _ _ := .error .abort

instance : Inhabited Model := ⟨Model.unit⟩

/-- Every nominal carrier of a model has a value: the result of a row without inputs
that returns it. -/
def Model.inhabitant (model : Model) (row : Nat) : model.Carrier row :=
  (model.pure ⟨0, [], [.nominal row]⟩ .nil).get .here

/-- A static argument of a catalogue row. A `type` argument names nominal types by
their rows in the same package. -/
inductive Static where
  | domain (name : String)
  | nat (value : Nat)
  | type (type : Ty)
  deriving Repr, Inhabited

/-- The catalogue identity of a type row or an operation row: a catalogue name
applied to static arguments. -/
structure CatalogueRow where
  name : String
  statics : List Static
  deriving Repr, Inhabited

/-- The catalogue identities of a package's nominal types and operation rows, by
position. This is data for readers and tools: no typing rule, residual condition or
meaning inspects it, and the kernel never compares two of its strings. -/
structure Catalogue where
  types : List CatalogueRow
  operations : List CatalogueRow
  deriving Repr, Inhabited

/-- A static program point: a definition's row number and a site number local to it. -/
structure Site where
  definition : Nat
  number : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The effects of a side's process. The signature depends on the value family only:
every side and every definition shares it. -/
inductive Effect (Value : Ty → Type) where
  /-- A role of the side sends to a role outside it. -/
  | send (site : Site) (type : Ty) (value : Value type)
  /-- A role of the side receives from a role outside it. -/
  | receive (site : Site) (type : Ty)
  /-- A role of the side draws a public coin. -/
  | draw (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  /-- A role of the side samples a secret. -/
  | sample (site : Site) (law : SamplingRow) (inputs : Values Value law.inputs)
  /-- A role of the side reads an oracle at a position. -/
  | read (site : Site) (type : Ty) (position : Value type)

@[reducible] def Effect.Reply {Value : Ty → Type} : Effect Value → Type
  | .send .. => PUnit
  | .receive _ type => Value type
  | .draw _ law _ => Value law.output
  | .sample _ law _ => Value law.output
  | .read .. => PUnit

/-- The one effect signature of a model. -/
abbrev Effects (model : Model) : PIR.Signature := ⟨Effect model.Value, Effect.Reply⟩

/-- Draws and samples: the effects of randomness. -/
def Effect.random {Value : Ty → Type} : Effect Value → Prop
  | .draw .. | .sample .. => True
  | .send .. | .receive .. | .read .. => False

/-- Every effect a process may perform, along every reply, satisfies `allowed`. -/
def OnlyEffects {I : PIR.Signature} {A : Type} (allowed : I.Op → Prop) : PIR.Process I A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op next => allowed op ∧ ∀ reply, OnlyEffects allowed (next reply)

/-- A process never stops with the given reason, along every reply. -/
def NeverStops {I : PIR.Signature} {A : Type} (reason : PIR.Stop) : PIR.Process I A → Prop
  | .done _ => True
  | .halt why => why ≠ reason
  | .call _ next => ∀ reply, NeverStops reason (next reply)

/-- The value of a located type for a side. -/
@[reducible] def SideValue (model : Model) (side : Side) : Located → Type
  | ⟨type, holder⟩ => Held (model.Value type) (side holder)

end Zkc.Core

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.Value
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.Tuple
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.Variant
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Located.atRole
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Located.ofRoles
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.RoleMap.apply
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.distinctNumbers
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.increasingNumbers
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Located.rename
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Located.heldBy
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Side.ofMask
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Side.preimage
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Held
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Held.of
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Held.absent
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Held.value
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Held.elim
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.holdValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.presentValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.absentValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.absentHeldValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.unmapValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.remapValues
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Effect.Reply
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Effect.random
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.OnlyEffects
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.NeverStops
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Reason.stop
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.authoredStop
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.occursIn
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.SideValue
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.inhabitant
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.tupleInhabitant
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Core.Ty.inhabitants

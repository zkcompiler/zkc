module

public import Zkc.Core.Region

public section

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

/-- How often a value of a record type may be used: any number of times, at most once, or
exactly once. -/
inductive Use where
  | free
  | atMostOnce
  | exactlyOnce
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Core types: a structural grammar over the package's nominal types and declarations.

`nat` is the count type; `fin n` the naturals below `n`; `seq T none` a sequence whose
length is a property of the value and `seq T (some n)` one of exactly `n` elements; the
unit type is the empty tuple. A record and a variant are declared by the package: the
type carries the number of its declaration, which makes two declarations of one shape
different types, and the shape itself, which makes the values of a type a structural
recursion on the type. That the shape is the one the declaration has is a residual
condition of a package. A type may have no value: `fin 0`, a variant without
alternatives, and what needs a value of one of them. Oracle handle types are part of the
specified grammar and are not represented here yet. -/
inductive Ty where
  | bool
  | nat
  | fin (bound : Nat)
  | nominal (row : Nat)
  | seq (element : Ty) (size : Option Nat)
  | tuple (components : List Ty)
  | record (declaration : Nat) (use : Use) (fields : List Ty)
  | variant (declaration : Nat) (alternatives : List Ty)
  deriving Repr, Inhabited, BEq

/-- The type of the one value that carries nothing. -/
@[expose, reducible] def Ty.unit : Ty := .tuple []

/-! Decidable equality of core types: structural recursion over the nested type. -/
mutual
  def Ty.decEq : (left right : Ty) → Decidable (left = right)
    | .bool, .bool => isTrue rfl
    | .nat, .nat => isTrue rfl
    | .fin a, .fin b =>
        if same : a = b then isTrue (congrArg Ty.fin same)
        else isFalse fun equal => same (Ty.fin.inj equal)
    | .nominal a, .nominal b =>
        if same : a = b then isTrue (congrArg Ty.nominal same)
        else isFalse fun equal => same (Ty.nominal.inj equal)
    | .seq a m, .seq b n =>
        match Ty.decEq a b with
        | isTrue same =>
            if sameSize : m = n then isTrue (by rw [same, sameSize])
            else isFalse fun equal => sameSize (Ty.seq.inj equal).2
        | isFalse differ => isFalse fun equal => differ (Ty.seq.inj equal).1
    | .tuple a, .tuple b =>
        match Ty.decEqList a b with
        | isTrue same => isTrue (congrArg Ty.tuple same)
        | isFalse differ => isFalse fun equal => differ (Ty.tuple.inj equal)
    | .record d u a, .record e v b =>
        if sameDeclaration : d = e then
          if sameUse : u = v then
            match Ty.decEqList a b with
            | isTrue same => isTrue (by rw [sameDeclaration, sameUse, same])
            | isFalse differ => isFalse fun equal => differ (Ty.record.inj equal).2.2
          else isFalse fun equal => sameUse (Ty.record.inj equal).2.1
        else isFalse fun equal => sameDeclaration (Ty.record.inj equal).1
    | .variant d a, .variant e b =>
        if sameDeclaration : d = e then
          match Ty.decEqList a b with
          | isTrue same => isTrue (by rw [sameDeclaration, same])
          | isFalse differ => isFalse fun equal => differ (Ty.variant.inj equal).2
        else isFalse fun equal => sameDeclaration (Ty.variant.inj equal).1
    | .bool, .nat | .bool, .fin _ | .bool, .nominal _ | .bool, .seq .. | .bool, .tuple _
    | .bool, .record .. | .bool, .variant .. | .nat, .bool | .nat, .fin _
    | .nat, .nominal _ | .nat, .seq .. | .nat, .tuple _ | .nat, .record ..
    | .nat, .variant .. | .fin _, .bool | .fin _, .nat | .fin _, .nominal _
    | .fin _, .seq .. | .fin _, .tuple _ | .fin _, .record .. | .fin _, .variant ..
    | .nominal _, .bool | .nominal _, .nat | .nominal _, .fin _ | .nominal _, .seq ..
    | .nominal _, .tuple _ | .nominal _, .record .. | .nominal _, .variant ..
    | .seq .., .bool | .seq .., .nat | .seq .., .fin _ | .seq .., .nominal _
    | .seq .., .tuple _ | .seq .., .record .. | .seq .., .variant .. | .tuple _, .bool
    | .tuple _, .nat | .tuple _, .fin _ | .tuple _, .nominal _ | .tuple _, .seq ..
    | .tuple _, .record .. | .tuple _, .variant .. | .record .., .bool | .record .., .nat
    | .record .., .fin _ | .record .., .nominal _ | .record .., .seq ..
    | .record .., .tuple _ | .record .., .variant .. | .variant .., .bool
    | .variant .., .nat | .variant .., .fin _ | .variant .., .nominal _
    | .variant .., .seq .. | .variant .., .tuple _ | .variant .., .record .. =>
        isFalse (by intro equal; cases equal)

  def Ty.decEqList : (left right : List Ty) → Decidable (left = right)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Ty.decEq a b, Ty.decEqList as bs with
        | isTrue same, isTrue sameRest => isTrue (by rw [same, sameRest])
        | isFalse differ, _ => isFalse fun equal => differ (List.cons.inj equal).1
        | _, isFalse differ => isFalse fun equal => differ (List.cons.inj equal).2
    | [], _ :: _ => isFalse (by intro equal; cases equal)
    | _ :: _, [] => isFalse (by intro equal; cases equal)
end

instance : DecidableEq Ty := Ty.decEq

mutual
  /-- Values of a type, given the carriers of the nominal rows. -/
  @[expose, reducible] def Ty.Value (Carrier : Nat → Type) : Ty → Type
    | .bool => Bool
    | .nat => Nat
    | .fin bound => Fin bound
    | .nominal row => Carrier row
    | .seq element none => List (Ty.Value Carrier element)
    | .seq element (some size) =>
        { values : List (Ty.Value Carrier element) // values.length = size }
    | .tuple components => Ty.Tuple Carrier components
    | .record _ _ fields => Ty.Tuple Carrier fields
    | .variant _ alternatives => Ty.Variant Carrier alternatives

  /-- Records by position. -/
  @[reducible] def Ty.Tuple (Carrier : Nat → Type) : List Ty → Type
    | [] => PUnit
    | component :: rest => Ty.Value Carrier component × Ty.Tuple Carrier rest

  /-- One of the alternatives of a variant, tagged by position. No alternative gives the
  empty type. -/
  @[reducible] def Ty.Variant (Carrier : Nat → Type) : List Ty → Type
    | [] => PEmpty
    | alternative :: rest => Ty.Value Carrier alternative ⊕ Ty.Variant Carrier rest
end

mutual
  /-- A type that has a value whenever every nominal carrier has one. A pure row returns
  values of such types only: it is a total function. -/
  @[expose] def Ty.populated : Ty → Bool
    | .bool | .nat | .nominal _ => true
    | .fin bound => Nat.blt 0 bound
    | .seq _ none => true
    | .seq element (some size) => Nat.beq size 0 || element.populated
    | .tuple components => Ty.allPopulated components
    | .record _ _ fields => Ty.allPopulated fields
    | .variant _ alternatives => Ty.anyPopulated alternatives

  /-- Every type of a list is populated. -/
  @[expose] def Ty.allPopulated : List Ty → Bool
    | [] => true
    | type :: rest => type.populated && Ty.allPopulated rest

  /-- Some type of a list is populated. -/
  @[expose] def Ty.anyPopulated : List Ty → Bool
    | [] => false
    | type :: rest => type.populated || Ty.anyPopulated rest
end

/-- A declared record: how often a value of it may be used, and the types of its fields
by position. Field names are annotations and are not here. -/
structure RecordDeclaration where
  use : Use
  fields : List Ty
  deriving Repr, Inhabited, DecidableEq

/-- A declared variant: the payload types of its alternatives by position. An alternative
without a payload has the unit type. -/
structure VariantDeclaration where
  alternatives : List Ty
  deriving Repr, Inhabited, DecidableEq

/-- The type table of a package: the number of its nominal rows and its declarations of
records and variants. A type names a declaration by its number and carries the
declaration's shape, so no declaration contains itself. -/
structure TypeTable where
  nominals : Nat
  records : List RecordDeclaration
  variants : List VariantDeclaration
  deriving Repr, Inhabited

/-- A located type `T @ r`: a type and its one holder. -/
structure Located where
  type : Ty
  holder : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The types of a list, all held by one role. -/
@[expose, reducible] def Located.atRole (role : Nat) (types : List Ty) : List Located :=
  types.map fun type => ⟨type, role⟩

/-- One value of a type for each role of a list, in order. -/
@[expose, reducible] def Located.ofRoles (type : Ty) (roles : List Nat) : List Located :=
  roles.map fun role => ⟨type, role⟩

/-- A map from a callee's roles to the caller's roles: callee role `j` runs as entry `j`. -/
abbrev RoleMap := List Nat

@[expose] def RoleMap.apply (map : RoleMap) (role : Nat) : Nat := map.getD role 0

/-- A number is one of a list. -/
@[expose] def occursIn (numbers : List Nat) (number : Nat) : Bool := numbers.any (Nat.beq number)

/-- No number occurs twice in the list. A role map with distinct entries is
injective: no caller role runs two callee roles. -/
@[expose] def distinctNumbers : List Nat → Bool
  | [] => true
  | number :: rest => !(occursIn rest number) && distinctNumbers rest

@[expose, reducible] def Located.rename (map : RoleMap) (located : Located) : Located :=
  ⟨located.type, map.apply located.holder⟩

/-- Every located type is held by one of the roles. -/
@[expose] def Located.heldBy (roles : List Nat) (types : List Located) : Bool :=
  types.all fun located => occursIn roles located.holder

/-- A side: the membership of each role. -/
abbrev Side := Nat → Bool

/-- The side whose members are the set bits of a mask. -/
def Side.ofMask (mask : Nat) : Side := fun role => mask.testBit role

/-- The callee's side of an application: callee role `j` is in it when the caller
role that runs it is in the caller's side. -/
@[expose, reducible] def Side.preimage (map : RoleMap) (side : Side) : Side :=
  fun role => side (map.apply role)

/-- A value that exists only when `present` holds. -/
@[expose] def Held (X : Type) : Bool → Type
  | true => X
  | false => PUnit

namespace Held

variable {X : Type}

/-- Keep a value when present; the unit value otherwise. -/
@[expose] def of : (present : Bool) → X → Held X present
  | true, value => value
  | false, _ => PUnit.unit

/-- The unit value of an absent holder. -/
def absent : (present : Bool) → present = false → Held X present
  | false, _ => PUnit.unit

/-- The value of a present holder. -/
@[expose] def value : (present : Bool) → present = true → Held X present → X
  | true, _, held => held

/-- Eliminate a held value: continue with it when present, otherwise with the
absence fact. -/
@[expose] def elim {α : Sort _} : (present : Bool) → Held X present → (X → α) → (present = false → α) → α
  | true, held, onPresent, _ => onPresent held
  | false, _, _, onAbsent => onAbsent rfl

/-- A function applied to a held value. -/
@[expose] def map {Y : Type} (f : X → Y) : (present : Bool) → Held X present → Held Y present
  | true, held => f held
  | false, _ => PUnit.unit

/-- A function of two values applied to two values of one holder. -/
@[expose] def map₂ {Y Z : Type} (f : X → Y → Z) :
    (present : Bool) → Held X present → Held Y present → Held Z present
  | true, first, second => f first second
  | false, _, _ => PUnit.unit

end Held


/-- The values of a present holder. -/
@[expose] def presentValues {X : Ty → Type} : (present : Bool) → present = true →
    {types : List Ty} → Values (fun type => Held (X type) present) types → Values X types
  | true, _, _, values => values

/-- The unit values of an absent holder. -/
@[expose] def absentValues {X : Ty → Type} : (types : List Ty) → Values (fun type => Held (X type) false) types
  | [] => .nil
  | _ :: rest => .cons PUnit.unit (absentValues rest)

/-- Values all held by one holder: the values when it is present, unit values
otherwise. The match is on the presence, so the values of a present holder reduce to
themselves whatever their form. -/
@[expose] def holdValues {X : Ty → Type} :
    (present : Bool) → {types : List Ty} → Values X types →
      Values (fun type => Held (X type) present) types
  | true, _, values => values
  | false, types, _ => absentValues types

/-- The unit values of a holder known to be absent. -/
@[expose] def absentHeldValues {X : Ty → Type} : (present : Bool) → present = false →
    (types : List Ty) → Values (fun type => Held (X type) present) types
  | false, _, types => absentValues types

/-- View values indexed by a mapped list as values indexed by the original list. -/
@[expose] def unmapValues {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → Values F (items.map f) → Values (fun item => F (f item)) items
  | [], _ => .nil
  | _ :: rest, values => .cons (values.get .here) (unmapValues f rest values.tail)

/-- The inverse of `unmapValues`. -/
@[expose] def remapValues {α β : Type} {F : β → Type} (f : α → β) :
    (items : List α) → Values (fun item => F (f item)) items → Values F (items.map f)
  | [], _ => .nil
  | _ :: rest, values => .cons (values.get .here) (remapValues f rest values.tail)

-- The instances that the kind derives are exposed: a module that reads a comparison of two
-- kinds evaluates it.
@[expose] section

/-- The kind of a catalogue operation row. A pure row is a total function. A restricted
row is total on a domain: a model defines it there. It may name its *domain row*, a pure
row of the table with the same inputs and one `bool` output, by its number: the model's
laws make the restricted row defined exactly where the domain row gives `true`, and an
application of it is justified by a value of the domain row that is known to be `true`. A
restricted row without a domain row has a domain that only the model knows, and no
application of it is justified. A sampling row is a law: its one output is a type that
has a value. No row stops with an authored reason. -/
inductive OperationKind where
  | pure
  | restricted (domain : Option Nat)
  | sampling
  deriving Repr, Inhabited, BEq, DecidableEq

end

/-- A row an operation may compute with: pure or restricted, not a sampling law. -/
@[expose] def OperationKind.computes : OperationKind → Bool
  | .pure | .restricted _ => true
  | .sampling => false

/-- A row of the package's operation table: a catalogue operation instantiated at its
static arguments, with its signature and kind. Operations name a row by a variable
into the table, so their use of the row agrees with its signature and kind by typing. -/
structure OperationSignature where
  inputs : List Ty
  outputs : List Ty
  kind : OperationKind
  deriving Repr, Inhabited, DecidableEq

/-- A row a local operation may apply: a restricted row, or a pure row whose outputs are
populated types. -/
@[expose] def OperationSignature.applies (signature : OperationSignature) : Bool :=
  match signature.kind with
  | .pure => Ty.allPopulated signature.outputs
  | .restricted _ => true
  | .sampling => false

/-- A pure or restricted row as a model interprets it: its number and its signature. -/
structure OperationRow where
  row : Nat
  inputs : List Ty
  outputs : List Ty
  deriving Repr, Inhabited, BEq

/-- A sampling row: a law whose output distribution the inputs determine. A law is a type
that has a value: the output type is populated. -/
structure SamplingRow where
  row : Nat
  inputs : List Ty
  output : Ty
  populated : output.populated = true
  deriving Repr

instance : Inhabited SamplingRow := ⟨⟨0, [], .bool, rfl⟩⟩

instance : BEq SamplingRow where
  beq first second :=
    first.row == second.row && first.inputs == second.inputs && first.output == second.output

/-- The model's key of the pure or restricted row that a variable into an operation
table names. -/
@[expose, reducible] def OperationRow.of {operations : List OperationSignature} {inputs outputs : List Ty}
    {kind : OperationKind} (row : Var operations ⟨inputs, outputs, kind⟩) : OperationRow :=
  ⟨row.index, inputs, outputs⟩

/-- The sampling law that a variable into an operation table names, when its output type
is populated. -/
@[expose, reducible] def SamplingRow.of {operations : List OperationSignature} {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true) : SamplingRow :=
  ⟨law.index, inputs, output, populated⟩

/-- A literal: a value written in the program. A literal of a nominal type is the numbers
that a model reads it from; a label and a proof identity are such literals. A literal of
`fin n` is below `n` and a byte is below 256 by typing. -/
inductive Literal where
  | nat (value : Nat)
  | bool (value : Bool)
  | fin (bound : Nat) (value : Fin bound)
  | nominal (row : Nat) (data : List Nat)
  | bytes (data : List (Fin 256))
  deriving Repr, Inhabited, DecidableEq

/-- The type of a literal. -/
@[expose, reducible] def Literal.type : Literal → Ty
  | .nat _ => .nat
  | .bool _ => .bool
  | .fin bound _ => .fin bound
  | .nominal row _ => .nominal row
  | .bytes data => .seq (.fin 256) (some data.length)

/-- A function known by its header only, as a model interprets it: its number among the
functions of the program, in program order, and its signature. -/
structure OpaqueFunction where
  number : Nat
  inputs : List Ty
  outputs : List Ty
  deriving Repr, Inhabited, BEq

/-- The reasons a program or a model stops with. Two reasons of `PIR.Stop` are not among
them. `incomplete` belongs to the meaning of a side whose roles disagree on a control
value. `undefined` belongs to an operation applied outside its domain. No guard, no
function and no authored stop can name either. -/
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
  | .incomplete | .undefined => false
  | .reject | .abort | .exhausted | .refused => true

/-- An authored reason is not `incomplete`. -/
theorem authoredStop_ne_incomplete {reason : PIR.Stop} (authored : authoredStop reason = true) :
    reason ≠ .incomplete := by
  intro same
  subst same
  cases authored

theorem Reason.stop_ne_incomplete (reason : Reason) : reason.stop ≠ .incomplete := by
  cases reason <;> exact PIR.Stop.noConfusion

theorem Reason.stop_ne_undefined (reason : Reason) : reason.stop ≠ .undefined := by
  cases reason <;> exact PIR.Stop.noConfusion

/-- A model: carriers for the nominal types, a meaning for every pure and restricted
operation row, and a meaning for every function that a program knows by its header only.

A pure row is a total function; its outputs are populated types, so the function exists
whatever the row. A restricted row is defined on its domain: outside it the model gives
no value, and the process of an application stops `undefined`. A function known by its
header returns its outputs or stops with an authored reason. None of the three performs
an effect. A sampling row needs no meaning: a side's process leaves the reply of a `draw`
or `sample` unconstrained. Statements about programs hold for an arbitrary model; laws
are hypotheses about `pure`, `restricted` and `opaque`.

Every nominal carrier has a value, the one `literal` reads from no data. A type built
from the carriers may still have none. -/
structure Model where
  Carrier : Nat → Type
  pure : (row : OperationRow) → Ty.allPopulated row.outputs = true →
    Values (Ty.Value Carrier) row.inputs → Values (Ty.Value Carrier) row.outputs
  restricted : (row : OperationRow) →
    Values (Ty.Value Carrier) row.inputs → Option (Values (Ty.Value Carrier) row.outputs)
  «opaque» : (function : OpaqueFunction) →
    Values (Ty.Value Carrier) function.inputs →
      Except Reason (Values (Ty.Value Carrier) function.outputs)
  /-- The value of a literal of a nominal type. -/
  literal : (row : Nat) → List Nat → Carrier row

abbrev Model.Value (model : Model) : Ty → Type := Ty.Value model.Carrier

mutual
  /-- A value of a populated type, from a value of every nominal carrier. -/
  @[expose] def Ty.inhabitant {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
      (type : Ty) → type.populated = true → Ty.Value Carrier type
    | .bool, _ => false
    | .nat, _ => (0 : Nat)
    | .fin 0, populated => absurd populated (by decide)
    | .fin (_ + 1), _ => (0 : Fin _)
    | .nominal row, _ => carrier row
    | .seq _ none, _ => ([] : List _)
    | .seq _ (some 0), _ => ⟨[], rfl⟩
    | .seq element (some (size + 1)), populated =>
        ⟨List.replicate (size + 1)
            (Ty.inhabitant carrier element (by simpa [Ty.populated] using populated)),
          List.length_replicate⟩
    | .tuple components, populated =>
        Ty.tupleInhabitant carrier components (by simpa [Ty.populated] using populated)
    | .record _ _ fields, populated =>
        Ty.tupleInhabitant carrier fields (by simpa [Ty.populated] using populated)
    | .variant _ alternatives, populated =>
        Ty.variantInhabitant carrier alternatives (by simpa [Ty.populated] using populated)

  /-- A record of a value of every component. -/
  def Ty.tupleInhabitant {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
      (components : List Ty) → Ty.allPopulated components = true → Ty.Tuple Carrier components
    | [], _ => PUnit.unit
    | component :: rest, populated =>
        (Ty.inhabitant carrier component
            (by simp [Ty.allPopulated] at populated; exact populated.1),
          Ty.tupleInhabitant carrier rest
            (by simp [Ty.allPopulated] at populated; exact populated.2))

  /-- A value of the first populated alternative. -/
  def Ty.variantInhabitant {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
      (alternatives : List Ty) → Ty.anyPopulated alternatives = true →
        Ty.Variant Carrier alternatives
    | [], populated => absurd populated (by simp [Ty.anyPopulated])
    | alternative :: rest, populated =>
        if first : alternative.populated = true then
          .inl (Ty.inhabitant carrier alternative first)
        else
          .inr (Ty.variantInhabitant carrier rest
            (by simp [Ty.anyPopulated, first] at populated; exact populated))
end

mutual
  /-- A type that has a value is populated, whatever the carriers. -/
  theorem Ty.populated_of_value {Carrier : Nat → Type} :
      ∀ (type : Ty), Ty.Value Carrier type → type.populated = true
    | .bool, _ => rfl
    | .nat, _ => rfl
    | .nominal _, _ => rfl
    | .fin bound, value => by
        have below : value.val < bound := value.isLt
        exact Nat.blt_eq.mpr (by omega)
    | .seq _ none, _ => rfl
    | .seq _ (some 0), _ => rfl
    | .seq element (some (size + 1)), ⟨values, counted⟩ => by
        cases values with
        | nil => cases counted
        | cons first _ => exact Ty.populated_of_value element first
    | .tuple components, value => Ty.allPopulated_of_tuple components value
    | .record _ _ fields, value => Ty.allPopulated_of_tuple fields value
    | .variant _ alternatives, value => Ty.anyPopulated_of_variant alternatives value

  /-- The components of a record that has a value are populated. -/
  theorem Ty.allPopulated_of_tuple {Carrier : Nat → Type} :
      ∀ (components : List Ty), Ty.Tuple Carrier components → Ty.allPopulated components = true
    | [], _ => rfl
    | component :: rest, (value, others) => by
        show (component.populated && Ty.allPopulated rest) = true
        rw [Ty.populated_of_value component value, Ty.allPopulated_of_tuple rest others]
        rfl

  /-- A variant that has a value has a populated alternative. -/
  theorem Ty.anyPopulated_of_variant {Carrier : Nat → Type} :
      ∀ (alternatives : List Ty), Ty.Variant Carrier alternatives →
        Ty.anyPopulated alternatives = true
    | [], value => nomatch value
    | alternative :: rest, .inl value => by
        show (alternative.populated || Ty.anyPopulated rest) = true
        rw [Ty.populated_of_value alternative value]
        rfl
    | alternative :: rest, .inr later => by
        show (alternative.populated || Ty.anyPopulated rest) = true
        rw [Ty.anyPopulated_of_variant rest later, Bool.or_true]
end

/-- Types that all have a value are populated. -/
theorem Ty.allPopulated_of_values {Carrier : Nat → Type} :
    ∀ {types : List Ty}, Values (Ty.Value Carrier) types → Ty.allPopulated types = true
  | _, .nil => rfl
  | _, .cons (ty := type) value rest => by
      show (type.populated && Ty.allPopulated _) = true
      rw [Ty.populated_of_value type value, Ty.allPopulated_of_values rest]
      rfl

/-- A value of every type of a list of populated types. -/
@[expose] def Ty.inhabitants {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row) :
    (types : List Ty) → Ty.allPopulated types = true → Values (Ty.Value Carrier) types
  | [], _ => .nil
  | type :: rest, populated =>
      .cons (Ty.inhabitant carrier type (by simp [Ty.allPopulated] at populated; exact populated.1))
        (Ty.inhabitants carrier rest (by simp [Ty.allPopulated] at populated; exact populated.2))

/-- A model exists: one-point carriers, every pure row returning a value of each of its
output types, every restricted row undefined, every function known by its header
stopping. A statement quantified over models is therefore not vacuous. -/
def Model.unit : Model where
  Carrier _ := PUnit
  pure row populated _ := Ty.inhabitants (fun _ => PUnit.unit) row.outputs populated
  restricted _ _ := none
  «opaque» _ _ := .error .abort
  literal _ _ := PUnit.unit

instance : Inhabited Model := ⟨Model.unit⟩

theorem allPopulated_bool : Ty.allPopulated [.bool] = true := rfl

/-- The value that `Ty.inhabitants` gives the one output `bool` is `false`. -/
theorem Ty.inhabitants_bool {Carrier : Nat → Type} (carrier : (row : Nat) → Carrier row)
    (populated : Ty.allPopulated [.bool] = true) :
    (Ty.inhabitants carrier [.bool] populated).get .here = false := by rfl

/-- The domain laws of a model for an operation table: a restricted row that names a domain
row has a value exactly where the domain row gives `true`. The domain row is read at the
inputs of the restricted row and the one output `bool`, the signature that a well-formed
table gives it. -/
@[expose] def Model.DomainLaws (model : Model) (operations : List OperationSignature) : Prop :=
  ∀ (row domain : Nat) (inputs outputs : List Ty),
    operations[row]? = some ⟨inputs, outputs, .restricted (some domain)⟩ →
      ∀ arguments : Values (Ty.Value model.Carrier) inputs,
        (model.restricted ⟨row, inputs, outputs⟩ arguments).isSome =
          (model.pure ⟨domain, inputs, [.bool]⟩ allPopulated_bool arguments).get .here

/-- The one-point model satisfies the domain laws of every table: no restricted row of it
has a value, and every `bool` that a pure row of it returns is `false`. -/
theorem Model.unit_domainLaws (operations : List OperationSignature) :
    Model.unit.DomainLaws operations :=
  fun _ _ _ _ _ _ => rfl

/-- The value of a literal. -/
@[expose] def Literal.value (model : Model) : (literal : Literal) → model.Value literal.type
  | .nat value => value
  | .bool value => value
  | .fin _ value => value
  | .nominal row data => model.literal row data
  | .bytes data => ⟨data, rfl⟩

/-- A catalogue name, as the code points of its characters. The kernel decides the
rules on names; it computes with numerals natively, and it reduces a string or a
character through their byte and bit-vector representations, which costs about a
millisecond per character. -/
abbrev Name := List Nat

/-- The name with the given text. -/
def Name.ofString (text : String) : Name := text.toList.map Char.toNat

/-- The text of a name. -/
def Name.toString (name : Name) : String := String.ofList (name.map Char.ofNat)

/-- A static argument of a catalogue row. A `type` argument names nominal types by
their rows in the same package. -/
inductive Static where
  | domain (name : Name)
  | nat (value : Nat)
  | type (type : Ty)
  deriving Repr, Inhabited, DecidableEq

/-- The catalogue identity of a type row or an operation row: a catalogue name
applied to static arguments. -/
structure CatalogueRow where
  name : Name
  statics : List Static
  deriving Repr, Inhabited, DecidableEq

/-- The catalogue identities of a package's nominal types and operation rows, by
position. This is data for readers and tools: no typing rule, residual condition or
meaning inspects it, and the kernel never compares two of its strings. -/
structure Catalogue where
  types : List CatalogueRow
  operations : List CatalogueRow
  deriving Repr, Inhabited

/-- A program point of one definition: the definition's identity and a site number local
to it. -/
structure Point where
  definition : Nat
  number : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The site of an effect: the sites of the applications that reached the operation,
outermost first, then the identity of the operation's definition and the operation's
site number in it. The identity of a definition is a number that steps keep: a
definition's images after a step and the operations of its expansion report it. -/
structure Site where
  path : List Nat
  definition : Nat
  number : Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The path of the effects of a protocol applied at a site. -/
@[expose, reducible] def Site.below (site : Site) : List Nat := site.path ++ [site.number]

/-- The labelling of a definition's sites: under the applications that reached it, by its
identity and its own site numbers. -/
abbrev ownSites (identity : Nat) (path : List Nat) : Nat → Site :=
  fun site => ⟨path, identity, site⟩

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

@[expose, reducible] def Effect.Reply {Value : Ty → Type} : Effect Value → Type
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

theorem NeverStops.done {I : PIR.Signature} {A : Type} (reason : PIR.Stop) (value : A) :
    NeverStops reason (.done value : PIR.Process I A) := trivial

theorem NeverStops.halt_iff {I : PIR.Signature} {A : Type} {reason why : PIR.Stop} :
    NeverStops reason (.halt why : PIR.Process I A) ↔ why ≠ reason := Iff.rfl

theorem NeverStops.call_iff {I : PIR.Signature} {A : Type} {reason : PIR.Stop} {op : I.Op}
    {next : I.Reply op → PIR.Process I A} :
    NeverStops reason (.call op next) ↔ ∀ reply, NeverStops reason (next reply) := Iff.rfl

/- The predicate is read through the three statements above. Unfolding it on the process of
a function would evaluate the function. -/
attribute [irreducible] NeverStops

/-- The value of a located type for a side. -/
@[expose, reducible] def SideValue (model : Model) (side : Side) : Located → Type
  | ⟨type, holder⟩ => Held (model.Value type) (side holder)

end Zkc.Core


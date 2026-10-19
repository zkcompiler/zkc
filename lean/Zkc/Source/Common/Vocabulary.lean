module

public import Zkc.Source.Common

@[expose] public section

/-! Nominal scalar vocabulary for the native common-source connection.

Domain strings remain part of source sorts and operation signatures. An
interpretation must separately justify their carriers and algebraic laws.
-/

set_option autoImplicit false

namespace Zkc.Source.Common.Native

inductive Ty where
  | boolean
  | field (domain : String)
  | group (domain : String)
  | service (contract : String)
  deriving DecidableEq, Repr

inductive Op where
  | fieldConstant (domain : String) (value : Nat)
  | fieldAdd (domain : String)
  | fieldSubtract (domain : String)
  | fieldMultiply (domain : String)
  | fieldEqual (domain : String)
  | groupIdentity (domain : String)
  | groupAdd (domain : String)
  | groupScale (group scalar : String)
  | groupEqual (domain : String)
  | booleanConstant (value : Bool)
  | booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual
  | select (ty : Ty)
  deriving DecidableEq, Repr

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments
    | .fieldConstant .. | .groupIdentity .. | .booleanConstant .. => []
    | .fieldAdd d | .fieldSubtract d | .fieldMultiply d | .fieldEqual d => [.field d, .field d]
    | .groupAdd d | .groupEqual d => [.group d, .group d]
    | .groupScale g f => [.group g, .field f]
    | .booleanAnd | .booleanOr | .booleanXor | .booleanEqual | .booleanNotEqual => [.boolean, .boolean]
    | .select ty => [.boolean, ty, ty]
  result
    | .fieldConstant d _ | .fieldAdd d | .fieldSubtract d | .fieldMultiply d => .field d
    | .groupIdentity d | .groupAdd d | .groupScale d _ => .group d
    | .fieldEqual _ | .groupEqual _ | .booleanConstant _ | .booleanAnd | .booleanOr |
        .booleanXor | .booleanEqual | .booleanNotEqual => .boolean
    | .select ty => ty
  condition := .boolean

/-- A draw is an open service call, not a built-in uniform sampler. The handle
is an actual input operand, so distinct service bindings remain distinguishable. -/
abbrev services : Participant.Services Ty where
  Op := String
  arguments field := [.service ("random." ++ field ++ "/0")]
  result field := .field field

inductive Instruction where
  | pure (op : Op) (arguments : List Nat)
  | restrict (roles : List Nat) (ty : Ty) (value : Nat)
  | exchange (site : String) (sender receiver : Nat) (ty : Ty) (value : Nat)
  | draw (site : String) (owner : Nat) (field : String) (service : Nat)
  | guard (site : String) (owner value : Nat)
  | statement (relation : String) (types : List Ty) (selectors arguments : List Nat)
  deriving DecidableEq, Repr

structure Snapshot where
  source : String
  symbol : String
  roles : List String
  inputs : List Ty
  inputRoles : List (List Nat)
  result : Ty
  outputRoles : List Nat
  instructions : List Instruction
  returned : Nat
  deriving DecidableEq, Repr

end Zkc.Source.Common.Native

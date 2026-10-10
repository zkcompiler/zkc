import Zkc.Source.Definitions
import Zkc.Source.Protocol.Context

/-! Typed common-source syntax with explicit local and protocol call kinds.

Ports include role ownership. A receive binds a new value; shared protocol
definitions return only their declared ordered ports. The count carrier selects
resolved naturals or symbolic templates; loops retain their body and accumulator
ports without unrolling. Meanings consume resolved natural counts. Global branches and role
remapping are not yet part of this resolved subset.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol

structure Signature (Role Ty : Type) where
  arguments : List (Port Role Ty)
  results : List (Port Role Ty)
  deriving DecidableEq, Repr

/-- A resolved body reference and its separately selected semantic binding. -/
structure Instance (Role Binding Ty : Type) (scope : List (Signature Role Ty))
    (signature : Signature Role Ty) where
  callee : Var scope signature
  binding : Binding

inductive Program (Count : Type) (Role Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (scope : List (Signature Role language.Ty)) :
    List (Port Role language.Ty) → List (Port Role language.Ty) → Type where
  | ret {Γ results} (values : Operands Γ results) :
      Program Count Role Binding Schema language locals scope Γ results
  | stop {Γ results} (site : Nat) (role : Role) (reason : PIR.Stop) :
      Program Count Role Binding Schema language locals scope Γ results
  | localCall {Γ results signature} (site : Nat) (role : Role)
      (callee : Var locals signature) (args : Operands Γ (owned role signature.arguments))
      (next : Program Count Role Binding Schema language locals scope
        ((role, signature.result) :: Γ) results) :
      Program Count Role Binding Schema language locals scope Γ results
  | message {Γ results ty} (site : Nat) (schema : Schema) (sender receiver : Role)
      (different : sender ≠ receiver) (value : Var Γ (sender, ty))
      (next : Program Count Role Binding Schema language locals scope ((receiver, ty) :: Γ) results) :
      Program Count Role Binding Schema language locals scope Γ results
  | invoke {Γ results signature} (site : Nat)
      (callee : Instance Role Binding language.Ty scope signature)
      (args : Operands Γ signature.arguments)
      (next : Program Count Role Binding Schema language locals scope (signature.results ++ Γ) results) :
      Program Count Role Binding Schema language locals scope Γ results
  | repeat {Γ results ports} (site : Nat) (count : Count) (initial : Operands Γ ports)
      (body : Program Count Role Binding Schema language locals scope (ports ++ Γ) ports)
      (next : Program Count Role Binding Schema language locals scope (ports ++ Γ) results) :
      Program Count Role Binding Schema language locals scope Γ results
  | bind {Γ ports results}
      (body : Program Count Role Binding Schema language locals scope Γ ports)
      (next : Program Count Role Binding Schema language locals scope (ports ++ Γ) results) :
      Program Count Role Binding Schema language locals scope Γ results

/-- Protocol bodies reference earlier protocol definitions and the shared local library. -/
inductive Definitions (Count : Type) (Role Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) :
    List (Signature Role language.Ty) → Type where
  | nil : Definitions Count Role Binding Schema language locals []
  | snoc {scope : List (Signature Role language.Ty)}
      (previous : Definitions Count Role Binding Schema language locals scope)
      (signature : Signature Role language.Ty)
      (body : Program Count Role Binding Schema language locals scope
        signature.arguments signature.results) :
      Definitions Count Role Binding Schema language locals (signature :: scope)

end Zkc.Source.Protocol

import Zkc.Source.Protocol.Syntax

/-! Scheduled participant syntax with separate send and receive instructions.

One typed in-flight packet connects an explicit sender to its receiver. The
structured schedule retains shared calls and loops. It is not an asynchronous
network machine or an independently deployable participant-module format.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Participant

open Zkc.Source Zkc.Source.Protocol

structure Transfer (Role Schema Ty : Type) where
  site : Nat
  schema : Schema
  sender : Role
  receiver : Role
  different : sender ≠ receiver
  ty : Ty

inductive Program (Count : Type) (Role Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (scope : List (Signature Role language.Ty)) :
    Option (Transfer Role Schema language.Ty) →
      List (Port Role language.Ty) → List (Port Role language.Ty) → Type where
  | ret {Γ results} (values : Operands Γ results) :
      Program Count Role Binding Schema language locals scope none Γ results
  | stop {Γ results} (site : Nat) (role : Role) (reason : PIR.Stop) :
      Program Count Role Binding Schema language locals scope none Γ results
  | localCall {Γ results signature} (site : Nat) (role : Role)
      (callee : Var locals signature) (args : Operands Γ (owned role signature.arguments))
      (next : Program Count Role Binding Schema language locals scope none
        ((role, signature.result) :: Γ) results) :
      Program Count Role Binding Schema language locals scope none Γ results
  | send {Γ results} (transfer : Transfer Role Schema language.Ty)
      (value : Var Γ (transfer.sender, transfer.ty))
      (next : Program Count Role Binding Schema language locals scope (some transfer) Γ results) :
      Program Count Role Binding Schema language locals scope none Γ results
  | receive {Γ results transfer}
      (next : Program Count Role Binding Schema language locals scope none
        ((transfer.receiver, transfer.ty) :: Γ) results) :
      Program Count Role Binding Schema language locals scope (some transfer) Γ results
  | invoke {Γ results signature} (site : Nat)
      (callee : Instance Role Binding language.Ty scope signature)
      (args : Operands Γ signature.arguments)
      (next : Program Count Role Binding Schema language locals scope none
        (signature.results ++ Γ) results) :
      Program Count Role Binding Schema language locals scope none Γ results
  | repeat {Γ results ports} (site : Nat) (count : Count) (initial : Operands Γ ports)
      (body : Program Count Role Binding Schema language locals scope none (ports ++ Γ) ports)
      (next : Program Count Role Binding Schema language locals scope none (ports ++ Γ) results) :
      Program Count Role Binding Schema language locals scope none Γ results
  | bind {Γ ports results}
      (body : Program Count Role Binding Schema language locals scope none Γ ports)
      (next : Program Count Role Binding Schema language locals scope none (ports ++ Γ) results) :
      Program Count Role Binding Schema language locals scope none Γ results

/-- A pending transfer has exactly one legal instruction shape in this synchronous target. -/
theorem Program.pending_receive {Count Role Binding Schema : Type} {language : Language}
    {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Role language.Ty)}
    {Γ results : List (Port Role language.Ty)} {transfer : Transfer Role Schema language.Ty}
    (program : Program Count Role Binding Schema language locals scope (some transfer) Γ results) :
    ∃ next, program = .receive next := by
  cases program with
  | receive next => exact ⟨next, rfl⟩

inductive Definitions (Count : Type) (Role Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) :
    List (Signature Role language.Ty) → Type where
  | nil : Definitions Count Role Binding Schema language locals []
  | snoc {scope : List (Signature Role language.Ty)}
      (previous : Definitions Count Role Binding Schema language locals scope)
      (signature : Signature Role language.Ty)
      (body : Program Count Role Binding Schema language locals scope none
        signature.arguments signature.results) :
      Definitions Count Role Binding Schema language locals (signature :: scope)

end Zkc.Compiler.Participant

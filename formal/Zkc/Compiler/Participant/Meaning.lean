import Zkc.Compiler.Participant.Context
import Zkc.Compiler.Participant.Syntax
import Zkc.Source.Protocol.Meaning

/-! Execute scheduled syntax through participant-local requests.

The packet is a typed driver value between send and receive, not a source-domain
value exposed to local computation. Return tuples belong to the joint observer.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Participant

open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.LocatedExecution (Frame Origin)

inductive Action (Role Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value Packet : language.Ty → Type) where
  | local {signature : DefinitionSignature language.Ty}
      (origin : Origin Role Entry Binding) (callee : Var locals signature)
      (args : Values Value signature.arguments)
  | send {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
      (receiver : Role) (value : Value ty)
  | receive {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
      (sender : Role) (packet : Packet ty)
  | stop (origin : Origin Role Entry Binding) (reason : PIR.Stop)

abbrev interface (Role Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value Packet : language.Ty → Type) :
    PIR.Signature where
  Op := Action Role Entry Binding Schema language locals Value Packet
  Reply
    | .local (signature := signature) .. => Value signature.result
    | .send (ty := ty) .. => Packet ty
    | .receive (ty := ty) .. => Value ty
    | .stop .. => Empty

variable {Role Entry Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value Packet : language.Ty → Type}

abbrev InFlight (Packet : language.Ty → Type) : Option (Transfer Role Schema language.Ty) → Type
  | none => Unit
  | some transfer => Packet transfer.ty

abbrev CallMeaning (scope : List (Signature Role language.Ty)) :=
  {signature : Signature Role language.Ty} → Var scope signature →
    Entry → Binding → List Frame → Environments Value signature.arguments →
      PIR.Proc (interface Role Entry Binding Schema language locals Value Packet)
        (Values (PortValue Value) signature.results)

def Program.denote {scope : List (Signature Role language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) (Packet := Packet) scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {pending Γ results} :
    Program Nat Role Binding Schema language locals scope pending Γ results →
      Environments Value Γ → InFlight Packet pending →
        PIR.Proc (interface Role Entry Binding Schema language locals Value Packet)
          (Values (PortValue Value) results)
  | .ret values, envs, _ => .done (Operands.eval (assemble envs) values)
  | .stop site role reason, _, _ =>
      .call (.stop ⟨role, entry, binding, path, site⟩ reason) fun reply => nomatch reply
  | .localCall site role callee args next, envs, _ =>
      .call (.local ⟨role, entry, binding, path, site⟩ callee
        (readLocal role (envs role) args)) fun value =>
          next.denote calls entry binding path (push envs value) ()
  | .send transfer value next, envs, _ =>
      .call (.send ⟨transfer.sender, entry, binding, path, transfer.site⟩ transfer.schema
        transfer.receiver (envs transfer.sender value)) fun packet =>
          next.denote calls entry binding path envs packet
  | .receive (transfer := transfer) next, envs, packet =>
      .call (.receive ⟨transfer.receiver, entry, binding, path, transfer.site⟩ transfer.schema
        transfer.sender packet) fun received =>
          next.denote calls entry binding path
            (push (port := (transfer.receiver, transfer.ty)) envs received) ()
  | .invoke site callee args next, envs, _ =>
      (calls callee.callee entry callee.binding (path ++ [.invocation site])
        (capture envs args)).bind fun values =>
          next.denote calls entry binding path (prepend envs values) ()
  | .repeat site count initial body next, envs, _ =>
      (PIR.repeatN count (fun acc =>
        (body.denote calls entry binding (path ++ [.iteration site acc.1])
          (prepend envs acc.2) ()).bind fun values =>
            .done (acc.1 + 1, values)) (0, Operands.eval (assemble envs) initial)).bind fun acc =>
              next.denote calls entry binding path (prepend envs acc.2) ()
  | .bind body next, envs, _ =>
      (body.denote calls entry binding path envs ()).bind fun values =>
        next.denote calls entry binding path (prepend envs values) ()

def Definitions.denote {scope : List (Signature Role language.Ty)}
    (definitions : Definitions Nat Role Binding Schema language locals scope) :
    CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) (Packet := Packet) scope :=
  match definitions with
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body => fun ref entry binding path envs =>
      match ref with
      | .here => body.denote previous.denote entry binding path envs ()
      | .there ref => previous.denote ref entry binding path envs

/-- Expand a common interaction into actual sender and receiver requests. -/
def expand : PIR.OperationInterpretation
    (Protocol.interface Role Entry Binding Schema language locals Value)
    (interface Role Entry Binding Schema language locals Value Packet)
  | .local origin callee args => .call (.local origin callee args) .done
  | .message origin schema receiver _ value =>
      .call (.send origin schema receiver value) fun packet =>
        .call (.receive { origin with role := receiver } schema origin.role packet) .done
  | .stop origin reason => .call (.stop origin reason) .done

end Zkc.Compiler.Participant

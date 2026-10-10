import Zkc.Compiler.Role.Syntax
import Zkc.Source.Protocol.Role.Interface

/-! An interpreter over actual role syntax and stored role definitions.
This module does not import the direct source-role interpreter or projection.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Role

open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.Protocol.Role (Environment interface CallMeaning)
open Zkc.Source.LocatedExecution (Frame)

variable {Party Entry Binding Schema : Type} {self : Party} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value : language.Ty → Type}

def Program.denote {scope : List (Signature Party language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {Γ results} :
    Program Nat self Binding Schema language locals scope Γ results →
      Environment Value self Γ →
        PIR.Proc (interface Party Entry Binding Schema language locals Value)
          (Environment Value self results)
  | .ret values, env => .done (env.capture values)
  | .stop site reason, _ =>
      .call (.stop ⟨entry, binding, path, site⟩ reason) fun reply => nomatch reply
  | .incomplete, _ => .halt .incomplete
  | .localCall site callee args next, env =>
      .call (.local ⟨entry, binding, path, site⟩ callee (env.read args)) fun value =>
        next.denote calls entry binding path (env.push value)
  | .send site schema receiver _ value next, env =>
      .call (.send ⟨entry, binding, path, site⟩ schema receiver (env value)) fun _ =>
        next.denote calls entry binding path env
  | .receive ty site schema sender _ next, env =>
      .call (.receive ty ⟨entry, binding, path, site⟩ schema sender) fun value =>
        next.denote calls entry binding path (env.push value)
  | .skip different next, env => next.denote calls entry binding path (env.skip different)
  | .invoke site callee args next, env =>
      (calls callee.callee entry callee.binding (path ++ [.invocation site])
        (env.capture args)).bind fun values =>
          next.denote calls entry binding path (env.prepend values)
  | .repeat (ports := ports) site count initial body next, env =>
      (PIR.repeatN count (fun (acc : Nat × Environment Value self ports) =>
        (body.denote calls entry binding (path ++ [.iteration site acc.1])
          (env.prepend acc.2)).bind fun values =>
            .done (acc.1 + 1, values)) (0, env.capture initial)).bind fun acc =>
              next.denote calls entry binding path (env.prepend acc.2)
  | .bind body next, env =>
      (body.denote calls entry binding path env).bind fun values =>
        next.denote calls entry binding path (env.prepend values)

def Definitions.denote {scope : List (Signature Party language.Ty)}
    (definitions : Definitions Nat self Binding Schema language locals scope) :
    CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope :=
  match definitions with
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body => fun ref entry binding path args =>
      match ref with
      | .here => body.denote previous.denote entry binding path args
      | .there ref => previous.denote ref entry binding path args

end Zkc.Compiler.Role

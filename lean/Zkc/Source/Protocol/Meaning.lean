import Zkc.Source.Protocol.Syntax
import Zkc.Source.LocatedExecution

/-! Interpret resolved common source in the existing complete execution semantics.

Protocol calls resolve to actual stored bodies. Primitive requests retain the
selected binding and traversal-derived origin. This is a joint reference
meaning; participant generation is a separate transformation.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol

open LocatedExecution (Frame Origin)

inductive Action (Role Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value : language.Ty → Type) where
  | local {signature : DefinitionSignature language.Ty}
      (origin : Origin Role Entry Binding) (callee : Var locals signature)
      (args : Values Value signature.arguments)
  | message {ty : language.Ty} (origin : Origin Role Entry Binding) (schema : Schema)
      (receiver : Role) (different : origin.role ≠ receiver) (value : Value ty)
  | stop (origin : Origin Role Entry Binding) (reason : PIR.Stop)

abbrev interface (Role Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value : language.Ty → Type) :
    PIR.Signature where
  Op := Action Role Entry Binding Schema language locals Value
  Reply
    | .local (signature := signature) .. => Value signature.result
    | .message (ty := ty) .. => Value ty
    | .stop .. => Empty

variable {Role Entry Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value : language.Ty → Type}

abbrev CallMeaning (scope : List (Signature Role language.Ty)) :=
  {signature : Signature Role language.Ty} → Var scope signature →
    Entry → Binding → List Frame → Values (PortValue Value) signature.arguments →
      PIR.Proc (interface Role Entry Binding Schema language locals Value)
        (Values (PortValue Value) signature.results)

def Program.denote {scope : List (Signature Role language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {Γ results} :
    Program Nat Role Binding Schema language locals scope Γ results →
      Environment (PortValue Value) Γ →
        PIR.Proc (interface Role Entry Binding Schema language locals Value)
          (Values (PortValue Value) results)
  | .ret values, env => .done (Operands.eval env values)
  | .stop site role reason, _ =>
      .call (.stop ⟨role, entry, binding, path, site⟩ reason) fun reply => nomatch reply
  | .localCall site role callee args next, env =>
      .call (.local ⟨role, entry, binding, path, site⟩ callee
        (localValues role (Operands.eval env args))) fun value =>
          next.denote calls entry binding path (Environment.push env value)
  | .message site schema sender receiver different value next, env =>
      .call (.message ⟨sender, entry, binding, path, site⟩ schema receiver different
        (env value)) fun received =>
          next.denote calls entry binding path
            (Environment.push (ty := (receiver, _)) env received)
  | .invoke site callee args next, env =>
      (calls callee.callee entry callee.binding (path ++ [.invocation site])
        (Operands.eval env args)).bind fun values =>
          next.denote calls entry binding path (Environment.prepend env values)
  | .repeat site count initial body next, env =>
      (PIR.repeatN count (fun acc =>
        (body.denote calls entry binding (path ++ [.iteration site acc.1])
          (Environment.prepend env acc.2)).bind fun values =>
            .done (acc.1 + 1, values)) (0, Operands.eval env initial)).bind fun acc =>
              next.denote calls entry binding path (Environment.prepend env acc.2)
  | .bind body next, env =>
      (body.denote calls entry binding path env).bind fun values =>
        next.denote calls entry binding path (Environment.prepend env values)

/-- A callee receives only its declared arguments; the caller context is not captured. -/
def Definitions.denote {scope : List (Signature Role language.Ty)}
    (definitions : Definitions Nat Role Binding Schema language locals scope) :
    CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) scope :=
  match definitions with
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body => fun ref entry binding path args =>
      match ref with
      | .here => body.denote previous.denote entry binding path args.get
      | .there ref => previous.denote ref entry binding path args

/-- The newest reference denotes the actual body under its selected binding. -/
theorem Definitions.denote_here {scope : List (Signature Role language.Ty)}
    (previous : Definitions Nat Role Binding Schema language locals scope)
    (signature : Signature Role language.Ty)
    (body : Program Nat Role Binding Schema language locals scope
      signature.arguments signature.results)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Values (PortValue Value) signature.arguments) :
    (previous.snoc signature body).denote .here entry binding path args =
      body.denote previous.denote entry binding path args.get := rfl

/-- Invoking a shared body preserves its complete execution and ordered result binding. -/
theorem Program.run_invoke {scope : List (Signature Role language.Ty)}
    (definitions : Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty} {Γ results} (site : Nat)
    (callee : Instance Role Binding language.Ty scope signature)
    (args : Operands Γ signature.arguments)
    (next : Program Nat Role Binding Schema language locals scope (signature.results ++ Γ) results)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (env : Environment (PortValue Value) Γ) {S E : Type}
    (handler : PIR.Handler (interface Role Entry Binding Schema language locals Value) S E)
    (state : S) :
    ((Program.invoke site callee args next).denote definitions.denote
      entry binding path env).run handler state =
      ((definitions.denote callee.callee entry callee.binding (path ++ [.invocation site])
        (Operands.eval env args)).run handler state).follow fun values =>
          (next.denote definitions.denote entry binding path
            (Environment.prepend env values)).run handler := by
  exact PIR.run_bind _ _ _ _

/-- A stopped child retains its full result; the parent's normal continuation is absent. -/
theorem Program.run_invoke_stopped {scope : List (Signature Role language.Ty)}
    (definitions : Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty} {Γ results} (site : Nat)
    (callee : Instance Role Binding language.Ty scope signature)
    (args : Operands Γ signature.arguments)
    (next : Program Nat Role Binding Schema language locals scope (signature.results ++ Γ) results)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (env : Environment (PortValue Value) Γ) {S E : Type}
    (handler : PIR.Handler (interface Role Entry Binding Schema language locals Value) S E)
    (state final : S) (events : List E) (reason : PIR.Stop)
    (stopped : (definitions.denote callee.callee entry callee.binding (path ++ [.invocation site])
      (Operands.eval env args)).run handler state = ⟨.stopped reason, final, events⟩) :
    ((Program.invoke site callee args next).denote definitions.denote
      entry binding path env).run handler state = ⟨.stopped reason, final, events⟩ := by
  rw [run_invoke, stopped]
  rfl

end Zkc.Source.Protocol

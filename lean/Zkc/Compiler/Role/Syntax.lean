import Zkc.Source.Protocol.Syntax

/-! Independently runnable role syntax. Receives contain no sender operand;
sends have only a local operand and do not deliver a value to another role.
Foreign ports are static metadata, introduced by `skip` without a runtime value.
Stored calls, fixed loops and shared continuations remain structural.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Role

open Zkc.Source Zkc.Source.Protocol

inductive Program (Count : Type) {Party : Type} (self : Party) (Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (scope : List (Signature Party language.Ty)) :
    List (Port Party language.Ty) → List (Port Party language.Ty) → Type where
  | ret {Γ results} (values : Operands Γ results) :
      Program Count self Binding Schema language locals scope Γ results
  | stop {Γ results} (site : Nat) (reason : PIR.Stop) :
      Program Count self Binding Schema language locals scope Γ results
  | incomplete {Γ results} : Program Count self Binding Schema language locals scope Γ results
  | localCall {Γ results signature} (site : Nat)
      (callee : Var locals signature) (args : Operands Γ (owned self signature.arguments))
      (next : Program Count self Binding Schema language locals scope
        ((self, signature.result) :: Γ) results) :
      Program Count self Binding Schema language locals scope Γ results
  | send {Γ results ty} (site : Nat) (schema : Schema) (receiver : Party)
      (different : receiver ≠ self) (value : Var Γ (self, ty))
      (next : Program Count self Binding Schema language locals scope Γ results) :
      Program Count self Binding Schema language locals scope Γ results
  | receive {Γ results} (ty : language.Ty) (site : Nat) (schema : Schema) (sender : Party)
      (different : sender ≠ self)
      (next : Program Count self Binding Schema language locals scope ((self, ty) :: Γ) results) :
      Program Count self Binding Schema language locals scope Γ results
  | skip {Γ results owner ty} (different : owner ≠ self)
      (next : Program Count self Binding Schema language locals scope ((owner, ty) :: Γ) results) :
      Program Count self Binding Schema language locals scope Γ results
  | invoke {Γ results signature} (site : Nat)
      (callee : Instance Party Binding language.Ty scope signature)
      (args : Operands Γ signature.arguments)
      (next : Program Count self Binding Schema language locals scope (signature.results ++ Γ) results) :
      Program Count self Binding Schema language locals scope Γ results
  | repeat {Γ results ports} (site : Nat) (count : Count) (initial : Operands Γ ports)
      (body : Program Count self Binding Schema language locals scope (ports ++ Γ) ports)
      (next : Program Count self Binding Schema language locals scope (ports ++ Γ) results) :
      Program Count self Binding Schema language locals scope Γ results
  | bind {Γ ports results}
      (body : Program Count self Binding Schema language locals scope Γ ports)
      (next : Program Count self Binding Schema language locals scope (ports ++ Γ) results) :
      Program Count self Binding Schema language locals scope Γ results

inductive Definitions (Count : Type) {Party : Type} (self : Party) (Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) :
    List (Signature Party language.Ty) → Type where
  | nil : Definitions Count self Binding Schema language locals []
  | snoc {scope : List (Signature Party language.Ty)}
      (previous : Definitions Count self Binding Schema language locals scope)
      (signature : Signature Party language.Ty)
      (body : Program Count self Binding Schema language locals scope
        signature.arguments signature.results) :
      Definitions Count self Binding Schema language locals (signature :: scope)

end Zkc.Compiler.Role

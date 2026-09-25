import Zkc.Source.Protocol.Syntax
import Zkc.Source.LocatedExecution
import Zkc.Source.Protocol.Role.Context

/-! The common observation boundary of two independently defined role meanings.
A receive request carries a type and peer/schema metadata, never a peer value.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol.Role

open LocatedExecution (Frame Origin)

structure Location (Entry Binding : Type) where
  entry : Entry
  binding : Binding
  path : List Frame
  site : Nat
  deriving DecidableEq, Repr

def Location.origin {Party Entry Binding : Type} (location : Location Entry Binding) (self : Party) :
    Origin Party Entry Binding := ⟨self, location.entry, location.binding, location.path, location.site⟩

inductive Action (Party Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value : language.Ty → Type) where
  | local {signature : DefinitionSignature language.Ty}
      (location : Location Entry Binding) (callee : Var locals signature)
      (args : Values Value signature.arguments)
  | send {ty : language.Ty} (location : Location Entry Binding) (schema : Schema)
      (receiver : Party) (value : Value ty)
  | receive (ty : language.Ty) (location : Location Entry Binding) (schema : Schema) (sender : Party)
  | stop (location : Location Entry Binding) (reason : PIR.Stop)

abbrev interface (Party Entry Binding Schema : Type) (language : Language)
    (locals : List (DefinitionSignature language.Ty)) (Value : language.Ty → Type) :
    PIR.Signature where
  Op := Action Party Entry Binding Schema language locals Value
  Reply
    | .local (signature := signature) .. => Value signature.result
    | .send .. => Unit
    | .receive ty .. => Value ty
    | .stop .. => Empty

variable {Party Entry Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value : language.Ty → Type}

abbrev CallMeaning (self : Party) (scope : List (Signature Party language.Ty)) :=
  {signature : Signature Party language.Ty} → Var scope signature →
    Entry → Binding → List Frame → Environment Value self signature.arguments →
      PIR.Proc (interface Party Entry Binding Schema language locals Value)
        (Environment Value self signature.results)

end Zkc.Source.Protocol.Role

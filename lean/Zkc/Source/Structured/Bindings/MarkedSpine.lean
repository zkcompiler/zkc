module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Lexical marks around selected operations of a single straight-line
region. Source denotation establishes which observations actually run. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Bindings
open Zkc.Source

structure MarkedSpine (Event : Type) where
  events : List (List String × Event)
  trailing : List String

/-- Never cross into a callback or through a stop to find a later event.
Preserve empty labels, repeated labels and their original order. -/
def markedSpine {Event : Type} (select : ProtocolOp → Option Event) (body : RawRegion Ty ProtocolOp) :
    Option (MarkedSpine Event) :=
  let rec visit (pending : List String) (events : List (List String × Event)) :
      RawRegion Ty ProtocolOp → Option (MarkedSpine Event)
    | .letOp (.mark label) _ _ .nil tail => visit (label :: pending) events tail
    | .letOp op _ _ .nil tail =>
      match select op with
      | some event => visit [] ((pending.reverse, event) :: events) tail
      | none => visit pending events tail
    | .ret _ => some ⟨events.reverse, pending.reverse⟩
    | _ => none
  visit [] [] body

end Zkc.Source.Structured.Bindings

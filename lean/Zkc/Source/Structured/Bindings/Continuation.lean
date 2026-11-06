module

public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! References that a straight-line continuation inherits from before a
selected repeat. Only a unique occurrence and a well-typed outer operand
can identify a port. Denotation still checks the entire continuation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Bindings
open Zkc.Source

inductive OperandUse where
  | operation (select : ProtocolOp → Bool) (operand : Nat)
  | returned (position : Nat)

def OperandUse.beforePrefix (depth index : Nat) : Option Nat :=
  if depth ≤ index then some (index - depth) else none

def OperandUse.collect (use : OperandUse) (depth : Nat) :
    RawRegion Ty ProtocolOp → Option (List (Option Nat))
  | .letOp op args results .nil next => do
    let rest ← use.collect (depth + results.length) next
    match use with
    | .operation select i =>
      if select op then return (args[i]?.bind (OperandUse.beforePrefix depth)) :: rest else return rest
    | .returned _ => return rest
  | .ret args =>
    match use with
    | .operation .. => some []
    | .returned i => some [args[i]?.bind (OperandUse.beforePrefix depth)]
  | _ => none

/-- Resolve one use back to a value in the pre-repeat environment. Shadowing
by a result, a missing operand or an ambiguous operation fails the lookup. -/
def RepeatSite.outerOperand (site : RepeatSite) (ty : Ty) (use : OperandUse) : Option (Var site.context ty) := do
  let [some index] ← use.collect site.spec.state.length site.next.erase | none
  Var.decode site.context ty index

/-- Lexical marks in traversal order. A process equation establishes which of
these marks are actually reached; the inventory alone does not. -/
def RepeatSite.continuationMarks (site : RepeatSite) (context : ProtocolContext) : List (String × String) :=
  site.next.erase.operations.filterMap fun op ↦ match op with
    | .mark label => some (label, qualifyProtocolSite context.applicationPrefix label)
    | _ => none

/-- The original repeat operation, including its environment, masks, trip
limit, iteration events and callback. Stops bypass the continuation. -/
def RepeatSite.iterations {I : PIR.Signature} (site : RepeatSite) (meaning : RegionMeaning protocolDialect I)
    (env : Environment meaning.Value site.context) : PIR.Process I (Values meaning.Value site.spec.state) :=
  meaning.operation (.repeat site.spec site.site) (Operands.eval env site.operands)
    (.cons (fun values ↦ site.body.denote meaning values.get) .nil)

theorem RepeatSite.denote_region {I : PIR.Signature} (site : RepeatSite) (meaning : RegionMeaning protocolDialect I)
    (env : Environment meaning.Value site.context) :
    site.region.denote meaning env = (site.iterations meaning env).bind
      (fun results ↦ site.next.denote meaning (env.prepend results)) := rfl

end Zkc.Source.Structured.Bindings

module

public import Zkc.Source.Structured.Bindings.Selection
public import Zkc.Source.Structured.ProtocolAlgebra

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

/-- A bounded source callback runs with both the input and output role
projections, including on loops carrying private and public state together. -/
def RepeatSite.maskedIteration {V : Ty → Type} {I : PIR.Signature} (site : RepeatSite)
    (algebra : ProtocolAlgebra V I) (table : ProtocolTable V I) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component V) site.spec.captures)
    (state : Values (Component V) site.spec.state) (index : Nat) :=
  let mask := maskValues self (context.mapScopes site.spec.stateScopes)
  (algebra.iteration context site.site index
    (site.body.denote (algebra.meaning table context self)
      (Values.cons (some (algebra.index index)) ((mask state).append captures)).get)).bind
    fun results ↦ .done (mask results)

theorem RepeatSite.maskedIterations {V : Ty → Type} {I : PIR.Signature} (site : RepeatSite)
    (algebra : ProtocolAlgebra V I) (table : ProtocolTable V I) (context : ProtocolContext) (self : Nat)
    (env : Environment (Component V) site.context) (countValue : Component V .index)
    (state : Values (Component V) site.spec.state) (captures : Values (Component V) site.spec.captures)
    (selected : Operands.eval env site.operands = .cons countValue (state.append captures))
    (active : (site.spec.roles.map context.roles).contains self = true)
    {count : Nat} (decoded : countValue.bind algebra.count = some count) (bound : count ≤ site.spec.maximum) :
    site.iterations (algebra.meaning table context self) env =
      Finite.fold (site.maskedIteration algebra table context self captures) (List.range count)
        (maskValues self (context.mapScopes site.spec.stateScopes) state) := by
  unfold RepeatSite.iterations
  erw [selected]
  change algebra.repeatProcess site.spec context self site.site countValue
    (Values.split site.spec.state (state.append captures)).1 (Values.split site.spec.state (state.append captures)).2
    (fun args ↦ site.body.denote (algebra.meaning table context self) args.get) = _
  rw [Values.split_append]
  simp only [ProtocolAlgebra.repeatProcess, active, decoded, bound, ite_true,
    Finite.execute, Finite.Domain.admit, Finite.admitThen]
  rfl

/-- Present a reached bounded repeat as its exact ordered fold. A fully
visible state needs no projection; callbacks still execute in the algebra's
real iteration frame, and their stops skip every remaining item. -/
theorem RepeatSite.visibleIterations {V : Ty → Type} {I : PIR.Signature} (site : RepeatSite)
    (algebra : ProtocolAlgebra V I) (table : ProtocolTable V I) (context : ProtocolContext) (self : Nat)
    (env : Environment (Component V) site.context) (countValue : Component V .index)
    (state : Values (Component V) site.spec.state) (captures : Values (Component V) site.spec.captures)
    (selected : Operands.eval env site.operands = .cons countValue (state.append captures))
    (active : (site.spec.roles.map context.roles).contains self = true)
    (visible : ∀ out : Values (Component V) site.spec.state, maskValues self (context.mapScopes site.spec.stateScopes) out = out)
    {count : Nat} (decoded : countValue.bind algebra.count = some count) (bound : count ≤ site.spec.maximum) :
    site.iterations (algebra.meaning table context self) env =
      Finite.fold (fun current index ↦ algebra.iteration context site.site index
        (site.body.denote (algebra.meaning table context self)
          (Values.cons (some (algebra.index index)) (current.append captures)).get)) (List.range count) state := by
  rw [site.maskedIterations algebra table context self env countValue state captures selected active decoded bound]
  rw [visible]
  congr 1
  funext current index
  simp only [maskedIteration, visible, PIR.Process.bind_done]


end Zkc.Source.Structured.Bindings

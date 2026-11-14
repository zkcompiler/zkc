module

public import Zkc.Core.Admissible

public section

/-! The maximum of a loop of a protocol body, from the facts.

A `repeat` with a run-time count states a maximum. The reference gives a loop of a protocol
body the bound `hi(b)` that each participant knows of the count, and writes no maximum; the
lowering writes 0. `fillMaxima` writes, at each such `repeat`, the largest upper end that its
participants know of their copies of the count, read from the facts of the normal form at
that instruction.

The traversal is the one of the check of facts (`justifyProtocol`), calling the same
functions for what the roles know, and collects the bound of each `repeat` in the order of
the body. The normal form keeps the `repeat`s of a body and their order, so the bounds are
written into the body as written in that order. It is outside the proved part: what it writes
is checked by admission.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Bounds

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The largest upper end that the participants know of their copies of a count, at the
levels given; none when a participant knows no upper end. A participant whose region never
runs asks for nothing, as in the check (`RoleFacts.countsWithin`). -/
def RoleFacts.countBound (state : RoleFacts) : List Nat → List Nat → Option Nat
  | role :: participants, count :: counts =>
      match cond (state.view role).dead (some 0) ((state.view role).hi count),
          RoleFacts.countBound state participants counts with
      | some own, some others => some (max own others)
      | _, _ => none
  | _, _ => some 0

/-- The stated maximum and the bound of an instruction that is a `repeat` with a run-time
count; nothing for any other instruction. In a region that never runs the bound is 0. -/
def ProtocolOp.repeatBound (state : RoleFacts) :
    ProtocolOp operations functions protocols deployed → List Nat → List (Nat × Option Nat)
  | .repeat participants (.runtime maximum) _ _ _ _, levels =>
      [(maximum, cond state.dead (some 0)
        (state.countBound participants (levels.take participants.length)))]
  | _, _ => []

mutual
  /-- What a region of a protocol body returns, and the bounds of its `repeat`s with a
  run-time count in the order of the body. The traversal goes on past an application that is
  not justified, with nothing known of its results: the bounds after it are still read, so
  that admission reports that application and not a loop after it. -/
  def boundsProtocol (state : RoleFacts) {Γ out : List Located} :
      Region (ProtocolDialect operations functions protocols deployed) Γ out →
        Outcome × List (Nat × Option Nat)
    | .ret values => (some (state.returned state.depth values), [])
    | .stop _ => (none, [])
    | .letOp op arguments bodies next =>
        -- a `repeat` over a value is not asked its maximum here: the bound is what is read
        let after := match (match op with
            | .repeat _ (.runtime _) _ _ _ _ => Except.ok (state.bind op.results.length)
            | _ => ProtocolOp.justify [] state op (Scope.numbers state.depth arguments)) with
          | .error _ => state.bind op.results.length
          | .ok after => after
        let (outcomes, inner) := boundsProtocols
          (ProtocolOp.regionState state op (Scope.numbers state.depth arguments)) 0 bodies
        let (outcome, rest) := boundsProtocol
          ((ProtocolOp.joined state.depth op outcomes after).inScope op.results) next
        (outcome,
          ProtocolOp.repeatBound state op (Scope.numbers state.depth arguments) ++ inner ++ rest)
    | .bind (mid := mid) body next =>
        let (outcome, inner) := boundsProtocol state body
        let (after, rest) := boundsProtocol
          (((state.bind mid.length).withResults state.depth mid outcome.intervals).inScope mid) next
        (after, inner ++ rest)

  def boundsProtocols (stateOf : Nat → RoleFacts) (number : Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions protocols deployed) signatures →
        List Outcome × List (Nat × Option Nat)
    | .nil => ([], [])
    | .cons body tail =>
        let (outcome, inner) := boundsProtocol (stateOf number) body
        let (outcomes, rest) := boundsProtocols stateOf (number + 1) tail
        (outcome :: outcomes, inner ++ rest)
end

/-- The bounds of the `repeat`s with a run-time count of a protocol, in the order of its body,
from the facts of its normal form. -/
def ProtocolDefinition.repeatBounds {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header) :
    List (Nat × Option Nat) :=
  (boundsProtocol ((RoleFacts.start header.inputs.length).inScope header.inputs)
    definition.normal.body).2

/-- The bounds of each protocol of a program, in program order. -/
def Protocols.repeatBounds {typeTable : TypeTable} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      List (List (Nat × Option Nat))
  | _, .nil => []
  | _, .snoc earlier definition _ => earlier.repeatBounds ++ [definition.repeatBounds]

end Bounds

namespace Raw

mutual
  /-- A region with the maxima of its `repeat`s with a run-time count taken from a list, in
  the order of the body; a `repeat` whose bound is absent keeps its maximum. -/
  partial def ProtocolRegion.withMaxima :
      ProtocolRegion → StateM (List (Nat × Option Nat)) ProtocolRegion
    | .ret values => pure (.ret values)
    | .stop reason => pure (.stop reason)
    | .block outputs body next => do
        let body ← body.withMaxima
        return .block outputs body (← next.withMaxima)
    | .step instruction next => do
        let instruction ← match instruction with
          | .repeat participants (.runtime maximum counts) carried captures collected body => do
              let bound ← modifyGet fun bounds =>
                match bounds with
                | (_, bound) :: rest => (bound, rest)
                | [] => (none, [])
              let body ← body.withMaxima
              pure (ProtocolStep.repeat participants (.runtime (bound.getD maximum) counts) carried
                captures collected body)
          | .repeat participants count carried captures collected body => do
              pure (ProtocolStep.repeat participants count carried captures collected
                (← body.withMaxima))
          | .choose participants tags tag captures outputs arms => do
              let arms ← arms.toList.mapM fun arm => arm.withMaxima
              pure (ProtocolStep.choose participants tags tag captures outputs (.ofList arms))
          | other => pure other
        return .step instruction (← next.withMaxima)
end

end Raw

/-- A package with the maximum of every `repeat` with a run-time count written from the
facts of its normal form. A package that does not elaborate is left as it is. -/
def fillMaxima (package : Raw.Package) : Raw.Package :=
  match elaborate package with
  | .error _ => package
  | .ok typed =>
      let bounds := typed.program.protocols.repeatBounds
      { package with
        protocols := (package.protocols.zip bounds).map fun (protocol, found) =>
          { protocol with body := (protocol.body.withMaxima.run found).1 } }

end Zkc.Core

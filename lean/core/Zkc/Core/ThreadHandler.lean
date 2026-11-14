module

public import Zkc.Core.ThreadDefinition
public import Zkc.Core.Specialize

public section

/-! The handler of a threading step.

The structural theorem of a step says that the image of a definition is the definition
interpreted by a handler (`definition_threads`). This module defines the handler, from the
meaning of the rule and the marks of the step (`Core/ThreadMarks.lean`):

- `threadAct`: what a side that holds exactly one transcript role does at an effect, given
  the mark of the effect's site. At a marked site it performs the rule's action for the
  side: the prover's `send` of a rewritten exchange, the verifier's `receive` of it, the
  owner's `draw` of a rewritten draw and the receiver's `receive` of its announcement. At
  every other site it performs the effect and leaves the state as it is.
- `threadHandler`: the handler that reads the mark of every effect's site from a function
  of sites; `marksBelow` gives the marks of a definition that is reached under a path.
- `Follows`: a handler acts, on every effect below a path, as the marks of a definition
  say. A handler that follows a definition's marks follows the marks of every callee below
  the site of its application.
- `stepFits`: what fits the images of the protocols of a program, for the structural
  theorem's statement about callees (`CalleesThread`): a side with exactly one transcript
  role and a handler that follows the callee's marks.

A side that holds both transcript roles has no such handler: an exchange between two roles
of the side performs no effect, so no handler of effects can absorb its value.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Handler

variable {model : Model} {operations : List OperationSignature} {t : Threads}

/-- An effect performed as it is, with the state unchanged. -/
@[expose] def passEffect {S : Type} (effect : Effect model.Value) (state : S) :
    PIR.Process (Effects model) (Effect.Reply effect × S) :=
  .call effect fun reply => .done (reply, state)

/-- What the side of the prover does at an effect whose site has the mark. -/
@[expose] def proverAct (sem : RuleMeaning model t operations) :
    Option (Mark operations) → (effect : Effect model.Value) → ThreadState model t true false →
      PIR.Process (Effects model) (Effect.Reply effect × ThreadState model t true false)
  | some (.exchange place number), .send site type value, state =>
      (sem.exchange true false place number site type value state).bind fun result =>
        .done (PUnit.unit, result.2)
  | some (.draw true place number (output := output) law), .receive site type, state =>
      if same : output = type then
        (sem.draw true false place number site law state).bind fun result =>
          .done (cast (congrArg model.Value same) result.1.1, result.2)
      else passEffect (.receive site type) state
  | some (.draw false place number (output := output) law), .draw site row inputs, state =>
      if same : output = row.output then
        (sem.draw true false place number site law state).bind fun result =>
          .done (cast (congrArg model.Value same) result.1.1, result.2)
      else passEffect (.draw site row inputs) state
  | _, effect, state => passEffect effect state

/-- What the side of the verifier does at an effect whose site has the mark. -/
@[expose] def verifierAct (sem : RuleMeaning model t operations) :
    Option (Mark operations) → (effect : Effect model.Value) → ThreadState model t false true →
      PIR.Process (Effects model) (Effect.Reply effect × ThreadState model t false true)
  | some (.exchange place number), .receive site type, state =>
      (sem.exchange false true place number site type PUnit.unit state).bind fun result =>
        .done (result.1, result.2)
  | some (.draw true place number (output := output) law), .draw site row inputs, state =>
      if same : output = row.output then
        (sem.draw false true place number site law state).bind fun result =>
          .done (cast (congrArg model.Value same) result.1.2, result.2)
      else passEffect (.draw site row inputs) state
  | some (.draw false place number (output := output) law), .receive site type, state =>
      if same : output = type then
        (sem.draw false true place number site law state).bind fun result =>
          .done (cast (congrArg model.Value same) result.1.2, result.2)
      else passEffect (.receive site type) state
  | _, effect, state => passEffect effect state

/-- What a side does at an effect whose site has the mark, for the memberships of the
prover and of the verifier. A side that holds neither or both performs the effect. -/
@[expose] def threadAct (sem : RuleMeaning model t operations) (mark : Option (Mark operations)) :
    (prover verifier : Bool) → (effect : Effect model.Value) →
      ThreadState model t prover verifier →
        PIR.Process (Effects model) (Effect.Reply effect × ThreadState model t prover verifier)
  | true, false => proverAct sem mark
  | false, true => verifierAct sem mark
  | true, true => fun effect state => passEffect effect state
  | false, false => fun effect state => passEffect effect state

/-- The handler of a step: at every effect, what the mark of its site says. -/
@[expose] def threadHandler (sem : RuleMeaning model t operations)
    (marks : Site → Option (Mark operations)) (prover verifier : Bool) :
    ThreadHandler model t prover verifier :=
  fun effect state => threadAct sem (marks effect.site) prover verifier effect state

/-- A path without a prefix. -/
@[expose] def pathBelow : List Nat → List Nat → Option (List Nat)
  | [], rest => some rest
  | _ :: _, [] => none
  | first :: path, other :: rest => if first = other then pathBelow path rest else none

/-- The marks of a definition that is reached under a path, as a function of the sites of
its effects: a site that is not below the path has no mark. -/
@[expose] def marksBelow (path : List Nat) (marks : Site → Option (Mark operations)) :
    Site → Option (Mark operations) :=
  fun site =>
    match pathBelow path site.path with
    | some rest => marks ⟨rest, site.definition, site.number⟩
    | none => none

/-- The side holds exactly one of the two transcript roles. -/
@[expose] def OneTranscriptRole (prover verifier : Bool) : Prop :=
  (prover = true ∧ verifier = false) ∨ (prover = false ∧ verifier = true)

/-- A handler acts, on every effect below a path, as the marks of the definition that is
reached under the path say. -/
@[expose] def Follows (sem : RuleMeaning model t operations) (prover verifier : Bool)
    (handler : ThreadHandler model t prover verifier) (path : List Nat)
    (marks : Site → Option (Mark operations)) : Prop :=
  ∀ (effect : Effect model.Value) (rest : List Nat), effect.site.path = path ++ rest →
    ∀ state : ThreadState model t prover verifier,
      handler effect state =
        threadAct sem (marks ⟨rest, effect.site.definition, effect.site.number⟩) prover verifier
          effect state

/-- A handler performs every effect below a path as it is. -/
@[expose] def PassesBelow {S : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S) (path : List Nat) :
    Prop :=
  ∀ (effect : Effect model.Value) (rest : List Nat), effect.site.path = path ++ rest →
    ∀ state : S, handler effect state = passEffect effect state

/-- Every protocol of a table is passed by a handler that performs, as it is, every effect
below the path under which the protocol is reached. -/
@[expose] def TablePasses {protocols : List ProtocolHeader} (table : ProtocolTable model protocols) :
    Prop :=
  ∀ {S : Type} (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S)
    {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) header.inputs),
    PassesBelow handler path → PIR.Passes handler ((table.get callee) path side arguments)

/-- What fits the images of the protocols of a program: a side with exactly one transcript
role, and a handler that follows the marks of the protocol for the image's roles. -/
@[expose] def stepFits (sem : RuleMeaning model t operations) :
    {protocols : List ProtocolHeader} → MarkTable operations protocols →
      Values (CalleeFit model t) protocols
  | [], _ => .nil
  | _ :: _, marks =>
      .cons (fun inner path _ prover verifier _ _ handler =>
          OneTranscriptRole prover verifier ∧
            Follows sem prover verifier handler path (marks.get .here inner))
        (stepFits sem marks.tail)

/-- What fits the images of one protocol. -/
theorem stepFits_get (sem : RuleMeaning model t operations) :
    ∀ {protocols : List ProtocolHeader} (marks : MarkTable operations protocols)
      {header : ProtocolHeader} (callee : Var protocols header),
      (stepFits sem marks).get callee =
        fun inner path _ prover verifier _ _ handler =>
          OneTranscriptRole prover verifier ∧
            Follows sem prover verifier handler path (marks.get callee inner)
  | [], _, _, callee => callee.elimNil
  | _ :: _, marks, _, callee => by
      cases callee with
      | here => rfl
      | there callee =>
          match marks with
          | .cons _ rest => exact stepFits_get sem rest callee

end Handler

end Zkc.Core

module

public import Zkc.Core.ThreadTheorem

public section

/-! The structural theorem of a threading step, for the image of a definition.

`definition_threads`: the image of a definition for a pair of transcript roles, which
takes the two threaded values before the definition's inputs and returns them before its
outputs, is the definition interpreted by a handler that fits its body, from the two
values the side holds. The image has the definition's identity, so the effects of the two
processes have the same sites.

`definition_plain`: the image with the definition's own header has the definition's
meaning, for every side.

Both are stated over the tables of the callees (`CalleesThread`, `PlainCallees`); a
program is covered by using them along the protocols in program order.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Definition

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {t : Threads} {rule : Rule t operations functions}
  {sem : RuleMeaning model t operations} {functionTable : FunctionTable model functions}
  {oldTable : ProtocolTable model old} {newTable : ProtocolTable model new}
  {table : CalleeTable t.header old new} {fits : Values (CalleeFit model t) old}

/-- The image of a definition that threads is the definition under the handler. -/
theorem definition_threads (quiet : QuietTable functionTable)
    (sound : RuleSound rule sem functionTable)
    (callees : CalleesThread table oldTable newTable fits) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions old header) (place : Place)
    (image : ProtocolDefinition operations functions new (t.header (some place.roles) header))
    (threads : threadRegion t rule table place definition.body
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).1
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.1
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.2 = .ok image.body)
    (identity : Nat) (path : List Nat) (side : Side)
    (handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier))
    (fit : Fits t rule sem functionTable oldTable table fits place side (ownSites identity path)
      handler definition.body)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (arguments : Values (SideValue model side) header.inputs) :
    image.meaning model functionTable newTable identity path side
        (.cons state.1 (.cons state.2 arguments)) =
      ((definition.meaning model functionTable oldTable identity path side
          arguments).interpretWith handler state).bind fun result =>
        .done (threadedValues result) := by
  have start := afterTwo_agrees (Value := SideValue model side)
    (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
    (old := Environment.empty) (new := Environment.empty) (fun reference => reference.elimNil)
    (t.first place.roles) (t.second place.roles) state.1 state.2 arguments
  have ih := threadRegion_meaning (label := ownSites identity path) (handler := handler) quiet
    sound callees definition.body _ _ _ image.body threads fit _ _ start.1
  exact restate (Prod.ext start.2.1 start.2.2) ih

/-- The image of a definition with the definition's own header is the definition. -/
theorem definition_plain (callees : PlainCallees table oldTable newTable)
    {header : ProtocolHeader} (definition : ProtocolDefinition operations functions old header)
    (image : ProtocolDefinition operations functions new header)
    (copies : plainRegion t table definition.body (Renaming.identity header.inputs) =
      .ok image.body) (identity : Nat) :
    image.meaning model functionTable newTable identity =
      definition.meaning model functionTable oldTable identity :=
  funext fun path => funext fun side => funext fun arguments =>
    plainRegion_meaning (label := ownSites identity path) callees definition.body _ image.body
      copies _ _ (Renaming.identity_agrees header.inputs arguments)

end Definition

end Zkc.Core

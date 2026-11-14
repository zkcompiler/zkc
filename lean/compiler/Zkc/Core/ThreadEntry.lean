module

public import Zkc.Core.ThreadHandler

public section

/-! What the entry of a threading step does around its threaded body.

A rule rewrites the declared entry with `Rule.entry`: it makes the two threaded values
before the threaded body and consumes them after it, and it may change the ports of the
entry. `EntryMeaning` says what that is for a side, in three parts:

- `arguments`: the inputs of the entry before the step, from the inputs of the rewritten
  entry;
- `start`: the two threaded values the body starts from, as a process of the inputs of the
  rewritten entry;
- `finish`: the outputs of the rewritten entry, as a process of the outputs of the entry
  before the step and the two final threaded values.

`EntrySound` is the obligation of a rule: whatever the threaded body is, when its meaning
is a function of the entry's inputs and the two values it starts from, the region that
the rule makes of it runs `start`, the body and `finish` in this order; and `start` and
`finish` perform no effect over functions that perform none.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Entry

variable {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What a threaded region returns, taken apart: the region's own results and the two
final threaded values. -/
@[expose] def threadedParts {model : Model} {t : Threads} {side : Side} {roles : TranscriptRoles}
    {out : List Located} (values : Values (SideValue model side) (t.states roles ++ out)) :
    Values (SideValue model side) out ×
      ThreadState model t (side roles.prover) (side roles.verifier) :=
  (values.tail.tail, (values.get .here, values.get (.there .here)))

/-- What the entry of a step does for a side before and after its threaded body. -/
structure EntryMeaning (model : Model) (t : Threads) (rule : Rule t operations functions) where
  /-- The inputs of the entry before the step. -/
  arguments : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
    Values (SideValue model side) (rule.entryPorts roles header).inputs →
      Values (SideValue model side) header.inputs
  /-- The two threaded values that the body starts from. -/
  start : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
    Values (SideValue model side) (rule.entryPorts roles header).inputs →
      PIR.Process (Effects model) (ThreadState model t (side roles.prover) (side roles.verifier))
  /-- The outputs of the rewritten entry, from the outputs of the entry before the step
  and the two final threaded values. -/
  finish : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
    Values (SideValue model side) header.outputs ×
        ThreadState model t (side roles.prover) (side roles.verifier) →
      PIR.Process (Effects model)
        (Values (SideValue model side) (rule.entryPorts roles header).outputs)

/-- The entry of a rule runs as its meaning says. -/
structure EntrySound {model : Model} {t : Threads} (rule : Rule t operations functions)
    (entry : EntryMeaning model t rule) (functionTable : FunctionTable model functions) : Prop where
  /-- The region that the rule makes of a threaded body is `start`, the body, `finish`. -/
  runs : ∀ {protocols : List ProtocolHeader} {deployed : Bool}
    (table : ProtocolTable model protocols) (label : Nat → Site) (side : Side) (place : Place)
    (header : ProtocolHeader)
    (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
      Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs)))
    (region : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (rule.entryPorts place.roles header).inputs)
      (rule.entryPorts place.roles header).outputs),
    rule.entry place header body = .ok region →
    ∀ (inner : Values (SideValue model side) header.inputs →
        ThreadState model t (side place.roles.prover) (side place.roles.verifier) →
          PIR.Process (Effects model)
            (Values (SideValue model side) (t.states place.roles ++ header.outputs))),
    (∀ {Δ : List Located} (rename : Renaming (bindAll [] header.inputs) Δ)
        (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
        (threaded : Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs)),
        body rename first second = .ok threaded →
        ∀ (arguments : Values (SideValue model side) header.inputs)
          (env : Environment (SideValue model side) Δ),
          rename.Agrees (Environment.ofValues arguments) env →
            threaded.denote (labelledMeaning model label functionTable table side) env =
              inner arguments (env first, env second)) →
    ∀ arguments : Values (SideValue model side) (rule.entryPorts place.roles header).inputs,
      region.denote (labelledMeaning model label functionTable table side)
          (Environment.ofValues arguments) =
        (entry.start side place.roles header arguments).bind fun state =>
          (inner (entry.arguments side place.roles header arguments) state).bind fun result =>
            entry.finish side place.roles header (threadedParts result)
  /-- Making the two values performs no effect. -/
  startQuiet : QuietTable functionTable → ∀ (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs),
    (entry.start side roles header arguments).Quiet
  /-- Consuming the two values performs no effect. -/
  finishQuiet : QuietTable functionTable → ∀ (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader)
    (result : Values (SideValue model side) header.outputs ×
      ThreadState model t (side roles.prover) (side roles.verifier)),
    (entry.finish side roles header result).Quiet

end Entry

end Zkc.Core

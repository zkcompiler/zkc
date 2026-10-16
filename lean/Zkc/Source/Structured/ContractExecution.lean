module

public import Zkc.Source.Structured.ContractMeaning
public import Zkc.Semantics.MonadExecution

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace BoundaryValuation
variable {Value : Ty → Type} {inputs outputs : List Ty}

/-- Project one participant's actual outcome. Other role copies remain absent;
a stopped process has no returned output tuple. -/
def ofOutcome (self : Nat) (arguments : Values (Component Value) inputs)
    (outcome : PIR.Outcome (Values (Component Value) outputs)) : BoundaryValuation Value inputs outputs :=
  ⟨fun role => if role = self then arguments else Values.absent Value inputs,
    fun role => if role = self then
      match outcome with
      | .returned results => results
      | .stopped _ => Values.absent Value outputs
    else Values.absent Value outputs⟩

def ofReturned (self : Nat) (arguments : Values (Component Value) inputs)
    (results : Values (Component Value) outputs) : BoundaryValuation Value inputs outputs :=
  ofOutcome self arguments (.returned results)

/-- A returned observation fails on every stop, including refusal and missing
input. This is an observation of the existing Outcome, not a new execution. -/
def ReturnedSatisfies (predicate : Values (Component Value) outputs → Prop) :
    PIR.Outcome (Values (Component Value) outputs) → Prop
  | .returned results => predicate results
  | .stopped _ => False

end BoundaryValuation

private theorem absent_get {Value : Ty → Type} {types : List Ty} {type : Ty}
    (ref : Var types type) : (Values.absent Value types).get ref = none := by
  induction ref <;> simp_all [Values.absent, Values.get]

namespace BoundarySelector
variable {signature : ProtocolSignature} {Value : Ty → Type} {type : Ty}
  (selector : BoundarySelector signature type) (context : ProtocolContext) (self : Nat)
  (arguments : Values (Component Value) signature.inputs)

theorem read_returned_output (results : Values (Component Value) signature.outputs)
    (ref : Var signature.outputs type) (output : selector.port = .output ref)
    (selectedRole : context.roles selector.role = self) :
    selector.read context (BoundaryValuation.ofReturned self arguments results) = results.get ref := by
  simp only [read, output, selectedRole, BoundaryValuation.ofReturned, BoundaryValuation.ofOutcome, ↓reduceIte]

theorem read_stopped_output (reason : PIR.Stop) (ref : Var signature.outputs type)
    (output : selector.port = .output ref) :
    selector.read context (BoundaryValuation.ofOutcome self arguments (.stopped reason)) = none := by
  simp only [read, output, BoundaryValuation.ofOutcome]
  split <;> exact absent_get ref

theorem other_output_absent (outcome : PIR.Outcome (Values (Component Value) signature.outputs))
    (ref : Var signature.outputs type) (output : selector.port = .output ref)
    (otherRole : context.roles selector.role ≠ self) :
    selector.read context (BoundaryValuation.ofOutcome self arguments outcome) = none := by
  simp only [read, output, BoundaryValuation.ofOutcome, otherRole, ↓reduceIte]
  exact absent_get ref

end BoundarySelector

/-- Exact selected-decision observation on one participant's outcome. Neither a
stop nor a different participant's Boolean can satisfy this proposition. -/
theorem BoundarySelector.returnedSatisfies_decision
    {signature : ProtocolSignature} {Value : Ty → Type} (boolean : Value .boolean = Bool)
    (selector : BoundarySelector signature .boolean) (context : ProtocolContext) (self : Nat)
    (arguments : Values (Component Value) signature.inputs)
    (outcome : PIR.Outcome (Values (Component Value) signature.outputs))
    (ref : Var signature.outputs .boolean) (output : selector.port = .output ref)
    (selectedRole : context.roles selector.role = self) :
    selector.read context (BoundaryValuation.ofOutcome self arguments outcome) = some (boolean.symm ▸ true) ↔
      BoundaryValuation.ReturnedSatisfies (fun results => results.get ref = some (boolean.symm ▸ true)) outcome := by
  cases outcome with
  | returned results =>
    rw [show BoundaryValuation.ofOutcome self arguments (.returned results) =
      BoundaryValuation.ofReturned self arguments results from rfl]
    rw [selector.read_returned_output context self arguments results ref output selectedRole]
    rfl
  | stopped reason =>
    rw [selector.read_stopped_output context self arguments reason ref output]
    exact iff_false_intro (by intro contradiction; cases contradiction)

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- A process-facing subject has no supplied result or final theorem. Outcomes
are obtained by running its actual admitted invocation under the chosen handler.
The same returned-event function can be used by deterministic and probabilistic
consumers, with their own quantifiers and interaction assumptions. -/
structure ComponentInput (owner : ContractBinding imported) (F G : Type) where
  context : ProtocolContext
  self : Nat
  arguments : Values (Component (assignment F G)) owner.protocol.inputs

namespace ComponentInput
variable {owner : ContractBinding imported}

def process (input : ComponentInput owner F G) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) owner.protocol.outputs) :=
  invokeProtocol (imported.program.payload.protocolTable F G) owner.protocol.signature
    input.context input.self input.arguments

def runM (input : ComponentInput owner F G) {M : Type → Type} [Monad M]
    {State Event : Type} (handler : PIR.MonadHandler M (observedInterface F G) State Event) (initial : State) :=
  input.process.runM handler initial

def boundary (input : ComponentInput owner F G)
    (outcome : PIR.Outcome (Values (Component (assignment F G)) owner.protocol.outputs)) :
    BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs :=
  BoundaryValuation.ofOutcome input.self
    (maskValues input.self (input.context.mapScopes owner.protocol.inputScopes) input.arguments) outcome

def returnedEvent (input : ComponentInput owner F G)
    (predicate : BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs → Prop) :
    PIR.Outcome (Values (Component (assignment F G)) owner.protocol.outputs) → Prop
  | .returned results => predicate (input.boundary (.returned results))
  | .stopped _ => False

end ComponentInput

end Zkc.Source.Structured

import ZkcExamples.Executable.SumcheckProof
import Zkc.Executable.Cleanup
import Zkc.Executable.Helpers
import Mathlib.Algebra.Field.ZMod

/-! Controls for the lowering rule on the actual executable Sumcheck validator.

Program mutations change the round loop, a helper function or the participant's
return; the rule must refuse each with the named reason. A helper whose body
observes the transcript is refused, while a changed constant in the terminal
check's body is accepted: the rule reads helper bodies only for their sorts and
their freedom from transcript operations, and what a body computes is the
preparation proof of the committed program. The helper rule reads what a body
computes: it accepts the empty point and the point extension, refuses the
terminal check as outside its recipe table (the check iterates), and refuses
the changed constant, an installed operation that implements another structured
operation and a rebound name, each with its named reason. Semantic controls run
the executable meaning on a small concrete instance (values in `ZMod 5`, every
message a one-byte frame, a constant challenge) and fix observations the runtime
reports for the same situations: the honest run returns from 186 instructions, a round
message that fails the round check stops at the check's explicit rejection inside
its local call after 21 instructions, and a stop inside a loop iteration leaves
the call's frame, the iteration's frame and the participant's frame, innermost
first. -/

namespace Tests.ExecutableSumcheckControls
open Zkc.Construction Zkc.Executable ZkcExamples.Construction

abbrev actual : Validator := ZkcExamples.Executable.SumcheckProof.validator
abbrev constructed : Participant := SumcheckProof.participant

def refusal : Except Refusal Lowered → Option Refusal
  | .error refusal => some refusal
  | .ok _ => none

/-- Change one local function. -/
def withFunction (validator : Validator) (symbol : String)
    (change : Zkc.Executable.Function → Zkc.Executable.Function) : Validator :=
  { validator with functions := validator.functions.map fun function =>
      if function.symbol = symbol then change function else function }

/-- Change the participant's round loop. -/
def withLoop (validator : Validator) (change : Action → Action) : Validator :=
  { validator with body := validator.body.map fun action =>
      match action with
      | .loop .. => change action
      | _ => action }

theorem accepted : refusal (checkLowering installed constructed actual) = none := by decide +kernel

/-! ## Rule mutations -/

/-- The loop may run three rounds: the second anchor, the loop, differs. -/
def maximumRaised : Validator :=
  withLoop actual fun
    | .loop site count _ induction carried captures body outputs =>
        .loop site count 3 induction carried captures body outputs
    | action => action

theorem maximumRaised_refused :
    refusal (checkLowering installed constructed maximumRaised) = some (.anchor 1) := by
  decide +kernel

/-- The round check compares the round's sum with itself instead of with the
running claim. Inside the loop body, the guard's operand denotes another term;
the body's fifth anchor is the guard. -/
def roundCheckTrivial : Validator :=
  withFunction actual "_calculation_3" fun function =>
    { function with
      body := function.body.modify 1 fun
        | .operation site binding parameters [_, right] outputs =>
            .operation site binding parameters [right, right] outputs
        | step => step }

theorem roundCheckTrivial_refused :
    refusal (checkLowering installed constructed roundCheckTrivial) = some (.anchorOperand 4 0) := by
  decide +kernel

/-- The loop counts with the claim instead of the round count. -/
def countRetargeted : Validator :=
  withLoop actual fun
    | .loop site _ maximum induction carried captures body outputs =>
        .loop site "v401" maximum induction carried captures body outputs
    | action => action

theorem countRetargeted_refused :
    refusal (checkLowering installed constructed countRetargeted) =
      some (.loop "apply_18_label_726564756365_s15") := by
  decide +kernel

/-- The empty point helper observes the transcript: its body is the first
round's observation. -/
def helperObserves : Validator :=
  withFunction actual "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f" fun function =>
    { function with body := match actual.function? "_transcript_1" with
        | some observation => observation.body
        | none => [] }

theorem helperObserves_refused :
    refusal (checkLowering installed constructed helperObserves) =
      some (.helper "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f") := by
  decide +kernel

/-- The terminal check reads its first constant as 2: the rule still accepts,
because what a helper body computes is the preparation proof's obligation. -/
def checkConstantChanged : Validator :=
  withFunction actual "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc" fun function =>
    { function with body := function.body.map fun
        | .operation "lc_7_lc_2_s2" binding [.text "1"] inputs outputs =>
            .operation "lc_7_lc_2_s2" binding [.text "2"] inputs outputs
        | step => step }

theorem checkConstantChanged_accepted :
    refusal (checkLowering installed constructed checkConstantChanged) = none := by
  decide +kernel

/-! ## Helper rule -/

abbrev program := SumcheckProof.program
abbrev emptyName := ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper.name
abbrev appendName := ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name
abbrev checkName := ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name

def helperRefusal (validator : Validator) (name : String) : Option HelperRefusal :=
  match checkHelper installed validator program.payload.definitions name with
  | .error refusal => some refusal
  | .ok () => none

/-- The rule accepts the empty point and the point extension. -/
theorem rule_accepts : helperRefusal actual emptyName = none ∧ helperRefusal actual appendName = none := by
  decide +kernel

/-- The terminal check iterates, which the recipe table does not cover: it keeps
a preparation proof of its own. -/
theorem check_outside_table : helperRefusal actual checkName = some (.recipe "loop") := by
  decide +kernel

/-- The changed constant of the terminal check, which the lowering rule accepts,
is refused at its step: the installed constant is not the structured one. -/
theorem checkConstantChanged_refused :
    helperRefusal checkConstantChanged checkName = some (.step "lc_7_lc_2_s2") := by
  decide +kernel

/-- The point extension applies the empty vector's binding: the installed
operation implements another structured operation. -/
def appendWrongOperation : Validator :=
  withFunction actual appendName fun function =>
    { function with body := function.body.map fun
        | .operation site _ parameters inputs outputs => .operation site "zkl_binding_7" parameters inputs outputs
        | step => step }

theorem appendWrongOperation_refused : helperRefusal appendWrongOperation appendName = some (.step "s0") := by
  decide +kernel

/-- The point extension binds its result to the name of its first formal: a
rebound name could change what the formal denotes. -/
def appendRebound : Validator :=
  withFunction actual appendName fun function =>
    { function with body := [.operation "s0" "zkl_binding_11" [] ["v105", "v106"] ["v105"], .ret ["v105"]] }

theorem appendRebound_refused : helperRefusal appendRebound appendName = some (.rebound "s0") := by
  decide +kernel

/-! ## Semantic controls on a concrete instance -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

/-- A one-byte toy codec: a byte below 5 decodes as a scalar. -/
def decodeToy : PhysicalType → List UInt8 → Option (Payload F G)
  | ⟨.data (.field domain), _⟩, [byte] =>
      if byte.toNat < 5 then some (.field domain (byte.toNat : ZMod 5)) else none
  | _, _ => none

/-- One length-framed message of one byte. -/
def frame (byte : UInt8) : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, byte]

/-- Two rounds of zero messages for the zero table and claim: every check holds
with the zero challenge. -/
def honest : List UInt8 := frame 0 ++ frame 0 ++ frame 0 ++ frame 0

/-- The first round message is 1, so the first round sum is not the claim. -/
def wrongRound : List UInt8 := frame 1 ++ frame 0 ++ frame 0 ++ frame 0

def challengeToy (_ : History F G) : Id F := 0

def runAt (budget : Nat) (bytes : List UInt8) : Run F G :=
  Id.run (execute installed actual SumcheckProof.context challengeToy decodeToy budget
    (SumcheckProof.inputs (G := G) [0, 0, 0, 0] 0 2) [] bytes)

/-- The observations the native report carries: stop site and local call,
charged instructions, applied transitions and read messages. -/
def observed (run : Run F G) :
    Option (Option String × Option (String × String)) × Nat × Nat × Nat :=
  (match run.result with
    | .stopped _ site call => some (site, call)
    | .returned _ => none, run.used, run.transitions, run.messages)

/-- The honest proof is accepted from 186 instructions, with 8 transitions and
4 messages, as the runtime reports; at 185 the final return is not charged. -/
theorem honest_threshold :
    (runAt 186 honest).accepts SumcheckProof.acceptancePosition = true ∧
      observed (runAt 186 honest) = (none, 186, 8, 4) ∧
      (runAt 185 honest).result.outcome = .stopped .exhausted := by
  decide +kernel

/-- A first round message that fails the round check stops at the check's
explicit rejection inside its local call, after 21 instructions, 2 transitions
and 2 messages, as the runtime reports. -/
theorem wrong_round_rejected :
    (runAt 1000 wrongRound).result matches .stopped (.explicit .reject) _ _ ∧
      observed (runAt 1000 wrongRound) =
        (some (some "apply_18_label_726564756365_s24",
          some ("apply_18_label_726564756365_s24", "_calculation_3")), 21, 2, 2) := by
  decide +kernel

/-- Budget 100 stops inside the terminal check's region, as the runtime reports
for that budget: the stop site is the instruction's, the local call the
check's. -/
theorem exhausted_in_check :
    observed (runAt 100 honest) =
      (some (some "lc_h_12c01db8f313ed943761ac0825838046ef00d84dcfc058d37638790cc3129f63",
        some ("s7", "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc")), 100, 8, 4) := by
  decide +kernel

/-- A stop inside a round's local call leaves the call's frame, the iteration's
frame and the participant's frame, innermost first, and the run is cleaned up. -/
theorem cleanup_in_loop :
    (runAt 1000 wrongRound).events.drop ((runAt 1000 wrongRound).events.length - 3) =
      [.leave (.call "apply_18_label_726564756365_s24" "_calculation_3") .stopped,
        .leave (.loop "apply_18_label_726564756365_s15" 0) .stopped, .leave .participant .stopped] ∧
      (runAt 1000 wrongRound).Cleaned := by
  decide +kernel

end Tests.ExecutableSumcheckControls

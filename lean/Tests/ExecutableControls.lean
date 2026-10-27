import ZkcExamples.Executable.SchnorrProofFacts
import ZkcExamples.Construction.SchnorrProof
import Zkc.Executable.DomainLowering
import Zkc.Executable.Relation
import Zkc.Executable.Decoding
import Zkc.Executable.NativeLaws
import Zkc.Executable.Cleanup
import Mathlib.Algebra.Field.ZMod

/-! Controls for the lowering rule on the actual executable Schnorr validator.

Artifact mutations change one instruction, operand, binding, type, symbol
table entry or identity of the retained `zkc.program/0` validator; the rule
must refuse each with the named reason. Semantic controls run the executable meaning on a small concrete
instance (the field and group are both `ZMod 5`, a one-byte toy codec and a
constant challenge) and fix the observations the runtime reports for the same
situations: the budget at which each stop occurs, the charged instructions,
applied transitions, read messages and the stop site. They also show that the
relation needs its budget premise, distinguishes decoding failures from
rejection, and that a stop leaves every frame innermost first. -/

namespace Tests.ExecutableControls
open Zkc.Construction Zkc.Executable ZkcExamples.Construction

abbrev actual : Validator := ZkcExamples.Executable.SchnorrProof.validator
abbrev constructed : Participant := SchnorrProof.participant

def refusal : Except Refusal Lowered → Option Refusal
  | .error refusal => some refusal
  | .ok _ => none

/-- Replace one step of a local function. -/
def withStep (validator : Validator) (symbol : String) (index : Nat) (step : Zkc.Executable.Step) :
    Validator :=
  { validator with functions := validator.functions.map fun function =>
      if function.symbol = symbol then { function with body := function.body.set index step }
      else function }

/-- Replace one participant instruction. -/
def withAction (validator : Validator) (index : Nat) (action : Action) : Validator :=
  { validator with body := validator.body.set index action }

/-- Change the installed implementation of one binding. -/
def withImplementation (validator : Validator) (symbol implementation : String) : Validator :=
  { validator with bindings := validator.bindings.map fun binding =>
      if binding.symbol = symbol then { binding with implementation } else binding }

theorem accepted : refusal (checkLowering installed constructed actual) = none := by decide +kernel

/-- The mutation helpers alone preserve acceptance. -/
theorem unchanged_accepted :
    refusal (checkLowering installed constructed
      (withStep actual "_calculation_2" 2 (.operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_4" [] ["v12", "v14"] ["v15"])))
      = none := by
  decide +kernel

/-! ## Arithmetic and result mutations -/

/-- The final addition takes its operands in the other order. The sum is a pure
term, so the rule finds the difference where the decision it feeds is returned. -/
def additionSwapped : Validator :=
  withStep actual "_calculation_2" 2 (.operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_4" [] ["v14", "v12"] ["v15"])

theorem additionSwapped_refused :
    refusal (checkLowering installed constructed additionSwapped) = some (.returned 0) := by
  decide +kernel

/-- The final comparison compares one side with itself: the returned decision
denotes another term. -/
def comparisonTrivial : Validator :=
  withStep actual "_calculation_2" 3 (.operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_3" [] ["v13", "v13"] ["v16"])

theorem comparisonTrivial_refused :
    refusal (checkLowering installed constructed comparisonTrivial) = some (.returned 0) := by
  decide +kernel

/-- The participant returns its decision and transcript in the other order. -/
def resultsSwapped : Validator := withAction actual 7 (.ret ["v21", "v22"])

theorem resultsSwapped_refused :
    refusal (checkLowering installed constructed resultsSwapped) = some (.returned 0) := by
  decide +kernel

/-! ## Transcript mutations -/

/-- The first observation absorbs the base instead of the received commitment:
the second anchor's second operand denotes another term. -/
def baseObserved : Validator :=
  withAction actual 1 (.call "_transcript_12" "_transcript_0" ["v14", "v12"] ["v16"])

theorem baseObserved_refused :
    refusal (checkLowering installed constructed baseObserved) = some (.anchorOperand 1 1) := by
  decide +kernel

/-- The delivery is observed on the transcript state from before the challenge:
a consumed transcript unit is used again. -/
def staleTranscript : Validator :=
  withAction actual 3 (.call "_transcript_14" "_transcript_5" ["v16", "v17"] ["v19"])

theorem staleTranscript_refused :
    refusal (checkLowering installed constructed staleTranscript) = some (.operation "lc_10_transition") := by
  decide +kernel

/-! ## Installation mutations -/

/-- An implementation outside the installed vocabulary. -/
def uninstalled : Validator := withImplementation actual "_numerical_binding_4" "fast/curve.add"

theorem uninstalled_refused :
    refusal (checkLowering installed constructed uninstalled) = some (.binding "_numerical_binding_4") := by
  decide +kernel

/-- Physical specialization is part of the installed binding's identity. -/
def withPhysicalArguments (validator : Validator) (symbol : String)
    (arguments : List PhysicalType) : Validator :=
  { validator with bindings := validator.bindings.map fun binding =>
      if binding.symbol = symbol then { binding with physicalArguments := arguments } else binding }

theorem missingSpecialization_refused :
    refusal (checkLowering installed constructed
      (withPhysicalArguments actual "_transcript_2" [])) = some (.binding "_transcript_2") := by
  decide +kernel

theorem wrongSpecialization_refused :
    refusal (checkLowering installed constructed
      (withPhysicalArguments actual "_transcript_2"
        [⟨.data (.group "bls12-381.g1"), "other.g1/0"⟩])) = some (.binding "_transcript_2") := by
  decide +kernel

theorem additionalSpecialization_refused :
    refusal (checkLowering installed constructed
      (withPhysicalArguments actual "_numerical_binding_4"
        [⟨.data (.group "bls12-381.g1"), "arkworks.g1/0"⟩])) = some (.binding "_numerical_binding_4") := by
  decide +kernel

/-- Retain the actual operation and implementation, but substitute its payload layout. -/
def foreignPayloadLayout : Validator :=
  { actual with bindings := actual.bindings.map fun binding =>
      if binding.symbol = "_transcript_2" then
        { binding with physicalArguments :=
          [⟨.data (.group "bls12-381.g1"), "foreign.g1/0"⟩] }
      else binding }

theorem foreignPayloadLayout_refused :
    refusal (checkLowering installed constructed foreignPayloadLayout) =
      some (.binding "_transcript_2") := by decide +kernel

/-- The field layout is installed for field absorption, not group absorption. -/
def crossedPayloadLayout : Validator :=
  { actual with bindings := actual.bindings.map fun binding =>
      if binding.symbol = "_transcript_2" then
        { binding with physicalArguments :=
          [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩] }
      else binding }

theorem crossedPayloadLayout_refused :
    refusal (checkLowering installed constructed crossedPayloadLayout) =
      some (.binding "_transcript_2") := by decide +kernel

/-- The commitment is received at a representation the vocabulary does not admit. -/
def uncheckedRepresentation : Validator :=
  withAction actual 0 (.receive "label_636f6d6d69746d656e74_0" "label_636f6d6d69746d656e74_0"
    "role00000000" "v15" ⟨.data (.group "bls12-381.g1"), "unchecked.g1/0"⟩)

theorem uncheckedRepresentation_refused :
    refusal (checkLowering installed constructed uncheckedRepresentation) = some .representation := by
  decide +kernel

/-! ## Declaration and identity mutations -/

/-- Change the declared formals or results of one local function. -/
def withSignature (validator : Validator) (symbol : String)
    (change : Function → Function) : Validator :=
  { validator with functions := validator.functions.map fun function =>
      if function.symbol = symbol then change function else function }

/-- The comparison helper declares its first formal, a group element, as a
Boolean. -/
def formalRetyped : Validator :=
  withSignature actual "_calculation_2" fun function =>
    { function with inputs := function.inputs.set 0 ("v8", ⟨.data .boolean, "native.bool/0"⟩) }

theorem formalRetyped_refused :
    refusal (checkLowering installed constructed formalRetyped) = some (.operation "calculation_0") := by
  decide +kernel

/-- The comparison helper declares its result at an unadmitted representation. -/
def resultUnadmitted : Validator :=
  withSignature actual "_calculation_2" fun function =>
    { function with results := [⟨.data .boolean, "unchecked.bool/0"⟩] }

theorem resultUnadmitted_refused :
    refusal (checkLowering installed constructed resultUnadmitted) = some .representation := by
  decide +kernel

/-- A second function under the comparison helper's symbol. -/
def functionDuplicated : Validator :=
  { actual with functions := actual.functions ++
      [⟨"_calculation_2", [], [⟨.data .boolean, "native.bool/0"⟩], [.unsupported "other"]⟩] }

theorem functionDuplicated_refused :
    refusal (checkLowering installed constructed functionDuplicated) = some (.duplicate "function") := by
  decide +kernel

/-- A second binding under the addition's symbol. -/
def bindingDuplicated : Validator :=
  { actual with bindings := actual.bindings ++
      [⟨"_numerical_binding_4", "curve.add", ["bls12-381.g1"], "fast/curve.add", []⟩] }

theorem bindingDuplicated_refused :
    refusal (checkLowering installed constructed bindingDuplicated) = some (.duplicate "binding") := by
  decide +kernel

/-- The program's validator for another entry. -/
theorem otherEntry_refused :
    refusal (checkLowering installed constructed { actual with entry := "other" }) =
      some (.different "entry") := by
  decide +kernel

/-- The program's participant for the producer role. -/
theorem producerRole_refused :
    refusal (checkLowering installed constructed { actual with role := constructed.policy.producer }) =
      some (.different "role") := by
  decide +kernel

/-! ## Semantic controls on a concrete instance -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

/-- A one-byte toy codec: a byte below 5 decodes at the receive's type. -/
def decodeToy : PhysicalType → List UInt8 → Option (Payload F G)
  | ⟨.data (.group domain), _⟩, [byte] =>
      if byte.toNat < 5 then some (.group domain (byte.toNat : ZMod 5)) else none
  | ⟨.data (.field domain), _⟩, [byte] =>
      if byte.toNat < 5 then some (.field domain (byte.toNat : ZMod 5)) else none
  | _, _ => none

/-- One length-framed message of one byte. -/
def frame (byte : UInt8) : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, byte]

/-- Base `1`, statement `3 = 3 · 1`, nonce `4`, challenge `2`: commitment `4`
and response `4 + 2 · 3 = 0` in `ZMod 5`. -/
def honest : List UInt8 := frame 4 ++ frame 0

def challengeToy (_ : History F G) : Id F := 2

def runAt (budget : Nat) (bytes : List UInt8) : Run F G :=
  Id.run (execute installed actual SchnorrProof.context challengeToy decodeToy budget
    ((SchnorrProof.inputs (F := F) (1 : G) 3).map .data) [] bytes)

/-- The observations the native report carries: stop site and local call,
charged instructions, applied transitions and read messages. -/
def observed (run : Run F G) :
    Option (Option String × Option (String × String)) × Nat × Nat × Nat :=
  (match run.result with
    | .stopped _ site call => some (site, call)
    | .returned _ => none, run.used, run.transitions, run.messages)

/-- Positive control: the honest proof is accepted with the runtime's 25
instructions, 4 transitions and 2 messages. -/
theorem honest_accepted :
    (runAt 25 honest).accepts SchnorrProof.acceptancePosition = true ∧
      observed (runAt 25 honest) = (none, 25, 4, 2) := by
  decide +kernel

/-- Exhaustion after the challenge: at budget 8 the challenge transition has
run (two transitions) and the stop is charged inside the challenge helper,
as the runtime reports for this budget. -/
theorem exhausted_after_challenge :
    (runAt 8 honest).result.outcome = .stopped .exhausted ∧
      observed (runAt 8 honest) = (some (some "_transcript_13", some ("_transcript_13", "_transcript_3")), 8, 2, 1) := by
  decide +kernel

/-- The canonical metered Domain execution at the actual checked reading. -/
def canonicalAt (budget : Nat) (bytes : List UInt8) :
    PIR.Outcome (List (Value F G)) × Proof F G :=
  DomainVM.validate SchnorrProof.program SchnorrProof.context id [] challengeToy
    (helperCost installed actual) budget constructed ZkcExamples.Executable.SchnorrProof.lowered
    (SchnorrDomainConnection.inputs (F := F) (G := G) 1 3)
    (decodeProof decodeToy ZkcExamples.Executable.SchnorrProof.receives bytes)

/-- The budget premise is necessary: the native execution at budget 8 stops,
while the canonical execution at its sufficient budget returns. -/
theorem budget_dropped :
    (runAt 8 honest).result.outcome ≠ (canonicalAt 25 honest).1 := by
  decide +kernel

/-- A commitment that does not decode stops at its receive after one charged
instruction, before any transition. -/
theorem commitment_undecodable :
    (runAt 25 (frame 9 ++ frame 0)).result.outcome = .stopped .refused ∧
      observed (runAt 25 (frame 9 ++ frame 0)) =
        (some (some "label_636f6d6d69746d656e74_0", none), 1, 0, 1) := by
  decide +kernel

/-- A response that does not decode stops after the challenge: three
transitions and fourteen charged instructions. -/
theorem response_undecodable :
    observed (runAt 25 (frame 4 ++ frame 9)) =
      (some (some "label_726573706f6e7365_0", none), 14, 3, 2) := by
  decide +kernel

/-- A missing response cancels the run after thirteen instructions and three
transitions. -/
theorem response_missing :
    (runAt 25 (frame 4)).result matches .stopped .truncated none none ∧
      observed (runAt 25 (frame 4)) = (some (none, none), 13, 3, 1) := by
  decide +kernel

/-- A trailing byte or a wrong response returns but is not accepted. -/
theorem trailing_and_wrong_rejected :
    (runAt 25 (honest ++ [0])).accepts SchnorrProof.acceptancePosition = false ∧
      (runAt 25 (honest ++ [0])).result.outcome matches .returned _ ∧
      (runAt 25 (frame 4 ++ frame 1)).accepts SchnorrProof.acceptancePosition = false := by
  decide +kernel

/-- A stop classification that reads an undecodable message as a verifier
rejection. -/
def misclassified : Zkc.Executable.Result F G → PIR.Outcome (List (Value F G))
  | .stopped .decode _ _ => .stopped .reject
  | result => result.outcome

/-- The relation's stop classes are not interchangeable: with the misclassified
decoding stop the metered equation fails on an undecodable commitment, while
the rule's classification satisfies it. -/
theorem stop_misclassified :
    misclassified (runAt 25 (frame 9 ++ frame 0)).result ≠
      (canonicalAt 25 (frame 9 ++ frame 0)).1 ∧
    (runAt 25 (frame 9 ++ frame 0)).result.outcome =
      (canonicalAt 25 (frame 9 ++ frame 0)).1 := by
  decide +kernel

/-- A stop inside a helper leaves that frame and then the participant frame,
and retires the live transcript. Skipping that cleanup leaves two entered
frames open, and leaving the participant frame before the helper's exits
frames out of order although entries and exits still balance; `execute_cleaned`
excludes both. -/
theorem cleanup_on_stop :
    (runAt 3 honest).events =
      [.enter .participant, .enter (.call "_transcript_12" "_transcript_0"),
        .leave (.call "_transcript_12" "_transcript_0") .stopped, .leave .participant .stopped] ∧
    (runAt 3 honest).retired = [[]] ∧ (runAt 3 honest).Cleaned ∧
    ¬ ({ runAt 3 honest with events := (runAt 3 honest).events.take 2 } : Run F G).Cleaned ∧
    ¬ ({ runAt 3 honest with events := [.enter .participant, .enter (.call "_transcript_12" "_transcript_0"),
        .leave .participant .stopped, .leave (.call "_transcript_12" "_transcript_0") .stopped] } :
      Run F G).Cleaned := by
  decide +kernel

end Tests.ExecutableControls

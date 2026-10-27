import Tests.StructuredSumcheckVerifierBodies
import Tests.StructuredSumcheckVerifierSupport

/-! Focused executions of complete originals and their literal callback. These
controls supply deterministic replies and preserve full state/event records. -/
namespace Tests.StructuredSumcheckVerifierExecution
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open SumcheckVerifierLaws (lowSite highSite challengeSite deliverySite)
open Tests.StructuredSumcheckVerifierSupport

variable {F : Type} [CommRing F] [DecidableEq F]

def reduceInputs (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F F)) SumcheckReduceBodies.runSignature.inputs :=
  .cons none (.cons none (.cons claim (.cons count (.cons service .nil))))

def reduceResult (values : Values (Component (assignment F F))
    SumcheckReduceBodies.runSignature.outputs) : Option (List F) × Option F :=
  (values.get (.there (.there .here)), values.get (.there (.there (.there .here))))

def reduceRun (claim : Option F) (count service : Option Nat) (state : State F) :=
  ((SumcheckReduceViews.program.participant F F 1 (reduceInputs claim count service)).bind
    fun values => .done (reduceResult values)).run handler state

def sourceInputs (raw : Option (List F)) (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F F)) SumcheckSourceBodies.runSignature.inputs :=
  .cons raw (.cons claim (.cons count (.cons service .nil)))

def sourceRun (raw : Option (List F)) (claim : Option F) (count service : Option Nat)
    (state : State F) :=
  ((SumcheckSourceViews.program.participant F F 1 (sourceInputs raw claim count service)).bind
    fun values => .done (values.get .here)).run handler state

def reduceContext : ProtocolContext := ProtocolContext.enter {} "s5" [0, 1]
def sourceContext : ProtocolContext := ProtocolContext.enter {} "label_726564756365" [0, 1]

def missingPointRun (state : State F) :=
  (SumcheckVerifierBodies.roundBody.denote
    (participantMeaningWith (.silent _) (participantActions F F)
      (SumcheckReduceViews.unit.definitions.foldl
        (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩)
      1 (SumcheckReduceViews.unit.plainProtocolTable F F) reduceContext)
    (Values.cons (some 0) (.cons none (.cons none (.cons none (.cons none
      (.cons none (.cons (some (1 : F)) (.cons (some 7) .nil)))))))).get).run handler state

private def sameExecution {A : Type} [DecidableEq A]
    (actual expected : PIR.Execution (State F) (Event F) A) : Bool :=
  actual.outcome == expected.outcome && actual.state == expected.state && actual.events == expected.events

private def stopped {A : Type} (actual : PIR.Execution (State F) (Event F) A)
    (reason : PIR.Stop) (state : State F) (events : List (Event F)) : Bool :=
  (match actual.outcome with | .stopped why => why == reason | _ => false) &&
    actual.state == state && actual.events == events

def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let test (name : String) (ok : Bool) : IO Unit :=
    unless ok do failures.modify (name :: ·)
  let untouched : State (ZMod 5) := ⟨[.stop .abort], 0⟩
  test "missing count precedes missing claim/service"
    (stopped (reduceRun none none none untouched) .incomplete untouched [])
  test "maximum refused before any callback"
    (stopped (reduceRun (some 0) (some 5) none untouched) .refused untouched [])
  test "zero requires no service and preserves present claim"
    (sameExecution (reduceRun (some 0) (some 0) none untouched)
      ⟨.returned (some [], some 0), untouched, []⟩)
  test "zero missing claim stops before rounds"
    (stopped (reduceRun none (some 0) none untouched) .incomplete untouched [])
  test "missing claim precedes excess count"
    (stopped (reduceRun none (some 5) none untouched) .incomplete untouched [])
  test "Source count three is refused before absent terminal data"
    (stopped (sourceRun none (some 0) (some 3) none untouched) .refused untouched [])
  test "Source zero still requires its claim"
    (stopped (sourceRun (some [1]) none (some 0) none untouched) .incomplete untouched [])
  for (name, raw, claim, expected) in [("singleton", [1], 1, true),
      ("unequal claim", [1], 0, false), ("empty raw", [], 0, false),
      ("nonsingleton", [0, 0], 0, false)] do
    test ("Source zero: " ++ name)
      (sameExecution (sourceRun (some raw) (some claim) (some 0) none untouched)
        ⟨.returned (some expected), untouched, []⟩)
  let replies : State (ZMod 5) := ⟨[.value 0, .value 1, .value 1, .ack, .value 4], 0⟩
  let received := [Event.receive (lowSite reduceContext) 0 0, .receive (highSite reduceContext) 0 1]
  let afterReceives : State (ZMod 5) := ⟨[.value 1, .ack, .value 4], 2⟩
  test "missing claim stops at Pending construction before receives"
    (stopped (reduceRun none (some 1) (some 7) replies) .incomplete replies [])
  test "false boundary wins over missing service"
    (stopped (reduceRun (some 0) (some 1) none replies) .reject afterReceives received)
  test "true boundary then missing service"
    (stopped (reduceRun (some 1) (some 1) none replies) .incomplete afterReceives received)
  test "missing callback point follows query and delivery"
    (stopped (missingPointRun replies) .incomplete ⟨[.value 4], 4⟩
      (roundEvents reduceContext 7 0 1 1))
  test "absent rawV is demanded only after a returning round"
    (stopped (sourceRun none (some 1) (some 1) (some 7) replies) .incomplete
      ⟨[.value 4], 4⟩ (roundEvents sourceContext 7 0 1 1))
  test "actual cv append and independent absent P operands"
    (sameExecution (reduceRun (some 1) (some 1) (some 7) replies)
      ⟨.returned (some [1], some 1), ⟨[.value 4], 4⟩, roundEvents reduceContext 7 0 1 1⟩)
  -- These are independent local executions; no paired delivery law is assumed.
  let proverInputs : Values (Component (assignment (ZMod 5) (ZMod 5)))
      SumcheckReduceBodies.runSignature.inputs :=
    .cons (some [0, 1]) (.cons (some 1) (.cons none (.cons (some 1) (.cons none .nil))))
  let prover := ((SumcheckReduceViews.program.participant (ZMod 5) (ZMod 5) 0 proverInputs).bind
    fun values => .done (values.get .here, values.get (.there .here),
      values.get (.there (.there .here)), values.get (.there (.there (.there .here))))).run
        handler ⟨[.ack, .ack, .value 2], 0⟩
  test "independent cp differs from cv without changing the V point"
    (sameExecution prover ⟨.returned (some [2], some [2], none, none), ⟨[], 3⟩,
      [.send (lowSite reduceContext) 1 0, .send (highSite reduceContext) 1 1,
        .receive (deliverySite reduceContext) 1 2]⟩ &&
      (reduceRun (some 1) (some 1) (some 7) replies).outcome == .returned (some [1], some 1))
  let characteristicTwo : State (ZMod 2) := ⟨[.value 1, .value 1, .value 1, .ack], 0⟩
  test "ZMod2 boundary 1+1=0 and endpoint interpolation"
    (sameExecution (reduceRun (some 0) (some 1) (some 7) characteristicTwo)
      ⟨.returned (some [1], some 1), ⟨[], 4⟩, roundEvents reduceContext 7 1 1 1⟩)
  let nonfield : State (ZMod 4) := ⟨[.value 1, .value 2, .value 2, .ack], 0⟩
  test "ZMod4 interpolation at a nonunit challenge"
    (sameExecution (reduceRun (some 3) (some 1) (some 7) nonfield)
      ⟨.returned (some [2], some 3), ⟨[], 4⟩, roundEvents reduceContext 7 1 2 2⟩)
  let dependentHigh : State (ZMod 5) := ⟨[.value 2, .consumedCount, .value 1, .ack], 0⟩
  test "HIGH reads the state retained after LOW"
    (sameExecution (reduceRun (some 3) (some 1) (some 7) dependentHigh)
      ⟨.returned (some [1], some 1), ⟨[], 4⟩, roundEvents reduceContext 7 2 1 1⟩)
  let zeroRound : List (Reply (ZMod 5)) := [.value 0, .value 0, .value 0, .ack]
  let twice : State (ZMod 5) := ⟨zeroRound ++ zeroRound, 0⟩
  test "Reduction count two uses the actual complete body"
    (sameExecution (reduceRun (some 0) (some 2) (some 7) twice)
      ⟨.returned (some [0, 0], some 0), ⟨[], 8⟩,
        roundEvents reduceContext 7 0 0 0 ++ roundEvents reduceContext 7 0 0 0⟩)
  test "Source count two composes its actual terminal"
    (sameExecution (sourceRun (some [0, 0, 0, 0]) (some 0) (some 2) (some 7) twice)
      ⟨.returned (some true), ⟨[], 8⟩,
        roundEvents sourceContext 7 0 0 0 ++ roundEvents sourceContext 7 0 0 0⟩)
  test "Reduction supports count three"
    (sameExecution (reduceRun (some 0) (some 3) (some 7) ⟨zeroRound ++ zeroRound ++ zeroRound, 0⟩)
      ⟨.returned (some [0, 0, 0], some 0), ⟨[], 12⟩,
        roundEvents reduceContext 7 0 0 0 ++ roundEvents reduceContext 7 0 0 0 ++
          roundEvents reduceContext 7 0 0 0⟩)
  let rawFamily : Nat → Option (List (ZMod 5)) := fun role => if role == 0 then some [4] else some [0, 1]
  let countFamily : Nat → Option Nat := fun role => if role == 0 then some 0 else some 1
  let zeroCountProver := ((SumcheckSourceViews.program.participant (ZMod 5) (ZMod 5) 0
    (sourceInputs (rawFamily 0) none (countFamily 0) none)).bind
      fun values => .done (values.get .here)).run handler untouched
  test "independent P/V counts and raw values select V's actual inputs"
    (rawFamily 0 != rawFamily 1 && countFamily 0 != countFamily 1 &&
      sameExecution zeroCountProver ⟨.returned none, untouched, []⟩ &&
      sameExecution (sourceRun (rawFamily 1) (some 1) (countFamily 1) (some 7) replies)
        ⟨.returned (some true), ⟨[.value 4], 4⟩, roundEvents sourceContext 7 0 1 1⟩)
  let outer : ProtocolContext := ⟨some "outer", roleSubstitution [2, 0]⟩
  let mappedReduction := ((invokeProtocol (SumcheckReduceViews.unit.plainProtocolTable (ZMod 5) (ZMod 5))
    SumcheckReduceBodies.runSignature outer 0 (reduceInputs (some 1) (some 1) (some 7))).bind
      fun values => .done (reduceResult values)).run handler replies
  test "mapped Reduction keeps root self0 and peer2"
    ((outer.enter "s5" [0, 1]).roles 0 == 2 &&
      (outer.enter "s5" [0, 1]).roles 1 == 0 &&
      sameExecution mappedReduction ⟨.returned (some [1], some 1), ⟨[.value 4], 4⟩,
      roundEvents (outer.enter "s5" [0, 1]) 7 0 1 1⟩)
  let mappedSource := ((invokeProtocol (SumcheckSourceViews.unit.plainProtocolTable (ZMod 5) (ZMod 5))
    SumcheckSourceBodies.runSignature outer 0 (sourceInputs (some [0, 1]) (some 1) (some 1) (some 7))).bind
      fun values => .done (values.get .here)).run handler replies
  test "mapped Source preserves the distinct child prefix"
    ((outer.enter "label_726564756365" [0, 1]).roles 0 == 2 &&
      (outer.enter "label_726564756365" [0, 1]).roles 1 == 0 &&
      sameExecution mappedSource ⟨.returned (some true), ⟨[.value 4], 4⟩,
      roundEvents (outer.enter "label_726564756365" [0, 1]) 7 0 1 1⟩)
  -- A complete first iteration precedes each stopping cut in the second one.
  -- Every later reply, iteration and root result is suppressed.
  let stoppingCuts : List (String × List (Reply (ZMod 5)) × List (Reply (ZMod 5)) × List (Event (ZMod 5))) := [
      ("LOW", [], [.value 0, .value 0, .ack], [Event.stop (lowSite reduceContext) .abort]),
      ("HIGH", [Reply.value 0], [.value 0, .ack],
        [.receive (lowSite reduceContext) 0 0, .stop (highSite reduceContext) .abort]),
      ("query", [Reply.value 0, .value 0], [.ack],
        [.receive (lowSite reduceContext) 0 0, .receive (highSite reduceContext) 0 0,
          .stop (challengeSite reduceContext) .abort]),
      ("delivery", [Reply.value 0, .value 0, .value 0], [],
        roundEvents reduceContext 7 0 0 0 ++ [.stop (deliverySite reduceContext) .abort])]
  for (name, beforeStop, suffix, events) in stoppingCuts do
    let state : State (ZMod 5) := ⟨zeroRound ++ beforeStop ++ [.stop .abort] ++ suffix ++ zeroRound, 0⟩
    test ("second-round " ++ name ++ " stop retains state/events and suppresses suffix")
      (stopped (reduceRun (some 0) (some 3) (some 7) state) .abort
        ⟨suffix ++ zeroRound, 5 + beforeStop.length⟩
        (roundEvents reduceContext 7 0 0 0 ++ events))
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate "\n" errors.reverse))
  IO.println "structured Sumcheck execution controls passed"

#eval run
end Tests.StructuredSumcheckVerifierExecution

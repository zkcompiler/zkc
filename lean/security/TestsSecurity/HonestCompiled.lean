import ZkcSecurity.FiatShamir.HonestCompiled
import Mathlib.Data.ZMod.Basic

/-! Actual constructed instruction controls. The small participants below are
operational fixtures, not native exports or root completeness receipts. -/
set_option autoImplicit false
namespace TestsSecurity.HonestCompiled
open Zkc.Source Zkc.Construction Zkc.Construction.Domain
open ZkcSecurity
open ZkcSecurity.FiatShamir OracleComp OracleSpec

abbrev Scalar := ZMod 5
def model := Structured.ringModel Scalar Scalar

def snapshot : Structured.Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"main", .protocol, .publicDef, [], [],
    some ⟨["P", "V"], [], []⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩]
  contracts := [⟨"main", []⟩]
  catalogue := ⟨[], [], []⟩

def mainBody : Region Structured.protocolDialect [] [] := .ret .nil
def mainDefinition : Structured.CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [], [], [], []⟩, mainBody.erase, mainBody, mainBody.elaborate_erase⟩
def unit : Structured.UnitPayload where
  definitions := []
  protocols := [mainDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel
def program : Structured.Program := ⟨snapshot, unit⟩

def context : Context :=
  Context.fiatShamir "main" (["P", "V"]) 0 1 0 "random.field/0" (some (.draw "field")) "suite" ([])
def policy : Policy := ⟨"main", "P", "V", 0, "suite", [], [], [], "test", "test"⟩
def query : Template :=
  ⟨"main", [], ["query", "main", "q", "input_0", "random.field/0", "draw", "V"]⟩
def message : Template :=
  ⟨"main", [], ["message", "main", "m", "m", "P", "V"]⟩
def constructed (instructions : List Instruction) (returned : List Nat) : Participant :=
  { source := snapshot.source, candidate := snapshot.source, policy, symbol := "fixture",
    inputs := [.transcript "suite"], outputs := [.data .boolean, .transcript "suite"],
    instructions, returned }

def queryInstructions : List Instruction :=
  [⟨.indicesEmpty, [], [.indices], []⟩,
   ⟨.challenge "suite" "field" query, [0, 1],
     [.data (.field "field"), .transcript "suite"], []⟩]

def producer : Participant := constructed (queryInstructions ++
  [⟨.send "m" "m" "V", [2], [], []⟩,
   ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]) [4, 3]

def validator : Participant := constructed (queryInstructions ++
  [⟨.receive "m" "m" "P" (.field "field"), [], [.data (.field "field")], []⟩,
   ⟨.calculate (.fieldEqual "field"), [2, 4], [.data .boolean], []⟩]) [5, 3]

def inputs : Environment model.toCarriers := [.transcript "suite" []]
def computation := FiatShamir.HonestCompiled.computation model program context producer validator inputs inputs

-- Each raw answer type is the actual requested nominal field or Unit.
instance sampleRaw (event : Event model.toCarriers) : SampleableType (Raw event) := by
  cases event with
  | challenge origin =>
      rcases origin with ⟨port, occurrence, request⟩
      cases request with
      | none => exact inferInstanceAs (SampleableType Unit)
      | some request =>
          rcases request with ⟨method, arguments, sort⟩
          cases sort with
          | field domain => change SampleableType Scalar; infer_instance
          | boolean | index | vector _ | group _ | service _ | sequence _ | product _ _ _ =>
              change SampleableType Unit; infer_instance
  | message => exact inferInstanceAs (SampleableType Unit)
  | publicBinding => exact inferInstanceAs (SampleableType Unit)

noncomputable instance : DecidableEq (Event model.toCarriers) := Classical.decEq _

theorem booleanConstant_calculates (value : Bool) :
    Domain.calculate model (.booleanConstant value) [] = .returned [.data (.boolean value)] := by rfl

theorem fieldEqual_calculates (left right : model.toCarriers.Field "field") :
    Domain.calculate model (.fieldEqual "field") [.data (.field "field" left), .data (.field "field" right)] =
      .returned [.data (.boolean (decide (left = right)))] := by rfl

theorem accepts_all_tables (answers : QueryImpl (FiatShamir.TranscriptOracle.DomainSpec model.toCarriers) Id) :
    Domain.PairExecution.Success 0 (evalWithAnswerFn answers computation) := by
  unfold computation
  rw [FiatShamir.HonestCompiled.eval_computation]
  simp [executePair, produce, validate, run, participant, producer, validator,
    constructed, queryInstructions, inputs, evaluate, step, handler,
    PIR.Process.runM, PIR.Execution.followM, PIR.Process.bind, sortsMatch,
    queryOrigin, templateOrigin, Template.origin, Template.qualify, Template.repeats,
    Template.applicationPrefix, atCoordinates, Context.query, Context.role, Origin.query,
    Structured.qualifyProtocolSite, context, query, decimal, decimalDigit, Domain.read,
    Domain.dataType, Domain.Value.encode, Domain.Payload.ofValue, Domain.Value.sort, drawRequest, Request.draw,
    FiatShamir.HonestCompiled.tableOracle, Typed.readTable,
    booleanConstant_calculates, fieldEqual_calculates,
    Domain.Payload.value, bind, pure,
    Domain.PairExecution.Success, Domain.acceptanceAt]
theorem perfect : Honest.failure computation (Domain.PairExecution.Success 0) = 0 := by
  classical
  exact Honest.failure_zero_of_all_tables _ _ accepts_all_tables

def stoppedProducer : Participant := { producer with instructions :=
  [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
   ⟨.indicesEmpty, [], [.indices], []⟩,
   ⟨.send "m" "m" "V", [1], [], []⟩,
   ⟨.observe "suite" message, [0, 1, 2], [.transcript "suite"], []⟩,
   ⟨.guard "stop", [1], [], []⟩] }

def tableOracle : Oracle Id model.toCarriers Unit := by
  intro history event state
  cases event with
  | challenge origin =>
      rcases origin with ⟨port, occurrence, request⟩
      cases request with
      | none => exact (.returned (), state)
      | some request =>
          rcases request with ⟨method, arguments, sort⟩
          cases sort with
          | field domain => exact (.returned (0 : Scalar), state)
          | boolean | index | vector _ | group _ | service _ | sequence _ | product _ _ _ =>
              exact (.returned (), state)
  | message => exact (.returned (), state)
  | publicBinding => exact (.returned (), state)

def stopped := executePair model program context stoppedProducer validator inputs inputs tableOracle ()
example : stopped.producer.outcome = .stopped .reject := by rfl
example : stopped.producer.state.proof = [.boolean false] := by rfl
example : stopped.producer.events = [.message (context.message "m" 0 1) (.boolean false)] := by rfl
example : stopped.producer.state.environment.length = 4 := by rfl
example : stopped.validator = none := by rfl
example : ¬ Domain.PairExecution.Success 0 stopped :=
  Domain.PairExecution.stopped_fails _ _ .reject rfl

def stoppedComputation := FiatShamir.HonestCompiled.computation model program context
  stoppedProducer validator inputs inputs

theorem stopped_all_tables (answers : QueryImpl (FiatShamir.TranscriptOracle.DomainSpec model.toCarriers) Id) :
    ¬ Domain.PairExecution.Success 0 (evalWithAnswerFn answers stoppedComputation) := by
  unfold stoppedComputation
  rw [FiatShamir.HonestCompiled.eval_computation]
  exact Domain.PairExecution.stopped_fails _ _ .reject rfl

theorem stopped_failure : Honest.failure stoppedComputation (Domain.PairExecution.Success 0) = 1 :=
  Honest.failure_one_of_all_tables _ _ stopped_all_tables

def extraProducer : Participant := { producer with instructions := queryInstructions ++
  [⟨.send "m" "m" "V", [2], [], []⟩,
   ⟨.send "m" "m" "V", [2], [], []⟩,
   ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩] }

def unreadPair := executePair model program context extraProducer validator inputs inputs tableOracle ()
def unreadValidation := validate model program context validator inputs
  [.field "field" 0, .field "field" 0] tableOracle ()

example : unreadPair.producer.state.proof = [.field "field" 0, .field "field" 0] := by rfl
example : unreadPair.validator = some unreadValidation := by rfl
example : unreadValidation.state.proof = [.field "field" 0] := by rfl
example : ¬ Domain.PairExecution.Success 0 unreadPair :=
  Domain.PairExecution.unread_fails _ _ unreadValidation rfl (by decide +kernel)

def constantProducer : Participant := constructed
  [⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩] [1, 0]
def falseValidator : Participant :=
  { constructed
      [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
       ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩] [1, 2, 0] with
    outputs := [.data .boolean, .data .boolean, .transcript "suite"] }
def falsePair := executePair model program context constantProducer falseValidator inputs inputs tableOracle ()
def falseValidation := validate model program context falseValidator inputs [] tableOracle ()
def falseResult : Result model.toCarriers :=
  ⟨[.data (.boolean false), .data (.boolean true), .transcript "suite" []],
    [.transcript "suite" [], .data (.boolean false), .data (.boolean true)]⟩

example : falsePair.validator = some falseValidation := by rfl
example : falseValidation.outcome = .returned falseResult := by rfl
example : Domain.acceptanceAt 1 falseResult.values = some true := by rfl
example : ¬ Domain.PairExecution.Success 0 falsePair :=
  Domain.PairExecution.false_fails _ _ falseValidation rfl falseResult rfl rfl

-- A successful verifier return cannot hide an unread generated payload.
example (execution : PairExecution model.toCarriers Unit)
    (checked : PIR.Execution (RuntimeState model.toCarriers Unit) (Event model.toCarriers)
      (Result model.toCarriers)) (selected : execution.validator = some checked)
    (leftover : checked.state.proof ≠ []) : ¬ Domain.PairExecution.Success 0 execution :=
  Domain.PairExecution.unread_fails _ _ _ selected leftover

-- Completed but false selected returns are failures, even when another
-- Boolean returned by the same verifier is true.
example (execution : PairExecution model.toCarriers Unit)
    (checked : PIR.Execution (RuntimeState model.toCarriers Unit) (Event model.toCarriers)
      (Result model.toCarriers)) (selected : execution.validator = some checked)
    (result : Result model.toCarriers) (returned : checked.outcome = .returned result)
    (rejected : Domain.acceptanceAt 0 result.values = some false) :
    ¬ Domain.PairExecution.Success 0 execution := by
  rintro ⟨_, actual, value, _, same, completed, _, accepted⟩
  rw [selected] at same
  cases Option.some.inj same
  rw [returned] at completed
  cases PIR.Outcome.returned.inj completed
  rw [rejected] at accepted
  cases accepted

#print axioms accepts_all_tables
#print axioms perfect
#print axioms stopped_failure
#print axioms FiatShamir.HonestCompiled.eval_computation
#print axioms Domain.PairExecution.false_fails
end TestsSecurity.HonestCompiled

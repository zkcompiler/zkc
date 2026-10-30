import ZkcSecurityExamples.Components.GkrFiniteCalls
import TestsSecurity.GkrRoundsReference

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.GkrFiniteGate
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcSecurity.Examples.Components
open ZkcSecurity.Families.Sumcheck

/-- A stateful honest delivery script; all actions are retained as observations. -/
def handler : PIR.Handler (participantInterface ℚ ℚ) (List ℚ) (participantInterface ℚ ℚ).Op
  | action@(.send ..), state => ⟨.returned (), state, [action]⟩
  | action@(.query ..), state => ⟨.returned (0 : ℚ), state, [action]⟩
  | action@(.receive (.field _) _ _), state =>
    match state with
    | value :: rest => ⟨.returned value, rest, [action]⟩
    | [] => ⟨.stopped .refused, [], [action]⟩
  | action@(.receive _ _ _), state => ⟨.stopped .refused, state, [action]⟩

def coefficients : List ℚ := [120, -15, -105, 0, 64, 56]

def roundEvents (ctx : ProtocolContext) : List (participantInterface ℚ ℚ).Op :=
  [.receive (.field GkrRoundsBinding.field) (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0") (ctx.roles 0),
   .receive (.field GkrRoundsBinding.field) (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1") (ctx.roles 0),
   .receive (.field GkrRoundsBinding.field) (qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_2") (ctx.roles 0),
   GkrRoundsBinding.query ctx 83,
   .send (ty := .field GkrRoundsBinding.field)
     (qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0") (ctx.roles 0) 0]

/-- Actual state, messages, query service, deliveries and unread suffix. -/
theorem honest_gate_run (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (suffix : List ℚ) :
    (GkrFiniteCalls.call (G := ℚ) 83 ⟨ctx, 0, 120⟩).run handler (coefficients ++ suffix) =
      ⟨.returned true, suffix, roundEvents ctx ++ roundEvents ctx⟩ := by
  unfold GkrFiniteCalls.call
  rw [GkrFiniteGate.binding 2 (by decide) ctx distinct 83 _ (GkrCallerRealization.reference 0) _
    (GkrCallerRealization.represented 0)]
  dsimp only [GkrRoundsBinding.program, Program.remaining]
  norm_num [GkrRoundsBinding.program, Program.remaining, GkrRoundsBinding.receive,
    GkrRoundsBinding.delivery, GkrRoundsBinding.query, PIR.Process.run, PIR.Process.bind,
    PIR.Execution.follow, PIR.run_bind, handler, coefficients, GkrRoundsBinding.initial,
    GkrRoundsBinding.advance, GkrRoundsReference.restrict, GkrRoundsReference.total,
    GkrCallerRealization.reference, GkrCallerRealization.addTable, GkrCallerRealization.mulTable,
    GkrCallerRealization.below, GkrRoundsLayout.state, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, GkrRoundsLayout.leading, GkrRoundsLayout.trailing,
    Zkc.Polynomial.Multilinear.booleanSum, Zkc.Polynomial.Multilinear.fixFirst,
    Zkc.Polynomial.Multilinear.half, Message.coefficientTriples, Message.ofTriple,
    Zkc.Protocols.AlgebraicRounds.Message.boundary, Zkc.Protocols.AlgebraicRounds.Message.evaluate,
    Zkc.Protocols.AlgebraicRounds.Gate.value, roundEvents]

theorem honest_gate (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (suffix : List ℚ) :
    ((GkrFiniteCalls.call (G := ℚ) 83 ⟨ctx, 0, 120⟩).run handler (coefficients ++ suffix)).outcome =
      .returned true := congrArg PIR.Execution.outcome (honest_gate_run ctx distinct suffix)

/-- Every selected child has its own immutable source-label prefix. -/
def inputs (count : Nat) (wrong : Bool) : List (GkrFiniteCalls.Input ℚ) :=
  (List.range count).map fun index =>
    ⟨{ applicationPrefix := some ("gate" ++ protocolSiteDecimal index) }, 0, if wrong then 121 else 120⟩

theorem inputs_valid (count : Nat) (wrong : Bool) : GkrFiniteCalls.Valid (inputs count wrong) := by
  intro input member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact RosterDistinct.root 1 2

theorem inputs_false (count : Nat) (positive : 0 < count) :
    ∃ input ∈ inputs count true, GkrFiniteCalls.FalseInput input := by
  refine ⟨⟨{ applicationPrefix := some ("gate" ++ protocolSiteDecimal 0) }, 0, 121⟩, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨0, List.mem_range.mpr positive, rfl⟩
  · norm_num [GkrFiniteCalls.FalseInput, GkrCallerRealization.honestClaim]

def proof (count : Nat) : List ℚ := (List.replicate count coefficients).flatten

/-- One resource-sensitive composition proof, instantiated below at 1/2/4.
No local success premise is imposed on an empty or exhausted proof buffer. -/
theorem honest_composed (count : Nat) (suffix : List ℚ) : ∃ events,
    (GkrFiniteCalls.verifier (G := ℚ) 83 (inputs count false)).run handler (proof count ++ suffix) =
      ⟨.returned true, suffix, events⟩ := by
  let invariant := fun (remaining : List (GkrFiniteCalls.Input ℚ)) (buffer : List ℚ) =>
    (∀ input ∈ remaining, input.point = 0 ∧ input.claim = 120 ∧ RosterDistinct input.context 1 2) ∧
      buffer = proof remaining.length ++ suffix
  have step : ∀ input rest h, invariant (input :: rest) h → ∃ next events,
      (GkrFiniteCalls.call (G := ℚ) 83 input).run handler h = ⟨.returned true, next, events⟩ ∧
        invariant rest next := by
    intro input rest h ready
    obtain ⟨point, claim, distinct⟩ := ready.1 input List.mem_cons_self
    refine ⟨proof rest.length ++ suffix, roundEvents input.context ++ roundEvents input.context, ?_, ?_⟩
    · rw [ready.2]
      have same : input = ⟨input.context, 0, 120⟩ := by cases input; simp_all
      rw [same]
      simpa only [List.length_cons, proof, List.replicate_succ, List.flatten_cons, List.append_assoc]
        using honest_gate_run input.context distinct (proof rest.length ++ suffix)
    · exact ⟨fun item member => ready.1 item (List.mem_cons_of_mem input member), rfl⟩
  have initial : invariant (inputs count false) (proof count ++ suffix) := by
    constructor
    · intro input member
      obtain ⟨index, member, rfl⟩ := List.mem_map.mp member
      exact ⟨rfl, rfl, RosterDistinct.root 1 2⟩
    · simp only [inputs, List.length_map, List.length_range]
  obtain ⟨final, events, run, complete⟩ := FiniteCalls.honest_run_invariant
    (GkrFiniteCalls.call (G := ℚ) 83) handler invariant step (inputs count false) _ initial
  have finalEq : final = suffix := by simpa [invariant, proof] using complete.2
  exact ⟨events, finalEq ▸ run⟩

variable {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
  {absorb : Zkc.Transcript.Interface (participantInterface ℚ ℚ) E P Raw}
  {charge : List E → E → ENNReal}

/-- The very same composed imported verifier under arbitrary received triples. -/
def rejected_composed (count : Nat) (positive : 0 < count)
    (queries : QueryInterface (GkrRoundsBinding.program (F := ℚ) (G := ℚ) 83) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation 83) 2 2 charge)
    (history : List E) :=
  GkrFiniteCalls.rejected 83 (inputs count true) (inputs_valid count true)
    (inputs_false count positive) queries sampling history

example : ∃ events, (GkrFiniteCalls.verifier (G := ℚ) 83 (inputs 1 false)).run handler (proof 1) =
    ⟨.returned true, [], events⟩ := by simpa using honest_composed 1 []
example : ∃ events, (GkrFiniteCalls.verifier (G := ℚ) 83 (inputs 2 false)).run handler (proof 2) =
    ⟨.returned true, [], events⟩ := by simpa using honest_composed 2 []
example : ∃ events, (GkrFiniteCalls.verifier (G := ℚ) 83 (inputs 4 false)).run handler (proof 4) =
    ⟨.returned true, [], events⟩ := by simpa using honest_composed 4 []

/-- Zero rounds is a direct terminal check, not a zero-error assertion from an
empty schedule. Wrong constant claims are actually rejected. -/
theorem zero_false (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) :
    GkrFiniteGate.verifier (F := ℚ) (G := ℚ) 0 ctx 83
      ⟨[0], [0], [1], [1]⟩ 1 = .done false := by
  unfold GkrFiniteGate.verifier
  rw [GkrRoundsBinding.zero ctx distinct]
  norm_num [GkrFiniteGate.finish, GkrFiniteGate.terminalValue, GkrFiniteGate.restrictList,
    Values.get, PIR.Process.bind, Zkc.Protocols.AlgebraicRounds.Gate.value]

example : ¬ GkrRoundsReference.admissible TestsSecurity.GkrRoundsReference.cubicState :=
  TestsSecurity.GkrRoundsReference.cubic_refuses
example : (GkrRoundsReference.message TestsSecurity.GkrRoundsReference.cubicState).evaluate 2 ≠
    GkrRoundsReference.total (GkrRoundsReference.restrict TestsSecurity.GkrRoundsReference.cubicState 2) :=
  TestsSecurity.GkrRoundsReference.cubic_off_cube

#print axioms GkrFiniteGate.binding
#print axioms GkrFiniteCircuit.reference_total
#print axioms GkrFiniteCircuit.active_independence
#print axioms GkrFiniteCircuit.degree_two
#print axioms GkrFiniteGate.rejected
#print axioms GkrFiniteGate.honest_run
#print axioms GkrFiniteCalls.binding
#print axioms GkrFiniteCalls.rejected
#print axioms honest_gate
#print axioms honest_composed
#print axioms rejected_composed
#print axioms zero_false
end TestsSecurity.GkrFiniteGate

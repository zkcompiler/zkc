module

public import ZkcSecurity.Examples.Components.TwoSumsValidatorLeftRound
public import ZkcSecurity.Examples.Components.TwoSumsValidatorRightRound
public import ZkcSecurity.Examples.Components.SumcheckValidatorHelpers
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution

@[expose] public section
noncomputable section

/-! The full actual sequential validator. The second child consumes the first
child's complete returned frame and actual reached history, including when its
Boolean is false. The final helper computes the actual conjunction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Components.TwoSums.Validator
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
open ZkcSecurity.FiatShamir.DomainReduction
open ZkcExamples.Structured ZkcExamples.Structured.Generated.Constructed
open ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev field := ValidatorLeftRound.field
abbrev context := ValidatorLeftRound.context
abbrev program := ValidatorLeftRound.program
abbrev suite := "merlin3.bls12-381.fr64be/0"

theorem context_suite : ValidatorLeftRound.context.suite = suite := rfl
theorem right_context_suite : ValidatorRightRound.context.suite = suite := rfl

def inputs (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector field left), .data (.vector field right), .data (.field field leftClaim),
    .data (.field field rightClaim), .data (.index count), .transcript suite history]

def leftCaptured (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  inputs left right leftClaim rightClaim count history ++ [.data (.vector field [])]

def decision (raw : List F) (state : CompiledValidator.State F G) : Bool :=
  decide (PrimitiveLibrary.HasShape raw state.point.length 1 ∧
    (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum = state.scalar)

def rightCaptured (capture output : Domain.Environment (uniformCarriers F G)) (leftAccepted : Bool) :
    Domain.Environment (uniformCarriers F G) :=
  (capture ++ output ++ [.data (.boolean leftAccepted)]) ++ [.data (.vector field [])]

noncomputable def finish (right : List F) (capture : Domain.Environment (uniformCarriers F G))
    (leftAccepted : Bool) (output : Domain.Environment (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) :=
  match CompiledValidator.decode output with
  | none => .halt .refused
  | some state =>
      if right.length < indexLimit then
        let rightAccepted := decision right state
        let accepted := leftAccepted && rightAccepted
        .done ⟨[.data (.boolean accepted), .transcript suite state.history],
          (capture ++ output ++ [.data (.boolean rightAccepted)]) ++ [.data (.boolean accepted)]⟩
      else .halt .exhausted

noncomputable def afterLeft (left right : List F) (rightClaim : F) (count : Nat)
    (capture output : Domain.Environment (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) :=
  match CompiledValidator.decode output with
  | none => .halt .refused
  | some state =>
      if left.length < indexLimit then
        let leftAccepted := decision left state
        ((CompiledValidator.run field ValidatorRightRound.sites (List.range count) ⟨[], rightClaim, state.history⟩).bind
          (fun final => .done (CompiledValidator.carried field suite final))).bind
            (finish right (rightCaptured capture output leftAccepted) leftAccepted)
      else .halt .exhausted

noncomputable def presented (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) :=
  if count ≤ 4 then
    ((CompiledValidator.run field ValidatorLeftRound.sites (List.range count) ⟨[], leftClaim, history⟩).bind
      (fun final => .done (CompiledValidator.carried field suite final))).bind
        (afterLeft left right rightClaim count (leftCaptured left right leftClaim rightClaim count history))
  else .halt .refused

 theorem bridge (left right : List F) (leftClaim rightClaim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Bridge (Nominal.interface (G := G) field) (fun _ _ => True) history
      (Domain.participant (ringModel F G) program context TwoSumsValidator.artifact
        (inputs left right leftClaim rightClaim count history))
      (presented left right leftClaim rightClaim count history) := by
  have emptyLaw := SumcheckDomainHelpers.empty (F := F) (G := G) program domain_bodies.sumcheck
  by_cases allowed : count ≤ 4
  all_goals
    rw [TwoSumsValidator.participant_eq]
    simp only [TwoSumsValidator.view, Domain.View.participant, TwoSumsValidator.inputSorts,
      TwoSumsValidator.outputSorts, TwoSumsValidator.returned, inputs, field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, Domain.sortsMatch,
      Domain.Value.sort, Domain.Payload.ty, field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, List.map_cons, List.map_nil, beq_self_eq_true,
      ite_true, presented, allowed, ite_false]
    unfold_component_bodies [TwoSumsValidator.view]
    normalize_table_validator [emptyLaw] unfolding [field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, allowed, ite_false]
  · conv => arg 4; simp only [PIR.Process.bind_assoc]
    validator_capture actualLeftCaptured
    have loops := CompiledValidator.loop_bridge ValidatorLeftRound.connection actualLeftCaptured
      (List.range count) ⟨[], leftClaim, history⟩
    simp only [show actualLeftCaptured.length = round0.validatorCapture from rfl, Nat.reduceAdd] at loops
    rw [← round0.validator_block F G program context rfl] at loops
    simp only [context_suite] at loops
    apply loops.bind
    intro reached leftOutput post
    obtain ⟨leftState, historyEq, lengthEq, rfl⟩ := post
    have pointLength : leftState.point.length = count := by
      simpa only [List.length_nil, Nat.zero_add, List.length_range] using lengthEq
    have small : leftState.point.length < 64 := by omega
    have terminal := SumcheckValidatorHelpers.terminal_all (F := F) (G := G) program domain_bodies
      left leftState.point leftState.scalar small
    subst reached
    simp only [afterLeft, CompiledValidator.carried, CompiledValidator.decode]
    normalize_table_validator [terminal, emptyLaw] unfolding [actualLeftCaptured, leftCaptured, inputs, field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, allowed, ite_false]
    by_cases leftBound : left.length < indexLimit
    · normalize_table_validator [emptyLaw] unfolding [field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, leftBound, allowed, ite_false]
      conv => arg 4; simp only [PIR.Process.bind_assoc]
      validator_capture actualRightCaptured
      have loops := CompiledValidator.loop_bridge ValidatorRightRound.connection actualRightCaptured
        (List.range count) ⟨[], rightClaim, leftState.history⟩
      simp only [show actualRightCaptured.length = round1.validatorCapture from rfl, Nat.reduceAdd] at loops
      rw [← round1.validator_block F G program context rfl] at loops
      simp only [right_context_suite] at loops
      apply loops.bind
      intro reached rightOutput post
      obtain ⟨rightState, historyEq, lengthEq, rfl⟩ := post
      have pointLength : rightState.point.length = count := by
        simpa only [List.length_nil, Nat.zero_add, List.length_range] using lengthEq
      have small : rightState.point.length < 64 := by omega
      have terminal := SumcheckValidatorHelpers.terminal_all (F := F) (G := G) program domain_bodies
        right rightState.point rightState.scalar small
      subst reached
      simp only [finish, CompiledValidator.carried, CompiledValidator.decode]
      normalize_table_validator [terminal] unfolding [actualRightCaptured, actualLeftCaptured, rightCaptured, leftCaptured, inputs, decision, field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, ite_false]
      by_cases rightBound : right.length < indexLimit
      · normalize_table_validator [] unfolding [actualRightCaptured, actualLeftCaptured, rightCaptured, leftCaptured, inputs, decision, field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq, suite, context_suite, right_context_suite, ValidatorRightRound.field, ValidatorRightRound.field_eq, List.length_cons, List.length_nil, leftBound, rightBound, ite_false]
        exact .done _ _ trivial
      · simp only [rightBound, ite_false, PIR.Process.bind]
        exact .halt _ .exhausted
    · simp only [leftBound, ite_false, PIR.Process.bind]
      exact .halt _ .exhausted
  · exact .halt _ .refused

#print axioms bridge

end ZkcSecurity.Examples.Components.TwoSums.Validator

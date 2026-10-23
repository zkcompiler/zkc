module

public import ZkcSecurity.Examples.Components.TwoSumsValidatorLeftRound
public import ZkcSecurity.Examples.Components.TwoSumsValidatorRightRound
public import ZkcSecurity.Examples.Components.SumcheckValidatorHelpers
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution
public meta import ZkcSecurity.Tools.ComponentBridge

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
  have leftLoop := sourceLoop field program context round0.plan.toPlan ValidatorLeftRound.sites
    ValidatorLeftRound.connection _ _ (round0.validator_block F G program context rfl)
  have rightLoop := sourceLoop field program context round1.plan.toPlan ValidatorRightRound.sites
    ValidatorRightRound.connection _ _ (round1.validator_block F G program context rfl)
  dsimp only [round0.validatorCapture, round0.descriptor] at leftLoop
  dsimp only [round1.validatorCapture, round1.descriptor] at rightLoop
  simp only [field, ValidatorLeftRound.field_eq, context_suite, suite, Nat.reduceAdd,
    CompiledValidator.carried] at leftLoop rightLoop
  rw [TwoSumsValidator.participant_eq]
  simp only [TwoSumsValidator.view, Domain.View.participant, TwoSumsValidator.inputSorts,
    TwoSumsValidator.outputSorts, TwoSumsValidator.returned, inputs, field, ValidatorLeftRound.field,
    ValidatorLeftRound.field_eq, suite, Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, context_suite,
    List.map_cons, List.map_nil, beq_self_eq_true, ite_true]
  unfold_component_bodies [TwoSumsValidator.view]
  compose_component_bridge [leftLoop, rightLoop]
    normalizing (
      try (rename_i reached output post; obtain ⟨state, historyEq, lengthEq, rfl⟩ := post; subst reached; simp only [List.length_nil, List.length_range, Nat.zero_add] at *)
      repeat first
        | fail_if_no_progress (simp (disch := omega) only [SumcheckValidatorHelpers.terminal_all program domain_bodies])
        | fail_if_no_progress (
            normalize_table_validator [emptyLaw] unfolding
              [Validator.presented, Validator.afterLeft, Validator.finish, Validator.decision,
                CompiledValidator.decode, CompiledValidator.carried, rightCaptured, leftCaptured, inputs,
                field, ValidatorLeftRound.field, ValidatorLeftRound.field_eq,
                ValidatorRightRound.field, ValidatorRightRound.field_eq, suite, context_suite, right_context_suite,
                List.length_nil, List.length_range, Nat.zero_add]
            try simp_all only [ite_true, ite_false])
        | fail_if_no_progress (conv => arg 4; simp only [PIR.Process.bind_assoc]))
    solving rfl
    finishing trivial


#print axioms bridge

end ZkcSecurity.Examples.Components.TwoSums.Validator

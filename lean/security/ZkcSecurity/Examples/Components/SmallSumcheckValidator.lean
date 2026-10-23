module

public import ZkcSecurity.Examples.Components.SmallSumcheckValidatorRound
public import ZkcSecurity.Examples.Components.SumcheckValidatorHelpers
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution
public meta import ZkcSecurity.Tools.ComponentBridge

@[expose] public section
noncomputable section

/-! Full actual SmallSumcheck validator connection: ABI, setup, bounded loop,
terminal helper, complete return map and retained SSA frame. All typed raw
tables and counts are admitted by this theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Components.SmallSumcheck.Validator
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
open ZkcSecurity.FiatShamir.DomainReduction
open ZkcExamples.Structured
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
open ZkcExamples.Structured.Generated.Constructed

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev field := ValidatorRound.field
abbrev context := ValidatorRound.context
abbrev program := ValidatorRound.program
abbrev suite := "merlin3.bls12-381.fr64be/0"

theorem context_suite : ValidatorRound.context.suite = suite := rfl

def inputs (raw : List F) (claim : F) (count : Nat) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector field raw), .data (.field field claim), .data (.index count), .transcript suite history]

def captured (raw : List F) (claim : F) (count : Nat) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  inputs raw claim count history ++ [.data (.vector field [])]

noncomputable def finish (raw : List F) (capture : Domain.Environment (uniformCarriers F G))
    (output : Domain.Environment (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) :=
  match CompiledValidator.decode output with
  | none => .halt .refused
  | some state =>
      if raw.length < indexLimit then
        let accepted := decide (PrimitiveLibrary.HasShape raw state.point.length 1 ∧
          (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum = state.scalar)
        .done ⟨[.data (.boolean accepted), .transcript suite state.history],
          capture ++ output ++ [.data (.boolean accepted)]⟩
      else .halt .exhausted

noncomputable def presented (raw : List F) (claim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) :=
  if count ≤ 2 then
    ((CompiledValidator.run field ValidatorRound.sites (List.range count) ⟨[], claim, history⟩).bind
      (fun final => .done (CompiledValidator.carried field suite final))).bind
        (finish raw (captured raw claim count history))
  else .halt .refused

 theorem bridge (raw : List F) (claim : F) (count : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Bridge (Nominal.interface (G := G) field) (fun _ _ => True) history
      (Domain.participant (ringModel F G) program context SmallSumcheckValidator.artifact (inputs raw claim count history))
      (presented raw claim count history) := by
  have emptyLaw := SumcheckDomainHelpers.empty (F := F) (G := G) program helper_bodies.sumcheck
  have loopLaw := sourceLoop field program context round0.plan.toPlan ValidatorRound.sites
    ValidatorRound.connection _ _ (round0.validator_block F G program context rfl)
  dsimp only [round0.validatorCapture, round0.descriptor] at loopLaw
  simp only [field, ValidatorRound.field_eq, context_suite, suite, Nat.reduceAdd, CompiledValidator.carried] at loopLaw
  rw [SmallSumcheckValidator.participant_eq]
  simp only [SmallSumcheckValidator.view, Domain.View.participant, SmallSumcheckValidator.inputSorts,
    SmallSumcheckValidator.outputSorts, SmallSumcheckValidator.returned, inputs, field, ValidatorRound.field,
    ValidatorRound.field_eq, suite, Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, context_suite,
    List.map_cons, List.map_nil, beq_self_eq_true, ite_true]
  unfold_component_bodies [SmallSumcheckValidator.view]
  compose_component_bridge [loopLaw]
    normalizing (
      try (rename_i reached output post; obtain ⟨state, historyEq, lengthEq, rfl⟩ := post; subst reached; simp only [List.length_nil, List.length_range, Nat.zero_add] at *)
      repeat first
        | fail_if_no_progress (simp (disch := omega) only [SumcheckValidatorHelpers.terminal_all program helper_bodies])
        | fail_if_no_progress (
            normalize_table_validator [emptyLaw] unfolding
              [Validator.presented, Validator.finish, CompiledValidator.decode, CompiledValidator.carried,
                captured, inputs, field, ValidatorRound.field, ValidatorRound.field_eq, suite, context_suite,
                List.length_nil, List.length_range, Nat.zero_add]
            try simp_all only [ite_true, ite_false])
        | fail_if_no_progress (conv => arg 4; simp only [PIR.Process.bind_assoc]))
    solving rfl
    finishing trivial


#print axioms bridge

end ZkcSecurity.Examples.Components.SmallSumcheck.Validator

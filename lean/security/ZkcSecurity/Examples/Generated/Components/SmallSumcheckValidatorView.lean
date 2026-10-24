module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
public import ZkcSecurity.Realizations.Sumcheck.ValidatorHelpers
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorOrigins
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution
public import Zkc.Source.Structured.BodyBindings
public meta import ZkcSecurity.Tools.ComponentView

@[expose] public section
noncomputable section

/-! Generated from the retained pair by ZkcSecurity.Generation.SumcheckViews.
The generic constructor infers the full presentation and proves its bridge.
All source guards, complete returns and exact stopped outcomes are retained.
Regenerate; do not hand edit. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
open ZkcSecurity.FiatShamir.DomainReduction
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

abbrev program := ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program
abbrev context := ZkcSecurity.Examples.Generated.SmallSumcheck.subject.selection.context
abbrev field := ("bls12-381.fr")
abbrev suite := ("merlin3.bls12-381.fr64be/0")
theorem context_suite : context.suite = suite := rfl

theorem helper_bodies : DomainHelpers.Bodies program := by
  bind_structured_bodies

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (input0 : List F) (input1 : F) (input2 : Nat) (input3 : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector ("bls12-381.fr") input0), .data (.field ("bls12-381.fr") input1), .data (.index input2), .transcript ("merlin3.bls12-381.fr64be/0") input3]

theorem round0_field : round0.plan.field = field := rfl
theorem round0_connection : CompiledValidator.RoundConnection (F := F) (G := G)
    round0.plan.field program context round0.plan.toPlan round0.schedule := by
  apply CompiledValidator.connectionOfOrigins round0.plan program context round0.bases round0.origins_checked
  intro point challenge
  exact DomainHelpers.append (F := F) (G := G) program helper_bodies.sumcheck point challenge

noncomputable def assembled (input0 : List F) (input1 : F) (input2 : Nat) (input3 : Domain.History (uniformCarriers F G)) :
    {presented : PIR.Process (Nominal.signature F field) (Domain.Result (uniformCarriers F G)) //
      Bridge (Nominal.interface (G := G) field) (fun _ _ => True) input3
        (Domain.participant (ringModel F G) program context ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact
          (inputs input0 input1 input2 input3)) presented} := by
  have emptyLaw := DomainHelpers.empty (F := F) (G := G) program helper_bodies.sumcheck
  have round0Rule := sourceLoopBind (B := Domain.Result (uniformCarriers F G))
    round0.plan.field program context round0.plan.toPlan round0.schedule
    round0_connection _ _ (round0.validator_block F G program context rfl)
  dsimp only [round0.validatorCapture, round0.descriptor] at round0Rule
  simp only [round0_field, field, context_suite, suite, Nat.reduceAdd, CompiledValidator.carried] at round0Rule
  construct_component_view [round0Rule]
    normalizing (
      try (
        rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.participant_eq]
        simp only [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.view, Domain.View.participant, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.inputSorts,
          ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.outputSorts, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.returned, inputs, field, suite, context_suite,
          Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons, List.map_nil,
          beq_self_eq_true, ite_true]
        unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.view])
      try simp only [List.length_nil, List.length_range, Nat.zero_add] at *
      repeat first
        | fail_if_no_progress (simp (disch := omega) only [ValidatorHelpers.terminal_all program helper_bodies])
        | fail_if_no_progress (
            normalize_table_validator [emptyLaw] unfolding
              [CompiledValidator.carried, round0_field, field, suite, context_suite,
                List.length_nil, List.length_range, Nat.zero_add]
            try simp_all only [ite_true, ite_false])
        | fail_if_no_progress (conv => arg 4; simp only [PIR.Process.bind_assoc]))
    solving rfl
    finishing trivial

project_checked_view assembled as presented with bridge

end ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView

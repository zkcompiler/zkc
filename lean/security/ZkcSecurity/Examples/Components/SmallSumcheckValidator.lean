module

public import ZkcSecurity.Examples.Components.SmallSumcheckValidatorRound
public import ZkcSecurity.Examples.Components.SumcheckValidatorHelpers
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorExecution

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
  by_cases allowed : count ≤ 2
  all_goals
    rw [SmallSumcheckValidator.participant_eq]
    simp only [SmallSumcheckValidator.view, Domain.View.participant, SmallSumcheckValidator.inputSorts,
      SmallSumcheckValidator.outputSorts, SmallSumcheckValidator.returned, inputs, field, ValidatorRound.field, ValidatorRound.field_eq, suite, Domain.sortsMatch,
      Domain.Value.sort, Domain.Payload.ty, context_suite, List.map_cons, List.map_nil, beq_self_eq_true, ite_true,
      presented, allowed, ite_false]
    unfold_component_bodies [SmallSumcheckValidator.view]
    normalize_table_validator [emptyLaw] unfolding [ValidatorRound.field_eq, context_suite, allowed, ite_false]
  · conv => arg 4; simp only [PIR.Process.bind_assoc]
    validator_capture actualCaptured
    have loops := CompiledValidator.loop_bridge ValidatorRound.connection actualCaptured
      (List.range count) ⟨[], claim, history⟩
    simp only [show actualCaptured.length = round0.validatorCapture from rfl, Nat.reduceAdd] at loops
    rw [← round0.validator_block F G program context rfl] at loops
    simp only [context_suite] at loops
    apply loops.bind
    intro reached output post
    obtain ⟨state, historyEq, lengthEq, rfl⟩ := post
    have pointLength : state.point.length = count := by
      simpa only [List.length_nil, Nat.zero_add, List.length_range] using lengthEq
    have small : state.point.length < 64 := by omega
    have terminal := SumcheckValidatorHelpers.terminal_all (F := F) (G := G) program helper_bodies raw state.point state.scalar small
    subst reached
    simp only [CompiledValidator.carried, finish, CompiledValidator.decode]
    by_cases bounded : raw.length < indexLimit
    all_goals
      normalize_table_validator [terminal] unfolding [actualCaptured, captured, inputs, field, ValidatorRound.field, ValidatorRound.field_eq, suite, context_suite, bounded, ite_false]
    · exact .done _ _ trivial
    · exact .halt _ .exhausted
  · exact .halt _ .refused

#print axioms bridge

end ZkcSecurity.Examples.Components.SmallSumcheck.Validator

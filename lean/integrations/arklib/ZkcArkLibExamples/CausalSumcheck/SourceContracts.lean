module

public import ZkcArkLibExamples.CausalSumcheck.SourceVerifier
public import ZkcExamples.Structured.SumcheckContractRequests

@[expose] public section

/-! Source-bound false-claim experiments. Inputs are selected from actual masked
component/application boundaries, and acceptance is the declared target decision.
The reduction exports a typed external request against one fixed original table.
These retained run roots are components, not selected proof Entries. -/
namespace ZkcSecurity.Examples.CausalSumcheck.SourceContracts
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open ZkcSecurity.VCVio.Execution ZkcSecurity.VCVio.StructuredUniform
open ZkcSecurity.Examples.CausalSumcheck.UniformService
open SumcheckContractBindings SumcheckContractInterpretations SumcheckContractRequests
open scoped ENNReal

set_option smartUnfolding false

variable {F G S E : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
variable {sourceEnvironment : RelationEnvironment SumcheckSourceViews.imported F G}
variable {reductionEnvironment : RelationEnvironment SumcheckReduceViews.imported F G}

/-- The request includes formula adequacy and its capacity domain at V's actual
read inputs. Its refutation is inherited by Reduce's initial_sum in this same
snapshot. The bound composes the residual theorem with the actual terminal. -/
theorem public_target_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (n : Nat) (rawV : List F) (table : Table F n)
    (decoded : ofList? n rawV = some table) (claim : F) (handle : Nat)
    (falseTarget : (publicRefutation (G := G) (sourceEnvironment := sourceEnvironment)
      rawV claim n handle).Meaning) (bounded : rawV.length < indexLimit) (state : S) :
    mass (do
      let execution ← ((publicInput (G := G) rawV claim n handle).process.interpret forgetSites).runM
        (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after) state
      pure ((publicInput rawV claim n handle).returnedEvent
        ((publicContract (sourceEnvironment := sourceEnvironment)).Accepts {}
          (publicOwner.namedClause "public_sum"))
        execution.outcome)) ≤ (n : ENNReal) / Fintype.card F := by
  have child := child_refutation rawV claim n handle (.stopped .incomplete) falseTarget
    (public_translation rawV claim n handle (.stopped .incomplete) bounded)
  have bound := SourceVerifier.source_composed_bound network before after n rawV table decoded
    bounded claim handle child state
  have observed : (fun execution : PIR.Execution S E (Values (Component (assignment F G)) [.boolean]) =>
      (publicInput rawV claim n handle).returnedEvent
        ((publicContract (sourceEnvironment := sourceEnvironment)).Accepts {}
          (publicOwner.namedClause "public_sum")) execution.outcome) =
      (fun execution => returnedSatisfies (fun outputs => outputs.get .here = some true) execution) := by
    funext execution
    exact propext (public_accepts rawV claim n handle execution.outcome)
  change mass (do
    let execution ← (SumcheckSourceViews.imported.program.participant F G 1
      (SumcheckSourceVerifier.sourceRootInputs (some rawV) (some claim) (some n) (some handle))).runM
      (withUniformQueries network [queryKey SumcheckSourceVerifier.childContext handle] before after) state
    pure ((publicInput rawV claim n handle).returnedEvent
      ((publicContract (sourceEnvironment := sourceEnvironment)).Accepts {}
        (publicOwner.namedClause "public_sum")) execution.outcome)) ≤ _
  refine Eq.trans_le ?_ bound
  apply congrArg mass
  apply bind_congr
  intro execution
  exact congrArg pure (congrFun observed execution)

/-- The terminal request reads the actual returned boundary of the wrapper.
Parameters are the same raw table, remaining dimension and count used by its
input refutation; no independently chosen table occurs in the residual. -/
def residualRequest (raw : List F) (remaining count : Nat)
    (input : ComponentInput reductionRoot F G) :
    PIR.Outcome (Values (Component (assignment F G)) reductionRoot.protocol.outputs) → Prop :=
  input.returnedEvent (fun boundary =>
    (wrapperRequest (reductionEnvironment := reductionEnvironment) raw remaining count boundary).Meaning)

theorem residual_request_iff (raw : List F) (remaining count : Nat)
    (table : Table F (remaining + count)) (decoded : ofList? (remaining + count) raw = some table)
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (execution : PIR.Execution S E (Values (Component (assignment F G)) reductionRoot.protocol.outputs)) :
    residualRequest (reductionEnvironment := reductionEnvironment) raw remaining count
      (reductionRootInput proverValues proverDimension claim count handle) execution.outcome ↔
      returnedSatisfies (SourceVerifier.residualObservation remaining count table) execution := by
  cases execution with | mk outcome state events => ?_
  cases outcome with
  | stopped reason => rfl
  | returned outputs =>
    exact wrapper_terminal_iff raw remaining count table decoded proverValues proverDimension claim handle outputs

/-- Reduce's input clause is refuted at the actual child call boundary. P's
runtime inputs remain arbitrary, and the final event consumes the typed external
terminal. This root has no acceptance Boolean and makes no terminal claim. -/
theorem reduction_request_bound [Fintype F] [SampleableType F]
    (network : PIR.MonadHandler ProbComp (participantInterface F G) S E)
    (before : Key → Phase S E Unit) (after : Key → F → Phase S E Unit)
    (proverValues : Option (List F)) (proverDimension : Option Nat)
    (remaining count : Nat) (raw : List F) (table : Table F (remaining + count))
    (decoded : ofList? (remaining + count) raw = some table) (claim : F) (handle : Nat)
    (falseTarget : (reductionRefutation (G := G) (reductionEnvironment := reductionEnvironment)
      raw (remaining + count) claim count handle).Meaning) (bounded : raw.length < indexLimit) (state : S) :
    mass (do
      let execution ← ((reductionRootInput proverValues proverDimension claim count handle).process.interpret
        forgetSites).runM
        (withUniformQueries network [queryKey (ProtocolContext.enter {} "s5" [0,1]) handle] before after) state
      pure (residualRequest (reductionEnvironment := reductionEnvironment) raw remaining count
        (reductionRootInput proverValues proverDimension claim count handle) execution.outcome)) ≤
      (count : ENNReal) / Fintype.card F := by
  have bound := SourceVerifier.reduction_typed_bound network before after proverValues proverDimension
    remaining count raw table decoded claim handle falseTarget ⟨reduction_formula_law, bounded⟩ state
  have observed : (fun execution : PIR.Execution S E
      (Values (Component (assignment F G)) reductionRoot.protocol.outputs) =>
      residualRequest (reductionEnvironment := reductionEnvironment) raw remaining count
        (reductionRootInput proverValues proverDimension claim count handle) execution.outcome) =
      (fun execution => returnedSatisfies
        (SourceVerifier.wrapperResidualRequest raw remaining count proverValues proverDimension claim handle) execution) := by
    funext execution
    cases execution with | mk outcome state events => cases outcome <;> rfl
  change mass (do
    let execution ← (SumcheckReduceViews.imported.program.participant F G 1
      (SumcheckReduceVerifier.reduceRootInputs proverValues proverDimension (some claim)
        (some count) (some handle))).runM
      (withUniformQueries network [queryKey (ProtocolContext.enter {} "s5" [0,1]) handle] before after) state
    pure (residualRequest (reductionEnvironment := reductionEnvironment) raw remaining count
      (reductionRootInput proverValues proverDimension claim count handle) execution.outcome)) ≤ _
  refine Eq.trans_le ?_ bound
  apply congrArg mass
  apply bind_congr
  intro execution
  exact congrArg pure (congrFun observed execution)

end ZkcSecurity.Examples.CausalSumcheck.SourceContracts

module

public import ZkcTools.StructuredSource.InferReferenceInstallation
public import Zkc.Source.Structured.SumReferenceInstallation
public import ZkcExamples.Structured.SumcheckSourceSelections
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

@[expose] public section

/-! The same exact-body search installs a sum library in two actual sources.
No helper indices, names, finite-domain identifiers or body proofs are authored.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.ReferenceBindingInference
open Zkc.Source Zkc.Source.Structured ReferenceLibrary
open ZkcExamples.Structured.Generated.Bindings

def small : {bindings : Sum.Bindings // ∀ model,
    Sum.Bodies model SmallSumcheckInputs.program.payload.definitions "bls12-381.fr" bindings} := by
  infer_reference_installation

def two : {bindings : Sum.Bindings // ∀ model,
    Sum.Bodies model TwoSumsInputs.program.payload.definitions "bls12-381.fr" bindings} := by
  infer_reference_installation

example (model : DomainModel) (xs : List (model.Field "bls12-381.fr")) :
    invoke (Multilinear.closed model (definitions := SmallSumcheckInputs.program.payload.definitions))
      (Sum.totalHelper "bls12-381.fr" small.val) (.cons xs .nil) =
      primitiveOutcome (Sum.totalOutcome model "bls12-381.fr" xs) :=
  Sum.total_eq model SmallSumcheckInputs.program.payload.linked (small.property model) xs

example : True := by
  fail_if_success
    have wrongDomain : {bindings : Sum.Bindings // ∀ model,
        Sum.Bodies model SmallSumcheckInputs.program.payload.definitions "wrong.field" bindings} := by
      infer_reference_installation
  trivial

/-- Declaration order is not a binding identity. -/
def reordered : {bindings : Sum.Bindings // ∀ model,
    Sum.Bodies model SmallSumcheckInputs.program.payload.definitions.reverse
      "bls12-381.fr" bindings} := by
  infer_reference_installation

/-- Selection cannot silently fill unrelated author data. -/
structure ExtraBindings where
  sum : Sum.Bindings
  unrelated : String

example : True := by
  fail_if_success
    have extra : {bindings : ExtraBindings // ∀ model,
        Sum.Bodies model SmallSumcheckInputs.program.payload.definitions
          "bls12-381.fr" bindings.sum} := by
      infer_reference_installation
  trivial

/-- Exact signature matching does not erase an inconsistent dependency body. -/
structure Conflicting (model : DomainModel) (bindings : Sum.Bindings) : Prop where
  actual : Sum.Bodies model SmallSumcheckInputs.program.payload.definitions "bls12-381.fr" bindings
  different : BodyIn SmallSumcheckInputs.program.payload.definitions
    (Sum.addHelper "bls12-381.fr" bindings)
    (.letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
      (.ret (.cons .here .nil)))

example : True := by
  fail_if_success
    have contradiction : {bindings : Sum.Bindings // ∀ model, Conflicting model bindings} := by
      infer_reference_installation
  trivial

/-- A premise is not an installed association, even if it would close the goal. -/
example : True := by
  fail_if_success
    have premise : {bindings : Sum.Bindings // False → ∀ model,
        Sum.Bodies model SmallSumcheckInputs.program.payload.definitions
          "bls12-381.fr" bindings} := by
      infer_reference_installation
  fail_if_success
    have vacuous : {bindings : Sum.Bindings // True} := by
      infer_reference_installation
  trivial

/-- The selected pair relation fixes the outer chain even if the physical
library order is reversed. The other sum chain is a real ambiguity in TwoSums. -/
def anchoredReordered : {bindings : Sum.Bindings // ∀ model,
    Sum.PairBodies model TwoSumsInputs.program.payload.definitions.reverse "bls12-381.fr"
      TwoSumsInputs.helper4Helper.name bindings} := by
  infer_reference_installation

example : anchoredReordered.val =
    ZkcExamples.Structured.SumcheckSourceSelections.outerSumBindings := by kernel_rfl

example : ZkcExamples.Structured.SumcheckSourceSelections.sumBindings ≠
    ZkcExamples.Structured.SumcheckSourceSelections.outerSumBindings := by
  intro same
  have distinct : ZkcExamples.Structured.SumcheckSourceSelections.sumBindings.domain ≠
      ZkcExamples.Structured.SumcheckSourceSelections.outerSumBindings.domain := by decide +kernel
  exact distinct (congrArg Sum.Bindings.domain same)

example : True := by
  fail_if_success
    have wrongTarget : {bindings : Sum.Bindings // ∀ model,
        Sum.PairBodies model TwoSumsInputs.program.payload.definitions "bls12-381.fr"
          TwoSumsInputs.helper25Helper.name bindings} := by
      infer_reference_installation
  trivial

set_option maxHeartbeats 500000 in
/-- A partial library record does not determine its admission helpers. Refuse
as soon as the association is complete, rather than retrying every binding. -/
example : True := by
  fail_if_success
    have incomplete : {bindings : MultilinearBodies.Bindings //
        Multilinear.Bodies SmallSumcheckInputs.program.payload.definitions "bls12-381.fr" bindings} := by
      infer_reference_installation
  trivial

#print axioms ZkcExamples.Structured.SumcheckSourceSelections.scalarInstallation
#print axioms ZkcExamples.Structured.SumcheckSourceSelections.pairInstallation
#print axioms ZkcExamples.Structured.SumcheckSourceSelections.multilinearInstallation
#print axioms anchoredReordered

#print axioms small
#print axioms two
#print axioms reordered
end Tests.ReferenceBindingInference

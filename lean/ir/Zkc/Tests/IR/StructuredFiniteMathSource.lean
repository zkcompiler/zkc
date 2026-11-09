import Zkc.IR.Source.Structured.Availability
import Zkc.IR.Source.Structured.DomainComponent
import Zkc.IR.Source.Structured.NormalForm.Soundness
import Zkc.Program.Source.DerivationLaws

/-! A typed slice of the retained scalar FRI power_word fold and its two actual
callback helpers. The ABI and operations follow the unmodified original MLIR.
This slice is a source-derived control, not full-source association or a native
field-realization proof. The uniform ring model tests the generic evaluator. -/
set_option autoImplicit false
set_option maxRecDepth 2048
open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredFiniteMathSource

def field := "koala-bear.ext8-binomial3"
abbrev scalar : Ty := .field field

def formed {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, .math, inputs, outputs, body.erase, body, body.elaborate_erase⟩

def routineBody : Region dialect [scalar, scalar, .index, .index] [scalar, scalar, .index] :=
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp (.indexBitAnd) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp (.indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply field)
    (.cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.select scalar)
    (.cons (.there .here) (.cons .here
      (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.fieldMultiply field)
    (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
      (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp (.indexLogicalShiftRight)
    (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there
      (.there .here)))))))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons .here .nil)))

def routine : CheckedDefinition :=
  formed "zkl_1a2e4785483066d8b0fd3368b37363fe403d5142f89276ff62679d35b3d441f5" routineBody

def domain : DomainSpec :=
  ⟨"finite_zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca_s5_domain",
    [.index, .index], [.index], .letNode (.range .here (.there .here)) (.ret .here)⟩

def spec : FoldSpec :=
  ⟨domain, [scalar, scalar, .index], [],
    "finite_zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca_s5_body",
    "", .math⟩

def stepBody : Region dialect spec.stepHelper.inputs spec.stepHelper.outputs :=
  .letOp (.invoke routine.helper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))) .nil
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))

def step : CheckedDefinition := formed spec.step stepBody

def tables (model : DomainModel) : Evaluation.ComponentTablesOn model.toCarriers closedInterface :=
  [routine, step].foldl (Evaluation.ComponentTablesOn.extend model SiteObservations.closed) ⟨[], []⟩

theorem tables_adequate (model : DomainModel) : (tables model).Adequate :=
  Evaluation.ComponentTablesOn.adequate_fold model SiteObservations.closed _
    Evaluation.ComponentTablesOn.adequate_empty _

def model := ringModel Int Int

theorem two_bits_preserve_full_state :
    Evaluation.componentOperationOn model SiteObservations.closed (tables model) (.fold spec)
      (.cons (some 0) (.cons (some 2) (.cons (some 1) (.cons (some 2)
        (.cons (some 3) .nil))))) .nil =
      .done (.cons (some 8) (.cons (some 16) (.cons (some 0) .nil))) := rfl

theorem empty_exponent_returns_one_even_for_zero_base :
    Evaluation.componentOperationOn model SiteObservations.closed (tables model) (.fold spec)
      (.cons (some 0) (.cons (some 0) (.cons (some 1) (.cons (some 0)
        (.cons (some 0) .nil))))) .nil =
      .done (.cons (some 1) (.cons (some 0) (.cons (some 0) .nil))) := rfl

theorem empty_exponent_still_requires_base :
    Evaluation.componentOperationOn model SiteObservations.closed (tables model) (.fold spec)
      (.cons (some 0) (.cons (some 0) (.cons (some 1) (.cons none
        (.cons (some 0) .nil))))) .nil =
      .done (.cons none (.cons none (.cons none .nil))) := rfl

def body : Region protocolDialect spec.arguments spec.state :=
  .letOp (.calculate (.fold spec) rfl) (Operands.identity _) .nil
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))

theorem full_state_normalizes :
    (NormalForm.normalize {} body 0 2
      (.cons .present (.cons .present (.cons .present (.cons .present
        (.cons .present .nil)))))).isOk = true := rfl

def retainedFold : Region dialect spec.arguments spec.state :=
  .letOp (.fold spec) (Operands.identity _) .nil
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))

def twoBitInputs : Values model.Value spec.arguments :=
  .cons 0 (.cons 2 (.cons 1 (.cons 2 (.cons 3 .nil))))

/-- The existing typed derivation proves this retained source occurrence directly.
It does not consume an availability summary as a semantic premise. -/
theorem retained_fold_derivation :
    Region.Derivation
      (Evaluation.meaningOn model SiteObservations.closed (tables model).closed)
      (fun op => .call op .done) retainedFold twoBitInputs.get
      (.done (.cons 8 (.cons 16 (.cons 0 .nil)))) := by
  refine Region.Derivation.letOpReturn
    (meaning := Evaluation.meaningOn model SiteObservations.closed (tables model).closed)
    (values := .cons 8 (.cons 16 (.cons 0 .nil)))
    (Op.fold spec) (Operands.identity _) .nil ?_ ?_
  · apply RegionMeaning.OperationLaw.identity
    rfl
  · exact .ret _ _

theorem retained_fold_process :
    retainedFold.denote
      (Evaluation.meaningOn model SiteObservations.closed (tables model).closed)
      twoBitInputs.get = .done (.cons 8 (.cons 16 (.cons 0 .nil))) :=
  retained_fold_derivation.sound_identity

end Tests.StructuredFiniteMathSource

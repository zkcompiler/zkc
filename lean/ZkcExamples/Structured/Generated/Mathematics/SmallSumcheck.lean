module

public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import Zkc.Source.Structured.MathematicsAliases

@[expose] public section

/-! Generated from the selected admitted target and dependency paths.
Synthetic paths assert no compiler origin metadata. All associations and
selection equations are independently checked by the Lean kernel. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck
open Zkc.Source Zkc.Source.Structured
abbrev imported := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported
abbrev original := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.snapshot
def owner : ContractBinding imported := by bind_contract
abbrev clause := owner.clause (owner.namedClause "public_sum")
theorem target_kind : clause.kind = .target := by kernel_rfl
def relation : RelationBinding original clause.subject := by bind_contract
def formula : FormulaBinding imported relation := by bind_contract

abbrev public_sum.helper : Helper := (⟨"zkf_116f3285742dd1275b8149c69b78a6713cd6256a8af715be7c346da1c793a766", .math, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper)
def public_sum.body : Region dialect public_sum.helper.inputs public_sum.helper.outputs :=
  (.letOp (.invoke (⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here .nil) .nil (.letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))
theorem public_sum.association : BodyIn imported.program.payload.definitions public_sum.helper public_sum.body := by bind_structured_bodies

abbrev public_sum.callee.helper : Helper := (⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sum.callee.body : Region dialect public_sum.callee.helper.inputs public_sum.callee.helper.outputs :=
  (.letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil (.letOp (.fold ⟨⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here))⟩, [(.field "bls12-381.fr")], [], "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", "", .math⟩) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))
theorem public_sum.callee.association : BodyIn imported.program.payload.definitions public_sum.callee.helper public_sum.callee.body := by bind_structured_bodies

def public_sum.callee.fold : FoldSpec := ⟨⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here))⟩, [(.field "bls12-381.fr")], [], "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", "", .math⟩
theorem public_sum.callee.fold_selected : MathematicsAliases.folds public_sum.callee.body.erase = [public_sum.callee.fold] := by kernel_rfl

abbrev public_sum.callee.foldStep.helper : Helper := (⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sum.callee.foldStep.body : Region dialect public_sum.callee.foldStep.helper.inputs public_sum.callee.foldStep.helper.outputs :=
  (.letOp (.invoke (⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
theorem public_sum.callee.foldStep.association : BodyIn imported.program.payload.definitions public_sum.callee.foldStep.helper public_sum.callee.foldStep.body := by bind_structured_bodies

abbrev public_sum.callee.foldStep.calleeDependency0.helper : Helper := (⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sum.callee.foldStep.calleeDependency0.body : Region dialect public_sum.callee.foldStep.calleeDependency0.helper.inputs public_sum.callee.foldStep.calleeDependency0.helper.outputs :=
  (.letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
theorem public_sum.callee.foldStep.calleeDependency0.association : BodyIn imported.program.payload.definitions public_sum.callee.foldStep.calleeDependency0.helper public_sum.callee.foldStep.calleeDependency0.body := by bind_structured_bodies

theorem public_sum.callee.foldStep.calls : MathematicsAliases.calls public_sum.callee.foldStep.body.erase = [public_sum.callee.foldStep.calleeDependency0.helper] := by kernel_rfl

theorem public_sum.callee.fold_step : public_sum.callee.fold.stepHelper = public_sum.callee.foldStep.helper := by kernel_rfl

theorem public_sum.calls : MathematicsAliases.calls public_sum.body.erase = [public_sum.callee.helper] := by kernel_rfl

theorem public_sum.selected : formula.definition.helper = public_sum.helper := by kernel_rfl

theorem entry_final_absent : MathematicsAliases.finalMath? imported.program.payload.entry.raw = none := by kernel_rfl

end ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck

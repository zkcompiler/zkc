module

public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public import Zkc.Source.Structured.MathematicsAliases

@[expose] public section

/-! Generated from the selected admitted target and dependency paths.
Synthetic paths assert no compiler origin metadata. All associations and
selection equations are independently checked by the Lean kernel. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace ZkcExamples.Structured.Generated.Mathematics.TwoSums
open Zkc.Source Zkc.Source.Structured
abbrev imported := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported
abbrev original := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.snapshot
def owner : ContractBinding imported := by bind_contract
abbrev clause := owner.clause (owner.namedClause "public_sums")
theorem target_kind : clause.kind = .target := by kernel_rfl
def relation : RelationBinding original clause.subject := by bind_contract
def formula : FormulaBinding imported relation := by bind_contract

abbrev public_sums.helper : Helper := (⟨"zkf_71838ae694224dd160cf5b65d1bde35de122773b8eeb322b05ddaf4708d2957e", .math, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper)
def public_sums.body : Region dialect public_sums.helper.inputs public_sums.helper.outputs :=
  (.letOp (.invoke (⟨"zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here .nil) .nil (.letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.invoke (⟨"zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil (.letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))
theorem public_sums.association : BodyIn imported.program.payload.definitions public_sums.helper public_sums.body := by bind_structured_bodies

abbrev public_sums.callee.helper : Helper := (⟨"zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sums.callee.body : Region dialect public_sums.callee.helper.inputs public_sums.callee.helper.outputs :=
  (.letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil (.letOp (.fold ⟨⟨"finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here))⟩, [(.field "bls12-381.fr")], [], "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body", "", .math⟩) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))
theorem public_sums.callee.association : BodyIn imported.program.payload.definitions public_sums.callee.helper public_sums.callee.body := by bind_structured_bodies

def public_sums.callee.fold : FoldSpec := ⟨⟨"finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here))⟩, [(.field "bls12-381.fr")], [], "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body", "", .math⟩
theorem public_sums.callee.fold_selected : MathematicsAliases.folds public_sums.callee.body.erase = [public_sums.callee.fold] := by kernel_rfl

abbrev public_sums.callee.foldStep.helper : Helper := (⟨"finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sums.callee.foldStep.body : Region dialect public_sums.callee.foldStep.helper.inputs public_sums.callee.foldStep.helper.outputs :=
  (.letOp (.invoke (⟨"zkl_e6c7f1789c6410d7df7f947de61fe27fb3436c5e9f5e23ae73c9b66a88fd7d1a", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
theorem public_sums.callee.foldStep.association : BodyIn imported.program.payload.definitions public_sums.callee.foldStep.helper public_sums.callee.foldStep.body := by bind_structured_bodies

abbrev public_sums.callee.foldStep.calleeDependency0.helper : Helper := (⟨"zkl_e6c7f1789c6410d7df7f947de61fe27fb3436c5e9f5e23ae73c9b66a88fd7d1a", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def public_sums.callee.foldStep.calleeDependency0.body : Region dialect public_sums.callee.foldStep.calleeDependency0.helper.inputs public_sums.callee.foldStep.calleeDependency0.helper.outputs :=
  (.letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
theorem public_sums.callee.foldStep.calleeDependency0.association : BodyIn imported.program.payload.definitions public_sums.callee.foldStep.calleeDependency0.helper public_sums.callee.foldStep.calleeDependency0.body := by bind_structured_bodies

theorem public_sums.callee.foldStep.calls : MathematicsAliases.calls public_sums.callee.foldStep.body.erase = [public_sums.callee.foldStep.calleeDependency0.helper] := by kernel_rfl

theorem public_sums.callee.fold_step : public_sums.callee.fold.stepHelper = public_sums.callee.foldStep.helper := by kernel_rfl

theorem public_sums.calls : MathematicsAliases.calls public_sums.body.erase = [public_sums.callee.helper] := by kernel_rfl

theorem public_sums.selected : formula.definition.helper = public_sums.helper := by kernel_rfl

abbrev public_sums.entryFinal.helper : Helper := (⟨"s3h7a6b637h626f6f6c65616e4h626f7468", .math, [.boolean, .boolean], [.boolean]⟩ : Helper)
def public_sums.entryFinal.body : Region dialect public_sums.entryFinal.helper.inputs public_sums.entryFinal.helper.outputs :=
  (.letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
theorem public_sums.entryFinal.association : BodyIn imported.program.payload.definitions public_sums.entryFinal.helper public_sums.entryFinal.body := by bind_structured_bodies

theorem public_sums.entry_final : MathematicsAliases.finalMath? imported.program.payload.entry.raw =
    some public_sums.entryFinal.helper := by kernel_rfl

end ZkcExamples.Structured.Generated.Mathematics.TwoSums

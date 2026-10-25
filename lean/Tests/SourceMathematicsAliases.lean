import ZkcExamples.Structured.Generated.Mathematics.TwoSums
import ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck
import ZkcTools.StructuredSource.MathematicsAliases

/-! Focused source-selection and exact-body controls. Reordering below tests
association only: reversing a dependency-ordered table need not preserve linking. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.SourceMathematicsAliases
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.Generated.Mathematics.TwoSums

example : ZkcTools.StructuredSource.MathematicsAliases.target imported.program "missing_target" =
    .error "source-mathematics-target-clause" := by kernel_rfl

/-- Untrusted generation inputs with duplicate owners or relations refuse. -/
example : ZkcTools.StructuredSource.MathematicsAliases.target
    { imported.program with snapshot := { original with contracts := original.contracts ++ original.contracts } }
    "public_sums" = .error "source-mathematics-target-owner" := by kernel_rfl

example : ZkcTools.StructuredSource.MathematicsAliases.target
    { imported.program with snapshot := { original with relations := original.relations ++ original.relations } }
    "public_sums" = .error "source-mathematics-target-relation" := by kernel_rfl

example : ZkcTools.StructuredSource.MathematicsAliases.target
    { imported.program with snapshot := { original with
      relations := original.relations.map (fun relation => { relation with kind := "opaque" }) } }
    "public_sums" = .error "source-mathematics-formula-kind" := by kernel_rfl

example : ZkcTools.StructuredSource.MathematicsAliases.target
    { imported.program with snapshot := { original with
      relations := original.relations.map (fun relation => { relation with formula := none }) } }
    "public_sums" = .error "source-mathematics-formula-reference" := by kernel_rfl

example : ZkcTools.StructuredSource.MathematicsAliases.source imported.program "invalid.name"
    ⟨"Unused", "Unused"⟩ = .error "source-mathematics-target-spelling" := by kernel_rfl

example : True := by
  fail_if_success
    have : formula.definition.helper = public_sums.entryFinal.helper := by kernel_rfl
  trivial

/-- An existing same-ABI helper still cannot replace the target's actual callee. -/
example : True := by
  fail_if_success
    have : Structured.MathematicsAliases.calls public_sums.body.erase =
        [ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck.public_sum.callee.helper] := by
      kernel_rfl
  trivial

example : ZkcTools.StructuredSource.MathematicsAliases.definition imported.program
    { public_sums.callee.helper with name := "missing_callee" } =
    .error "source-mathematics-helper-association" := by kernel_rfl

example : Structured.MathematicsAliases.definition? imported.program.payload.definitions
    { public_sums.callee.helper with kind := .local } = none := by kernel_rfl

private def mapped : CheckedDefinition := CheckedDefinition.ofBody
    ⟨"mapped", .math, [.vector "field"], [.vector "field"]⟩
    (.letOp (.map ⟨"map_step", "field", [true]⟩) (.cons .here .nil) .nil
      (.ret (.cons .here .nil)))

/-- A helper-bearing operation outside this small graph cannot be omitted. -/
example : ZkcTools.StructuredSource.MathematicsAliases.graph imported.program 1 "mapped" mapped =
    .error "source-mathematics-map-dependency" := by kernel_rfl

example : ZkcTools.StructuredSource.MathematicsAliases.graph imported.program 0 "mapped" mapped =
    .error "source-mathematics-dependency-depth" := by kernel_rfl

private def ambiguousCalls : CheckedDefinition := CheckedDefinition.ofBody
    public_sums.callee.helper
    (.letOp (.invoke public_sums.callee.helper) (.cons .here .nil) .nil
      (.letOp (.invoke ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck.public_sum.callee.helper)
        (.cons (.there .here) .nil) .nil (.ret (.cons .here .nil))))

example : ZkcTools.StructuredSource.MathematicsAliases.graph imported.program 1 "ambiguous" ambiguousCalls =
    .error "source-mathematics-callee-ambiguity" := by kernel_rfl

private def filteredFold : CheckedDefinition := CheckedDefinition.ofBody
    public_sums.callee.helper
    (.letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil
      (.letOp (.fold { public_sums.callee.fold with predicate := "predicate" })
        (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))

example : ZkcTools.StructuredSource.MathematicsAliases.graph imported.program 1 "filtered" filteredFold =
    .error "source-mathematics-filtered-fold" := by kernel_rfl

private def ambiguousFolds : CheckedDefinition := CheckedDefinition.ofBody
    public_sums.callee.helper
    (.letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil
      (.letOp (.fold public_sums.callee.fold) (.cons (.there .here) (.cons .here .nil)) .nil
        (.letOp (.fold public_sums.callee.fold) (.cons (.there (.there .here)) (.cons .here .nil))
          .nil (.ret (.cons .here .nil)))))

example : ZkcTools.StructuredSource.MathematicsAliases.graph imported.program 1 "ambiguous" ambiguousFolds =
    .error "source-mathematics-fold-ambiguity" := by kernel_rfl

/-- A second identical candidate still refuses unique selection. -/
example : Structured.MathematicsAliases.definition?
    [CheckedDefinition.ofBody public_sums.callee.helper public_sums.callee.body,
      CheckedDefinition.ofBody public_sums.callee.helper public_sums.callee.body]
    public_sums.callee.helper = none := by kernel_rfl

example : True := by
  fail_if_success
    have : Structured.MathematicsAliases.folds public_sums.callee.body.erase =
        [ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck.public_sum.callee.fold] := by
      kernel_rfl
  trivial

example : True := by
  fail_if_success
    have : public_sums.callee.fold.stepHelper =
        ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck.public_sum.callee.foldStep.helper := by
      kernel_rfl
  trivial

/-- A matching signature with a false typed body cannot obtain an association. -/
example : True := by
  fail_if_success
    have : BodyIn imported.program.payload.definitions public_sums.entryFinal.helper
        (.letOp .booleanOr (.cons .here (.cons (.there .here) .nil)) .nil
          (.ret (.cons .here .nil))) := by bind_structured_bodies
  trivial

/-- The actual final-call selector checks that the call's result is returned. -/
example : Structured.MathematicsAliases.finalMath?
    (.letOp (.calculate (.invoke public_sums.entryFinal.helper) rfl) [0, 1]
      [.boolean] .nil (.ret [1])) = none := by kernel_rfl

example : Structured.MathematicsAliases.finalMath? imported.program.payload.entry.raw =
    some public_sums.entryFinal.helper := public_sums.entry_final

/-- Inventory order is not part of either the name or exact body association. -/
example : BodyIn imported.program.payload.definitions.reverse public_sums.helper public_sums.body :=
  public_sums.association.perm (List.reverse_perm _).symm

example : (Structured.MathematicsAliases.definition? imported.program.payload.definitions.reverse
    public_sums.callee.helper).map (·.helper) = some public_sums.callee.helper := by kernel_rfl

#print axioms public_sums.selected
#print axioms public_sums.association
#print axioms public_sums.callee.fold_selected
#print axioms public_sums.callee.fold_step
#print axioms public_sums.entry_final

end Tests.SourceMathematicsAliases

module

public import ZkcTools.StructuredSource.Methods.SumcheckRoot

@[expose] public section

/-! Bounded controls for the original-root generator. The production driver
supplies admitted programs; this module owns no root or family selections. -/
set_option autoImplicit false
namespace Tests.OriginalRootGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.OriginalRoot ZkcTools.StructuredSource.Methods.SumcheckRoot

def refusal {α : Type} (label expected : String) (result : Except String α) : IO Unit :=
  match result with
  | .error reason => unless reason == expected do throw (IO.userError (label ++ ": " ++ reason))
  | .ok _ => throw (IO.userError (label ++ ": accepted"))

def run (program : Program) : IO Unit := do
  refusal "missing association" "original-root-unique-association" (uniqueIndex ([] : List Nat) 0)
  refusal "ambiguous association" "original-root-unique-association" (uniqueIndex [0, 0] 0)
  unless uniqueIndex [1, 0] 0 == .ok 1 do throw (IO.userError "catalogue order")
  refusal "missing binder" "original-root-binder" (binderAt [] 0)
  refusal "invalid binder type" "original-root-binder-type" (binderType ⟨"x", .value .boolean, 0⟩)
  refusal "invalid result binder" "original-root-binder-type" (binderType ⟨"x", .results [], 0⟩)
  refusal "unsupported field component" "original-root-component"
    (compDependencies (Comp.present (Term.field "other-field" 0) : Comp [] [] (.field "other-field")))
  refusal "nonoptional callee input" "original-root-callee-pattern"
    (componentArguments (Values.cons (Term.bool true) .nil :
      Values (Argument [] []) [.value .boolean]))
  refusal "missing helper" "original-root-helper-association"
    (helperAlias program ⟨"absent", .math, [], []⟩)
  let some firstHelper := program.payload.definitions.head? | throw (IO.userError "missing helper")
  refusal "wrong nominal helper domain" "original-root-helper-association"
    (helperAlias program ⟨firstHelper.name, .math, [.field "other-field"], []⟩)
  refusal "missing callee" "original-root-callee-association"
    (calleeIndex program ⟨"absent", [], [], [], [], []⟩)
  refusal "missing family repeat" "original-root-family-repeat" (libraryMaximum program.payload.entry)
  refusal "stopped root spine" "original-root-terminal"
    (assemble program [] [] [] (Form.halt .incomplete : Form [] [] [] [.boolean]) 0)
  refusal "unsupported dynamic spine" "original-root-unsupported-form"
    (assemble program [] [] [] (Form.split (ty := .boolean) .absent (.halt .incomplete) (.halt .incomplete) :
      Form [] [] [] [.boolean]) 0)
  refusal "ambiguous family repeat" "original-root-family-repeat" (selectMaximum [2, 4])
  IO.println "PASS original-root refusal controls and source catalogue order"

end Tests.OriginalRootGeneration

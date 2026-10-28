module

public import ZkcTools.StructuredSource.InferReferenceInstallation
public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs

@[expose] public section

/-! Exact body discovery also covers a nominal group relation. This is a syntax
association, not a proof of protocol soundness or knowledge extraction. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Tests.ReferenceBindingGroup
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.Generated.Bindings

structure Bindings where
  name : String
  group : String
  field : String

def relation (bindings : Bindings) : Helper :=
  ⟨bindings.name, .math, [.group bindings.group, .group bindings.group, .field bindings.field], [.boolean]⟩

def body (bindings : Bindings) : Region dialect (relation bindings).inputs (relation bindings).outputs :=
  .letOp (.groupScale bindings.group bindings.field)
    (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.groupEqual bindings.group)
    (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

noncomputable def installed : {bindings : Bindings //
    BodyIn SchnorrRandomizedInputs.program.payload.definitions (relation bindings) (body bindings)} := by
  infer_reference_installation

example : installed.val.group = "bls12-381.g1" := by kernel_rfl
example : installed.val.field = "bls12-381.fr" := by kernel_rfl

example : True := by
  fail_if_success
    have collapsed : {name : String //
        BodyIn SchnorrRandomizedInputs.program.payload.definitions
          (relation ⟨name, "bls12-381.fr", "bls12-381.fr"⟩)
          (body ⟨name, "bls12-381.fr", "bls12-381.fr"⟩)} := by
      infer_reference_installation
  trivial

#print axioms installed
end Tests.ReferenceBindingGroup

module

public import ZkcExamples.Structured.MapFirstBodies

@[expose] public section

/-! Exact templates for the ordered restriction fold and values realization.
Private computation names are supplied by each source's checked associations. -/
namespace ZkcExamples.Structured.MultilinearPrefixBodies
open Zkc.Source Zkc.Source.Structured

structure Bindings where
  fold : String
  values : String

abbrev foldWrapperHelper : Helper := ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def foldWrapperBody (computation : String) : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨computation, .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev foldHelper (computation : String) : Helper := ⟨computation, .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

abbrev foldSpec : FoldSpec :=
  ⟨DomainSpec.elements "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain" [.vector "bls12-381.fr"] (.vector "bls12-381.fr") .here,
    [.vector "bls12-381.fr", .index, .index], [], "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", "", .local⟩

def foldBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.fold foldSpec) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev valuesRealizationHelper (computation : String) : Helper :=
  ⟨computation, .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

abbrev valuesRealizationBody := MapFirstBodies.valuesRealizationBody

end ZkcExamples.Structured.MultilinearPrefixBodies

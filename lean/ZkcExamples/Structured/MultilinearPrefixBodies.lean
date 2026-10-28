module

public import ZkcExamples.Structured.MultilinearSourceBindings

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
  MultilinearBodies.foldWrapperBody "bls12-381.fr" ({ MultilinearSourceBindings.common with fold := computation })

abbrev foldHelper (computation : String) : Helper := ⟨computation, .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

abbrev foldSpec : FoldSpec :=
  MultilinearBodies.foldSpec "bls12-381.fr" (MultilinearSourceBindings.common)

def foldBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.foldBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev valuesRealizationHelper (computation : String) : Helper :=
  ⟨computation, .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

abbrev valuesRealizationBody := MapFirstBodies.valuesRealizationBody

end ZkcExamples.Structured.MultilinearPrefixBodies

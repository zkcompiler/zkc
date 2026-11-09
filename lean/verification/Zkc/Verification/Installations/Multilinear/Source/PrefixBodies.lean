module

public import Zkc.Verification.Installations.Multilinear.Source.Bindings

public import Zkc.Verification.Installations.Multilinear.Source.MapFirstBodies

@[expose] public section

/-! Exact templates for the ordered restriction fold and values realization.
Private computation names are supplied by each source's checked associations. -/
namespace ZkcExamples.Structured.MultilinearPrefixBodies
open Zkc.Source Zkc.Source.Structured

structure Bindings where
  fold : String
  values : String
  symbols : MultilinearBodies.FoldNames

abbrev foldWrapperHelper (symbols : MultilinearBodies.FoldNames) : Helper := ⟨symbols.wrapper, .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def foldWrapperBody (computation : String) : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.foldWrapperBody "bls12-381.fr" ({ MultilinearSourceBindings.common with fold := computation })

abbrev foldHelper (computation : String) : Helper := ⟨computation, .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

abbrev foldSpec (symbols : MultilinearBodies.FoldNames) : FoldSpec :=
  MultilinearBodies.foldSpec "bls12-381.fr" (MultilinearSourceBindings.common.withFoldNames symbols)

def foldBody (symbols : MultilinearBodies.FoldNames) : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  MultilinearBodies.foldBody "bls12-381.fr" (MultilinearSourceBindings.common.withFoldNames symbols)

abbrev foldStepHelper (symbols : MultilinearBodies.FoldNames) :=
  (foldSpec symbols).stepHelper

def prefixBody (symbols : MultilinearBodies.FoldNames) :=
  MultilinearBodies.prefixBody "bls12-381.fr" (MultilinearSourceBindings.common.withFoldNames symbols)

abbrev valuesRealizationHelper (computation : String) : Helper :=
  ⟨computation, .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

abbrev valuesRealizationBody := MapFirstBodies.valuesRealizationBody

end ZkcExamples.Structured.MultilinearPrefixBodies

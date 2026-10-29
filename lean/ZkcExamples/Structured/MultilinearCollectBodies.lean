module

public import ZkcExamples.Structured.MultilinearSourceBindings

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Reusable exact body templates for multilinear restriction. These names are
parameters of an association proof, not a formula classifier. Each source must
prove membership and literal body equality in its own checked helper table. -/
namespace ZkcExamples.Structured.MultilinearCollectBodies
open Zkc.Source Zkc.Source.Structured

structure Bindings where
  collection : String
  domain : String
  callback : String
  computation : String


abbrev interpolateHelper : Helper :=
  ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateBody : Region dialect interpolateHelper.inputs interpolateHelper.outputs :=
  MultilinearBodies.interpolateBody "bls12-381.fr" (MultilinearSourceBindings.common)

abbrev firstHelper : Helper :=
  ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

abbrev halvesHelper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

abbrev interpolateRealizationHelper (bindings : Bindings) : Helper :=
  ⟨bindings.computation, .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateRealizationBody (bindings : Bindings) : Region dialect (interpolateRealizationHelper bindings).inputs (interpolateRealizationHelper bindings).outputs :=
  MultilinearBodies.interpolateRealizationBody "bls12-381.fr" ({ MultilinearSourceBindings.common with collection := bindings.collection, collectionDomain := bindings.domain, callback := bindings.callback, interpolation := bindings.computation })

abbrev mapCallbackHelper (bindings : Bindings) : Helper :=
  ⟨bindings.callback, .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def mapCallbackBody (bindings : Bindings) : Region dialect (mapCallbackHelper bindings).inputs (mapCallbackHelper bindings).outputs :=
  MultilinearBodies.mapCallbackBody "bls12-381.fr" ({ MultilinearSourceBindings.common with collection := bindings.collection, collectionDomain := bindings.domain, callback := bindings.callback, interpolation := bindings.computation })

abbrev mapHelper (bindings : Bindings) : Helper :=
  ⟨bindings.collection, .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

abbrev collectSpec (bindings : Bindings) : CollectSpec :=
  MultilinearBodies.collectSpec "bls12-381.fr" ({ MultilinearSourceBindings.common with collection := bindings.collection, collectionDomain := bindings.domain, callback := bindings.callback, interpolation := bindings.computation })

def mapBody (bindings : Bindings) : Region dialect (mapHelper bindings).inputs (mapHelper bindings).outputs :=
  MultilinearBodies.mapBody "bls12-381.fr" ({ MultilinearSourceBindings.common with collection := bindings.collection, collectionDomain := bindings.domain, callback := bindings.callback, interpolation := bindings.computation })

def firstBody (bindings : Bindings) : Region dialect firstHelper.inputs firstHelper.outputs :=
  MultilinearBodies.firstBody "bls12-381.fr" ({ MultilinearSourceBindings.common with collection := bindings.collection, collectionDomain := bindings.domain, callback := bindings.callback, interpolation := bindings.computation })

end ZkcExamples.Structured.MultilinearCollectBodies

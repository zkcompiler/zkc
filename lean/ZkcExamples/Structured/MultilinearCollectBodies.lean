module

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
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev firstHelper : Helper :=
  ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

abbrev halvesHelper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

abbrev interpolateRealizationHelper (bindings : Bindings) : Helper :=
  ⟨bindings.computation, .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateRealizationBody (bindings : Bindings) : Region dialect (interpolateRealizationHelper bindings).inputs (interpolateRealizationHelper bindings).outputs :=
  .letOp (.invoke {name := "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev mapCallbackHelper (bindings : Bindings) : Helper :=
  ⟨bindings.callback, .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def mapCallbackBody (bindings : Bindings) : Region dialect (mapCallbackHelper bindings).inputs (mapCallbackHelper bindings).outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke {name := bindings.computation, kind := .local, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev mapHelper (bindings : Bindings) : Helper :=
  ⟨bindings.collection, .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

abbrev collectSpec (bindings : Bindings) : CollectSpec where
  domain := {
    name := bindings.domain
    inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr"]
    items := [.field "bls12-381.fr", .field "bls12-381.fr"]
    body := .letNode (.elements (.vector "bls12-381.fr") .here) <|
      .letNode (.elements (.vector "bls12-381.fr") (.there .here)) <|
      .letNode (.zip [[.field "bls12-381.fr"], [.field "bls12-381.fr"]]
        (.cons (.there .here) (.cons .here .nil))) <|
      .ret .here }
  collection := .vector "bls12-381.fr"
  captures := [.field "bls12-381.fr"]
  body := bindings.callback
  predicate := ""
  kind := .local

def mapBody (bindings : Bindings) : Region dialect (mapHelper bindings).inputs (mapHelper bindings).outputs :=
  .letOp (.collect (collectSpec bindings)) (.cons .here (.cons (.there .here)
    (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def firstBody (bindings : Bindings) : Region dialect firstHelper.inputs firstHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke {name := bindings.collection, kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

end ZkcExamples.Structured.MultilinearCollectBodies

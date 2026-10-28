module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Exact multilinear library body templates. Domain identities and the complete
callee names are parameters. Signatures, guards, source markers, ordered tuples
and finite-domain captures remain in the typed bodies. These are the shared
templates used by the retained source views and the nominal reference laws. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.MultilinearBodies
open Zkc.Source

structure Bindings where
  less : String
  rows : String
  shape : String
  table : String
  halves : String
  interpolate : String
  first : String
  step : String
  foldStep : String
  foldDomain : String
  foldWrapper : String
  restrictPrefix : String
  values : String
  dimension : String
  width : String
  sums : String
  checkTable : String
  interpolation : String
  callback : String
  collection : String
  collectionDomain : String
  fold : String
  valuesRealization : String

def lessBody (_domain : String) (_bindings : Bindings) : Region dialect [.index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexLess)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

def rowsBody (_domain : String) (bindings : Bindings) : Region dialect [.index] [.index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨bindings.less, .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s2_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) (.cons (.letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 2)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.indexMul)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)

def shapeBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨bindings.less, .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨bindings.less, .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s7") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.branch [.vector domain, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) (.cons (.letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.vectorLength domain)) (.cons .here .nil) .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.exec (.indexMod)) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s17") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.branch [.vector domain, .index, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) (.cons (.letOp (.mark "s23") .nil .nil <|
  .letOp (.exec (.vectorLength domain)) (.cons .here .nil) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.exec (.indexDiv)) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s25") .nil .nil <|
  .letOp (.invoke ⟨bindings.rows, .local, [.index], [.index]⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s26") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)) (.cons (.letOp (.mark "s28") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)) .nil)) <|
  .ret (.cons .here .nil)

def tableBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index] [.vector domain, .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨bindings.shape, .local, [.vector domain, .index, .index], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s1_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

def halvesBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index] [.vector domain, .vector domain] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨bindings.less, .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s3_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit domain)) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def interpolateBody (domain : String) (_bindings : Bindings) : Region dialect [.field domain, .field domain, .field domain] [.field domain] :=
  .letOp (.fieldSubtract domain) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply domain) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd domain) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def interpolateRealizationBody (domain : String) (bindings : Bindings) : Region dialect [.field domain, .field domain, .field domain] [.field domain] :=
  .letOp (.invoke {name := bindings.interpolate, kind := .math, inputs := [.field domain, .field domain, .field domain], outputs := [.field domain]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def mapCallbackBody (domain : String) (bindings : Bindings) : Region dialect [.field domain, .field domain, .vector domain, .vector domain, .field domain] [.field domain] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke {name := bindings.interpolation, kind := .local, inputs := [.field domain, .field domain, .field domain], outputs := [.field domain]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev collectSpec (domain : String) (bindings : Bindings) : CollectSpec where
  domain := {
    name := bindings.collectionDomain
    inputs := [.vector domain, .vector domain]
    items := [.field domain, .field domain]
    body := .letNode (.elements (.vector domain) .here) <|
      .letNode (.elements (.vector domain) (.there .here)) <|
      .letNode (.zip [[.field domain], [.field domain]]
        (.cons (.there .here) (.cons .here .nil))) <|
      .ret .here }
  collection := .vector domain
  captures := [.field domain]
  body := bindings.callback
  predicate := ""
  kind := .local

def mapBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .vector domain, .field domain] [.vector domain] :=
  .letOp (.collect (collectSpec domain bindings)) (.cons .here (.cons (.there .here)
    (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def firstBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index, .field domain] [.vector domain, .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := bindings.halves, kind := .local, inputs := [.vector domain, .index, .index], outputs := [.vector domain, .vector domain]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke {name := bindings.collection, kind := .local, inputs := [.vector domain, .vector domain, .field domain], outputs := [.vector domain]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

abbrev foldSpec (domain : String) (bindings : Bindings) : FoldSpec :=
  ⟨DomainSpec.elements bindings.foldDomain [.vector domain] (.vector domain) .here,
    [.vector domain, .index, .index], [], bindings.foldStep, "", .local⟩

def foldBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .vector domain, .index, .index] [.vector domain, .index, .index] :=
  .letOp (.fold (foldSpec domain bindings)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def foldWrapperBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index, .vector domain] [.vector domain, .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨bindings.fold, .local, [.vector domain, .vector domain, .index, .index], [.vector domain, .index, .index]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def stepBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index, .field domain] [.vector domain, .index, .index] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨bindings.first, .local, [.vector domain, .index, .index, .field domain], [.vector domain, .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def foldStepBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index, .field domain, .vector domain] [.vector domain, .index, .index] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨bindings.step, .local, [.vector domain, .index, .index, .field domain], [.vector domain, .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def prefixBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index, .vector domain] [.vector domain, .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨bindings.foldWrapper, .local, [.vector domain, .index, .index, .vector domain], [.vector domain, .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

def sumsBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .index, .index] [.field domain, .field domain] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨bindings.halves, .local, [.vector domain, .index, .index], [.vector domain, .vector domain]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorSum domain)) (.cons .here .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSum domain)) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def checkTableBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .vector domain, .field domain] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength domain)) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨bindings.table, .local, [.vector domain, .index, .index], [.vector domain, .index, .index]⟩) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨bindings.restrictPrefix, .local, [.vector domain, .index, .index, .vector domain], [.vector domain, .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke ⟨bindings.valuesRealization, .local, [.vector domain, .index, .index], [.vector domain]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.vectorSum domain)) (.cons .here .nil) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.fieldEqual domain)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .ret (.cons .here .nil)

def checkTrueBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .vector domain, .field domain] [.boolean] :=
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.invoke ⟨bindings.checkTable, .local, [.vector domain, .vector domain, .field domain], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def checkFalseBody (domain : String) (_bindings : Bindings) : Region dialect [.vector domain, .vector domain, .field domain] [.boolean] :=
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .ret (.cons .here .nil)

def checkBody (domain : String) (bindings : Bindings) : Region dialect [.vector domain, .vector domain, .field domain] [.boolean] :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorLength domain)) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨bindings.shape, .local, [.vector domain, .index, .index], [.boolean]⟩) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.branch [.vector domain, .vector domain, .field domain] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons (checkTrueBody domain bindings) (.cons (checkFalseBody domain bindings) .nil)) <|
  .ret (.cons .here .nil)

end Zkc.Source.Structured.MultilinearBodies

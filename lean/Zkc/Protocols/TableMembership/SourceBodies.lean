module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Reusable typed bodies for the eager finite table scan. Nominal domains,
product identities, helper identities and finite-domain identities are explicit
parameters. Exact association and linking remain obligations of each source. -/
namespace Zkc.Protocols.TableMembership.Source
open Zkc.Source Zkc.Source.Structured

structure Names where
  containsDecision : String
  containsStep : String
  contains : String
  queryDecision : String
  queryStep : String
  membership : String
  formula : String
  containsDomain : String
  membershipDomain : String
  queryName : String
  queryConstructor : String

abbrev containsDecisionHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.containsDecision, .math, [.boolean, (.field field), (.field field)], [.boolean]⟩

def containsDecisionBody (field : String) (bindings : Names) : Region dialect (containsDecisionHelper field bindings).inputs (containsDecisionHelper field bindings).outputs :=
  .letOp (.fieldEqual field) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp .booleanOr (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev containsStepHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.containsStep, .math, [.boolean, (.field field), (.vector field), (.field field)], [.boolean]⟩

def containsStepBody (field : String) (bindings : Names) : Region dialect (containsStepHelper field bindings).inputs (containsStepHelper field bindings).outputs :=
  .letOp (.invoke {name := bindings.containsDecision, kind := .math, inputs := [.boolean, .field field, .field field], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev containsHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.contains, .math, [(.vector field), (.field field)], [.boolean]⟩

def containsBody (field : String) (bindings : Names) : Region dialect (containsHelper field bindings).inputs (containsHelper field bindings).outputs :=
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.fold {domain := {name := bindings.containsDomain, inputs := [.vector field], items := [.field field], body := DomainBody.letNode (DomainNode.elements (Collection.vector field) .here) (DomainBody.ret .here)}, state := [.boolean], captures := [.field field], step := bindings.containsStep, predicate := "", kind := .math}) (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev queryDecisionHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.queryDecision, .math, [.boolean, .boolean, (.field field), (.vector field)], [.boolean]⟩

def queryDecisionBody (field : String) (bindings : Names) : Region dialect (queryDecisionHelper field bindings).inputs (queryDecisionHelper field bindings).outputs :=
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp .booleanEqual (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.invoke {name := bindings.contains, kind := .math, inputs := [.vector field, .field field], outputs := [.boolean]}) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp .booleanOr (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev queryStepHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.queryStep, .math, [.boolean, (.product bindings.queryName bindings.queryConstructor (.cons .boolean (.cons (.field field) .nil))), (.sequence (.product bindings.queryName bindings.queryConstructor (.cons .boolean (.cons (.field field) .nil)))), (.vector field)], [.boolean]⟩

def queryStepBody (field : String) (bindings : Names) : Region dialect (queryStepHelper field bindings).inputs (queryStepHelper field bindings).outputs :=
  .letOp (.getProduct bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil)) .boolean .here) (.cons (.there .here) .nil) .nil <|
  .letOp (.getProduct bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil)) (.field field) (.there .here)) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.invoke {name := bindings.queryDecision, kind := .math, inputs := [.boolean, .boolean, .field field, .vector field], outputs := [.boolean]}) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev membershipHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.membership, .math, [(.vector field), (.sequence (.product bindings.queryName bindings.queryConstructor (.cons .boolean (.cons (.field field) .nil))))], [.boolean]⟩

def membershipBody (field : String) (bindings : Names) : Region dialect (membershipHelper field bindings).inputs (membershipHelper field bindings).outputs :=
  .letOp (.booleanConstant true) .nil .nil <|
  .letOp (.fold {domain := {name := bindings.membershipDomain, inputs := [(.sequence (.product bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil))))], items := [.product bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil))], body := DomainBody.letNode (DomainNode.elements (Collection.sequence (.product bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil)))) .here) (DomainBody.ret .here)}, state := [.boolean], captures := [.vector field], step := bindings.queryStep, predicate := "", kind := .math}) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.formula, .math, [(.vector field), (.sequence (.product bindings.queryName bindings.queryConstructor (.cons .boolean (.cons (.field field) .nil))))], [.boolean]⟩

def formulaBody (field : String) (bindings : Names) : Region dialect (formulaHelper field bindings).inputs (formulaHelper field bindings).outputs :=
  .letOp (.invoke {name := bindings.membership, kind := .math, inputs := [.vector field, (.sequence (.product bindings.queryName bindings.queryConstructor (ProductFields.cons .boolean (ProductFields.cons (.field field) ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)


end Zkc.Protocols.TableMembership.Source

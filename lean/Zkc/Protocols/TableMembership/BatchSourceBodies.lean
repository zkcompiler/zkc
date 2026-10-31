module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Finite point/value record validation templates. These ordinary records
carry no polynomial commitment interpretation. All nominal identities and
helper dependencies are explicit parameters of exact source association. -/
namespace Zkc.Protocols.TableMembership.BatchSource
open Zkc.Source Zkc.Source.Structured

structure Names where
  checkOpening : String
  batchStep : String
  batchValues : String
  formula : String
  mathematicalAdmission : String
  checkBatch : String
  batchDomain : String
  openingName : String
  openingConstructor : String
  checkSite : String

abbrev checkOpeningHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.checkOpening, .math, [.boolean, (.field field), (.field field), (.field field), (.field field)], [.boolean]⟩

def checkOpeningBody (field : String) (bindings : Names) : Region dialect (checkOpeningHelper field bindings).inputs (checkOpeningHelper field bindings).outputs :=
  .letOp (.fieldEqual field) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldEqual field) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev batchStepHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.batchStep, .math, [.boolean, (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)))), (.field field), (.field field)], [.boolean]⟩

def batchStepBody (field : String) (bindings : Names) : Region dialect (batchStepHelper field bindings).inputs (batchStepHelper field bindings).outputs :=
  .letOp (.getProduct bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)) (.field field) .here) (.cons (.there .here) .nil) .nil <|
  .letOp (.getProduct bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)) (.field field) (.there .here)) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.invoke (⟨ bindings.checkOpening, .math, [.boolean, (.field field), (.field field), (.field field), (.field field)], [.boolean] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev batchValuesHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.batchValues, .math, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean]⟩

def batchValuesBody (field : String) (bindings : Names) : Region dialect (batchValuesHelper field bindings).inputs (batchValuesHelper field bindings).outputs :=
  .letOp (.booleanConstant true) .nil .nil <|
  .letOp (.fold ⟨⟨ bindings.batchDomain, [(.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [(.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)))], (.letNode (.elements (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)))) .here) (.ret .here)) ⟩, [.boolean], [(.field field), (.field field)], bindings.batchStep, "", .math⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.formula, .math, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean]⟩

def formulaBody (field : String) (bindings : Names) : Region dialect (formulaHelper field bindings).inputs (formulaHelper field bindings).outputs :=
  .letOp (.invoke (⟨ bindings.batchValues, .math, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev mathematicalAdmissionHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.mathematicalAdmission, .local, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean]⟩

def mathematicalAdmissionBody (field : String) (bindings : Names) : Region dialect (mathematicalAdmissionHelper field bindings).inputs (mathematicalAdmissionHelper field bindings).outputs :=
  .letOp (.invoke (⟨ bindings.batchValues, .math, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev checkBatchHelper (field : String) (bindings : Names) : Helper :=
  ⟨bindings.checkBatch, .local, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean]⟩

def checkBatchBody (field : String) (bindings : Names) : Region dialect (checkBatchHelper field bindings).inputs (checkBatchHelper field bindings).outputs :=
  .letOp (.mark bindings.checkSite) .nil .nil <|
  .letOp (.invoke (⟨ bindings.mathematicalAdmission, .local, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)


/-- Protocol identity and navigation labels are source data, never dispatch keys. -/
structure ProtocolNames where
  name : String
  producerRole : String
  validatorRole : String
  messageSite : String
  checkSite : String

def runSignature (field : String) (bindings : Names) (protocol : ProtocolNames) : ProtocolSignature where
  name := protocol.name
  roles := [protocol.producerRole, protocol.validatorRole]
  inputs := [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))]
  outputs := [.boolean, (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))]
  inputScopes := [[1], [1], [0]]
  outputScopes := [[1], [1]]

def runBody (field : String) (bindings : Names) (protocol : ProtocolNames) :
    Region protocolDialect (runSignature field bindings protocol).inputs
      (runSignature field bindings protocol).outputs :=
  .letOp (.mark protocol.messageSite) .nil .nil <|
  .letOp (.exchange (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)))) 0 1 protocol.messageSite) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil)))) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark protocol.checkSite) .nil .nil <|
  .letOp (.localCall (⟨ bindings.checkBatch, .local, [(.field field), (.field field), (.sequence (.product bindings.openingName bindings.openingConstructor (.cons (.field field) (.cons (.field field) .nil))))], [.boolean] ⟩ : Helper) rfl 1 protocol.checkSite) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))


end Zkc.Protocols.TableMembership.BatchSource

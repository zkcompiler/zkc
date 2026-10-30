module

public import TestsSecurity.ABIInstallations.Fixtures
public import ZkcSecurityTools.SourceInputClauses

@[expose] public section
noncomputable section

/-! An authored model fixture with two tables, an unrelated scalar coordinate,
shared rounds, repeated selectors, and a nonempty retained input contract.
This is deliberately separate from the native export integration controls. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceAdmission.ShapeFixture
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open TestsSecurity.ABIInstallations
open ZkcSecurity.Claims.HonestPair TestsSecurity.ABIInstallations.Fixtures

abbrev config : Configuration := {
  dataTypes := [.vector Fixtures.scalarDomain, .field Fixtures.scalarDomain, .vector Fixtures.scalarDomain, .index]
  selectors := [] }
abbrev shapeTypes : List Ty := [.vector Fixtures.scalarDomain, .index]

def shapeBlock : Block := .block
  [.instruction (.vectorLength Fixtures.scalarDomain) [0] [.index] [] "",
   .instruction .indexPowerOfTwo [0, 2] [.boolean] [] "",
   .instruction (.indexConstant "4") [] [.index] [] "",
   .instruction .indexLess [0, 4] [.boolean] [] "",
   .instruction (.booleanConstant true) [] [.boolean] [] "",
   .instruction .booleanXor [1, 0] [.boolean] [] "",
   .instruction .booleanAnd [4, 0] [.boolean] [] ""] (.ret [0])

def original : Snapshot := { source config with
  relations := (source config).relations ++
    [{ name := "TableShape", visibility := .publicDef, kind := "zkc.language.formula/0",
       key := "shape", revision := "0", inputs := shapeTypes, outputs := [.boolean],
       purposes := ["parameter", "parameter"], formula := some "shapeFormula" }]
  definitions := (source config).definitions ++
    [.function ⟨"shapeFormula", .math, .privateDef, shapeTypes, [.boolean], none, [], none, shapeBlock⟩]
  contracts := [⟨"main", ((source config).contracts.head (by decide +kernel)).clauses ++
    [⟨.input, "left_shape", ⟨"TableShape", [⟨.input, 0, "V", false⟩, ⟨.input, 3, "V", false⟩]⟩, none, none⟩,
     ⟨.input, "right_shape", ⟨"TableShape", [⟨.input, 2, "V", false⟩, ⟨.input, 3, "V", false⟩]⟩, none, none⟩]⟩] }

abbrev targetHelper : Helper := ⟨"targetFormula", .math, [], [.boolean]⟩
def targetBody : Region dialect targetHelper.inputs targetHelper.outputs :=
  .letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil))
abbrev shapeHelper : Helper := ⟨"shapeFormula", .math, shapeTypes, [.boolean]⟩
def shapeBody : Region dialect shapeHelper.inputs shapeHelper.outputs :=
  .letOp (.vectorLength Fixtures.scalarDomain) (.cons .here .nil) .nil
    (.letOp .indexPowerOfTwo (.cons .here (.cons (.there (.there .here)) .nil)) .nil
      (.letOp (.indexConstant 4) .nil .nil
        (.letOp .indexLess (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil
          (.letOp (.booleanConstant true) .nil .nil
            (.letOp .booleanXor (.cons (.there .here) (.cons .here .nil)) .nil
              (.letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))
                .nil (.ret (.cons .here .nil))))))))
def rootSignature : ProtocolSignature :=
  ⟨"main", ["P", "V"], config.types, [.boolean],
    config.dataTypes.map (fun _ => [0, 1]) ++ [[1]], [[1]]⟩
def rootBody : Region protocolDialect rootSignature.inputs rootSignature.outputs :=
  .letOp (.mark "") .nil .nil
    (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil)))

structured_views original
  helpers [target, shape]
  protocols [root]
abbrev artifacts := Fixtures.artifacts config
def selected : AuthoredPair.Selection original :=
  (AuthoredPair.select original artifacts "claim").toOption.get (by decide +kernel)
def subject : Subject model original imported selected := by
  bind_authored_subject "claim" exports digest, digest, digest
abbrev validatorArtifacts := subject.validatorArtifacts
def validatorSubject := subject.validatorSubject []

end TestsSecurity.SourceAdmission.ShapeFixture

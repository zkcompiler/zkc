module

public import TestsSecurity.ABIInstallations.Fixtures

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ABIInstallations.Permuted
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair TestsSecurity.ABIInstallations.Fixtures
def config : Configuration := { dataTypes := [.field Fixtures.scalarDomain, .field Fixtures.scalarDomain], selectors := [1, 0] }
abbrev original := source config
abbrev targetHelper : Helper := ⟨"targetFormula", .math, config.arguments, [.boolean]⟩
def targetBody : Region dialect targetHelper.inputs targetHelper.outputs :=
  .letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil))
def rootSignature : ProtocolSignature :=
  ⟨"main", ["P", "V"], config.types, [.boolean],
    config.dataTypes.map (fun _ => if config.publicData then [0, 1] else [0]) ++ [[1]], [[1]]⟩
def rootBody : Region protocolDialect rootSignature.inputs rootSignature.outputs :=
  .letOp (.mark "") .nil .nil
    (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil)))
structured_views original
  helpers [target]
  protocols [root]
abbrev artifacts := Fixtures.artifacts config
def selected : AuthoredPair.Selection original :=
  (AuthoredPair.select original artifacts "claim").toOption.get (by decide +kernel)
def subject : Subject model original imported selected := by
  bind_authored_subject "claim" exports digest, digest, digest
abbrev validatorArtifacts := subject.validatorArtifacts
def validatorSubject := subject.validatorSubject []
end TestsSecurity.ABIInstallations.Permuted

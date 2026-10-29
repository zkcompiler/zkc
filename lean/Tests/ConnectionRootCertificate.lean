import Tests.ConnectionCertificate
import Zkc.Construction.ConnectionRootCertificate
import ZkcTools.ConstructionBindings.Root
import Zkc.Source.Structured.UnitViews

/-! The actual admitted arithmetic root and its actual constructed instructions.
One finite root record serves all nominal models, input rows and both roles.
No instance supplies input-decoding, full-return or source-equivalence proofs. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRootCertificate
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionInputs ConnectionRoot ConnectionInstallation
open Tests.ConnectionCertificate

abbrev rootSignature := arithmeticChecked.signature
abbrev rootBody := arithmeticBody
structured_views arithmeticSnapshot helpers [] protocols [root]
theorem admitted : check arithmeticSnapshot = .ok program := kernel_admission

def artifact : Participant where
  source := arithmeticSnapshot.source
  candidate := "arithmetic-root-certificate-test"
  symbol := "validator"
  policy := ⟨"arithmetic", "P", "V", 0, "", [], [0, 1], [], "zkc.framed/0", ""⟩
  inputs := [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")]
  outputs := [.data .boolean, .data (.field "bls12-381.fr")]
  instructions := [
    ⟨.calculate (.fieldSubtract "bls12-381.fr"), [0, 1], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩]
  returned := [3, 2]

def routing (mode : Domain.Mode) : Original.Routing := { arithmeticRouting with mode := mode }

def validator : RootCertificate program (routing .validator) 1 artifact := by
  derive_root_connection
    target (arithmeticView false)
    correspondence (fun _ => Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _) Domain.Correspondence.empty))
    services []

def producer : RootCertificate program (routing .producer) 0 artifact := by
  derive_root_connection
    target (arithmeticView false)
    correspondence (fun _ => Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _) Domain.Correspondence.empty))
    services []

-- The checked conclusion needs no sorts/ABI/source-equation premise from an
-- author. Wrong sorts and missing inputs follow the shared refusal branch.
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns rootSignature arithmeticRouting.context 1 artifact)
      (InputFrames validator.inputs.abi rootSignature.inputs physical)
      (validator.source model physical)
      (Domain.participant model program arithmeticRouting.context artifact physical) :=
  validator.simulation model physical

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns rootSignature arithmeticRouting.context 0 artifact)
      (InputFrames producer.inputs.abi rootSignature.inputs physical)
      (producer.source model physical)
      (Domain.participant model program arithmeticRouting.context artifact physical) :=
  producer.simulation model physical

example (model : DomainModel) : validator.source model [] = .halt .refused := rfl
example (model : DomainModel) (other : model.Field "other") (value : model.Field "bls12-381.fr") :
    validator.source model [.data (.field "other" other), .data (.field "bls12-381.fr" value)] =
      .halt .refused := rfl

-- A root's non-Boolean return selector is fixed independently of the body
-- proposal. Preserving true acceptance does not justify substituting an input.
/-- error: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : ConnectionCertificate.Certificate (routing .validator) {} program.payload.definitions 1 2
    program.payload.entry arithmeticPattern [.data 3, .data 0] none [] arithmeticLayout (arithmeticView false) := by
  derive_connection_alignment

#print axioms RootCertificate.simulation
end Tests.ConnectionRootCertificate

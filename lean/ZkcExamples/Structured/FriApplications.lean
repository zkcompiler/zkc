module

public import ZkcExamples.Structured.FriSource
public import Zkc.Source.Structured.ProtocolDerivation
public import Zkc.Source.DeriveRegion

@[expose] public section

/-! The retained root delegates to the scalar low-degree component. A component
law installed at that call must be associated with its complete checked body.
Its input condition is checked on the two actual copies of the public shift.
The caller preserves the marked call, its frame, and its verifier result. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriSource
open Zkc.Source Zkc.Source.Structured
open FriSourceBodies FriSourceViews

abbrev verifierAlgebra (model : DomainModel) :=
  OracleProtocol.algebra model 1 (unit.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩)
    (unit.oracleCalculations model 1)

abbrev verifierTable (model : DomainModel) :=
  unit.protocols.foldl (verifierAlgebra model).extend []

abbrev verifierValue (model : DomainModel) := ProtocolValue model.toCarriers

def lowDegreeArguments (model : DomainModel) (shift : model.Field extension)
    (rounds queries service : Nat) :
    Values (Component (verifierValue model)) protocol5Signature.inputs :=
  ProtocolValue.embedComponents (.cons none (.cons (some shift) (.cons (some shift)
    (.cons (some rounds) (.cons (some queries) (.cons (some service) .nil))))))

abbrev lowDegreeContext := ({} : ProtocolContext).enter "s0" [0, 1]

def rootCall (model : DomainModel) (law : ProtocolLaw (verifierAlgebra model) protocol5Signature)
    (shift : model.Field extension) (rounds queries service : Nat) :
    PIR.Process (OracleProtocol.Interface model)
      (Values (Component (verifierValue model)) runSignature.outputs) :=
  let arguments := lowDegreeArguments model shift rounds queries service
  let child := (law.reference (verifierTable model) lowDegreeContext 1 arguments).bind fun out ↦
    .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) out)
  .call (.mark "s0" "s0") fun _ ↦
    ((verifierAlgebra model).application {} protocol5Signature "s0" child).bind fun out ↦
      .done (.cons (out.get .here) .nil)

/-- Every possible child reply, halt and event passes through the actual
caller. The fresh component supplies its mathematics at this one boundary. -/
theorem root_body (model : DomainModel)
    (law : ProtocolLaw (verifierAlgebra model) protocol5Signature)
    (associated : protocol5Definition.raw = law.body.erase)
    (shift : model.Field extension) (rounds queries service : Nat)
    (ready : law.Requires (verifierTable model) lowDegreeContext 1
      (lowDegreeArguments model shift rounds queries service)) :
    runBody.denote ((verifierAlgebra model).meaning (verifierTable model) {} 1)
      (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)).get =
        rootCall model law shift rounds queries service := by
  derive_process using
    (exact law.applyMember (definition := protocol5Definition) unit.protocolsLinked
      protocol5_member associated {} 1 "s0" [0, 1]
      (lowDegreeArguments model shift rounds queries service) (by decide) ready)

theorem root_participant (model : DomainModel)
    (law : ProtocolLaw (verifierAlgebra model) protocol5Signature)
    (associated : protocol5Definition.raw = law.body.erase)
    (shift : model.Field extension) (rounds queries service : Nat)
    (ready : law.Requires (verifierTable model) lowDegreeContext 1
      (lowDegreeArguments model shift rounds queries service)) :
    subject.imported.program.oracleParticipant model 1
      (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)) =
        (rootCall model law shift rounds queries service).bind (fun out ↦
          .done (maskValues 1 runSignature.outputScopes out)) := by
  change invokeProtocol (verifierTable model) runDefinition.signature {} 1 _ = _
  refine ((verifierAlgebra model).invokeBody unit.protocolsLinked runDefinition run_member {}
    1 (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service))).trans ?_
  let environment : Environment (Component (verifierValue model)) runSignature.inputs :=
    (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)).get
  apply congrArg (fun p : PIR.Process (OracleProtocol.Interface model)
      (Values (Component (verifierValue model)) runSignature.outputs) ↦
    p.bind (fun out ↦ .done (maskValues 1 runSignature.outputScopes out)))
  exact (NormalForm.normalizeActions_process ((verifierAlgebra model).meaning (verifierTable model) {} 1)
    runBody environment).trans (root_body model law associated shift rounds queries service ready)

end ZkcExamples.Structured.FriSource

module

public import ZkcExamples.Structured.FriSource
public import ZkcExamples.Structured.FriSourceCalls
public import Zkc.Source.Structured.ProtocolDerivation
public import Zkc.Source.DeriveRegion

@[expose] public section

/-! The retained root delegates to the scalar low-degree component. Its actual
table supplies the child. The caller preserves the two copies of the public
shift, the marked call, its frame, and the verifier result. -/
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

abbrev rootSite := FriSourceCalls.lowDegree
abbrev lowDegreeContext := rootSite.childContext {}

def rootCall (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    PIR.Process (OracleProtocol.Interface model)
      (Values (Component (verifierValue model)) runSignature.outputs) :=
  let child := invokeProtocol (verifierTable model) protocol5Signature lowDegreeContext 1
    (lowDegreeArguments model shift rounds queries service)
  .call (.mark rootSite.site rootSite.site) fun _ ↦
    ((verifierAlgebra model).application {} protocol5Signature rootSite.site child).bind fun out ↦
      .done (.cons (out.get .here) .nil)

/-- Every reply and halt of the selected low-degree component passes through
the actual caller. No assumption on the child's behavior is needed here. -/
theorem root_body (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    runBody.denote ((verifierAlgebra model).meaning (verifierTable model) {} 1)
      (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)).get =
        rootCall model shift rounds queries service := by
  derive_process using
    (exact (verifierAlgebra model).applyActive (verifierTable model) protocol5Signature {} 1 rootSite.site rootSite.roles
      (lowDegreeArguments model shift rounds queries service) (by decide))

theorem root_participant (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    subject.imported.program.oracleParticipant model 1
      (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)) =
        (rootCall model shift rounds queries service).bind (fun out ↦
          .done (maskValues 1 runSignature.outputScopes out)) := by
  change invokeProtocol (verifierTable model) runDefinition.signature {} 1 _ = _
  exact (verifierAlgebra model).invokePresented unit.protocolsLinked runDefinition run_member {}
    1 _ _ (root_body model shift rounds queries service)

end ZkcExamples.Structured.FriSource

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

abbrev partyAlgebra (model : DomainModel) (self : Nat) :=
  OracleProtocol.algebra model self (unit.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩)
    (unit.oracleCalculations model self)

abbrev partyTable (model : DomainModel) (self : Nat) :=
  unit.protocols.foldl (partyAlgebra model self).extend []

abbrev verifierAlgebra (model : DomainModel) := partyAlgebra model 1
abbrev verifierTable (model : DomainModel) := partyTable model 1

abbrev verifierValue (model : DomainModel) := ProtocolValue model.toCarriers

/-- The root passes its public shift to both child ports. The child masks
the two copies according to its input scopes. Private ports belong to their
original roles from the start. -/
def partyArguments (model : DomainModel) (self : Fin 2) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) :
    Values (Component (verifierValue model)) protocol5Signature.inputs :=
  ProtocolValue.embedComponents (.cons (if self.val == 0 then some word else none)
    (.cons (some shift) (.cons (some shift) (.cons (some rounds) (.cons (some queries)
      (.cons (if self.val == 1 then some service else none) .nil))))))

abbrev lowDegreeArguments (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :=
  partyArguments model 1 [] shift rounds queries service

abbrev rootSite := FriSourceCalls.lowDegree
abbrev lowDegreeContext := rootSite.childContext {}

def partyCall (model : DomainModel) (self : Fin 2) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) :
    PIR.Process (OracleProtocol.Interface model) (Values (Component (verifierValue model)) runSignature.outputs) :=
  let child := invokeProtocol (partyTable model self.val) protocol5Signature lowDegreeContext self.val
    (partyArguments model self word shift rounds queries service)
  .call (.mark rootSite.site rootSite.site) fun _ ↦
    ((partyAlgebra model self.val).application {} protocol5Signature rootSite.site child).bind fun out ↦
      .done (.cons (out.get .here) .nil)

abbrev rootCall (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :=
  partyCall model 1 [] shift rounds queries service

theorem partyRootBody (model : DomainModel) (self : Fin 2) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) :
    runBody.denote ((partyAlgebra model self.val).meaning (partyTable model self.val) {} self.val)
      (ProtocolValue.embedComponents (inputs self.val word shift rounds queries service)).get =
        partyCall model self word shift rounds queries service := by
  have active : (ProtocolContext.enter {} rootSite.site rootSite.roles).contains protocol5Signature self.val = true := by
    have roles : self = 0 ∨ self = 1 := by omega
    rcases roles with rfl | rfl <;> decide +kernel
  derive_process using
    (exact (partyAlgebra model self.val).applyActive (partyTable model self.val) protocol5Signature {} self.val
      rootSite.site rootSite.roles (partyArguments model self word shift rounds queries service) active)

/-- Both original participants enter the same checked low-degree call. Each
keeps its own arguments, role mask and complete exits. -/
theorem partyRoot (model : DomainModel) (self : Fin 2) (word : List (model.Field extension))
    (shift : model.Field extension) (rounds queries service : Nat) :
    subject.imported.program.oracleParticipant model self.val
      (ProtocolValue.embedComponents (inputs self.val word shift rounds queries service)) =
        (partyCall model self word shift rounds queries service).bind (fun out ↦
          .done (maskValues self.val runSignature.outputScopes out)) := by
  change invokeProtocol (partyTable model self.val) runDefinition.signature {} self.val _ = _
  have masked : maskValues self.val (({} : ProtocolContext).mapScopes runDefinition.inputScopes)
      (ProtocolValue.embedComponents (inputs self.val word shift rounds queries service)) =
        ProtocolValue.embedComponents (inputs self.val word shift rounds queries service) := by
    have roles : self = 0 ∨ self = 1 := by omega
    rcases roles with rfl | rfl <;> rfl
  apply (partyAlgebra model self.val).invokePresented unit.protocolsLinked runDefinition run_member {} self.val
  exact (congrArg (fun args : Values (Component (verifierValue model)) runSignature.inputs ↦
    runBody.denote ((partyAlgebra model self.val).meaning (partyTable model self.val) {} self.val) args.get) masked).trans
    (partyRootBody model self word shift rounds queries service)

theorem root_participant (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    subject.imported.program.oracleParticipant model 1
      (ProtocolValue.embedComponents (inputs 1 [] shift rounds queries service)) =
        (rootCall model shift rounds queries service).bind (fun out ↦
          .done (maskValues 1 runSignature.outputScopes out)) :=
  partyRoot model 1 [] shift rounds queries service

end ZkcExamples.Structured.FriSource

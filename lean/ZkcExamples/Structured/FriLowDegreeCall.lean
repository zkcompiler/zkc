module

public import ZkcExamples.Structured.FriPhaseCalls

@[expose] public section

/-! Chronological decomposition of the retained scalar verifier. Each phase
uses the source-selected declaration, actual arguments, and original caller
frame. Replies determine every subsequent handle and scalar operand. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriLowDegreeCall
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceViews FriSourceBodies FriBinding FriPhaseCalls
open OracleProtocol (concrete)

def caller : Caller :=
  ⟨lowDegreeContext, (schedule protocol5Body.erase).get (by decide +kernel)⟩

def inputSites := (twoTransferGroups (caller.transferSites inputsOnly)).get (by decide +kernel)
def projectionSites := (twoTransferGroups (caller.transferSites projectionsOnly)).get (by decide +kernel)

def query (model : DomainModel) (sampled : Value model .indices)
    (bound : Values (Value model) protocol2Signature.outputs) :
    Process model (Values (Value model) protocol5Signature.outputs) :=
  fields bound fun initialData initial layerData layers foldData folds shift size coeffs indices rounds queries ↦ do
    let handles ← caller.inputs inputSites.2 (pairs initialData initial layerData layers foldData folds)
    let projected ← caller.projections projectionSites.2 handles
    let result ← caller.call FriSourceCalls.query (prependPairs projected (.cons shift (.cons size
      (.cons coeffs (.cons indices (.cons rounds (.cons queries .nil)))))))
    caller.marks model caller.schedule.trailing
    return .cons (result.get .here) (.cons none (.cons sampled (.cons (result.get (.there .here)) .nil)))

def afterCommit (model : DomainModel) (count service : Nat)
    (committed : Values (Value model) protocol0Signature.outputs) :
    Process model (Values (Value model) protocol5Signature.outputs) :=
  fields committed fun initialData initial layerData layers foldData folds shift size coeffs rounds ↦ do
    let handles ← caller.inputs inputSites.1 (pairs initialData initial layerData layers foldData folds)
    let sampled ← caller.call FriSourceCalls.scalarQueries (.cons (concrete model .index count)
      (.cons (concrete model (.service FriScalarLoop.contract) service) .nil))
    let projected ← caller.projections projectionSites.1 handles
    let bound ← caller.call FriSourceCalls.binding (prependPairs projected (.cons shift (.cons size
      (.cons coeffs (.cons rounds (.cons (sampled.get .here) .nil))))))
    query model (sampled.get .here) bound

def program (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    Process model (Values (Value model) protocol5Signature.outputs) := do
  let committed ← caller.call FriSourceCalls.commitment (.cons none (.cons none
    (.cons (concrete model (.field extension) shift) (.cons (concrete model .index rounds)
      (.cons (concrete model (.service FriScalarLoop.contract) service) .nil)))))
  afterCommit model queries service committed

set_option maxHeartbeats 2500000 in
theorem body (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    protocol5Body.denote ((verifierAlgebra model).meaning (verifierTable model) lowDegreeContext 1)
      (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.inputScopes)
        (lowDegreeArguments model shift rounds queries service)).get = program model shift rounds queries service := by
  trans ?generated
  · derive_process using
      (first
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol0Signature lowDegreeContext
           1 FriSourceCalls.commitment.site FriSourceCalls.commitment.roles _ (by decide +kernel)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol1Signature lowDegreeContext
           1 FriSourceCalls.scalarQueries.site FriSourceCalls.scalarQueries.roles _ (by decide +kernel)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol2Signature lowDegreeContext
           1 FriSourceCalls.binding.site FriSourceCalls.binding.roles _ (by decide +kernel)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol4Signature lowDegreeContext
           1 FriSourceCalls.query.site FriSourceCalls.query.roles _ (by decide +kernel))
  · simp only [program, query, afterCommit, Caller.inputs, Caller.projections, Caller.input, Caller.project,
      Caller.marks, Caller.call, bind, pure, PIR.Process.bind]
    rfl

theorem installed (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    invokeProtocol (verifierTable model) protocol5Signature lowDegreeContext 1
        (lowDegreeArguments model shift rounds queries service) =
      (program model shift rounds queries service).bind fun values ↦
        .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) values) :=
  (verifierAlgebra model).invokePresented unit.protocolsLinked protocol5Definition protocol5_member
    lowDegreeContext 1 _ _ (body model shift rounds queries service)

/-- The published verifier runs the four installed phases under its real
caller frame. This equality includes all refusals, events and provider state. -/
theorem verifier {m : Type → Type} [Monad m] [LawfulMonad m] {Aux E : Type}
    (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) (auxiliary : Aux)
    (ordinary : PublishedWords.Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E) :
    FriSource.verifier shift rounds queries service auxiliary ordinary choose =
      (PIR.Process.call (I := OracleProtocol.Interface model) (.mark rootSite.site rootSite.site) fun _ ↦
        ((verifierAlgebra model).application {} protocol5Signature rootSite.site
          ((program model shift rounds queries service).bind fun out ↦
            .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) out))).bind fun output ↦
          .done (maskValues 1 runSignature.outputScopes (.cons (output.get .here) .nil))).runM
        (PublishedWords.actionM subject.unit.oracles ordinary choose)
        (start 1 [] shift rounds queries service auxiliary).state := by
  change (subject.imported.program.oracleParticipant model 1
    (ProtocolValue.embedComponents (FriSource.inputs 1 [] shift rounds queries service))).runM _ _ = _
  have invokes : invokeProtocol (partyTable model (1 : Fin 2).val) protocol5Signature lowDegreeContext (1 : Fin 2).val
      (partyArguments model 1 [] shift rounds queries service) = _ := installed model shift rounds queries service
  rw [FriSource.root_participant, rootCall, partyCall, invokes]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc, PublishedWords.actionM]
  kernel_rfl

end ZkcExamples.Structured.FriLowDegreeCall

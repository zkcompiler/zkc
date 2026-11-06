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

def caller : Caller := ⟨lowDegreeContext, 1⟩
def scalarSite := "label_71756572696573"

def query (model : DomainModel) (sampled : Value model .indices)
    (bound : Values (Value model) protocol2Signature.outputs) :
    Process model (Values (Value model) protocol5Signature.outputs) :=
  fields bound fun initialData initial layerData layers foldData folds shift size coeffs indices rounds queries ↦ do
    let handles ← caller.inputs 9 (pairs initialData initial layerData layers foldData folds)
    let projected ← caller.projections 12 handles
    let result ← caller.call protocol4Signature "s6" (prependPairs projected (.cons shift (.cons size
      (.cons coeffs (.cons indices (.cons rounds (.cons queries .nil)))))))
    caller.mark model ""
    caller.mark model ""
    return .cons (result.get .here) (.cons none (.cons sampled (.cons (result.get (.there .here)) .nil)))

def afterCommit (model : DomainModel) (count service : Nat)
    (committed : Values (Value model) protocol0Signature.outputs) :
    Process model (Values (Value model) protocol5Signature.outputs) :=
  fields committed fun initialData initial layerData layers foldData folds shift size coeffs rounds ↦ do
    let handles ← caller.inputs 1 (pairs initialData initial layerData layers foldData folds)
    let sampled ← caller.call protocol1Signature scalarSite (.cons (concrete model .index count)
      (.cons (concrete model (.service FriScalarLoop.contract) service) .nil))
    let projected ← caller.projections 5 handles
    let bound ← caller.call protocol2Signature "s4" (prependPairs projected (.cons shift (.cons size
      (.cons coeffs (.cons rounds (.cons (sampled.get .here) .nil))))))
    query model (sampled.get .here) bound

def program (model : DomainModel) (shift : model.Field extension) (rounds queries service : Nat) :
    Process model (Values (Value model) protocol5Signature.outputs) := do
  let committed ← caller.call protocol0Signature "s0" (.cons none (.cons none
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
           1 "s0" [0, 1] _ (by decide)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol1Signature lowDegreeContext
           1 scalarSite [0, 1] _ (by decide)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol2Signature lowDegreeContext
           1 "s4" [0, 1] _ (by decide)
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol4Signature lowDegreeContext
           1 "s6" [0, 1] _ (by decide))
  · simp only [program, query, afterCommit, Caller.inputs, Caller.projections, Caller.input, Caller.project,
      Caller.mark, Caller.call, bind, pure, PIR.Process.bind]
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
      (PIR.Process.call (I := OracleProtocol.Interface model) (.mark "s0" "s0") fun _ ↦
        ((verifierAlgebra model).application {} protocol5Signature "s0"
          ((program model shift rounds queries service).bind fun out ↦
            .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) out))).bind fun output ↦
          .done (maskValues 1 runSignature.outputScopes (.cons (output.get .here) .nil))).runM
        (PublishedWords.actionM subject.unit.oracles ordinary choose)
        (start 1 [] shift rounds queries service auxiliary).state := by
  change (subject.imported.program.oracleParticipant model 1
    (ProtocolValue.embedComponents (FriSource.inputs 1 [] shift rounds queries service))).runM _ _ = _
  rw [FriSource.root_participant, rootCall, installed]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc, PublishedWords.actionM]
  kernel_rfl

end ZkcExamples.Structured.FriLowDegreeCall

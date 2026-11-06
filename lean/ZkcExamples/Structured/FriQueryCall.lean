module

public import ZkcExamples.Structured.FriPhaseCalls
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! The unassociated query wrapper calls the installed checker with the
bound state, the explicit false flag, and the empty vector. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriQueryCall
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding FriPhaseCalls
open OracleProtocol (concrete)

def caller : Caller := ⟨FriSourceCalls.query.childContext lowDegreeContext⟩

def inputSites := (oneTransferGroup (transferSites inputsOnly protocol4Body.erase)).get (by decide +kernel)
def projectionSites := (oneTransferGroup (transferSites projectionsOnly protocol4Body.erase)).get (by decide +kernel)

def checkArgs (model : DomainModel) (projected : Pairs model) (state : Committed model)
    (xs : FriScalarLoop.Positions) : Values (Value model) protocol3Signature.inputs :=
  prependPairs projected (.cons state.shift (.cons state.size (.cons state.coefficients
    (.cons (concrete model .indices (xs.map Fin.val)) (.cons state.rounds (.cons (concrete model .index 8)
      (.cons (concrete model .boolean false) (.cons (concrete model (.vector extension) []) .nil))))))))

def program (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) :
    Process model (Values (Value model) protocol4Signature.outputs) := do
  let handles ← caller.inputs inputSites (pairs none state.initial none state.layers none state.folds)
  caller.mark model "s0"
  caller.mark model ""
  let projected ← caller.projections projectionSites handles
  let checked ← caller.call FriSourceCalls.check (checkArgs model projected state xs)
  return .cons (checked.get .here) (.cons (checked.get (.there .here)) .nil)

private theorem emptyStep (model : DomainModel) :
    ((verifierAlgebra model).meaning (verifierTable model) caller.context 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper26Helper rfl 1 "s0") .nil .nil
      (.done (.cons (concrete model (.vector extension) []) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper26Helper
      (ProtocolValue.embedComponents (Values.nil (Value := model.Value)).present) = _
  rw [OracleProtocol.owned_present,
      (ReferenceLibrary.emptyVector model extension "s0").invokeOn (helper := helper26Helper)
        unit.definitions unit.linked (by exact_body helper26Definition) .nil trivial]
  rfl

set_option maxHeartbeats 1600000 in
theorem body (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) :
    protocol4Body.denote ((verifierAlgebra model).meaning (verifierTable model) caller.context 1)
      (FriBinding.output state xs).get = program model state xs := by
  trans ?generated
  · derive_process using
      (first
       | apply emptyStep model
       | apply (verifierAlgebra model).applyActive (verifierTable model) protocol3Signature
           caller.context 1 FriSourceCalls.check.site FriSourceCalls.check.roles _ (by decide +kernel))
  · simp only [program, Caller.inputs, Caller.projections, Caller.input, Caller.project, Caller.mark,
      Caller.call, bind, pure, PIR.Process.bind]
    rfl

theorem installed (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) :
    invokeProtocol (verifierTable model) protocol4Signature caller.context 1 (FriBinding.output state xs) =
      (program model state xs).bind fun values ↦
        .done (maskValues 1 (caller.context.mapScopes protocol4Signature.outputScopes) values) :=
  (verifierAlgebra model).invokePresented unit.protocolsLinked protocol4Definition protocol4_member
    caller.context 1 _ _ (body model state xs)

end ZkcExamples.Structured.FriQueryCall

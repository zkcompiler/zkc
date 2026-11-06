import ZkcExamples.Structured.FriBindingExecution

/-! Both correspondence proposals have the same well-typed output layout.
The declared field association distinguishes them on an actual return. -/
namespace Tests.FriBindingAssociation
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriBinding FriBindingExecution

def swappedOrigin : List String → Option PortForwarding.Origin
  | ["state", "layers"] => some (.input ["committed", "folds"])
  | ["state", "folds"] => some (.input ["committed", "layers"])
  | path => FriBinding.origin path

def swapped : PortForwarding.Plan protocol2Signature.inputs [.index] protocol2Signature.outputs :=
  (PortForwarding.compile FriSourceData.snapshot.sourceDeclarations protocol2Signature [.index] swappedOrigin).get
    (by decide +kernel)

def layers : Var protocol2Signature.outputs layersSort.type :=
  (PortForwarding.outputField FriSourceData.snapshot.sourceDeclarations protocol2Signature
    ["state", "layers"] (.receiverHandle layersSort.type) layersSort.type).get (by decide +kernel)

/-- Type, placement and arity all agree. Returning the swapped layout would
identify two distinct sequences of nominal anchors. -/
theorem swap_refused {model : DomainModel} (handles : Handles) (rest : Committed model)
    (xs : FriScalarLoop.Positions) (distinct : handles.layers ≠ handles.folds) :
    output (handles.attach rest) xs ≠ swapped.apply (FriBinding.inputs model (handles.attach rest) xs)
      (.cons (OracleProtocol.concrete model .index 8) .nil) := by
  intro same
  have projected := congrArg
    (fun (values : Values (Value model) protocol2Signature.outputs) ↦
      (values.get layers).bind ProtocolValue.toConcrete) same
  apply distinct
  have good : (output (handles.attach rest) xs).get layers =
      OracleProtocol.concrete model layersSort.type handles.layers := by kernel_rfl
  have bad : (swapped.apply (FriBinding.inputs model (handles.attach rest) xs)
      (.cons (OracleProtocol.concrete model .index 8) .nil)).get layers =
      OracleProtocol.concrete model layersSort.type handles.folds := by kernel_rfl
  rw [good, bad] at projected
  simpa only [OracleProtocol.concrete, Option.bind_some, ProtocolValue.toConcrete_ofConcrete,
    Option.some.injEq] using projected

end Tests.FriBindingAssociation

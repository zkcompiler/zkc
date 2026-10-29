module

public import Zkc.Construction.SourceConnection
public import Zkc.Construction.ConnectionRootRoutes

@[expose] public section

/-! Deterministic selection of the source-connection obligation. The owning
artifact admission fixes the source, context, role mode and actual participant
before evidence. This module fixes the input ABI and source routing from those
values. It does not select a proof method or replace export/policy admission. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionAdmission
open Zkc.Source Zkc.Source.Structured ConnectionRoot

structure Boundary where
  abi : Original.InputABI
  routing : Original.Routing

def role (context : Context) : Domain.Mode → Nat
  | .producer => context.producer
  | .validator => context.validator

/-- Failed discovery leaves no weakened or vacuous semantic obligation. -/
def select (program : Program) (context : Context) (mode : Domain.Mode)
    (artifact : Participant) : Except String Boundary := do
  let abi ← SourceConnection.canonicalABI program (role context mode) artifact
  let proposal ← ConnectionRootRoutes.propose program.snapshot context mode
    (ConnectionRootInputs.serviceCapabilities program.payload.entry.inputs) artifact
  return ⟨abi, {
    snapshot := program.snapshot, context, mode
    selectedHandle := proposal.selectedHandle
    messages := proposal.messages
    draws := proposal.draws
    deliveries := proposal.deliveries
    locals := proposal.locals }⟩

/-- This fixed proposition accepts any kernel-checked proof of the complete
connection. A RootCertificate is its default implementation, not its meaning. -/
def Required (program : Program) (context : Context) (mode : Domain.Mode)
    (artifact : Participant) : Prop :=
  match select program context mode artifact with
  | .error _ => False
  | .ok boundary => SourceConnection.Connected program boundary.routing
      (role context mode) boundary.abi artifact

theorem select_canonical {program : Program} {context : Context} {mode : Domain.Mode}
    {artifact : Participant} {boundary : Boundary}
    (selected : select program context mode artifact = .ok boundary) :
    SourceConnection.canonicalABI program (role context mode) artifact = .ok boundary.abi := by
  unfold select at selected
  cases canonical : SourceConnection.canonicalABI program (role context mode) artifact with
  | error reason => simp [canonical, Except.bind, bind] at selected
  | ok abi =>
    cases proposed : ConnectionRootRoutes.propose program.snapshot context mode
        (ConnectionRootInputs.serviceCapabilities program.payload.entry.inputs) artifact with
    | error reason => simp [canonical, proposed, Except.bind, bind] at selected
    | ok proposal =>
      simp [canonical, proposed, Except.bind, bind, pure] at selected
      cases selected
      rfl

theorem ofConnected {program : Program} {context : Context} {mode : Domain.Mode}
    {artifact : Participant} {boundary : Boundary}
    (selected : select program context mode artifact = .ok boundary)
    (connection : SourceConnection.Connected program boundary.routing
      (role context mode) boundary.abi artifact) : Required program context mode artifact := by
  simpa only [Required, selected] using connection

theorem refused {program : Program} {context : Context} {mode : Domain.Mode}
    {artifact : Participant} {reason : String}
    (failed : select program context mode artifact = .error reason) :
    ¬ Required program context mode artifact := by
  simp only [Required, failed, not_false_eq_true]

end Zkc.Construction.ConnectionAdmission

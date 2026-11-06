module

public import ZkcArkLibExamples.Fri.CommitIngress
public import Zkc.Semantics.ReturnedPostcondition

@[expose] public section

/-! The original Commit body establishes its publications before reaching
the terminal exchange. Later source operations preserve all three base
and virtual associations, including across provider state changes. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitBody
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceViews FriSourceBodies FriCommitAdmission
open OracleProtocol (concrete)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriCommitRound (roundOccurrence roundSite)
open CommitLoop (State Rounds)
variable {M : Type → Type} [Monad M] [LawfulMonad M] [MonadAttach M] [LawfulMonadAttach M]
  {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

set_option maxRecDepth 6000 in
private theorem split (context : ProtocolContext) (shift : Octic) (service : Nat) :
    let inputs := arguments model shift service
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    protocol0Body.denote meaning inputs.get = (admission.denote meaning inputs.get).bind fun live ↦
      (roundSite.iterations meaning live.get).bind fun values ↦ roundSite.next.denote meaning (Environment.prepend live.get values) := by
  dsimp only
  rw [← admission_exact]
  exact roundOccurrence.denote_prefix ((verifierAlgebra model).meaning (verifierTable model) context 1) roundOnSpine _

/-- A terminal proof receives the genuine loop publications, the entered
state and the three inherited return ports. Its conclusion applies to the
whole source body for every receiver frame with this role assignment. -/
theorem afterRounds (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nz : shift ≠ 0) (service : Nat) (before : State Aux) (role : before.oracle.self = 1)
    (post : Values (FriBinding.Value model) protocol0Signature.outputs → State Aux → Prop)
    (finish : ∀ (live : Values (FriBinding.Value model) roundSite.context)
        (after : State Aux) (rounds : Rounds 5 3),
      live.get shiftPort = concrete model (.field extension) shift → live.get sizePort = concrete model .index 32 →
      live.get countPort = concrete model .index 3 → rounds.Installed after.oracle shift → after.oracle.self = 1 →
      PIR.Process.OnReturn (CommitLoop.handler network choose) after (roundSite.next.denote
        ((verifierAlgebra model).meaning (verifierTable model) context 1)
        (Environment.prepend live.get (CommitLoop.packed 2 (rounds.endingShift shift) rounds.sources rounds.views))) post) :
    PIR.Process.OnReturn (CommitLoop.handler network choose) before (protocol0Body.denote
      ((verifierAlgebra model).meaning (verifierTable model) context 1) (arguments model shift service).get) post := by
  rw [split]
  have entry := CommitIngress.installed network choose context receiver separate shift nz service before.oracle role before rfl
  apply PIR.Process.OnReturn.bind (middle := fun live state ↦ state.oracle = before.oracle ∧
    roundSite.operands.eval live.get = .cons (concrete model .index 3)
      ((CommitLoop.packed 5 shift [] []).append (CommitLoop.captures service)) ∧
    live.get shiftPort = concrete model (.field extension) shift ∧ live.get sizePort = concrete model .index 32 ∧
    live.get countPort = concrete model .index 3)
  · exact entry.weaken (fun rec h live returned ↦ And.intro h.1 (h.2 live returned))
  rintro live state ⟨kept, inputs, offset, rows, count⟩
  apply PIR.Process.OnReturn.bind (middle := fun values after ↦ ∃ rounds : Rounds 5 3,
    rounds.Installed after.oracle shift ∧ after.oracle.self = 1 ∧ values =
      CommitLoop.packed 2 (rounds.endingShift shift) ([] ++ rounds.sources) ([] ++ rounds.views))
  · exact CommitLoop.installed network choose context receiver separate live.get shift nz service inputs state (kept ▸ role)
  rintro values after ⟨rounds, stored, self, result⟩
  rw [List.nil_append, List.nil_append] at result
  subst values
  exact finish live after rounds offset rows count stored self

/-- The actual role projection of the linked protocol definition at
this call. The two private holder inputs are absent at the receiver. -/
theorem invokeReceiver (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (shift : Octic) (service : Nat) :
    let inputs := arguments model shift service
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    invokeProtocol (verifierTable model) protocol0Signature context 1 inputs =
      (protocol0Body.denote meaning inputs.get).bind fun out ↦
        .done (maskValues 1 (context.mapScopes protocol0Signature.outputScopes) out) := by
  dsimp only
  have masked : maskValues 1 (context.mapScopes protocol0Signature.inputScopes) (arguments model shift service) =
      arguments model shift service := by
    change maskValues 1 ([[0], [0], [1], [0,1], [1]].map (List.map context.roles)) _ = _
    simp [arguments, protocol0Signature, maskValues, Participant.restrict, receiver]
  exact (verifierAlgebra model).invokePresented unit.protocolsLinked protocol0Definition protocol0_member context 1
    (arguments model shift service) _ (congrArg (fun inputs : Values (FriBinding.Value model) protocol0Signature.inputs ↦
      protocol0Body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) inputs.get) masked)

/-- Every returning invocation retains all six table associations in its
own store, even if receiving the terminal vector changed provider state. -/
theorem registered (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nz : shift ≠ 0) (service : Nat) (before : State Aux) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (CommitLoop.handler network choose) before (invokeProtocol (verifierTable model)
      protocol0Signature context 1 (arguments model shift service))
      (fun _ after ↦ ∃ rounds : Rounds 5 3, rounds.Installed after.oracle shift ∧ after.oracle.self = 1) := by
  rw [invokeReceiver context receiver shift service]
  apply PIR.Process.OnReturn.bind (middle := fun _ after ↦ ∃ rounds : Rounds 5 3,
    rounds.Installed after.oracle shift ∧ after.oracle.self = 1)
  · apply afterRounds network choose context receiver separate shift nz service before role
    intro live after rounds _ _ _ installed self
    exact (PublishedWords.processPublicationFrame checkedUnit.oracles network choose _ after).weaken
      (fun rec frame _ _ ↦ ⟨rounds, rounds.transport frame shift installed, frame.registry.1.trans self⟩)
  · intro _ after kept
    exact Zkc.MonadicPostcondition.pure _ _ (fun _ _ ↦ kept)

end ZkcSecurity.ArkLib.Fri.CommitBody

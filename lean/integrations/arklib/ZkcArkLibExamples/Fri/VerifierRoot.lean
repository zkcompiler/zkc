module

public import ZkcArkLibExamples.Fri.VerifierCalls

@[expose] public section

/-! The scalar verifier follows the word and the challenge fixed in Commit
through the actual subsequent sampler, BindQueries, query wrapper and Check. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.VerifierRoot
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriPhaseCalls
open OracleProtocol (concrete)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitReturn (Publication)
open CommitLoop (State handler)
open VerifierCalls (accepts cells geometry committed)
open FriLowDegreeCall (caller inputSites projectionSites)

variable {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)
local notation "sourceOracles" => checkedUnit.oracles
local notation "sourceNetwork" => PublishedWords.liftM network
local notation "sourceReads" => PublishedWords.readM (model := model)
local notation "sourcePublisher" => PublishedWords.publishM choose

def sampled (xs : Fin 8 → Fin 32) := concrete model .indices ((List.ofFn xs).map Fin.val)
def output (pub : Publication) (xs : Fin 8 → Fin 32) : Values (FriBinding.Value model) protocol5Signature.outputs :=
  .cons (concrete model .boolean true) (.cons none (.cons (sampled xs) (VerifierQueries.packed (cells pub xs))))

private theorem sample (service : Nat) (before : State Aux) :
    PIR.Process.OnReturn (handler network choose) before
      (caller.call FriSourceCalls.scalarQueries (.cons (concrete model .index 8)
        (.cons (concrete model (.service FriScalarLoop.contract) service) .nil)))
      (fun out _ ↦ ∃ xs : Fin 8 → Fin 32, out = FriScalarLoop.packed model (List.ofFn xs)) := by
  apply Caller.callReturns sourceOracles sourceNetwork sourceReads sourcePublisher (caller := caller) (selected := FriSourceCalls.scalarQueries)
    (post := fun out _ ↦ ∃ xs : Fin 8 → Fin 32, out = FriScalarLoop.packed model (List.ofFn xs))
  intro entered _
  change PIR.Process.OnReturn _ entered (invokeProtocol (verifierTable model) protocol1Signature FriScalarLoop.context 1
    (.cons (concrete model .index 8) (.cons (concrete model (.service FriScalarLoop.contract) service) .nil))) _
  rw [RetainedQueries.installed model service]
  apply PIR.Process.OnReturn.bindAny
  intro _ afterMarks
  apply PIR.Process.OnReturn.bindAny
  intro xs afterDraws
  exact PIR.Process.OnReturn.done ⟨xs, rfl⟩

private theorem binding (pub : Publication) (shift : Octic) (xs : Fin 8 → Fin 32)
    (before : State Aux) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (handler network choose) before
      (caller.call FriSourceCalls.binding (FriBinding.inputs model (committed pub shift) (List.ofFn xs)))
      (fun out state ↦ state.oracle = before.oracle ∧ out = FriBinding.output (committed pub shift) (List.ofFn xs)) := by
  apply Caller.callReturns sourceOracles sourceNetwork sourceReads sourcePublisher (caller := caller) (selected := FriSourceCalls.binding)
    (post := fun out store ↦ store = before.oracle ∧ out = FriBinding.output (committed pub shift) (List.ofFn xs))
  intro entered same
  exact (FriBindingExecution.installed sourceOracles sourceNetwork sourceReads sourcePublisher before.oracle role
    (FriSourceCalls.binding.childContext caller.context) rfl (by decide) pub.handles (geometry pub shift)
    (List.ofFn xs) List.length_ofFn).onReturn same

set_option maxRecDepth 6000 in
private theorem queries (pub : Publication) (shift : Octic) (nonzero : shift ≠ 0) (xs : Fin 8 → Fin 32)
    (before : State Aux) (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift) :
    PIR.Process.OnReturn (handler network choose) before
      (FriLowDegreeCall.query model (sampled xs) (FriBinding.output (committed pub shift) (List.ofFn xs)))
      (fun out after ↦ accepts pub shift xs = true ∧ out = output pub xs ∧ after.oracle = VerifierPath.charged before.oracle 96) := by
  unfold FriLowDegreeCall.query
  apply PIR.Process.OnReturn.bind (head := (inputsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
    (publish := sourcePublisher) caller rfl (by decide) role inputSites.2 pub.handles).onReturn rfl)
  rintro _ gathered ⟨same, rfl⟩
  apply PIR.Process.OnReturn.bind (head := (projectionsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
    (publish := sourcePublisher) caller rfl (by decide) (same ▸ role) projectionSites.2 pub.handles).onReturn rfl)
  rintro _ current ⟨kept, rfl⟩
  have start := kept.trans same
  apply PIR.Process.OnReturn.bind (middle := fun out after ↦ accepts pub shift xs = true ∧
    out = Values.cons (concrete model .boolean true) (VerifierQueries.packed (cells pub xs)) ∧
    after.oracle = VerifierPath.charged before.oracle 96)
  · apply Caller.callReturns sourceOracles sourceNetwork sourceReads sourcePublisher (caller := caller) (selected := FriSourceCalls.query) (post := fun out store ↦ accepts pub shift xs = true ∧
      out = Values.cons (concrete model .boolean true) (VerifierQueries.packed (cells pub xs)) ∧
      store = VerifierPath.charged before.oracle 96)
    intro nested entry
    have initial := entry.trans start
    exact (VerifierCalls.query network choose pub shift nonzero xs nested (initial ▸ role) (initial ▸ live)).weaken
      fun _ law out returned ↦
        let ⟨ok, value, reads⟩ := law out returned
        ⟨ok, value, reads.trans (congrArg (VerifierPath.charged · 96) initial)⟩
  · rintro _ checked ⟨ok, rfl, reads⟩
    apply PIR.Process.OnReturn.bind (head := (ReceiverForwarding.marks sourceOracles sourceNetwork sourceReads sourcePublisher checked.oracle _).onReturn rfl)
    intro _ after marked
    exact PIR.Process.OnReturn.done ⟨ok, rfl, marked.1.trans reads⟩

variable [MonadAttach M] [LawfulMonadAttach M]

def Checked (pub : Publication) (shift : Octic) (out : Values (FriBinding.Value model) protocol5Signature.outputs)
    (store : CommitIteration.Store Aux) : Prop :=
  ∃ xs : Fin 8 → Fin 32, accepts pub shift xs = true ∧ out = output pub xs ∧ pub.rounds.Installed store shift

set_option maxRecDepth 6000 in
/-- This publication is fixed before the eight scalar queries. Every
successful continuation uses its handles and the positions actually sampled. -/
theorem afterCommit (pub : Publication) (shift : Octic) (nonzero : shift ≠ 0) (service : Nat)
    (before : State Aux) (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift) :
    PIR.Process.OnReturn (handler network choose) before (FriLowDegreeCall.afterCommit model 8 service (pub.output shift))
      (fun out record ↦ Checked pub shift out record.oracle) := by
  unfold FriLowDegreeCall.afterCommit
  apply PIR.Process.OnReturn.bind (head := (inputsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
    (publish := sourcePublisher) caller rfl (by decide) role inputSites.1 pub.handles).onReturn rfl)
  rintro _ gathered ⟨gatheredAt, rfl⟩
  apply PIR.Process.OnReturn.bind (head := PublishedWords.withPublicationFrame sourceOracles network choose (sample network choose service gathered))
  rintro _ drawn ⟨⟨xs, rfl⟩, frame⟩
  have valid := pub.rounds.transport frame shift (gatheredAt ▸ live)
  have who := frame.registry.1.trans (gatheredAt ▸ role)
  apply PIR.Process.OnReturn.bind (head := (projectionsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
    (publish := sourcePublisher) caller rfl (by decide) who projectionSites.1 pub.handles).onReturn rfl)
  rintro _ current ⟨same, rfl⟩
  apply PIR.Process.OnReturn.bind (head := binding network choose pub shift xs current (same ▸ who))
  rintro _ bound ⟨kept, rfl⟩
  have original := kept.trans same
  apply (PublishedWords.withPublicationFrame sourceOracles network choose
    (queries network choose pub shift nonzero xs bound (original ▸ who) (original ▸ valid))).weaken
  intro rec law out returning
  obtain ⟨⟨ok, values, _⟩, survived⟩ := law out returning
  exact ⟨xs, ok, values, pub.rounds.transport survived shift (original ▸ valid)⟩

theorem program (shift : Octic) (nonzero : shift ≠ 0) (service : Nat)
    (before : State Aux) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (handler network choose) before (FriLowDegreeCall.program model shift 3 8 service)
      (fun out after ↦ ∃ pub : Publication, Checked pub shift out after.oracle) := by
  unfold FriLowDegreeCall.program
  apply PIR.Process.OnReturn.bind (middle := fun out after ↦ CommitReturn.Result shift out after.oracle)
  · apply Caller.callReturns sourceOracles sourceNetwork sourceReads sourcePublisher (caller := caller) (selected := FriSourceCalls.commitment) (post := CommitReturn.Result shift)
    intro entered same
    exact CommitReturn.installed network choose (FriSourceCalls.commitment.childContext caller.context)
      rfl (by decide) shift nonzero service entered (same ▸ role)
  · rintro _ current ⟨pub, rfl, live, who⟩
    exact (afterCommit network choose pub shift nonzero service current who live).weaken fun _ law out returned ↦
      ⟨pub, law out returned⟩

/-- The original verifier returns its actual acceptance bit. Its intermediate
output binds the three installed folds to the eight sampled positions; the
public entry exposes only the boolean. This law permits early stops. -/
theorem verifier (shift : Octic) (nonzero : shift ≠ 0) (service : Nat) (auxiliary : Aux) :
    Std.Do.Internal.Ensures (fun record ↦ ∀ out, record.outcome = .returned out →
      out = Values.cons (concrete model .boolean true) .nil ∧
      ∃ (pub : Publication) (xs : Fin 8 → Fin 32), accepts pub shift xs = true ∧ pub.rounds.Installed record.state.oracle shift)
      (FriSource.verifier shift 3 8 service auxiliary network choose) := by
  erw [FriLowDegreeCall.verifier model shift 3 8 service auxiliary network choose]
  let initial := (start (model := model) 1 [] shift 3 8 service auxiliary).state
  let low := (FriLowDegreeCall.program model shift 3 8 service).bind fun values ↦
    .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) values)
  have parent := ReceiverForwarding.atApplication sourceOracles sourceNetwork sourceReads sourcePublisher initial
    [(rootSite.site, rootSite.site)] protocol5Signature rootSite.site low
    (fun values store ↦ ∃ pub : Publication, Checked pub shift values store) (by
      intro entered aligned
      apply PIR.Process.OnReturn.bind (head := program network choose shift nonzero service entered (aligned ▸ rfl))
      rintro _ after ⟨pub, xs, ok, rfl, reg⟩
      exact PIR.Process.OnReturn.done ⟨pub, xs, ok, rfl, reg⟩)
  apply PIR.Process.OnReturn.bind (head := parent)
    (next := fun out ↦ .done (maskValues 1 runSignature.outputScopes (.cons (out.get .here) .nil)))
    (post := fun out (state : State Aux) ↦ out = Values.cons (concrete model .boolean true) .nil ∧
      ∃ (pub : Publication) (xs : Fin 8 → Fin 32), accepts pub shift xs = true ∧ pub.rounds.Installed state.oracle shift)
  rintro _ after ⟨pub, xs, ok, rfl, reg⟩
  exact PIR.Process.OnReturn.done ⟨rfl, pub, xs, ok, reg⟩

end ZkcSecurity.ArkLib.Fri.VerifierRoot

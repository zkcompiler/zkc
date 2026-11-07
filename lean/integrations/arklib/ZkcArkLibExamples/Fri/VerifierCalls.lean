module

public import ZkcArkLibExamples.Fri.CommitReadback
public import ZkcExamples.Structured.FriPhaseTransfer
public import ZkcExamples.Structured.FriLowDegreeCall
public import ZkcArkLibExamples.Fri.RetainedQueries

@[expose] public section

/-! Link the actual query wrapper to the checked publication and the sampled
positions. Every phase enters and leaves its own source frame. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.VerifierCalls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriPhaseCalls
open OracleProtocol (concrete)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitReturn (Publication)
open CommitLoop (State handler)
open VerifierPath (charged)
variable {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

def geometry (pub : Publication) (shift : Octic) : FriBinding.Committed model :=
  ⟨none, none, none, concrete model (.field extension) shift, concrete model .index 32,
    concrete model (.vector extension) pub.coefficients, concrete model .index 3⟩

abbrev committed (pub : Publication) (shift : Octic) := pub.handles.attach (geometry pub shift)

def cells (pub : Publication) (xs : Fin 8 → Fin 32) := (List.finRange 8).map fun i ↦ pub.word (xs i)

def accepts (pub : Publication) (shift : Octic) (xs : Fin 8 → Fin 32) :=
  Phases.accepts RetainedDomain.root 0 (.fold pub.word pub.beta (pub.tail.transcript pub.coefficients)) shift xs

def checkedOutput (pub : Publication) (xs : Fin 8 → Fin 32) : Values (FriBinding.Value model) protocol3Signature.outputs :=
  Values.cons (concrete model .boolean true) (VerifierQueries.packed (cells pub xs))

local notation "sourceOracles" => checkedUnit.oracles
local notation "sourceNetwork" => PublishedWords.liftM network
local notation "sourceReads" => PublishedWords.readM (model := model)
local notation "sourcePublisher" => PublishedWords.publishM choose

theorem query (pub : Publication) (shift : Octic) (nonzero : shift ≠ 0) (xs : Fin 8 → Fin 32)
    (before : State Aux) (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift) :
    PIR.Process.OnReturn (handler network choose) before
      (invokeProtocol (verifierTable model) protocol4Signature FriQueryCall.caller.context 1
        (FriBinding.output (committed pub shift) (List.ofFn xs)))
      (fun out after ↦ accepts pub shift xs = true ∧ out = checkedOutput pub xs ∧ after.oracle = charged before.oracle 96) := by
  rw [FriQueryCall.installed]
  apply PIR.Process.OnReturn.bind (middle := fun out after ↦
    accepts pub shift xs = true ∧ out = checkedOutput pub xs ∧ after.oracle = charged before.oracle 96)
  · unfold FriQueryCall.program
    apply PIR.Process.OnReturn.bind (head := (inputsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
      (publish := sourcePublisher) FriQueryCall.caller rfl (by decide) role FriQueryCall.inputSites pub.handles).onReturn rfl)
    rintro _ entered ⟨same, rfl⟩
    apply PIR.Process.OnReturn.bind (head := (projectionsKeep (oracles := sourceOracles) (ordinary := sourceNetwork) (base := sourceReads)
      (publish := sourcePublisher) FriQueryCall.caller rfl (by decide) (same ▸ role) FriQueryCall.projectionSites pub.handles).onReturn rfl)
    rintro _ current ⟨kept, rfl⟩
    have start := kept.trans same
    apply PIR.Process.OnReturn.bind (middle := fun out after ↦
      accepts pub shift xs = true ∧ out = checkedOutput pub xs ∧ after.oracle = charged before.oracle 96)
    · apply Caller.callReturns sourceOracles sourceNetwork sourceReads sourcePublisher (caller := FriQueryCall.caller) (selected := FriSourceCalls.check)
        (post := fun out store ↦ accepts pub shift xs = true ∧ out = checkedOutput pub xs ∧ store = charged before.oracle 96)
      intro nested entry
      have initial := entry.trans start
      have correct := CommitReadback.checked network choose (source := pub.source) (view := pub.view) (word := pub.word) (beta := pub.beta) pub.tail pub.coefficients pub.singleton xs nonzero
        (FriSourceCalls.check.childContext FriQueryCall.caller.context) rfl (by decide) nested (initial ▸ role) (initial ▸ live)
      exact correct.weaken fun _ law value returned ↦
        let ⟨ok, output, chargedReads⟩ := law value returned
        ⟨ok, output, chargedReads.trans (congrArg (charged · 96) initial)⟩
    · rintro _ after ⟨ok, rfl, reads⟩
      exact PIR.Process.OnReturn.done ⟨ok, rfl, reads⟩
  · rintro _ after ⟨ok, rfl, reads⟩
    exact PIR.Process.OnReturn.done ⟨ok, rfl, reads⟩

end ZkcSecurity.ArkLib.Fri.VerifierCalls

module

public import ZkcArkLibExamples.Fri.CommitCaptures
public import Zkc.Source.Structured.MarkedPublication

@[expose] public section

/-! The existing delivery handler can change private auxiliary state. It
keeps the whole published word available to the virtual construction in
the same source continuation. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitDelivery
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (checkedUnit verifierAlgebra verifierTable)
open FriCommitRound (virtualConstruction)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitCaptures (RegisteredAt RegisteredConstruction ReachedView roundState)
open OracleProtocol (AtMarkedCall withMarks)

variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

noncomputable def throughView (context : ProtocolContext) (marks : List (String × String)) (step : Nat)
    (st : FriCommitRound.State model) (source : OracleAnchor) (beta : Octic) :
    PIR.Process (OracleProtocol.Interface model) ReachedView :=
  let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
  let inputs := FriCommitRound.deliveredValues step st source beta
  withMarks marks (.call (FriCommitRound.delivery context beta) fun _ ↦ virtualConstruction.reached meaning inputs.get)

set_option maxRecDepth 6000 in
/-- A delivered field resumes the installed continuation on the SSA row
returned by its actual virtual construction. The marks are recovered from
the reached source occurrence, including repeated and empty marks. -/
theorem fromSample (context : ProtocolContext) (step : Nat) (st : FriCommitRound.State model)
    (source : OracleAnchor) (beta : Octic)
    (sampled : PIR.Process (OracleProtocol.Interface model) (Values (FriBinding.Value model) FriCommitRound.roundSite.spec.state))
    (reached : AtMarkedCall (FriCommitRound.delivery context beta)
      (fun next ↦ next () = FriCommitRound.deliveredSuffix context step st source beta) sampled) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    ∃ marks, sampled = (throughView context marks step st source beta).bind fun (live, reply) ↦
      virtualConstruction.next.denote meaning (Environment.prepend live.get reply) := by
  dsimp only
  obtain ⟨marks, next, actual, tail⟩ := reached
  refine ⟨marks, actual.trans ?_⟩
  rw [throughView, OracleProtocol.withMarks_bind]
  apply congrArg (withMarks marks)
  simp only [PIR.Process.bind]
  apply congrArg (PIR.Process.call (I := OracleProtocol.Interface model) (FriCommitRound.delivery context beta))
  funext token
  cases token
  exact tail.trans (virtualConstruction.resume _ _)

set_option maxRecDepth 6000 in
/-- The original iteration makes the newly published parent and fresh draw
available at the very same virtual construction. Every selected continuation
uses its actual reply, including arbitrary attacker words and challenges. -/
theorem iterationToView (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (step : Nat) (st : FriCommitRound.State model) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    AtMarkedCall (FriCommitRound.sendRequest context st.rows) (fun sent ↦ ∀ source,
      AtMarkedCall (FriCommitRound.appendRequest context st.layers source) (fun appended ↦
        AtMarkedCall (FriCommitRound.drawRequest context st.service) (fun sampled ↦ ∀ beta, ∃ marks,
          sampled beta = (throughView context marks step st source beta).bind fun (live, reply) ↦
            virtualConstruction.next.denote meaning (Environment.prepend live.get reply))
          (appended (.cons (OracleProtocol.concrete model FriBinding.layersSort.type (st.layers ++ [source])) .nil)))
        (sent (.cons (OracleProtocol.concrete model FriBinding.initialSort.type source) .nil)))
      (FriCommitRound.iteration model context step st) := by
  dsimp only
  obtain ⟨marks, sent, actual, append⟩ := FriCommitRound.beforeChallenge context receiver step st
  refine ⟨marks, sent, actual, fun source ↦ ?_⟩
  obtain ⟨marks, appended, actual, draw⟩ := append source
  obtain ⟨drawMarks, sampled, sampledAt, deliver⟩ := draw
  exact ⟨marks, appended, actual, drawMarks, sampled, sampledAt,
    fun beta ↦ fromSample context step st source beta (sampled beta) (deliver beta)⟩

set_option maxRecDepth 6000 in
/-- Selection of the parent word at publication suffices through marks,
delivery and construction, even when the network changes its state. A
refused delivery skips the virtual operation. -/
theorem registered (context : ProtocolContext) (marks : List (String × String)) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (step n : Nat) (bound : n+1 ≤ 5) (shift beta : Octic) (nonzero : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat) (source : OracleAnchor) (word : Fin (2^(n+1)) → Octic)
    (before : OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
    (role : before.oracle.self = 1)
    (parent : PublishedWords.RegisteredWord (row := .field FriSource.extension)
      before.oracle.entries before.oracle.self source word before.oracle.provider) :
    Std.Do.Internal.Ensures (RegisteredConstruction n source word beta shift)
      ((throughView context marks step (roundState n shift layers folds service) source beta).runM
        (PublishedWords.actionM checkedUnit.oracles network choose) before) := by
  apply OraclePublication.markedOutcomes checkedUnit.oracles (PublishedWords.liftM network)
    PublishedWords.readM (PublishedWords.publishM choose) marks _ (RegisteredAt n source word beta shift)
    (fun _ _ eq ↦ by cases eq) before.oracle _ before rfl
  intro current same
  rw [PIR.Process.runM]
  apply (PublishedWords.RegisteredWord.throughOrdinary checkedUnit.oracles network choose
    (.send (ty := .field FriSource.extension) (FriCommitRound.serviceSite context 1) (context.roles 0) beta)
    current (same ▸ parent)).bind
  rintro ⟨out, after, trace⟩ ⟨self, ⟨live⟩⟩
  cases out with
  | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (by intro _ eq; cases eq)
  | returned token =>
    cases token
    have checked := CommitCaptures.registeredAfterDelivery network choose context receiver separate
      step n bound shift beta nonzero layers folds service source word after (self.trans (same ▸ role)) live
    exact Zkc.MonadicPostcondition.map checked _ (fun _ post ↦ post)

end ZkcSecurity.ArkLib.Fri.CommitDelivery

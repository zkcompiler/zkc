module

public import ZkcArkLibExamples.Fri.CommitDelivery
public import ZkcArkLibExamples.Fri.CommitPublication

@[expose] public section

/-! One whole receiver iteration, with the initial word obtained from its
own send before the draw. The result does not assume that the prover
chooses an honest word or that its next publication is the prescribed fold. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitIteration
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriSource (extension checkedUnit)
open FriCommitRound (kind sendRequest appendRequest drawRequest)
open OracleProtocol (concrete)
abbrev Store (Aux : Type) := OracleRuntimeState model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
  (PublishedWords.State model Aux)
abbrev LoopState := Values (FriBinding.Value model) FriCommitRound.roundSite.spec.state
variable {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

def Completed (n : Nat) (shift : Octic) (layers folds : List OracleAnchor)
    (prior : PublishedWords.Table model) (outcome : PIR.Outcome LoopState) (store : Store Aux) : Prop :=
  ∀ values, outcome = .returned values → ∃ source word beta,
    PublishedWords.PublishedAfter (row := .field extension) prior store.provider.words source (List.ofFn word) ∧
    CommitDelivery.RoundResult n source word shift beta layers folds values store

private def WordAt (n : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n+1)) → Octic) (store : Store Aux) :=
  store.self = 1 ∧ Nonempty (PublishedWords.RegisteredWord (row := .field extension) store.entries store.self source word store.provider)

set_option maxRecDepth 6000 in
/-- The word comes from this iteration's chooser and the challenge comes
from its later draw. Whenever the callback returns, its actual parent and
view, updated domain, and entire two handle collections reach the successor.
A refusal at any reached action preserves that action's stop. -/
theorem installed [MonadAttach M] [LawfulMonadAttach M] (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (step n : Nat) (bound : n+1 ≤ 5) (shift : Octic) (nonzero : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat)
    (before : OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
    (role : before.oracle.self = 1) :
    Std.Do.Internal.Ensures (fun record ↦ Completed n shift layers folds before.oracle.provider.words record.outcome record.state.oracle)
      ((FriCommitRound.iteration model context step (CommitCaptures.roundState n shift layers folds service)).runM
        (PublishedWords.actionM checkedUnit.oracles network choose) before) := by
  let st := CommitCaptures.roundState n shift layers folds service
  let post := Completed (Aux := Aux) n shift layers folds before.oracle.provider.words
  have stop (why : PIR.Stop) (store : Store Aux) : post (.stopped why) store := by intro _ eq; cases eq
  have room : 2 ^ (n+1) ≤ 32 := by exact Nat.pow_le_pow_right (by decide) bound
  let published (reply : (OracleProtocol.Interface model).Reply (sendRequest context st.rows)) (store : Store Aux) :=
    ∃ source word, reply = .cons (concrete model (.oracle kind) source) .nil ∧ WordAt n source word store ∧
      PublishedWords.PublishedAfter (row := .field extension) before.oracle.provider.words store.provider.words source (List.ofFn word)
  apply OraclePublication.markedActionOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) (FriCommitRound.beforeChallenge context receiver step st) before.oracle post
    (stop .refused) published _ _ before rfl
  · intro current same
    apply (CommitPublication.sendRegisters checkedUnit.oracles network choose context receiver separate (n+1)
      room current (same ▸ role)).weaken
    rintro ⟨out, after, trace⟩ info
    cases out with
    | stopped why => exact stop _ _
    | returned reply =>
      obtain ⟨handle, self, word, live, position⟩ := info reply rfl
      exact ⟨_, word, handle, ⟨self, live⟩, by simpa only [same] using position⟩
  · rintro sent app reply atSend ⟨source, word, rfl, ⟨self, ⟨live⟩⟩, position⟩
    let continuation (outcome : PIR.Outcome LoopState) (store : Store Aux) : Prop :=
      ∀ values, outcome = .returned values → ∃ beta, CommitDelivery.RoundResult n source word shift beta layers folds values store
    have preserved := PublishedWords.process_frame checkedUnit.oracles network choose
      (sent (.cons (concrete model (.oracle kind) source) .nil)) atSend
    refine (Zkc.MonadicPostcondition.conjunction (first := fun rec ↦ continuation rec.outcome rec.state.oracle) ?_ preserved).weaken ?_
    swap
    · intro rec both values returned
      obtain ⟨beta, result⟩ := both.1 values returned
      exact ⟨source, word, beta, position.transport both.2, result⟩
    have stops (why : PIR.Stop) (store : Store Aux) : continuation (.stopped why) store := by intro _ eq; cases eq
    let keptLayers := Values.cons (concrete model FriBinding.layersSort.type (layers ++ [source])) .nil
    apply OraclePublication.markedActionOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) (app source) atSend.oracle continuation (stops .refused)
      (fun reply store ↦ reply = keptLayers ∧ store = atSend.oracle) _ _ atSend rfl
    · intro state same
      have active : 1 ∈ ([0, 1] : List Nat).map context.roles := by simp [receiver]
      apply (ReceiverForwarding.sequenceAppendAction (oracles := checkedUnit.oracles) (ordinary := PublishedWords.liftM network)
        (base := PublishedWords.readM) (publish := PublishedWords.publishM choose) self active state same).weaken
      rintro ⟨out, after, trace⟩ ⟨preserved, value⟩
      cases out with
      | stopped why => exact stops _ _
      | returned reply => exact ⟨value reply rfl, preserved⟩
    · rintro appended draw reply atAppend ⟨rfl, same⟩
      apply OraclePublication.markedActionOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
        (PublishedWords.publishM choose) draw atAppend.oracle continuation (stops .refused)
        (fun _ store ↦ WordAt n source word store) _ _ atAppend rfl
      · intro state kept
        have retained := kept.trans same
        apply (PublishedWords.RegisteredWord.throughOrdinary checkedUnit.oracles network choose
          (.query (FriCommitRound.serviceSite context 0) (.draw extension) (.cons service .nil)) state (retained ▸ live)).weaken
        rintro ⟨out, after, trace⟩ ⟨unchanged, wordStillLive⟩
        cases out with
        | stopped why => exact stops _ _
        | returned beta => exact ⟨unchanged.trans (retained ▸ self), wordStillLive⟩
      · rintro sampled delivery beta atDraw ⟨who, ⟨parent⟩⟩
        apply (CommitDelivery.sampledReturn network choose context receiver separate step n bound shift beta nonzero
          layers folds service source word (sampled beta) (delivery beta) atDraw who parent).weaken
        intro result accepted values returned
        exact ⟨beta, accepted values returned⟩

end ZkcSecurity.ArkLib.Fri.CommitIteration

module

public import ZkcArkLibExamples.Fri.CommitLoop
public import ZkcArkLibExamples.Fri.CommitChallenge
public import ZkcSecurity.Bindings.Source.ReturnBound

@[expose] public section

/-! A fold error is charged at the receiver's actual draw, for the word
selected at its earlier publication. Delivery, virtual construction and
the remaining suffix may depend on that sample and may stop. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.CommitRoundProbability
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured OracleComp
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriSource (checkedUnit extension)
open FriCommitRound (kind)
open OracleProtocol (concrete)
open CommitIteration (LoopState)
open CommitLoop (State)
variable {Aux E : Type} [octicSampler : SampleableType Octic]
  (ordinary : PublishedSampling.Network model Aux E) (context : ProtocolContext) (service : Nat)
  (fieldAudit : PublishedWords.Table model → Octic → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

local instance : SampleableType (model.Field extension) := octicSampler

abbrev sourceNetwork := CommitChallenge.network ordinary context service fieldAudit indexAudit

def freshPositions : RetainedSampling.Fresh
    (CommitLoop.handler (sourceNetwork ordinary context service fieldAudit indexAudit) choose) service :=
  CommitChallenge.freshPositions (model := model) checkedUnit.oracles ordinary context service fieldAudit indexAudit choose

local notation "net" => sourceNetwork ordinary context service fieldAudit indexAudit
local notation "act" => CommitLoop.handler net choose
local notation "reached" => SourceReturnBound.reached checkedUnit.oracles (PublishedWords.liftM net)
  PublishedWords.readM (PublishedWords.publishM choose)

/-- The witnesses keep the word, sampled field, actual handle and position
in this invocation's publication history. -/
def Good {n : Nat} (bad : (Fin (2^(n+1)) → Octic) → Octic → Prop)
    (prior : PublishedWords.Table model) (shift : Octic) (layers folds : List OracleAnchor)
    (values : LoopState) (store : CommitIteration.Store Aux) : Prop :=
  ∃ source word beta, ¬ bad word beta ∧
    PublishedWords.PublishedAfter (row := .field extension) prior store.provider.words source (List.ofFn word) ∧
    CommitDelivery.RoundResult n source word shift beta layers folds values store

set_option maxHeartbeats 900000 in
set_option maxRecDepth 6000 in
theorem iteration (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (step n : Nat) (room : n + 1 ≤ 5) (shift : Octic) (nz : shift ≠ 0) (layers folds : List OracleAnchor)
    (before : State Aux) (role : before.oracle.self = 1)
    (bad : (Fin (2^(n+1)) → Octic) → Octic → Prop) (charge : ENNReal)
    (escape : ∀ word, Pr{let beta ← $ᵗ Octic}[bad word beta] ≤ charge) :
    ReturnBound ((FriCommitRound.iteration model context step (CommitCaptures.roundState n shift layers folds service)).runM act before)
      (fun a s ↦ Good bad before.oracle.provider.words shift layers folds a s.oracle) charge := by
  let st := CommitCaptures.roundState n shift layers folds service
  let position := fun (state : State Aux) source (word : Fin (2^(n+1)) → Octic) ↦
    PublishedWords.PublishedAfter (row := .field extension) before.oracle.provider.words state.oracle.provider.words source (List.ofFn word)
  let sent := fun (reply : (OracleProtocol.Interface model).Reply (FriCommitRound.sendRequest context st.rows)) (s : State Aux) ↦
    ∃ source word, reply = .cons (concrete model (.oracle kind) source) .nil ∧ s.oracle.self = 1 ∧
      Nonempty (PublishedWords.RegisteredWord (row := .field extension) s.oracle.entries s.oracle.self source word s.oracle.provider) ∧ position s source word
  rw [← zero_add charge]
  apply reached (FriCommitRound.beforeChallenge context receiver step st) before _ (step := sent)
  · intro current same
    apply ReturnBound.ofLaw
    apply (CommitPublication.sendRegisters checkedUnit.oracles net choose context receiver separate (n+1)
      (Nat.pow_le_pow_right (by decide) room) current (same ▸ role)).weaken
    intro record law reply returned
    obtain ⟨output, who, word, live, located⟩ := law reply returned
    exact ⟨_, word, output, who, live, by simpa only [position, same] using located⟩
  · rintro next after _ atSend ⟨source, word, rfl, self, ⟨parent⟩, located⟩
    let goal := fun a (s : State Aux) ↦ ∃ beta, ¬ bad word beta ∧
      CommitDelivery.RoundResult n source word shift beta layers folds a s.oracle
    have frame := PublishedWords.process_frame checkedUnit.oracles net choose
      (next (.cons (concrete model (.oracle kind) source) .nil)) atSend
    suffices tail : ReturnBound ((next (.cons (concrete model (.oracle kind) source) .nil)).runM act atSend) goal charge by
      apply (tail.withLaw (fact := fun _ s ↦ PublishedWords.Preserves atSend.oracle.provider.words s.oracle.provider.words) (frame.weaken fun record kept _ _ ↦ kept)).weaken
      rintro a s ⟨⟨beta, ok, result⟩, preserved⟩
      exact ⟨source, word, beta, ok, located.transport preserved, result⟩
    let appended := Values.cons (concrete model FriBinding.layersSort.type (layers ++ [source])) .nil
    rw [← zero_add charge]
    apply reached (after source) atSend goal (step := fun reply state ↦ reply = appended ∧ state.oracle = atSend.oracle)
    · intro current same
      apply ReturnBound.ofLaw
      apply (ReceiverForwarding.sequenceAppendAction (oracles := checkedUnit.oracles) (ordinary := PublishedWords.liftM net)
        (base := PublishedWords.readM) (publish := PublishedWords.publishM choose) self
        (show 1 ∈ ([0,1] : List Nat).map context.roles by simp [receiver]) current same).weaken
      exact fun _ pair reply eq ↦ ⟨pair.2 reply eq, pair.1⟩
    · rintro appendedNext draw _ atAppend ⟨rfl, preserved⟩
      rw [← add_zero charge]
      apply reached draw atAppend goal (step := fun beta state ↦ ¬ bad word beta ∧ state.oracle = atSend.oracle)
      · intro current same
        change ReturnBound (CommitChallenge.handler checkedUnit.oracles ordinary context service fieldAudit indexAudit choose
          (FriCommitRound.drawRequest context service) current) _ _
        rw [CommitChallenge.draw (model := model) checkedUnit.oracles ordinary context service fieldAudit indexAudit choose current]
        unfold ReturnBound
        simp only [← bind_pure_comp]
        let field : model.Field extension ≃ Octic := Equiv.refl _
        have uniform := SampleableType.prEvent_uniformSample_equiv field (bad word)
        simp [violates, same.trans preserved]
        with_unfolding_all exact uniform.le.trans (escape word)
      · rintro sampled delivery beta current ⟨ok, kept⟩
        apply ReturnBound.ofLaw
        apply (CommitDelivery.sampledReturn net choose context receiver separate step n room shift beta nz layers folds service
          source word (sampled beta) (delivery beta) current (kept ▸ self) (kept ▸ parent)).weaken
        exact fun record law values returned ↦ ⟨beta, ok, law values returned⟩

end ZkcSecurity.ArkLib.Fri.CommitRoundProbability

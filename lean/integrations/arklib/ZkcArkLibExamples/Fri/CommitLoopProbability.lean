module

public import ZkcArkLibExamples.Fri.CommitRoundProbability

@[expose] public section

/-! Compose fold errors on the receiver's actual bounded loop. A successful
safe witness fixes all the published words and challenges before the
terminal prover chooses any coefficient. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.CommitLoopProbability
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured OracleComp
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriSource (checkedUnit)
open CommitLoop (State Rounds packed callback captures)
open FriCommitRound (roundSite)
open CommitRoundProbability (Good)
open _root_.Fri (FoldingAgreementFailure FoldTrace)
open _root_.Domain (SmoothCosetFftDomain)
variable {Aux E : Type} [SampleableType Octic]
  (ordinary : PublishedSampling.Network model Aux E) (context : ProtocolContext) (service : Nat)
  (fieldAudit : PublishedWords.Table model → Octic → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

local notation "net" => CommitRoundProbability.sourceNetwork ordinary context service fieldAudit indexAudit
local notation "act" => CommitLoop.handler net choose

set_option maxRecDepth 6000 in
private theorem callbackBound (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (step n : Nat) (room : n+1 ≤ 5) (shift : Octic) (nz : shift ≠ 0) (layers folds : List OracleAnchor)
    (before : State Aux) (role : before.oracle.self = 1)
    (bad : (Fin (2^(n+1)) → Octic) → Octic → Prop) (charge : ENNReal)
    (escape : ∀ word, Pr{let beta ← $ᵗ Octic}[bad word beta] ≤ charge) :
    ReturnBound ((callback context service (packed (n+1) shift layers folds) step).runM act before)
      (fun a s ↦ Good bad before.oracle.provider.words shift layers folds a s.oracle) charge := by
  unfold callback Bindings.RepeatSite.maskedIteration
  dsimp only
  rw [CommitLoop.mask context receiver]
  apply ReturnBound.beforeExact (post := fun a (s : State Aux) ↦ Good bad before.oracle.provider.words shift layers folds a s.oracle)
  · apply SourceReturnBound.withinFrame checkedUnit.oracles (PublishedWords.liftM net) PublishedWords.readM
      (PublishedWords.publishM choose) before (.iteration roundSite.site step)
      (ReceiverForwarding.enterIteration _ _ _ _ _ _ _) (FriCommitRound.iteration model context step (CommitCaptures.roundState n shift layers folds service))
      (Good bad before.oracle.provider.words shift layers folds)
    intro current same
    have checked := CommitRoundProbability.iteration ordinary context service fieldAudit indexAudit choose receiver separate step n room shift nz layers folds current (same ▸ role) bad charge escape
    simpa only [same, CommitLoop.handler, PublishedWords.actionM] using checked
  · rintro _ current ⟨source, word, beta, ok, located, view, rfl, who, virtual, parent⟩
    apply PIR.Process.OnReturn.done
    exact ⟨source, word, beta, ok, located, view, CommitLoop.mask context receiver n (shift ^ 2) (layers ++ [source]) (folds ++ [view]), who, virtual, parent⟩

def Completed {n r : Nat} (D : SmoothCosetFftDomain (n+r) Octic) (shift : Octic)
    (layers folds : List OracleAnchor) (prior : PublishedWords.Table model)
    (values : CommitIteration.LoopState) (store : CommitIteration.Store Aux) : Prop :=
  ∃ rounds : Rounds (n+r) r, (∀ cs, (toTrace 0 D (rounds.transcript cs)).Safe (1/4)) ∧
    rounds.First prior store.provider.words ∧ rounds.Installed store shift ∧ store.self = 1 ∧
    values = packed n (rounds.endingShift shift) (layers ++ rounds.sources) (folds ++ rounds.views)

set_option maxRecDepth 6000 in
theorem fromStep (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (n r step : Nat) (room : n+r ≤ 5) (D : SmoothCosetFftDomain (n+r) Octic)
    (error : Nat → ENNReal) (escapes : FoldingEscapes 0 (1/4) D r error)
    (shift : Octic) (nz : shift ≠ 0) (layers folds : List OracleAnchor) (before : State Aux) (role : before.oracle.self = 1) :
    ReturnBound ((Finite.fold (callback context service) (List.range' step r) (packed (n+r) shift layers folds)).runM act before)
      (fun values s ↦ Completed (r := r) D shift layers folds before.oracle.provider.words values s.oracle)
      (∑ j ∈ Finset.range r, error j) := by
  induction r generalizing step shift layers folds before error with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    apply ReturnBound.ofOnReturn (PIR.Process.OnReturn.done ?_)
    exact ⟨.empty n, fun _ ↦ trivial, trivial, trivial, role, by simp [Rounds.endingShift, Rounds.sources, Rounds.views]⟩
  | succ r ih =>
    rw [List.range'_succ, Finite.fold, Finset.sum_range_succ']
    let bad := fun word beta ↦ FoldingAgreementFailure D word 1 (degreeBound r (2^0)) (1/4) beta
    have head := callbackBound ordinary context service fieldAudit indexAudit choose receiver separate step (n+r) room shift nz
      layers folds before role bad (error 0) escapes.1
    rw [add_comm _ (error 0)]
    apply ReturnBound.processBind head
    rintro _ current ⟨source, word, beta, ok, first, view, rfl, who, ⟨virtual⟩, ⟨parent⟩⟩
    let rest := Finite.fold (callback context service) (List.range' (step+1) r)
      (packed (n+r) (shift^2) (layers ++ [source]) (folds ++ [view]))
    have tail := ih (step+1) (by omega) (D.subdomain 1) (fun j ↦ error (j+1)) escapes.2 (shift^2) (pow_ne_zero _ nz)
      (layers ++ [source]) (folds ++ [view]) current who
    have frame := PublishedWords.processPublicationFrame checkedUnit.oracles net choose rest current
    apply (tail.withLaw (fact := fun _ s ↦ PublishedWords.PublicationFrame current.oracle s.oracle)
      (frame.weaken fun _ h _ _ ↦ h)).weaken
    rintro value final ⟨⟨later, safe, _, registered, self, output⟩, kept⟩
    exact ⟨.fold source view word beta later, fun cs ↦ And.intro ok (safe cs), first.transport kept.words,
      ⟨parent.transport kept, virtual.transport kept, registered⟩, self, by
        simpa only [Rounds.endingShift, Rounds.sources, Rounds.views, List.append_assoc, List.singleton_append] using output⟩

end ZkcSecurity.ArkLib.Fri.CommitLoopProbability

module

public import ZkcArkLibExamples.Fri.VerifierRoot
public import ZkcArkLibExamples.Fri.PublishedSampling
public import ZkcArkLibExamples.Fri.ObservedQueries

@[expose] public section

/-! Charge the actual query suffix after a prior publication. A safe, far
sequence was fixed before the first index draw. The eight checks allow
repetitions and keep stopped runs at their original probability. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.VerifierQueryProbability
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured Phases OracleComp
open FriSource FriSourceBodies FriPhaseCalls
open OracleProtocol (concrete)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitReturn (Publication)
open CommitLoop (State handler)
open FriLowDegreeCall (caller inputSites)
open VerifierCalls (accepts)

variable {Aux E : Type} (network : PublishedSampling.Network model Aux E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

private def request (service : Nat) :=
  caller.call (model := model) FriSourceCalls.scalarQueries (.cons (concrete model .index 8)
    (.cons (concrete model (.service FriScalarLoop.contract) service) .nil))

set_option maxRecDepth 6000 in
private theorem sample_le (service : Nat) (fresh : RetainedSampling.Fresh (handler network choose) service)
    (before : State Aux) (event : Values (FriBinding.Value model) protocol1Signature.outputs → Prop) :
    Pr{let record ← (request service).runM (handler network choose) before}[returned event record] ≤
    Pr{let xs ← $ᵗ (Fin 8 → Fin 32)}[event (FriScalarLoop.packed model (List.ofFn xs))] := by
  unfold request Caller.call
  apply boundAfterPrefix
  intro _ marked
  let child := invokeProtocol (verifierTable model) protocol1Signature FriScalarLoop.context 1
    (.cons (concrete model .index 8) (.cons (concrete model (.service FriScalarLoop.contract) service) .nil))
  change Pr{let r ← (OracleProtocol.enter model (.application protocol1Signature FriSourceCalls.scalarQueries.site) child).runM (handler network choose) marked}[returned event r] ≤ _
  unfold OracleProtocol.enter
  apply boundAfterPrefix
  intro _ entered
  exact (boundWithExit (first := child) (event := event) (fun _ ↦ .call .leave .done)).trans
    (RetainedSampling.installed_le (handler network choose) service fresh entered event)

private theorem positions_injective :
    Function.Injective (fun xs : Fin 8 → Fin 32 ↦ FriScalarLoop.packed model (List.ofFn xs)) := by
  intro xs ys eq
  have same := congrArg (fun out : Values (FriBinding.Value model) [.indices] ↦
    (out.get .here).bind ProtocolValue.toConcrete) eq
  simp only [FriScalarLoop.packed, Values.get, concrete, Option.bind_some, ProtocolValue.toConcrete_ofConcrete,
    Option.some.injEq, List.map_ofFn, List.ofFn_inj] at same
  funext i
  exact Fin.ext (congrFun same i)

theorem afterCommit_le (pub : Publication) (shift : Octic) (nonzero : shift ≠ 0) (service : Nat)
    (fresh : RetainedSampling.Fresh (handler network choose) service)
    (before : State Aux) (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift) :
    Pr{let result ← (FriLowDegreeCall.afterCommit model 8 service (pub.output shift)).runM (handler network choose) before}[
      returned (fun _ ↦ True) result] ≤ Pr{let xs ← $ᵗ (Fin 8 → Fin 32)}[accepts pub shift xs = true] := by
  let event := fun out ↦ ∃ xs : Fin 8 → Fin 32, out = FriScalarLoop.packed model (List.ofFn xs) ∧ accepts pub shift xs = true
  unfold FriLowDegreeCall.afterCommit
  apply boundAfterReturn (law := (inputsKeep (oracles := checkedUnit.oracles) (ordinary := PublishedWords.liftM network)
    (base := PublishedWords.readM) (publish := PublishedWords.publishM choose) caller rfl (by decide) role inputSites.1 pub.handles).onReturn rfl)
  rintro _ gathered ⟨initial, rfl⟩
  change Pr{let result ← ((request service).bind (VerifierRoot.resume pub shift)).runM (handler network choose) gathered}[
    returned (fun _ ↦ True) result] ≤ _
  refine (boundByEarlierEvent event (PublishedWords.withPublicationFrame checkedUnit.oracles network choose
    (VerifierRoot.sample network choose service gathered)) ?_).trans ((sample_le network choose service fresh gathered event).trans ?_)
  · rintro _ drawn ⟨⟨xs, rfl⟩, frame⟩
    have registered := pub.rounds.transport frame shift (initial ▸ live)
    exact (VerifierRoot.afterSample network choose pub shift nonzero xs drawn (frame.registry.1.trans (initial ▸ role)) registered).weaken
      fun _ law value returned _ ↦ ⟨xs, rfl, (law value returned).1⟩
  · apply prEvent_mono
    rintro xs ⟨ys, same, good⟩
    exact positions_injective same ▸ good

/-- Query contribution of the actual receiver after a safe, far publication. -/
theorem safeFar_le (pub : Publication) (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ) (service : Nat)
    (fresh : RetainedSampling.Fresh (handler network choose) service)
    (before : State Aux) (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift)
    (safe : (toTrace 0 (RetainedDomain.domain shift nonzero) (pub.rounds.transcript pub.coefficients)).Safe (1 / 4))
    (far : Far (RetainedDomain.domain shift nonzero) 8 δ pub.word) :
    Pr{let result ← (FriLowDegreeCall.afterCommit model 8 service (pub.output shift)).runM (handler network choose) before}[
      returned (fun _ ↦ True) result] ≤ ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ 8 := by
  apply (afterCommit_le network choose pub shift nonzero service fresh before role live).trans
  exact query_escape_le_of_accepts (toTrace 0 (RetainedDomain.domain shift nonzero) (pub.rounds.transcript pub.coefficients))
    (1 / 4) δ safe far (Equiv.refl _) (fun xs ↦ accepts pub shift xs = true)
    (fun xs ok ↦ Phases.accepts_trace RetainedDomain.root 0 (RetainedDomain.domain shift nonzero) shift
      (RetainedDomain.geometry shift nonzero) RetainedDomain.compatible _ xs ok)

end ZkcSecurity.ArkLib.Fri.VerifierQueryProbability

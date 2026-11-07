module

public import ZkcArkLibExamples.Fri.CommitLoopProbability
public import ZkcArkLibExamples.Fri.CommitReturn

@[expose] public section

/-! The actual invoked Commit produces a safe transcript except for the
three fold errors. Its coefficient can be chosen after all field draws. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.CommitProbability
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriCommitAdmission
open FriCommitRound (roundSite)
open CommitLoop (State Rounds packed captures)
open CommitReturn (Publication)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open OracleProtocol (concrete)

abbrev foldError := ∑ r ∈ Finset.range 3, uniqueDecodingError Octic 5 r

def SafeReturn {Aux : Type} (prior : PublishedWords.Table model) (shift : Octic) (nz : shift ≠ 0)
    (out : Values (FriBinding.Value model) protocol0Signature.outputs) (store : CommitIteration.Store Aux) : Prop :=
  ∃ pub : Publication, pub.Returned prior shift out store ∧
    (toTrace 0 (RetainedDomain.domain shift nz) (pub.rounds.transcript pub.coefficients)).Safe (1/4)

variable {Aux E : Type} [SampleableType Octic]
  (ordinary : PublishedSampling.Network model Aux E) (context : ProtocolContext) (service : Nat)
  (fieldAudit : PublishedWords.Table model → Octic → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

local notation "net" => CommitRoundProbability.sourceNetwork ordinary context service fieldAudit indexAudit
local notation "act" => CommitLoop.handler net choose

set_option maxRecDepth 6000 in
theorem installed (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nz : shift ≠ 0) (before : State Aux) (role : before.oracle.self = 1) :
    ReturnBound ((invokeProtocol (verifierTable model) protocol0Signature context 1 (arguments model shift service)).runM act before)
      (fun out s ↦ SafeReturn before.oracle.provider.words shift nz out s.oracle) foldError := by
  rw [CommitBody.invokeReceiver context receiver shift service]
  apply ReturnBound.beforeExact (post := fun out (s : State Aux) ↦ SafeReturn before.oracle.provider.words shift nz out s.oracle)
  · rw [CommitBody.split]
    have entry := CommitIngress.installed net choose context receiver separate shift nz service before.oracle role before rfl
    apply ReturnBound.afterExact (post := fun live (s : State Aux) ↦ s.oracle = before.oracle ∧
      roundSite.operands.eval live.get = .cons (concrete model .index 3) ((packed 5 shift [] []).append (captures service)) ∧
      live.get shiftPort = concrete model (.field extension) shift ∧ live.get sizePort = concrete model .index 32 ∧
      live.get countPort = concrete model .index 3)
    · exact entry.weaken fun rec h live returned ↦ And.intro h.1 (h.2 live returned)
    rintro live current ⟨same, inputs, offset, rows, count⟩
    let D := RetainedDomain.domain shift nz
    apply ReturnBound.beforeExact (post := fun values (s : State Aux) ↦ CommitLoopProbability.Completed
      (n := 2) (r := 3) D shift [] [] current.oracle.provider.words values s.oracle)
    · rw [roundSite.maskedIterations (verifierAlgebra model) (verifierTable model) context 1 live.get (concrete model .index 3)
        (packed 5 shift [] []) (captures service) inputs (by change ([0,1].map context.roles).contains 1 = true; simp [receiver])
        (ProtocolValue.toConcrete_ofConcrete (carriers := model.toCarriers) .index 3) (by decide),
        CommitLoop.mask context receiver, List.range_eq_range']
      exact CommitLoopProbability.fromStep ordinary context service fieldAudit indexAudit choose receiver separate 2 3 0 (by decide)
        D (uniqueDecodingError Octic 5) (Phases.foldingEscapes_uniqueDecoding D (by decide)) shift nz [] [] current (same ▸ role)
    · rintro values after ⟨rounds, safe, located, registered, who, output⟩
      rw [List.nil_append, List.nil_append] at output
      subst values
      have finish := CommitReturn.terminal net choose context receiver separate before.oracle.provider.words shift live after
        rounds offset rows count (by simpa only [same] using located) registered who
      exact finish.weaken fun _ law out returned ↦ by
        obtain ⟨pub, identity, result⟩ := law out returned
        exact ⟨pub, result, identity.symm ▸ safe pub.coefficients⟩
  · rintro _ current ⟨pub, ⟨rfl, located, registered, who⟩, safe⟩
    exact PIR.Process.OnReturn.done ⟨pub, ⟨pub.mask context receiver separate shift, located, registered, who⟩, safe⟩

end ZkcSecurity.ArkLib.Fri.CommitProbability

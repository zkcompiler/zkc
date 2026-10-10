import Zkc.Protocols.Sumcheck.LocalProver.Challenge
import Zkc.Protocols.CapturedPrograms.Probability
import Tests.ProviderSampling

set_option autoImplicit false

namespace Tests.ChallengeConsumption
open PIR
open ProductTape

def noSig : Signature := ⟨Empty,fun o => nomatch o⟩
def noLocal : MonadHandler PMF noSig Unit Empty := fun o => nomatch o

def two : Proc (sig Nat noSig) Nat := .call none fun (a : Nat) =>
  .call none fun (b : Nat) => .done (a+b)

/-- Actual first pop emits a value, then exhaustion retains it and the empty tape. -/
theorem exhausted_prefix : two.runM (persistent noLocal) ((),[7]) =
    (pure ⟨.stopped .exhausted,((),[]),[.inl 7]⟩ : PMF _) := by
  simp [two, Proc.runM, persistent, Execution.followM]

def stopAfterOne : Proc (sig Nat noSig) Nat := .call none fun _ => .halt .abort

theorem stopped_prefix : stopAfterOne.runM (persistent noLocal) ((),[7,9]) =
    (pure ⟨.stopped .abort,((),[9]),[.inl 7]⟩ : PMF _) := by
  simp [stopAfterOne, Proc.runM, persistent, Execution.followM]

def failingSig : Signature := ⟨Unit,fun _ => Unit⟩
noncomputable def failingLocal : MonadHandler PMF failingSig Nat Nat := fun _ s =>
  pure ⟨.stopped .refused,s+1,[42]⟩

/-- A local failure mutates its own state and emits an event. The provider suffix
    remains intact and the later draw is not executed. -/
theorem local_failure :
    (Proc.call (some ()) (fun _ => Proc.call none Proc.done) : Proc (sig Nat failingSig) Nat).runM
      (persistent failingLocal) (5,[7,9]) =
        (pure ⟨.stopped .refused,(6,[7,9]),[.inr 42]⟩ : PMF _) := by
  simp [Proc.runM, persistent, failingLocal, Execution.followM]

/-- Existing nonproduct controls retain their different actual finite populations. -/
theorem nonproduct_controls :
    (Tests.ProviderSampling.count Tests.ProviderSampling.iid
      (fun t => Tests.ProviderSampling.adaptive ⟨t,0⟩) : ℚ) / Tests.ProviderSampling.iid.length = 1/3 ∧
    (Tests.ProviderSampling.count Tests.ProviderSampling.urn
      (fun t => Tests.ProviderSampling.adaptive ⟨t,0⟩) : ℚ) / Tests.ProviderSampling.urn.length = 5/6 :=
  Tests.ProviderSampling.adaptive_probabilities

/-- The second bit is zero in half of this population, and that event does
    occur. Conditioning on the event and then asking for its probability
    restates the selection rather than measuring the population, so the
    conditional one is not stated here. -/
theorem postselection :
    let pop := Tests.ProviderSampling.binaryIid
    let selected := Tests.ProviderSampling.count pop (fun t => t[1]? == some 0)
    (selected : ℚ) / pop.length = 1/2 ∧ 0 < selected := by
  decide +kernel

def abortedView : View Nat Unit Empty (Zkc.Protocols.Sumcheck.LocalProver.Cut Int) :=
  ⟨.returned (.stopped (Zkc.Protocols.Sumcheck.LocalProver.initial [])),((),1),[]⟩

/-- Regression: the generic data-independent requester can consume a coordinate
    after a returned local Cut.stopped. Equal verdicts would conceal this effect. -/
theorem unguarded_abort_consumes :
    (request (fun _ => true) abortedView).runM (persistent noLocal) ((),[7]) =
      (pure ⟨.returned 7,((),[]),[.inl 7]⟩ : PMF _) := by
  simp [request, abortedView, Proc.runM, persistent, Execution.followM]

theorem guarded_abort_retains :
    (request (Zkc.Protocols.Sumcheck.LocalProver.committedOnly (fun _ => true)) abortedView).runM (persistent noLocal) ((),[7]) =
      (pure ⟨.stopped .abort,((),[7]),[]⟩ : PMF _) := by
  simp [request, Zkc.Protocols.Sumcheck.LocalProver.committedOnly, abortedView, Proc.runM]

end Tests.ChallengeConsumption

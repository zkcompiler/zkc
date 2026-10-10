import Zkc.Protocols.Sumcheck.LocalProver.Challenge
import ZkcArkLib.LocalProver.Source
import ZkcArkLib.LocalProver.Observation
import Zkc.Probability.ConditionalTape

set_option autoImplicit false

namespace ZkcArkLib.LocalProver.Provider
open PIR
open OracleComp ENNReal ProductTape Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver

variable {D S E F : Type} {J : Signature}

/-- The actual admitted-code interpretation can use local coins but cannot
    inspect the product provider. The complete local Cut remains in the result. -/
def source [Ring F] [DecidableEq F] (p : Code) (inputs : List F) :
    Proc (sig D Zkc.Protocols.Sumcheck.LocalProver.Source.sig) (Cut F) :=
  localSource (Zkc.Protocols.Sumcheck.LocalProver.Source.source p (initial inputs))

noncomputable def localHandler : MonadHandler PMF Zkc.Protocols.Sumcheck.LocalProver.Source.sig Unit Empty :=
  fun o st => liftM (ZkcArkLib.LocalProver.Source.handler o st)

theorem source_exact [Ring F] [DecidableEq F] (p : Code) (inputs : List F)
    (rest : List D) :
    (source p inputs).runM (persistent localHandler) ((),rest) =
      (do
        let c ← (liftM (pre p (initial inputs)) : PMF _)
        pure ⟨.returned c,((),rest),[]⟩) := by
  rw [source, local_source_exact]
  change ((Zkc.Protocols.Sumcheck.LocalProver.Source.source p (initial inputs)).runM
    (fun o st => (liftM (ZkcArkLib.LocalProver.Source.handler o st) : PMF _)) () >>= _) = _
  rw [← runM_lift, ZkcArkLib.LocalProver.Source.execution_exact]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, monadLift_bind, monadLift_pure, bind_assoc, pure_bind,
    ZkcArkLib.LocalProver.Source.retain, retainLocal, List.map_nil]

def verdict [CommRing F] [DecidableEq F] (embed : D → F) :
    View D S E (Cut F) × Outcome D → Option Unit
  | (⟨.returned (.committed b),_,_⟩,.returned d) =>
      Zkc.Protocols.Sumcheck.ProductFamily.OneRound.verdict b.claim b.message.1 b.message.2.1 b.message.2.2 (embed d)
  | _ => none

/-- ArkLib reduction consumer at the proved checkpoint kernel.
    A declined/exhausted request or source abort has explicit none verdict. -/
noncomputable def finish [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : ProbComp D) (active : View D S E (Cut F) → Bool)
    (v : View D S E (Cut F)) : PMF (Option Unit) :=
  if requesting active v then
    match v.outcome with
    | .returned (.committed b) => liftM (ZkcArkLib.Sumcheck.OneRound.Kernel.actualKernel embed draw
        (fun _ (b : Boundary F) => b.message) b.claim b)
    | _ => pure none
  else pure none

theorem request_consumer [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : ProbComp D) (localH : MonadHandler PMF J S E)
    (active : View D S E (Cut F) → Bool) (v : View D S E (Cut F)) :
    (do
      let next ← (request active v).runM (online (liftM draw) localH) v.state
      pure (verdict embed (v,next.outcome))) = finish embed draw active v := by
  rcases v with ⟨out,⟨s,n⟩,es⟩
  cases out with
  | stopped why => simp [request, requesting, Proc.runM, finish, verdict]
  | returned c =>
    by_cases ha : active ⟨.returned c,(s,n),es⟩ = true
    · cases n with
      | zero => simp [request, requesting, Proc.runM, online, Execution.followM,
          finish, verdict, ha]
      | succ n =>
        cases c with
        | stopped state =>
          simp [request, requesting, Proc.runM, online, Execution.followM, finish,
            verdict, ha, PMF.bind_const]
        | committed b =>
          simp only [request, requesting, ha, Bool.true_and, if_true, Proc.runM, online,
            bind_assoc, pure_bind, Execution.followM, List.append_nil,
            finish, verdict, ZkcArkLib.Sumcheck.OneRound.Kernel.kernel_transport, monadLift_bind, monadLift_pure]
          simp
    · simp [request, requesting, Proc.runM, finish, verdict, ha]

/-- The bound's consumer executes the existing reduction with the posterior
    challenge law derived above, after arbitrary persistent prior source calls. -/
theorem consumer_exact [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : ProbComp D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) (Cut F)) (st : S × Nat)
    (active : View D S E (Cut F) → Bool) :
    verdict embed <$> nextJoint (liftM draw) localH p st active =
      (p.runM (online (liftM draw) localH) st >>= finish embed draw active) := by
  rw [next_joint_exact, map_bind]
  congr 1
  funext v
  simpa only [map_bind, map_pure] using request_consumer embed draw localH active v

theorem lift_mass {A : Type} (c : ProbComp A) (a : A) :
    Pr[= a | (liftM c : PMF A)] = Pr[= a | c] := by
  rfl

theorem acceptance_bound [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (draw : ProbComp D)
    (localH : MonadHandler PMF J S E) (p : Proc (sig D J) (Cut F)) (st : S × Nat)
    (active : View D S E (Cut F) → Bool) (ε : ℝ≥0∞)
    (cap : ∀ d, Pr[= d | draw] ≤ ε)
    (false_claim : ∀ v ∈ (p.runM (online (liftM draw) localH) st).support,
      requesting active v = true → ∀ b, v.outcome = .returned (.committed b) → b.claim ≠ 2) :
    Pr[= some () | verdict embed <$> nextJoint (liftM draw) localH p st active] ≤ 2 * ε := by
  rw [consumer_exact, PMF.probOutput_eq_apply]
  apply mass_bind_le
  intro v hv
  rw [← PMF.probOutput_eq_apply]
  by_cases hr : requesting active v = true
  · cases ho : v.outcome with
    | stopped why => simp [finish, hr, ho]
    | returned c =>
      cases c with
      | stopped state => simp [finish, hr, ho]
      | committed b =>
        rw [finish, if_pos hr, ho, lift_mass]
        have hb := false_claim v hv hr b ho
        have bound := ZkcArkLib.Sumcheck.OneRound.Kernel.adaptive_claim_bound embed inj
          (pure b) (fun _ : Boundary F => draw)
          (fun _ (b : Boundary F) => b.message) Boundary.claim ε
          (by intros; exact cap _)
          (by intro b' hb'; have he : b' = b := (mem_support_pure_iff _ _).mp hb';
              simpa [he] using hb)
        simpa using bound
  · simp [finish, hr]

noncomputable def sourceJoint (q : PMF D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) (Cut F)) (st : S × Nat)
    (active : View D S E (Cut F) → Bool) :=
  nextJoint q localH p st (committedOnly active)

theorem source_consumer_exact [CommRing F] [DecidableEq F] (embed : D → F)
    (draw : ProbComp D) (localH : MonadHandler PMF J S E)
    (p : Proc (sig D J) (Cut F)) (st : S × Nat)
    (active : View D S E (Cut F) → Bool) :
    verdict embed <$> sourceJoint (liftM draw) localH p st active =
      (p.runM (online (liftM draw) localH) st >>= finish embed draw (committedOnly active)) :=
  consumer_exact embed draw localH p st (committedOnly active)

theorem source_acceptance_bound [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (draw : ProbComp D)
    (localH : MonadHandler PMF J S E) (p : Proc (sig D J) (Cut F)) (st : S × Nat)
    (active : View D S E (Cut F) → Bool) (ε : ℝ≥0∞)
    (cap : ∀ d, Pr[= d | draw] ≤ ε)
    (false_claim : ∀ v ∈ (p.runM (online (liftM draw) localH) st).support,
      requesting (committedOnly active) v = true →
        ∀ b, v.outcome = .returned (.committed b) → b.claim ≠ 2) :
    Pr[= some () | verdict embed <$> sourceJoint (liftM draw) localH p st active] ≤ 2 * ε :=
  acceptance_bound embed inj draw localH p st (committedOnly active) ε cap false_claim

/-- Mix arbitrary initial local/setup states and source selections while sampling
    the product suffix conditionally as stated. Falsity is required only on support. -/
theorem initialized_acceptance_bound [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (draw : ProbComp D)
    (localH : MonadHandler PMF J S E) (init : PMF (S × Nat))
    (p : S × Nat → Proc (sig D J) (Cut F))
    (active : View D S E (Cut F) → Bool) (ε : ℝ≥0∞)
    (cap : ∀ d, Pr[= d | draw] ≤ ε)
    (false_claim : ∀ st ∈ init.support,
      ∀ v ∈ ((p st).runM (online (liftM draw) localH) st).support,
        requesting (committedOnly active) v = true →
          ∀ b, v.outcome = .returned (.committed b) → b.claim ≠ 2) :
    Pr[= some () | (do
      let st ← init
      verdict embed <$> sourceJoint (liftM draw) localH (p st) st active)] ≤ 2 * ε := by
  rw [PMF.probOutput_eq_apply]
  apply mass_bind_le
  intro st hst
  rw [← PMF.probOutput_eq_apply]
  exact source_acceptance_bound embed inj draw localH (p st) st active ε cap
    (false_claim st hst)

end ZkcArkLib.LocalProver.Provider

import Zkc.Protocols.CorrelatedSetup.Service
import Zkc.Modules.ImmutableCache
import Mathlib.Data.ZMod.Basic


set_option autoImplicit false
namespace Zkc.Protocols.CorrelatedSetup.Service
open Zkc.Probability.AdaptiveTape
open Zkc.Protocols.CorrelatedSetup
variable {F : Type} [CommRing F]

/-- Only the coefficients are cached; each modeled response still takes its
    own fresh coordinate. This record is a bounded authoring example. -/
structure CoefficientCache (s : Setup F) (w : Witness F) (p : Triple F) where
  value : F × F
  valid : value = byPrefix s w p

def buildCache (s : Setup F) (w : Witness F) (p : Triple F) : CoefficientCache s w p :=
  let provider := fun _ : Unit => byPrefix s w p
  let cache := Zkc.Modules.ImmutableCache.empty
  ⟨(Zkc.Modules.ImmutableCache.lookup provider (fun _ _ => true) cache ()).1,
    Zkc.Modules.ImmutableCache.lookup_value provider (fun _ _ => true) cache ()
      (Zkc.Modules.ImmutableCache.empty_valid provider)⟩

def cachedStep (s : Setup F) (w : Witness F) (controller : Controller F) (p : Triple F)
    (value : F × F) :=
  advance controller p (actualResponse s value) (tags s (publicationsOf w p)).2.2

theorem cached_step_correct (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (cache : CoefficientCache s w p) (h : History F) (r : F) :
    cachedStep s w controller p cache.value h r = realStep s w controller p h r := by
  simp only [cachedStep,cache.valid,realStep]

theorem cached_continuation_correct (s : Setup F) (w : Witness F)
    (controller : Controller F) (p : Triple F) (cache : CoefficientCache s w p)
    (n : Nat) (h : History F) (r : Tape F n) :
    run (cachedStep s w controller p cache.value) n h r = run (realStep s w controller p) n h r :=
  run_congr _ _ (cached_step_correct s w controller p cache) n h r

/-- Precompute once after the authenticated wires are established. -/
def compiled (s : Setup F) (w : Witness F) (controller : Controller F) (n : Nat)
    (r : Triple F × Tape F n) : Triple F × History F :=
  let p := publicationsOf w r.1
  let cache := buildCache s w p
  (p,run (cachedStep s w controller p cache.value) n empty r.2)

theorem compiled_correct (s : Setup F) (w : Witness F) (controller : Controller F)
    (n : Nat) (r : Triple F × Tape F n) : compiled s w controller n r = real s w controller n r := by
  apply Prod.ext
  · rfl
  · exact cached_continuation_correct s w controller _ (buildCache s w _) n empty r.2

theorem compiled_coupling (s : Setup F) (w : Witness F) (controller : Controller F)
    (n : Nat) (r : Triple F × Tape F n) :
    compiled s w controller n r = simulated s controller n (wholeCoins s w controller n r) := by
  rw [compiled_correct,whole_coupling]

theorem compiled_mass [Fintype F] [DecidableEq F]
    (s : Setup F) (w : Witness F) (controller : Controller F)
    (n : Nat) (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // compiled s w controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // simulated s controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (wholeCoins s w controller n)
    (compiled s w controller n) (simulated s controller n) (compiled_coupling s w controller n) out)]

/-- Observer postprocessing can use the declared complete history, not the
    prover's retained cache or unused provider randomness. -/
theorem observed_coupling {O : Type} (observe : Triple F × History F → O)
    (s : Setup F) (w : Witness F) (controller : Controller F) (n : Nat)
    (r : Triple F × Tape F n) :
    observe (compiled s w controller n r) =
      observe (simulated s controller n (wholeCoins s w controller n r)) :=
  congrArg observe (compiled_coupling s w controller n r)

def testSetup : Setup (ZMod 7) := ⟨3,5,1,6,2⟩
def witnessOne : Witness (ZMod 7) := ⟨1,1,by decide⟩
def witnessTwo : Witness (ZMod 7) := ⟨2,4,by decide⟩
def commonPrefix : Triple (ZMod 7) := (6,4,5)

theorem exposing_cache_changes_observer :
    byPrefix testSetup witnessOne commonPrefix ≠ byPrefix testSetup witnessTwo commonPrefix := by decide

/-- Function types alone do not forbid a closure capturing a private witness.
    `witness_mass` requires the SAME controller in both compared executions. -/
def leakingController (w : Witness (ZMod 7)) : Controller (ZMod 7) :=
  fun _ _ => some ⟨2,w.x,false⟩

theorem witness_dependent_controller_changes_view :
    real testSetup witnessOne (leakingController witnessOne) 1
      (publicationsOf witnessOne commonPrefix,(0,())) ≠
    real testSetup witnessTwo (leakingController witnessTwo) 1
      (publicationsOf witnessTwo commonPrefix,(0,())) := by decide

end Zkc.Protocols.CorrelatedSetup.Service

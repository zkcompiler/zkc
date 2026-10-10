import Zkc.Modules.Allocation
import Zkc.Protocols.CapturedPrograms.Selection

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CapturedPrograms.Installation
open Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Protocols.CapturedPrograms Zkc.Source.Availability
variable {F : Type}

/-- A local source slot is interpreted by the actual namespaced World entry.
    Availability is checked before reading, including when the value is zero. -/
def localEnv (n : Namespace) (s : World F) : Env F :=
  fun i => fromSlots s.known s.values.challenge (addr n i)

theorem installed_slot (r : Request F) (s : World F) (i : Nat) (hi : i < r.captured.length) :
    localEnv r.namespaceId (patch r s) i = r.captured[i]? := by
  have hm : addr r.namespaceId i ∈ r.ids := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have hk : addr r.namespaceId i ∈ (patch r s).known := List.mem_append_left _ hm
  simp only [localEnv,fromSlots,if_pos hk,patch_capture r s i hi]
  simp [Request.localWorld,snapshot,List.getElem?_eq_getElem hi]

/-- Scope is exactly the captured local slots. Old data outside this finite
    patch, including old entries in the same namespace, cannot influence issue. -/
theorem installed_agreement (r t : Request F) (s u : World F)
    (captures : r.captured = t.captured) :
    Agree (List.range r.captured.length)
      (localEnv r.namespaceId (patch r s)) (localEnv t.namespaceId (patch t u)) := by
  intro i hi
  have hr := List.mem_range.mp hi
  have ht : i < t.captured.length := by simpa [← captures] using hr
  rw [installed_slot r s i hr,installed_slot t u i ht,captures]

variable [CommRing F] [DecidableEq F]

def afterInstall (capacity : Nat) (r : Request F) (tree : Tree) (s : World F) : Option (Issued F) :=
  let out := execute capacity r s
  if out.success then issue (List.range r.captured.length) (localEnv r.namespaceId out.world) tree
  else none

theorem afterInstall_accepted (capacity : Nat) (r : Request F) (tree : Tree) (s : World F)
    (x : Issued F) (accepted : afterInstall capacity r tree s = some x) :
    (execute capacity r s).success = true ∧
    issue (List.range r.captured.length) (localEnv r.namespaceId (patch r s)) tree = some x := by
  unfold afterInstall at accepted
  dsimp only at accepted
  split at accepted
  · rename_i ok
    exact ⟨ok,by simpa [Zkc.Modules.Allocation.execute_success_world capacity r s ok] using accepted⟩
  · contradiction

theorem afterInstall_outer_independent (capacity : Nat) (r : Request F) (tree : Tree)
    (s t : World F) : afterInstall capacity r tree s = afterInstall capacity r tree t := by
  unfold afterInstall execute
  split
  · dsimp only
    simp only [↓reduceIte]
    exact issue_agreement _ _ _ tree (installed_agreement r r s t rfl)
  · rfl

/-- Dynamic selection and actual input capture feed the existing full service
    law. Availability/value agreement is derived here, not supplied for Worlds. -/
theorem installed_service_controller (capacity : Nat) (r : Request F) (tree : Tree)
    (s t : World F) (x y : Issued F)
    (hx : afterInstall capacity r tree s = some x)
    (hy : afterInstall capacity r tree t = some y) (w v : Zkc.Protocols.CorrelatedSetup.Witness F) :
    controller x w = controller y v := by
  have ax := (afterInstall_accepted capacity r tree s x hx).2
  have ay := (afterInstall_accepted capacity r tree t y hy).2
  exact issued_same_controller _ _ _ tree x y ax ay (installed_agreement r r s t rfl) w v

theorem installed_service_mass [Fintype F] (capacity : Nat) (r : Request F) (tree : Tree)
    (s t : World F) (x y : Issued F)
    (hx : afterInstall capacity r tree s = some x)
    (hy : afterInstall capacity r tree t = some y) (w v : Zkc.Protocols.CorrelatedSetup.Witness F) (n : Nat)
    (out : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Protocols.CorrelatedSetup.Service.History F) :
    (Fintype.card {tape : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n //
      Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled x.code.service (setup x) w n tape = out} : ℚ) /
        Fintype.card (Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n) =
    (Fintype.card {tape : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n //
      Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled y.code.service (setup y) v n tape = out} : ℚ) /
        Fintype.card (Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n) :=
  issued_service_mass _ _ _ tree x y (afterInstall_accepted capacity r tree s x hx).2
    (afterInstall_accepted capacity r tree t y hy).2 (installed_agreement r r s t rfl) w v n out


end Zkc.Protocols.CapturedPrograms.Installation

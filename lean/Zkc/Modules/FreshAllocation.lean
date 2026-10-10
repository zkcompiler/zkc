import Zkc.Modules.FactorScopes

set_option autoImplicit false

namespace Zkc.Modules.FreshAllocation
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation Zkc.Modules.FactorScopes
variable {K : Type}

/-- Every caller-visible name belongs to this allocator's registered incarnation.
    This permits imported names only after actual registry reconciliation. -/
def Registered (p : Pool) (ns : Names) : Prop :=
  ∀ i n, ns i = some n → n.incarnation = 0 ∧ n.instanceId ∈ p.issued

def enterKeep (f : Fact) (fs : Facts) : Facts
  | 0 => some f
  | i+1 => fs i

theorem registered_push (p : Pool) (ns : Names) (reg : Registered p ns) :
    Registered (advance p) (push (chosen p) ns) := by
  intro i n hn
  cases i with
  | zero => simp only [push,Option.some.injEq] at hn; subst n; simp [chosen,advance]
  | succ i =>
    have h := reg i n hn
    exact ⟨h.1,by simp [advance,h.2]⟩

theorem kept_sound (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (fs : Facts) (ns : Names) (good : p.Good) (reg : Registered p ns)
    (sound : Sound fs ns s) (n : Namespace)
    (h : (allocate quota cap p r s).allocated = some n) :
    Sound (enterKeep (Zkc.Source.FactorInputs.fact r.source r.handle) fs) (push n ns)
      (allocate quota cap p r s).returned.world := by
  intro i f m hf hm
  cases i with
  | zero => exact entered_sound quota cap p r s ns n h 0 f m hf hm
  | succ i =>
    have old := sound i f m hf hm
    obtain ⟨inc,member⟩ := reg i m hm
    have shape : m = (⟨m.instanceId,0⟩ : Namespace) := by
      cases m; simp_all
    rw [shape] at old ⊢
    exact old_fact_preserved quota cap p r s good _ member f old

end Zkc.Modules.FreshAllocation

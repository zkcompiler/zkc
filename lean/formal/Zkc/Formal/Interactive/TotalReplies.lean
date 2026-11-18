module

public import Zkc.Formal.Interactive.Experiment
public import Zkc.Formal.Interactive.JointEntry

@[expose] public section
namespace Zkc.Formal.Interactive.Experiment
open Core
variable {S : Sig} {σ H A : Type} (K : Experiment S σ)

/-- All service mass replies at each reached call. Both terminal cases impose the same
condition. Zero-weight replies place no demand on later services. -/
def TotalOn : Process S H A → σ → Prop
  | .done _, _ | .halt _, _ => True
  | .call op k, s => (K.answer op s).expect (fun _ => 1) = 1 ∧
    ∀ reply next, (K.answer op s).Supports (reply,next) → TotalOn (k reply) next

theorem totalOn_of_normalized (full : ∀ op s, (K.answer op s).expect (fun _ => 1) = 1)
    (p : Process S H A) (s : σ) : K.TotalOn p s := by
  induction p generalizing s with
  | done | halt => trivial
  | call op k ih => exact ⟨full op s,fun r next _ => ih r next⟩

private theorem positiveTicket {B : Type} (ts : List (Weighted B))
    (full : Weighted.total (fun _ => 1) ts = 1) : ∃ t ∈ ts, 0 < t.weight := by
  induction ts with
  | nil => exact False.elim ((by decide : (0 : Mass) ≠ 1) full)
  | cons t ts ih =>
    by_cases positive : 0 < t.weight
    · exact ⟨t,List.mem_cons_self,positive⟩
    · have tail : Weighted.total (fun _ => 1) ts = 1 := by
        simpa only [Weighted.total,Mass.eq_zero_of_not_pos positive,Mass.zero_mul,Mass.zero_add] using full
      obtain ⟨w,member,pos⟩ := ih tail
      exact ⟨w,List.mem_cons_of_mem t member,pos⟩

/-- Select a positive-weight reply at each reached call to obtain a supported complete run. -/
theorem reaches_of_every (p : Process S H A) (s : σ) {P : A → Prop}
    (returns : JointEntry.Returns p P) (total : K.TotalOn p s) :
    ∃ a u, K.Reaches p s a u ∧ P a := by
  induction p generalizing s with
  | done a => exact ⟨a,s,.done a s,returns⟩
  | halt => exact False.elim returns
  | call op k ih =>
    obtain ⟨ticket,member,positive⟩ := positiveTicket (K.answer op s).tickets total.1
    have supported : (K.answer op s).Supports ticket.value := ⟨ticket,member,positive,rfl⟩
    obtain ⟨a,u,tail,good⟩ := ih ticket.value.1 ticket.value.2 (returns _ trivial)
      (total.2 _ _ supported)
    exact ⟨a,u,.call supported tail,good⟩

theorem probability_one_of_every (p : Process S H A) (s : σ) {P : A → Prop}
    (returns : JointEntry.Returns p P) (total : K.TotalOn p s) :
    K.probability p s (fun _ _ => true) = 1 := by
  induction p generalizing s with
  | done => rfl
  | halt => exact False.elim returns
  | call op k ih =>
    change (K.answer op s).expect (fun a => K.probability (k a.1) a.2 (fun _ _ => true)) = 1
    rw [← total.1]
    have equal : ∀ (a : S.Reply op × σ), (K.answer op s).Supports a →
        K.probability (k a.1) a.2 (fun _ _ => true) = 1 :=
      fun a h => ih a.1 a.2 (returns a.1 trivial) (total.2 a.1 a.2 h)
    exact Mass.le_antisymm ((K.answer op s).mono fun a h => (equal a h) ▸ Mass.le_refl)
      ((K.answer op s).mono fun a h => (equal a h) ▸ Mass.le_refl)

#print axioms probability_one_of_every
end Zkc.Formal.Interactive.Experiment

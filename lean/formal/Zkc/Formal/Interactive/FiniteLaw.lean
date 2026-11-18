module

public import Zkc.Formal.Interactive.Mass

@[expose] public section

namespace Zkc.Formal.Interactive

/-- An outcome of a finite experiment and its nonnegative rational weight. -/
structure Weighted (α : Type) where
  value : α
  weight : Mass
  nonnegative : 0 ≤ weight

namespace Weighted

def total {α : Type} (payoff : α → Mass) : List (Weighted α) → Mass
  | [] => 0
  | ticket :: rest => ticket.weight * payoff ticket.value + total payoff rest

theorem total_add {α : Type} (f g : α → Mass) (tickets : List (Weighted α)) :
    total (fun a => f a + g a) tickets = total f tickets + total g tickets := by
  induction tickets with
  | nil => simp [total, Mass.add_zero]
  | cons t rest ih =>
    simp only [total, Mass.mul_add, ih, Mass.add_assoc, Mass.add_left_comm]

theorem total_scale {α : Type} (f : α → Mass) (c : Mass) (tickets : List (Weighted α)) :
    total (fun a => f a * c) tickets = total f tickets * c := by
  induction tickets with
  | nil => simp [total]
  | cons t rest ih => simp only [total, ih, Mass.add_mul, Mass.mul_assoc]

/-- Zero-weight replies impose no obligation on the continuation. -/
theorem total_mono {α : Type} {f g : α → Mass} (tickets : List (Weighted α))
    (le : ∀ t ∈ tickets, 0 < t.weight → f t.value ≤ g t.value) :
    total f tickets ≤ total g tickets := by
  induction tickets with
  | nil => exact Mass.le_refl
  | cons t rest ih =>
    have restLe := ih (fun u hu => le u (List.mem_cons_of_mem _ hu))
    have headLe : t.weight * f t.value ≤ t.weight * g t.value := by
      by_cases positive : 0 < t.weight
      · exact Mass.mul_le_mul_of_nonneg_left (le t (by simp) positive) t.nonnegative
      · have zero : t.weight = 0 := Mass.eq_zero_of_not_pos positive
        simp [zero]
    change _ + total f rest ≤ _ + total g rest
    exact Mass.add_le_add headLe restLe

end Weighted

/-- Missing mass is the probability that the service supplies no reply. -/
structure FiniteLaw (α : Type) where
  tickets : List (Weighted α)
  mass_le_one : Weighted.total (fun _ => 1) tickets ≤ 1

namespace FiniteLaw

def expect {α : Type} (d : FiniteLaw α) (f : α → Mass) : Mass := Weighted.total f d.tickets

theorem expect_add {α : Type} (d : FiniteLaw α) (f g : α → Mass) :
    d.expect (fun a => f a + g a) = d.expect f + d.expect g :=
  Weighted.total_add f g d.tickets

theorem expect_scale {α : Type} (d : FiniteLaw α) (f : α → Mass) (c : Mass) :
    d.expect (fun a => f a * c) = d.expect f * c :=
  Weighted.total_scale f c d.tickets

def Supports {α : Type} (d : FiniteLaw α) (a : α) : Prop :=
  ∃ t ∈ d.tickets, 0 < t.weight ∧ t.value = a

theorem mono {α : Type} (d : FiniteLaw α) {f g : α → Mass}
    (le : ∀ a, d.Supports a → f a ≤ g a) : d.expect f ≤ d.expect g :=
  Weighted.total_mono d.tickets fun t member pos => le t.value ⟨t, member, pos, rfl⟩

theorem constant_le {α : Type} (d : FiniteLaw α) {c : Mass} (hc : 0 ≤ c) :
    d.expect (fun _ => c) ≤ c := by
  have eq := Weighted.total_scale (fun _ : α => 1) c d.tickets
  have le := Mass.mul_le_mul_of_nonneg_right d.mass_le_one hc
  simp only [Mass.one_mul] at eq le
  rw [expect, eq]
  exact le

def certain {α : Type} (a : α) : FiniteLaw α :=
  ⟨[⟨a, 1, by decide⟩], by simp [Weighted.total]⟩

end FiniteLaw
end Zkc.Formal.Interactive

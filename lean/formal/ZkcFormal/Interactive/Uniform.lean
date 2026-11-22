module

public import ZkcFormal.Interactive.FiniteLaw

@[expose] public section

namespace ZkcFormal.Interactive.FiniteLaw

variable {α : Type}

def ticketsAt (xs : List α) (w : Mass) (hw : 0 ≤ w) : List (Weighted α) :=
  xs.map fun x => ⟨x, w, hw⟩

theorem count_tickets (xs : List α) (w : Mass) (hw : 0 ≤ w) (p : α → Bool) :
    Weighted.total (fun a => if p a then 1 else 0) (ticketsAt xs w hw) =
      (xs.countP p : Mass) * w := by
  induction xs with
  | nil => simp [ticketsAt, Weighted.total]
  | cons a xs ih =>
    rw [List.countP_cons]
    change w * (if p a then 1 else 0) + Weighted.total _ (ticketsAt xs w hw) = _
    rw [ih]
    cases p a <;> simp [Mass.natCast_add, Mass.add_mul, Mass.add_comm]

/-- Sample a position uniformly in a nonempty list. Repeated values retain their
multiplicity. A finite field service supplies a list enumerating every field element once. -/
def uniform (xs : List α) (positive : 0 < xs.length) : FiniteLaw α :=
  let w := (xs.length : Mass)⁻¹
  let hw : 0 ≤ w := Mass.zero_le _
  ⟨ticketsAt xs w hw, by
    have total := count_tickets xs w hw (fun _ => true)
    simp only [ite_true, List.countP_true] at total
    rw [total, Mass.mul_inv_cancel _ (Mass.ne_of_gt (Mass.natCast_pos.mpr positive))]
    exact Mass.le_refl⟩

theorem uniform_event (xs : List α) (positive : 0 < xs.length) (p : α → Bool) :
    (uniform xs positive).expect (fun a => if p a then 1 else 0) =
      (xs.countP p : Mass) / (xs.length : Mass) := by
  simpa only [expect, uniform, Mass.div_def] using count_tickets xs
    (xs.length : Mass)⁻¹ (Mass.zero_le _) p

end ZkcFormal.Interactive.FiniteLaw

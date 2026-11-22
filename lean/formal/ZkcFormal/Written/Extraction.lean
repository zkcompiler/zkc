module

public import Std.WP
public import Std.Tactic

@[expose] public section
set_option autoImplicit false
set_option experimental.vcgen true

namespace ZkcFormal.Written
open Std.WP

/-- The suffix of one execution of a three-message protocol. The shared prefix is supplied once. -/
structure Branch (Challenge : Type) (Suffix : Type := Challenge) where
  challenge : Challenge
  suffix : Suffix
  deriving DecidableEq

/-- The extractor must actually return a witness for each accepting fork. -/
def SpecialSoundness {Statement History Challenge Suffix Witness : Type}
    (accepts : Statement → History → Branch Challenge Suffix → Prop)
    (relation : Statement → Witness → Prop)
    (returns : Statement → History → Branch Challenge Suffix → Branch Challenge Suffix → Witness → Prop) : Prop :=
  ∀ s history left right, accepts s history left → accepts s history right →
    left.challenge ≠ right.challenge → ∃ w, returns s history left right w ∧ relation s w

/-- Value-level interpretations used by the compiled mathematical declarations. -/
structure Operations (F G : Type) where
  zero : F
  sub : F → F → F
  mul : F → F → F
  inv : F → F
  add : G → G → G
  scale : G → F → G

/-- Elementary field and additive group action laws used in the two-equation argument. -/
structure ActionLaws {F G : Type} (ops : Operations F G) where
  one : F
  difference : G → G → G
  sub_zero : ∀ a b, ops.sub a b = ops.zero ↔ a = b
  cancel_left : ∀ a x y, difference (ops.add a x) (ops.add a y) = difference x y
  scale_sub : ∀ p x y, difference (ops.scale p x) (ops.scale p y) = ops.scale p (ops.sub x y)
  scale_mul : ∀ p x y, ops.scale (ops.scale p x) y = ops.scale p (ops.mul x y)
  scale_one : ∀ p, ops.scale p one = p
  mul_inv : ∀ x, x ≠ ops.zero → ops.mul x (ops.inv x) = one

variable {F G : Type} (ops : Operations F G)

/-- Subtract the two verifier equations and act on both sides by the inverse challenge gap. -/
theorem extract_difference (laws : ActionLaws ops) {g u a : G} {l r : Branch F}
    (first : ops.scale g l.suffix = ops.add a (ops.scale u l.challenge))
    (second : ops.scale g r.suffix = ops.add a (ops.scale u r.challenge))
    (apart : l.challenge ≠ r.challenge) :
    u = ops.scale g (ops.mul (ops.sub l.suffix r.suffix) (ops.inv (ops.sub l.challenge r.challenge))) := by
  have gap := fun h => apart ((laws.sub_zero _ _).mp h)
  have eqs : laws.difference (ops.scale g l.suffix) (ops.scale g r.suffix) =
      laws.difference (ops.add a (ops.scale u l.challenge)) (ops.add a (ops.scale u r.challenge)) := by rw [first, second]
  rw [laws.cancel_left, laws.scale_sub, laws.scale_sub] at eqs
  have scaled := congrArg (fun p => ops.scale p (ops.inv (ops.sub l.challenge r.challenge))) eqs
  rw [laws.scale_mul, laws.scale_mul, laws.mul_inv _ gap, laws.scale_one] at scaled
  exact scaled.symm

/-- A source guard or an undefined division aborts the extractor. -/
def require (test : Bool) : Option Unit := if test then some () else none

def divide [DecidableEq F] (x y : F) : Option F :=
  if y = ops.zero then none else some (ops.mul x (ops.inv y))

theorem require_spec (test : Bool) (Q : Unit → Prop) (E : Unit → Prop) :
    Triple (require test) (if test then Q () else E ()) Q E := by
  cases test <;> exact ⟨id⟩

theorem divide_spec [DecidableEq F] (x y : F) (Q : F → Prop) (E : Unit → Prop) :
    Triple (divide ops x y) (if y = ops.zero then E () else Q (ops.mul x (ops.inv y))) Q E := by
  unfold divide
  split <;> exact ⟨id⟩

/-- On a required successful return, the guard and the domain of division become explicit
verification conditions. The continuation receives its value directly. -/
theorem require_success (test : Bool) (Q : Unit → Prop) (E : Unit → Prop) (pass : test = true) :
    Triple (require test) (Q ()) Q E := by subst test; exact ⟨id⟩

theorem divide_success [DecidableEq F] (x y : F) (Q : F → Prop) (E : Unit → Prop) (domain : y ≠ ops.zero) :
    Triple (divide ops x y) (Q (ops.mul x (ops.inv y))) Q E := by
  simpa only [ite_eq_right domain] using divide_spec ops x y Q E

attribute [spec] require_success divide_success

/-- Turning a total-correctness VC into the successful return required by the written clause. -/
theorem returned_of_triple {W : Type} {prog : Option W} {Q : W → Prop}
    (h : Triple prog True Q (fun _ => False)) : ∃ w, prog = some w ∧ Q w := by
  cases prog with
  | none => exact False.elim (h.1 trivial)
  | some w => exact ⟨w, rfl, h.1 trivial⟩

/-- A specification of both outcomes classifies the successful transcripts of a verifier. -/
theorem accepts_of_triple {check : Option Unit} {P : Prop}
    (h : Triple check True (fun _ => P) (fun _ => ¬P)) : check = some () ↔ P := by
  cases check with
  | none => simpa using (show ¬ P from h.1 trivial)
  | some u => cases u; simpa using (show P from h.1 trivial)

end ZkcFormal.Written

import Zkc.Compiler.InputBinding
import Zkc.Compiler.Arithmetic.Horner
import Mathlib.Algebra.Ring.Nat

namespace Tests.InputBinding

open PIR Zkc.Source Zkc.Source.Arithmetic Zkc.Compiler

def interface : Signature := ⟨Empty, Empty.elim⟩
def handler : Handler interface Nat Unit := fun op => nomatch op
abbrev model := Arithmetic.Horner.model (fun n : Nat => (Proc.done n : Proc interface Nat)) handler
abbrev context : List Ty := [.scalar, .scalar]

def program : Program language context .scalar :=
  .letOp .add (.cons .here (.cons (.there .here) .nil)) (.ret .here)

def binding : Refinement.InputBinding (Refinement.exact model context .scalar)
    (fun _ state => state < 8) where
  bind env state := if state < 8 then some (env, state) else none
  covered env state allowed := ⟨(env, state), if_pos allowed⟩
  valid env state selected allowed chosen := by
    rw [if_pos allowed] at chosen
    cases Option.some.inj chosen
    exact ⟨rfl, rfl⟩

def values : Values (Value Nat) context := .cons 3 (.cons 4 .nil)

theorem selected_execution :
    ∃ selected, binding.bind values.get 0 = some selected ∧
      Execution.Relates Eq (fun a (_ : Nat) b (_ : Nat) => a = b)
        (fun e : Unit => [e]) (fun e => [e])
        (model.runSource program values.get 0)
        (model.runPlan (lower program) selected.1 selected.2) :=
  binding.realizes (Refinement.direct model program) values.get 0 (by decide)

theorem actual_plan_result :
    model.runPlan (lower program) values.get 0 = ⟨.returned 7, 0, []⟩ := rfl

theorem outside_advertised_profile : binding.bind values.get 8 = none := rfl

def emptyRelation : Refinement model model context context .scalar .scalar :=
  { Refinement.exact model context .scalar with initial := fun _ _ _ _ => False }

theorem vacuous_refinement : emptyRelation.Holds program (lower program) :=
  fun _ _ _ _ impossible => False.elim impossible

theorem vacuous_relation_cannot_cover :
    ¬ Nonempty (Refinement.InputBinding emptyRelation (fun _ _ => True)) := by
  rintro ⟨bad⟩
  obtain ⟨selected, chosen⟩ := bad.covered values.get 0 trivial
  exact bad.valid values.get 0 selected trivial chosen

/-- Source coverage and pairwise equivalence do not constrain extra target
inputs. Exporting target acceptance needs full-domain adequacy or admission
that excludes those inputs with a valid source correspondence. -/
theorem forward_coverage_does_not_cover_target_acceptance :
    (∀ _ : Unit, ∃ target : Bool, target = false) ∧
    (∀ (_ : Unit) (target : Bool), target = false → (False ↔ target = true)) ∧
    (∃ target : Bool, target = true) ∧ ¬ (∃ _ : Unit, False) := by
  refine ⟨fun _ => ⟨false, rfl⟩, ?_, ⟨true, rfl⟩, fun ⟨_, h⟩ => h⟩
  intro _ target eqv
  subst target
  simp

end Tests.InputBinding

import Zkc.Semantics.Interaction

set_option autoImplicit false

namespace Tests.Interaction
open PIR

theorem missing_input_refused : requireInput (none : Option Nat) = .stopped .refused := rfl
theorem zero_is_present : requireInput (some 0) = .returned 0 := rfl

/- Minimal hostile-input control: interface conformance cannot imply honesty. -/
namespace Controls
def bits : Signature := ⟨Unit, fun _ => Bool⟩
def bitProtocol : Interaction bits :=
  ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
def echo : Proc bits Bool := .call () Proc.done
def rejectTrue : Proc bits Bool := .call () (fun b =>
  match (show Bool from b) with
  | true => .halt .reject
  | false => .done false)
theorem every_bit_permitted : Conforms bitProtocol echo () := ⟨trivial, fun _ => trivial⟩
theorem hostile_branch_permitted : Conforms bitProtocol rejectTrue () := by
  refine ⟨trivial, ?_⟩
  intro b
  cases b <;> trivial
end Controls


/-- Conformance admits the hostile reply; it cannot establish a false-only reply policy. -/
theorem conformance_does_not_force_false :
    Conforms Controls.bitProtocol Controls.echo () ∧
    (Controls.echo.run (E := Unit) (fun _ state => ⟨.returned true, state, []⟩) ()).outcome ≠
      .returned false := by
  exact ⟨Controls.every_bit_permitted, by decide⟩

end Tests.Interaction

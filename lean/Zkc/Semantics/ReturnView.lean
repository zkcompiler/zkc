module

public import Zkc.Semantics.Execution

@[expose] public section

/-! Changing the presentation of a complete return value leaves the process
unchanged when encoding restores every value. Effects and stops are retained. -/

set_option autoImplicit false
namespace PIR.Process

/-- A reversible return view preserves the complete process, including every
reply continuation and stopped branch. Only the returned value is decoded. -/
theorem restore_return {I : Signature} {A B : Type}
    (encode : B → A) (decode : A → B)
    (roundtrip : ∀ value, encode (decode value) = value) (process : Process I A) :
    process = (process.bind fun value => .done (decode value)).bind
      (fun value => .done (encode value)) := by
  rw [bind_assoc]
  simp only [bind, roundtrip, bind_done]

end PIR.Process

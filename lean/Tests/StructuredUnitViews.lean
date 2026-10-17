import Zkc.Source.Structured.UnitViews
import ZkcExamples.Structured.ServiceOrderViews

/-! Controls for generated unit views and kernel-only equations. Every
admitted subject is a positive control of `structured_views`; these cases show
that `kernel_rfl` refuses false or open equations, that a stale body cannot
satisfy a generated phase equation, and that inconsistent entry lists are
refused before any declaration is emitted. -/
set_option autoImplicit false
namespace Tests.StructuredUnitViews
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured ServiceOrderBodies

/-- A false closed equation is refused by the kernel, not assumed. -/
example : (2 : Nat) + 2 ≠ 5 := by
  fail_if_success have : (2 : Nat) + 2 = 5 := by kernel_rfl
  decide

/-- An equation over local variables is refused; the tactic only closes
closed goals. -/
example (value : Nat) : value + 0 = value := by
  fail_if_success kernel_rfl
  rfl

/-- The service-order draw body with its two results swapped: the same
signature, a different tree. -/
def staleDrawBody : Region protocolDialect serviceTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s2")
    (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5_0") .nil .nil <|
  .letOp (.exchange fieldType 1 0 "s5_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict fieldType [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

/-- The indices returned at the end of a straight-line raw tree. -/
def returned : RawRegion Ty ProtocolOp → List Nat
  | .ret indices => indices
  | .stop _ => []
  | .letOp _ _ _ _ next => returned next
  | .bind _ _ next => returned next

/-- The generated phase equation pins the authored body: the phase it states
cannot also return the checked tree of a stale body. -/
theorem stale_draw_refused {result : Except String CheckedProtocol}
    (phase : result = .ok ServiceOrderViews.drawDefinition) :
    result ≠ .ok (CheckedProtocol.ofBody drawSignature staleDrawBody) := by
  rw [phase]
  intro same
  have returnedEq := congrArg (fun result : Except String CheckedProtocol =>
    result.toOption.map fun definition => returned definition.raw) same
  revert returnedEq
  decide +kernel

/-- The premise is the generated draw phase of the admitted unit. -/
example := stale_draw_refused ServiceOrderViews.draw_checked

/--
error: structured_views: no authored protocol body for retained declaration s6h73616d706c653h52756e
-/
#guard_msgs in
structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw]

/--
error: structured_views: authored protocol extra is not retained by the snapshot
-/
#guard_msgs in
structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw, run, extra := (drawSignature, drawBody)]

/--
error: structured_views: two generated declarations would be named headers_checked; rename an authored entry
-/
#guard_msgs in
structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw, headers := run]

end Tests.StructuredUnitViews

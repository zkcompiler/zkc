import Zkc.Source.Structured.UnitViews
import ZkcExamples.Structured.ServiceOrderViews

/-! Controls for generated unit views and kernel-only equations. Every
admitted subject is a positive control of `structured_views`; these cases show
that `kernel_rfl` refuses false equations, also under binders, that the
generator refuses a stale body at the phase equation it fails (leaving no
partial unit), and
that inconsistent entry lists are refused before any declaration is emitted. -/
set_option autoImplicit false
namespace Tests.StructuredUnitViews
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured ServiceOrderBodies

/-- A false closed equation is refused by the kernel, not assumed. -/
example : (2 : Nat) + 2 ≠ 5 := by
  fail_if_success have : (2 : Nat) + 2 = 5 := by kernel_rfl
  decide

/-- An equation over local variables is checked under its binders, for every
value at once; a false one is refused. -/
example (value : Nat) : value + 0 = value := by
  kernel_rfl

example (value : Nat) : value + 1 ≠ value := by
  fail_if_success have : value + 1 = value := by kernel_rfl
  omega

/-- Section variables and instances are reverted too: an equation that holds
only by a ring law, not by reduction, is refused. -/
example {F : Type} [CommRing F] (x : F) : x + 0 = x := by
  fail_if_success kernel_rfl
  simp

example : ∀ value : Nat, value + 0 = value := by
  kernel_rfl

/-- The service-order draw body with the operands of its first addition
swapped: the same signature, scopes and availability, a different tree. -/
def staleDrawBody : Region protocolDialect serviceTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s2")
    (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s5_0") .nil .nil <|
  .letOp (.exchange fieldType 1 0 "s5_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict fieldType [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

/-- The draw body with its two results swapped, which moves a value to a role
that cannot see it. -/
def unavailableDrawBody : Region protocolDialect serviceTypes resultTypes :=
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

/-- The operand lists of a straight-line raw tree, in order. -/
def operands : RawRegion Ty ProtocolOp → List (List Nat)
  | .ret _ => []
  | .stop _ => []
  | .letOp _ arguments _ _ next => arguments :: operands next
  | .bind _ _ next => operands next

/-- The generated phase equation pins the authored body: the phase it states
cannot also return the checked tree of a stale body. -/
theorem stale_draw_refused {result : Except String CheckedProtocol}
    (phase : result = .ok ServiceOrderViews.drawDefinition) :
    result ≠ .ok (CheckedProtocol.ofBody drawSignature staleDrawBody) := by
  rw [phase]
  intro same
  have operandsEq := congrArg (fun result : Except String CheckedProtocol =>
    result.toOption.map fun definition => operands definition.raw) same
  revert operandsEq
  decide +kernel

/-- The premise is the generated draw phase of the admitted unit. -/
example := stale_draw_refused ServiceOrderViews.draw_checked

/-! The generator itself refuses a stale body. With the swapped operands,
matching, ordering, the literal unit and the earlier phases are accepted and
the kernel rejects the draw phase equation; the command then stops and leaves
no partial unit. -/

/--
error: structured_views: the authored bodies do not satisfy the admission phase draw_checked
-/
#guard_msgs (substring := true) in
structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw := (drawSignature, staleDrawBody), run]

/-! With the swapped results the literal unit's stored availability obligation
already fails, before any phase equation is stated. -/

/--
error: structured_views: generated declaration unit was not accepted for the authored bodies
-/
#guard_msgs (substring := true) in
structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw := (drawSignature, unavailableDrawBody), run]

-- Neither refused command left a declaration behind.
run_cmd do
  for name in [`Tests.StructuredUnitViews.drawDefinition, `Tests.StructuredUnitViews.unit,
      `Tests.StructuredUnitViews.headers_checked, `Tests.StructuredUnitViews.draw_checked] do
    if (← Lean.getEnv).contains name then throwError "partial declaration {name} remains"

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

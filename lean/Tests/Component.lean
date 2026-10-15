import Zkc.Source.Structured.Table
import Zkc.Source.Component

/-! Value/interface polymorphism and optional named closure composition on the
existing Region. No arithmetic assignment, source carrier or recursion fuel. -/
set_option autoImplicit false
namespace Tests.Component
open Zkc.Source Zkc.Source.Structured

private def first (ty : Ty) : Region dialect [ty, ty] [ty] :=
  .ret (.cons .here .nil)

private def relay (ty : Ty) : Region dialect [ty, ty] [ty] :=
  .letOp (.invoke ⟨"first", [ty, ty], [ty]⟩)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

private abbrev calls {Value : Ty → Type} {interface : PIR.Signature}
    (table : HelperTable Value interface) : RegionMeaning dialect interface where
  Value := Value
  operation
    | .invoke helper, args, .nil => invoke table helper args
    | _, _, _ => .halt .refused

private def componentCalls {Value : Ty → Type} {interface : PIR.Signature}
    (closed : HelperTable Value interface) (components : HelperTable (Component Value) interface) :
    ComponentOperations (calls closed)
  | .invoke helper, args, .nil => invoke components helper args
  | op, args, bodies => strictComponent (calls closed) op args bodies

private def tables (Value : Ty → Type) (interface : PIR.Signature) (ty : Ty) :
    HelperTable (Component Value) interface :=
  let firstEntry : HelperDefinition (Component Value) interface :=
    ⟨⟨"first", [ty, ty], [ty]⟩, fun args =>
      (first ty).component (calls ([] : HelperTable Value interface))
        (componentCalls [] []) args.get⟩
  let relayEntry : HelperDefinition (Component Value) interface :=
    ⟨⟨"relay", [ty, ty], [ty]⟩, fun args =>
      (relay ty).component (calls ([] : HelperTable Value interface))
        (componentCalls [] [firstEntry]) args.get⟩
  [relayEntry, firstEntry]

/-- One equation without choosing a scalar or effect implementation. The named
relay captures the earlier closure, not its syntax. -/
theorem named_first {Value : Ty → Type} (interface : PIR.Signature) (ty : Ty)
    (x y : Option (Value ty)) :
    invoke (tables Value interface ty) ⟨"relay", [ty, ty], [ty]⟩ (.cons x (.cons y .nil)) =
      .done (.cons x .nil) := by
  dsimp only [tables]
  rw [invoke_cons_same]
  dsimp only [relay, Region.component, Regions.denote, componentCalls, Operands.eval, Values.get]
  rw [invoke_cons_same]
  rfl

/-- The generic lookup still checks the whole signature after finding a name. -/
theorem exact_signature {Value : Ty → Type} (interface : PIR.Signature) (ty : Ty) :
    invoke (tables Value interface ty) ⟨"first", [], []⟩ .nil = .halt .refused := by
  simp [tables, invoke]

end Tests.Component

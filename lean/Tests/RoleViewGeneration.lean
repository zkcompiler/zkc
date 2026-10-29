module

public import Tests.Generated.CounterRoleViews
public import Tests.Generated.NestedRoleViews

/-! Controls for source-derived role views. The nested dependency diamond has
multiple applications, same-ABI declarations, role substitutions, and a repeat
inside a callback. The counter has unrelated index/boolean state. -/
open Zkc.Source Zkc.Source.Structured
open Tests.Generated

-- ABI-only matching would select the wrong same-shaped callee in this root.
example : NestedRoleViews.Protocol3.role0Signature.names = true := by kernel_rfl
example : NestedRoleViews.Protocol3.role1Signature.names = true := by kernel_rfl
example : NestedRoleViews.Protocol3.role0Form.calleeCalls.length = 2 := by kernel_rfl
example : NestedRoleViews.Protocol3.role0Callback1Form.calleeCalls.length = 2 := by kernel_rfl

-- A nested repeat or application cannot use context-free callback transport.
example : NestedRoleViews.Protocol3.callback0Body.erase.operations.all
    OccurrencePresentation.contextFree = false := by kernel_rfl
example : NestedRoleViews.Protocol3.callback1Body.erase.operations.all
    OccurrencePresentation.contextFree = false := by kernel_rfl

-- All these views authorize complete bodies, not a prefix or a selected slot.
example : NestedRoleViews.Protocol3.role0Form.CallsMatch :=
  NestedRoleViews.Protocol3.role0_calls
example : CounterRoleViews.Protocol0.role0Form.CallsMatch :=
  CounterRoleViews.Protocol0.role0_calls

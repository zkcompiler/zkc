module

public import ZkcTools.StructuredSource.SourceCalls
public meta import ZkcTools.StructuredSource.SourceCalls

@[expose] public section
set_option autoImplicit false
namespace Tests.SourceCalls
open Zkc.Source Zkc.Source.Structured

def signature : ProtocolSignature := ⟨"child", ["Verifier"], [.index, .index], [.index], [[0], [0]], [[0]]⟩

def body : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.protocolApply signature [0] "actual")
    (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))

protocol_call selected from body to signature
example : selected.site = "actual" := rfl
example : selected.roles = [0] := rfl
example : selected.operands.indices = [1, 0] := rfl
example : selected_occurrence.position = [] := rfl
example : selected_occurrence.callSite = selected := selected_selected
example : selected_occurrence ∈ callInventory body := callInventory_complete _
example : selected.operands.indices ≠ [0, 1] := by decide

def nested : Region protocolDialect [.index, .index] [.index] :=
  .bind body (.letOp (.protocolApply signature [0] "other")
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
example : selectCall nested signature = none := rfl

/-- error: protocol-call-selection: expected one matching typed occurrence; select an explicit path when ambiguous -/
#guard_msgs in
protocol_call ambiguous from nested to signature

protocol_call first from nested to signature at [0]
protocol_call second from nested to signature at [1]
example : first.site = "actual" := rfl
example : second.site = "other" := rfl
example : first_occurrence.position ≠ second_occurrence.position := by decide

example : selectCall body { signature with roles := ["Other"] } = none := rfl
example : selectCall body { signature with inputs := [.index] } = none := rfl
example : selectCall body signature (some [1]) = none := rfl

/-- error: protocol-call-selection: expected one matching typed occurrence; select an explicit path when ambiguous -/
#guard_msgs in
protocol_call missing from body to { signature with roles := ["Other"] }

/-- error: protocol-call-selection: expected one matching typed occurrence; select an explicit path when ambiguous -/
#guard_msgs in
protocol_call wrongPath from body to signature at [1]

def repeated : Region protocolDialect [.index, .index, .index] [.index] :=
  .letOp (.repeat ⟨[.index], [.index], [0], [[0]], 4⟩ "loop")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    (.cons (.letOp (.protocolApply signature [0] "inside")
      (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil
      (.ret (.cons .here .nil))) .nil)
    (.ret (.cons .here .nil))

protocol_call child from repeated to signature
example : child.site = "inside" := rfl
example : child.operands.indices = [1, 2] := rfl
example : child_occurrence.position = [0] := rfl
example : child_occurrence.repeats = [([], 4)] := rfl

/-- Lexical presence after a stopped prefix is not claimed to be reached. -/
def unreachable : Region protocolDialect [.index, .index] [.index] :=
  .bind (.stop (out := []) .abort) body
protocol_call afterStop from unreachable to signature
example : afterStop.site = "actual" := rfl

end Tests.SourceCalls

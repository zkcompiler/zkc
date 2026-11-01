module

public import ZkcTools.StructuredSource.SourceCalls
public meta import ZkcTools.StructuredSource.SourceCalls

@[expose] public section
set_option autoImplicit false
namespace Tests.SourceCalls
open Zkc.Source Zkc.Source.Structured

open Lean Elab Command in
private meta def expectCallFailure (command : String) (expected : List String) : CommandElabM Unit := do
  let .ok stx := Parser.runParserCategory (← getEnv) `command command
    | throwError "invalid protocol_call test syntax: {command}"
  let `(protocol_call $name:ident from $_:term to $_:term $[at $_:term]?) := stx
    | throwError "expected a protocol_call test"
  let namespaceName ← getCurrNamespace
  let before ← getEnv
  let asynchronous := Elab.async.get (← getOptions)
  let failure ← try
    ZkcTools.StructuredSource.SourceCalls.elabProtocolCall stx
    pure none
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    pure (some (← error.toMessageData.toString))
  let some message := failure | throwError "protocol_call unexpectedly succeeded: {command}"
  for fragment in expected do
    unless message.contains fragment do
      throwError "expected diagnostic fragment {fragment}, got {message}"
  for suffix in ["", "_occurrence", "_selected", "_signature"] do
    let generated := namespaceName ++ name.getId.appendAfter suffix
    unless (← getEnv).contains generated == before.contains generated do
      throwError "failed protocol_call changed declaration {generated}"
  unless Elab.async.get (← getOptions) == asynchronous do
    throwError "failed protocol_call changed the caller's options"

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
example : selected_occurrence = CallOccurrence.here signature [0] "actual"
    (.cons (.there .here) (.cons .here .nil)) (.ret (.cons .here .nil)) := rfl
example : selectCall body signature = some selected_occurrence := rfl

protocol_call rootPath from body to signature at []
example : rootPath_occurrence = selected_occurrence := rfl

def nested : Region protocolDialect [.index, .index] [.index] :=
  .bind body (.letOp (.protocolApply signature [0] "other")
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))
example : selectCall nested signature = none := rfl

run_cmd do
  expectCallFailure "protocol_call ambiguous from nested to signature"
    ["protocol-call-selection:", "2 matching typed occurrences", "add 'at <path>'",
      "at [0]: site \"actual\", role map [0]", "at [1]: site \"other\", role map [0]"]

protocol_call first from nested to signature at [0]
protocol_call second from nested to signature at [1]
example : first.site = "actual" := rfl
example : second.site = "other" := rfl
example : first_occurrence.position ≠ second_occurrence.position := by decide
example : selectCall nested signature (some [0]) = some first_occurrence := rfl
example : selectCall nested signature (some [1]) = some second_occurrence := rfl

-- The failed command's name is reusable, and reducible path expressions work.
protocol_call ambiguous from nested to signature at [0 + 0]
example : ambiguous_occurrence = first_occurrence := rfl

example : selectCall body { signature with roles := ["Other"] } = none := rfl
example : selectCall body { signature with inputs := [.index] } = none := rfl
example : selectCall body signature (some [1]) = none := rfl

run_cmd do
  expectCallFailure
    "protocol_call missing from body to { signature with roles := [\"Other\"] }"
    ["protocol-call-selection:", "no matching signature", "full signature"]

run_cmd do
  expectCallFailure "protocol_call wrongPath from body to signature at [1]"
    ["protocol-call-selection:", "no matching typed occurrence at [1]", "choose a candidate path",
      "at []: site \"actual\", role map [0]"]

-- A path miss must retain both signature matches for the diagnostic.
run_cmd do
  expectCallFailure "protocol_call wrongNestedPath from nested to signature at [2]"
    ["protocol-call-selection:", "no matching typed occurrence at [2]",
      "at [0]: site \"actual\", role map [0]", "at [1]: site \"other\", role map [0]"]

opaque hiddenPath : List Nat := [0]

run_cmd do
  for command in
      ["protocol_call wrongPathType from nested to signature at (0 : Nat)",
       "protocol_call unknownPath from nested to signature at unknownCallPath",
       "protocol_call opaquePath from nested to signature at hiddenPath",
       "protocol_call pathHole from body to signature at _",
       "protocol_call elementHole from nested to signature at [_]",
       "protocol_call tailHole from nested to signature at (0 :: _)"] do
    expectCallFailure command
      ["protocol-call-selection:", "malformed or unresolved path", "closed List Nat"]

-- Fail after the header, occurrence and selected equation have been installed.
def rollback_signature : Nat := 7
run_cmd do
  expectCallFailure "protocol_call rollback from body to signature"
    ["protocol-call-generation"]
example : rollback_signature = 7 := rfl

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
example : selectCall repeated signature (some [0]) = some child_occurrence := rfl

def nestedRepeat : Region protocolDialect [.index, .index, .index] [.index] :=
  .letOp (.repeat ⟨[.index], [.index], [0], [[0]], 2⟩ "outer")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    (.cons repeated .nil) (.ret (.cons .here .nil))

protocol_call nestedChild from nestedRepeat to signature at [0, 0]
example : nestedChild.site = "inside" := rfl
example : nestedChild.roles = [0] := rfl
example : nestedChild.operands.indices = [1, 2] := rfl
example : nestedChild_occurrence.position = [0, 0] := rfl
example : nestedChild_occurrence.repeats = [([], 2), ([0], 4)] := rfl
example : selectCall nestedRepeat signature (some [0, 0]) = some nestedChild_occurrence := rfl

run_cmd do
  expectCallFailure "protocol_call wrongRepeatPath from nestedRepeat to signature at [0]"
    ["protocol-call-selection:", "no matching typed occurrence at [0]",
      "at [0, 0]: site \"inside\", role map [0]"]

/-- Lexical presence after a stopped prefix is not claimed to be reached. -/
def unreachable : Region protocolDialect [.index, .index] [.index] :=
  .bind (.stop (out := []) .abort) body
protocol_call afterStop from unreachable to signature
example : afterStop.site = "actual" := rfl

end Tests.SourceCalls

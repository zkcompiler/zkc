import ZkcTools.ConstructionBindings.LibraryPlan
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

/-! Discovery controls cover actual repeated use, local role substitution,
nested repeats and refusal of a malformed dependency order. The plan confers
no semantic authority: source-template and root checks remain separate. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionLibraryPlan
open Zkc.Source Zkc.Source.Structured ZkcTools.ConstructionBindings.LibraryPlan

private def callee : ProtocolSignature := ⟨"component", ["A", "B"], [], [], [], []⟩
private def call (roles : List Nat) : RawRegion Ty ProtocolOp :=
  .letOp (.protocolApply callee roles "use") [] [] .nil (.ret [])
private def repeated (roles : List Nat) (body : RawRegion Ty ProtocolOp) : RawRegion Ty ProtocolOp :=
  .letOp (.repeat ⟨[], [], roles, [], 100⟩ "loop") [0] []
    (.cons [.index] [] body .nil) (.ret [])

-- A swap maps the caller's role zero to the callee's role one.
example : calls 0 3 (call [1,0]) = .ok [⟨callee, 1⟩] := by decide +kernel
example : calls 2 3 (call [1,0]) = .ok [] := by decide +kernel
example : (calls 0 2 (call [0,0])).isOk = false := by decide +kernel
example : (calls 0 2 (call [0,2])).isOk = false := by decide +kernel
example : (calls 0 2 (call [0])).isOk = false := by decide +kernel

-- Loop bounds are never unrolled. Only active roles need the nested callee.
example : calls 0 2 (repeated [0,1] (repeated [0] (call [1,0]))) =
    .ok [⟨callee, 1⟩] := by decide +kernel
example : calls 1 2 (repeated [0,1] (repeated [0] (call [1,0]))) = .ok [] := by decide +kernel

private def leaf (name : String) : CheckedProtocol where
  toProtocolSignature := { callee with name := name }
  raw := .ret []
  body := .ret .nil
  formed := rfl

private def wrapper (name dependency : String) : CheckedProtocol where
  toProtocolSignature := { callee with name := name }
  raw := .letOp (.protocolApply { callee with name := dependency } [1,0] "use")
    [] [] .nil (.ret [])
  body := .letOp (.protocolApply { callee with name := dependency } [1,0] "use")
    .nil .nil (.ret .nil)
  formed := rfl

-- Two substitutions compose through a transitive dependency. Table order,
-- exact role rosters and the body signature are not inferred from names alone.
example : discover [leaf "leaf", wrapper "middle" "leaf", wrapper "root" "middle"] 2 [0] =
    .ok [⟨0,0⟩,⟨1,1⟩] := by decide +kernel
example : (discover [{ leaf "leaf" with roles := ["B", "A"] }, wrapper "root" "leaf"]
    1 [0]).isOk = false := by decide +kernel
example : (discover [wrapper "cycle" "cycle"] 0 [0]).isOk = false := by decide +kernel

private abbrev small := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.payload
private abbrev two := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.payload

-- Both actual roots select one shared declaration per role, even when called twice.
example : forPayload small [0,1] = .ok [⟨0,0⟩,⟨0,1⟩] := by decide +kernel
example : forPayload two [1,0,1] = .ok [⟨0,0⟩,⟨0,1⟩] := by decide +kernel
example : forPayload two [1] = .ok [⟨0,1⟩] := by decide +kernel
example : forPayload two [] = .ok [] := by decide +kernel
example : (forPayload two [2]).isOk = false := by decide +kernel
example : (discover two.protocols.reverse 0 [1]).isOk = false := by decide +kernel
example : (discover two.protocols 100 [1]).isOk = false := by decide +kernel

end Tests.ConnectionLibraryPlan

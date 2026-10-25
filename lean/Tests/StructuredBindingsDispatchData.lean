module

public import Tests.StructuredBindingsGeneric

@[expose] public section

/-! A shared dependency diamond with role remapping, heterogeneous callee ABIs
and calls inside a bounded repeat. Admission orders declarations by dependency,
independently of their encounter order below. -/
namespace Tests.StructuredBindingsDispatchData
open Zkc.Source.Structured

def leaf : Function := { Tests.StructuredBindingsGeneric.root with
  name := "leaf", origin := some (.protocol ⟨"leaf", []⟩) }

def booleanLeaf : Function where
  name := "booleanLeaf"
  kind := .protocol
  visibility := .publicDef
  inputs := [.boolean]
  outputs := [.boolean]
  interface := some ⟨["Alice", "Bob"], [["Bob"]], [["Bob"]]⟩
  preconditions := []
  origin := some (.protocol ⟨"booleanLeaf", []⟩)
  body := .block [] (.ret [0])

def middle : Function := { leaf with
  name := "middle"
  origin := some (.protocol ⟨"middle", []⟩)
  body := .block [
    .instruction (.protocolApply "leaf" ["Bob", "Alice"]) [0, 1] [.index] [] "swapped",
    .instruction (.protocolApply "leaf" ["Alice", "Bob"]) [0, 2] [.index] [] "again"
  ] (.ret [0]) }

def root : Function := { leaf with
  name := "root"
  origin := some (.protocol ⟨"root", []⟩)
  inputs := [.index, .index, .boolean]
  interface := some ⟨["Alice", "Bob"],
    [["Alice", "Bob"], ["Alice", "Bob"], ["Alice", "Bob"]], [["Alice", "Bob"]]⟩
  body := .block [
    .instruction (.protocolApply "middle" ["Bob", "Alice"]) [0, 1] [.index] [] "nested",
    .instruction (.protocolApply "booleanLeaf" ["Alice", "Bob"]) [3] [.boolean] [] "private",
    .instruction (.protocolApply "leaf" ["Alice", "Bob"]) [2, 3] [.index] [] "shared",
    .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [3, 0] [.index]
      [.region [.index, .index] [.index]
        (.block [.instruction (.protocolApply "leaf" ["Bob", "Alice"]) [0, 1] [.index] [] "inside"]
          (.yield [0]))] "round"
  ] (.ret [0]) }

def snapshot : Snapshot := { Tests.StructuredBindingsGeneric.snapshot with
  entry := "root"
  definitions := [.function root, .function leaf, .function booleanLeaf, .function middle]
  contracts := [⟨"root", []⟩, ⟨"leaf", []⟩, ⟨"booleanLeaf", []⟩, ⟨"middle", []⟩] }

def program : Program := (check snapshot).toOption.get (by decide +kernel)

example : program.payload.protocols.map (·.name) = ["leaf", "booleanLeaf", "middle", "root"] := by
  kernel_rfl

/-- Cyclic source dependencies cannot be used to justify recursive view aliases. -/
def cyclicFunction : Function := { leaf with
  name := "counter"
  origin := some (.protocol ⟨"counter", []⟩)
  body := .block [.instruction (.protocolApply "counter" ["Alice", "Bob"]) [0, 1] [.index] [] "self"]
    (.ret [0]) }

def cyclic : Snapshot := { Tests.StructuredBindingsGeneric.snapshot with
  definitions := [.function cyclicFunction] }

example : (check cyclic).isOk = false := by decide +kernel

end Tests.StructuredBindingsDispatchData

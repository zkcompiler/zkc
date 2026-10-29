module

public import Tests.StructuredBindingsDispatchData

@[expose] public section

/-! Pure nested-repeat source fixture. Generated proofs import this data rather
than its printer, so changing rendering does not invalidate the source itself. -/
namespace Tests.StructuredNestedRoleData
open Zkc.Source.Structured

def root : Function := { Tests.StructuredBindingsDispatchData.root with
  body := .block [
    .instruction (.protocolApply "middle" ["Bob", "Alice"]) [0, 1] [.index] [] "first",
    .instruction (.protocolApply "middle" ["Alice", "Bob"]) [0, 2] [.index] [] "second",
    .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [2, 0] [.index]
      [.region [.index, .index] [.index] (.block [
        .instruction (.protocolApply "leaf" ["Bob", "Alice"]) [0, 1] [.index] [] "before",
        .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [1, 0] [.index]
          [.region [.index, .index] [.index] (.block [
            .instruction (.protocolApply "leaf" ["Alice", "Bob"]) [0, 1] [.index] [] "inside",
            .instruction (.protocolApply "leaf" ["Bob", "Alice"]) [1, 0] [.index] [] "again"
          ] (.yield [0]))] "inner"
      ] (.yield [0]))] "outer"
  ] (.ret [0]) }

def snapshot : Snapshot := { Tests.StructuredBindingsDispatchData.snapshot with
  definitions := [.function root, .function Tests.StructuredBindingsDispatchData.leaf,
    .function Tests.StructuredBindingsDispatchData.booleanLeaf,
    .function Tests.StructuredBindingsDispatchData.middle] }

def program : Program := (check snapshot).toOption.get (by decide +kernel)

end Tests.StructuredNestedRoleData

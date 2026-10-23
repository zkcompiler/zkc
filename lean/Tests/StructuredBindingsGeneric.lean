module

public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! A genuinely unrelated repeat with no helper library. It exercises the
empty default callback presentation, rather than an installed family rule. -/

namespace Tests.StructuredBindingsGeneric
open Zkc.Source.Structured

def root : Function where
  name := "counter"
  kind := .protocol
  visibility := .publicDef
  inputs := [.index, .index]
  outputs := [.index]
  interface := some ⟨["Alice", "Bob"], [["Alice", "Bob"], ["Alice", "Bob"]], [["Alice", "Bob"]]⟩
  preconditions := []
  origin := none
  body := .block [
    .instruction (.protocolRepeat 1 3 ["Alice", "Bob"] [["Alice", "Bob"]]) [0, 1] [.index]
      [.region [.index, .index] [.index] (.block [] (.yield [1]))] "round"
  ] (.ret [0])

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "counter"
  domains := []
  relations := []
  bindings := []
  definitions := [.function root]
  contracts := [⟨"counter", []⟩]
  catalogue := blsCatalogue

example : (check snapshot).isOk = true := by decide +kernel

def program : Program := (check snapshot).toOption.get (by decide +kernel)

example : program.payload.definitions = [] := by kernel_rfl
example : (Zkc.Source.Structured.Bindings.findRepeat "round"
    (program.payload.protocols.get ⟨0, by decide +kernel⟩).body).isSome = true := by kernel_rfl
example : Zkc.Source.Structured.Bindings.findRepeat "missing"
    (program.payload.protocols.get ⟨0, by decide +kernel⟩).body = none := by kernel_rfl
end Tests.StructuredBindingsGeneric

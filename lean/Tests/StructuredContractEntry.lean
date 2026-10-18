import Zkc.Source.Structured.ContractEntry

open Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredContractEntry
set_option smartUnfolding false

private def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
private def clause (name role : String) : ContractClause :=
  ⟨.target, name, ⟨"R", [⟨.input, 0, "P"⟩]⟩, none, some ⟨.output, 0, role⟩⟩
private def original (target : String) : Function :=
  ⟨"main", .protocol, .publicDef, [.boolean], [.boolean],
    some ⟨["P", "V"], [["P", "V"]], [["P", "V"]]⟩, [], none,
    .block [.instruction (.statement "R" ["P"] 0 (some target)) [0] [] [] ""] (.ret [0])⟩
private def snapshot (target : String) : Snapshot :=
  ⟨digest, "main", [], [⟨"R", .publicDef, "opaque", "key", "rev", [.boolean], [.boolean],
    ["statement"], none⟩], [], [.function (original target)],
    [⟨"main", [clause "left" "P", clause "right" "V"]⟩]⟩
private def body : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.statement "R" [.boolean] ["P"] 0) (.cons .here .nil) .nil (.ret (.cons .here .nil)))
private def checked : CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [.boolean], [.boolean], [[0, 1]], [[0, 1]]⟩,
    body.erase, body, body.elaborate_erase⟩
private def payload : UnitPayload :=
  ⟨[], [checked], ⟨0, by decide⟩, by decide +kernel, by decide +kernel,
    by rfl, by decide +kernel, by decide +kernel⟩
private def left : Imported (snapshot "left") := ⟨⟨snapshot "left", payload⟩, by rfl⟩
private def right : Imported (snapshot "right") := ⟨⟨snapshot "right", payload⟩, by rfl⟩
private def leftOwner : ContractBinding left := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def rightOwner : ContractBinding right := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def leftEntry : EntryContractBinding left :=
  ⟨leftOwner, rfl, original "left", List.mem_cons_self, rfl, rfl,
    ⟨0, by decide⟩, rfl, ["P"], 0, [0], "", rfl,
    ⟨.output, 0, "P"⟩, rfl, rfl, rfl⟩
private def rightEntry : EntryContractBinding right :=
  ⟨rightOwner, rfl, original "right", List.mem_cons_self, rfl, rfl,
    ⟨1, by decide⟩, rfl, ["P"], 0, [0], "", rfl,
    ⟨.output, 0, "V"⟩, rfl, rfl, rfl⟩

example : leftEntry.decision.role = "P" := rfl
example : rightEntry.decision.role = "V" := rfl
example : leftEntry.decision.port = rightEntry.decision.port := rfl
example : leftEntry.owner.protocol = rightEntry.owner.protocol := rfl
example : leftEntry.decision ≠ rightEntry.decision := by decide
example : leftEntry.owner.contract.owner = "main" := leftEntry.selected_name
example : True := by
  fail_if_success have wrong : (leftOwner.clause ⟨1, by decide⟩).decision = some leftEntry.decision := rfl
  fail_if_success have wrong : EntryContractBinding right := leftEntry
  trivial

#eval do
  if (check (snapshot "missing")).isOk then throw (IO.userError "unknown selected target admitted")
  match check (snapshot "missing") with
  | .error "structured-statement-contract" => IO.println "exact selected target refusal passed"
  | _ => throw (IO.userError "wrong selected-target diagnostic")

-- Generic structured admission permits multiple independently checked named
-- statements. That does not establish a unique selected Entry profile.
private def ambiguousOriginal : Function :=
  { original "left" with body := .block [
      .instruction (.statement "R" ["P"] 0 (some "left")) [0] [] [] "",
      .instruction (.statement "R" ["P"] 0 (some "right")) [0] [] [] ""] (.ret [0]) }
private def ambiguousSnapshot : Snapshot :=
  { snapshot "left" with definitions := [.function ambiguousOriginal] }
private def ambiguousBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.statement "R" [.boolean] ["P"] 0) (.cons .here .nil) .nil body)
private def ambiguousChecked : CheckedProtocol :=
  ⟨checked.signature, ambiguousBody.erase, ambiguousBody, ambiguousBody.elaborate_erase⟩
private def ambiguousPayload : UnitPayload :=
  ⟨[], [ambiguousChecked], ⟨0, by decide⟩, by decide +kernel, by decide +kernel,
    by rfl, by decide +kernel, by decide +kernel⟩
private def ambiguous : Imported ambiguousSnapshot := ⟨⟨ambiguousSnapshot, ambiguousPayload⟩, by rfl⟩

theorem ambiguous_no_entry : ¬ Nonempty (EntryContractBinding ambiguous) := by
  rintro ⟨binding⟩
  have member := binding.original_mem
  change Definition.function binding.original ∈ [Definition.function ambiguousOriginal] at member
  have original_eq := Definition.function.inj (List.mem_singleton.mp member)
  have count := binding.named_statement_count
  rw [original_eq] at count
  change (2 : Nat) = 1 at count
  contradiction

example : (check ambiguousSnapshot).isOk = true := rfl
example : (leftEntry.original.body.topLevelInstructions.filter Instruction.isNamedStatement).length = 1 :=
  leftEntry.named_statement_count

namespace Native

-- Actual original-PIR exports of sample::Left and sample::Right from
-- compiler/test/fixtures/structured-source/selected-targets.zkc. Rendered with
-- bridges/structured/snapshot.py after language-emit and protocol-structured.
-- Constructor data are checked below; exporting is not a correctness proof.
private def leftSnapshot : Snapshot where
  source := "sha256:77afe6adb4eabb6693364a71f6829d94ba11f0617a2830e9d9e019cb62cc3ed8"
  entry := "s6h73616d706c653h52756e"
  domains := []
  relations := [⟨"s6h73616d706c651h52", .publicDef, "zkc.language.formula/0", "s6h73616d706c651h52", "2a503e2d2037410a4dd256b9f29dfc9dc0bf2ad85e126cc58b5c183d9ec3f610", [.boolean], [.boolean], ["statement"], some ("zkf_a1f8c00beabfe1b0a1ecc4074476dfa38f42d4e883f20d3a29821f20ee2eace4")⟩]
  bindings := []
  definitions := [.function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.boolean], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"]], [["role00000000", "role00000001"]]⟩, [], none, (.block [.instruction (.statement "s6h73616d706c651h52" ["role00000000"] 0 (some ("left"))) [0] [] [] ""] (.ret [0]))⟩, .function ⟨"zkf_a1f8c00beabfe1b0a1ecc4074476dfa38f42d4e883f20d3a29821f20ee2eace4", .math, .privateDef, [.boolean], [.boolean], none, [], none, (.block [] (.ret [0]))⟩]
  contracts := [⟨"s6h73616d706c653h52756e", [⟨.target, "left", ⟨"s6h73616d706c651h52", [⟨.input, 0, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000000"⟩)⟩, ⟨.target, "right", ⟨"s6h73616d706c651h52", [⟨.input, 0, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]

private def rightSnapshot : Snapshot where
  source := "sha256:5d771ea94fb901c502ebe138ef4df5a2a35c25fd058b42fa59b32bc589867931"
  entry := "s6h73616d706c653h52756e"
  domains := []
  relations := [⟨"s6h73616d706c651h52", .publicDef, "zkc.language.formula/0", "s6h73616d706c651h52", "2a503e2d2037410a4dd256b9f29dfc9dc0bf2ad85e126cc58b5c183d9ec3f610", [.boolean], [.boolean], ["statement"], some ("zkf_a1f8c00beabfe1b0a1ecc4074476dfa38f42d4e883f20d3a29821f20ee2eace4")⟩]
  bindings := []
  definitions := [.function ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.boolean], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"]], [["role00000000", "role00000001"]]⟩, [], none, (.block [.instruction (.statement "s6h73616d706c651h52" ["role00000000"] 0 (some ("right"))) [0] [] [] ""] (.ret [0]))⟩, .function ⟨"zkf_a1f8c00beabfe1b0a1ecc4074476dfa38f42d4e883f20d3a29821f20ee2eace4", .math, .privateDef, [.boolean], [.boolean], none, [], none, (.block [] (.ret [0]))⟩]
  contracts := [⟨"s6h73616d706c653h52756e", [⟨.target, "left", ⟨"s6h73616d706c651h52", [⟨.input, 0, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000000"⟩)⟩, ⟨.target, "right", ⟨"s6h73616d706c651h52", [⟨.input, 0, "role00000000"⟩]⟩, none, some (⟨.output, 0, "role00000001"⟩)⟩]⟩]

private def original (target : String) : Function :=
  ⟨"s6h73616d706c653h52756e", .protocol, .publicDef, [.boolean], [.boolean],
    some ⟨["role00000000", "role00000001"], [["role00000000", "role00000001"]],
      [["role00000000", "role00000001"]]⟩, [], none,
    .block [.instruction (.statement "s6h73616d706c651h52" ["role00000000"] 0
      (some target)) [0] [] [] ""] (.ret [0])⟩
private def formulaBody : Region dialect [.boolean] [.boolean] := .ret (.cons .here .nil)
private def formula : CheckedDefinition :=
  ⟨"zkf_a1f8c00beabfe1b0a1ecc4074476dfa38f42d4e883f20d3a29821f20ee2eace4", .math,
    [.boolean], [.boolean], formulaBody.erase, formulaBody, formulaBody.elaborate_erase⟩
private def body : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.mark "") .nil .nil
    (.letOp (.statement "s6h73616d706c651h52" [.boolean] ["role00000000"] 0)
      (.cons .here .nil) .nil (.ret (.cons .here .nil)))
private def checked : CheckedProtocol :=
  ⟨⟨"s6h73616d706c653h52756e", ["role00000000", "role00000001"], [.boolean], [.boolean],
    [[0, 1]], [[0, 1]]⟩, body.erase, body, body.elaborate_erase⟩
private def payload : UnitPayload :=
  ⟨[formula], [checked], ⟨0, by decide⟩, by decide +kernel, by decide +kernel,
    by rfl, by decide +kernel, by decide +kernel⟩
private def left : Imported leftSnapshot := ⟨⟨leftSnapshot, payload⟩, by rfl⟩
private def right : Imported rightSnapshot := ⟨⟨rightSnapshot, payload⟩, by rfl⟩
private def leftOwner : ContractBinding left := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def rightOwner : ContractBinding right := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
private def leftEntry : EntryContractBinding left :=
  ⟨leftOwner, rfl, original "left", List.mem_cons_self, rfl, rfl,
    ⟨0, by decide⟩, rfl, ["role00000000"], 0, [0], "", rfl,
    ⟨.output, 0, "role00000000"⟩, rfl, rfl, rfl⟩
private def rightEntry : EntryContractBinding right :=
  ⟨rightOwner, rfl, original "right", List.mem_cons_self, rfl, rfl,
    ⟨1, by decide⟩, rfl, ["role00000000"], 0, [0], "", rfl,
    ⟨.output, 0, "role00000001"⟩, rfl, rfl, rfl⟩

example : leftEntry.owner.protocol = rightEntry.owner.protocol := rfl
example : leftEntry.decision.port = rightEntry.decision.port := rfl
example : leftEntry.decision.role = "role00000000" := rfl
example : rightEntry.decision.role = "role00000001" := rfl
example : leftSnapshot.contracts = rightSnapshot.contracts := rfl
example : leftSnapshot.source ≠ rightSnapshot.source := by decide
example : leftEntry.decision ≠ rightEntry.decision := by decide
example : True := by
  fail_if_success have wrong : EntryContractBinding right := leftEntry
  fail_if_success have wrong : rightEntry.decision.role = leftEntry.decision.role := rfl
  trivial

end Native
end Tests.StructuredContractEntry

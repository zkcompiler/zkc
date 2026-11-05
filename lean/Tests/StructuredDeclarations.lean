import Zkc.Source.Structured.Import

/-! Current retained declarations, independent shape checks and native layout
association. No test treats retained source authority as a frontend proof. -/
namespace StructuredDeclarationsTests
open Lean Zkc.Source Zkc.Source.Structured

def decoded (text : String) : Except String SourceDeclarations := do
  DeclarationFormat.decode (← Json.parse text)

#guard (decoded "[[],[],[]]").isOk
#guard !(decoded "[[],[]]").isOk
#guard !(decoded "[[],[],null]").isOk

#guard (decoded r#"[[[["nominal","record","probe::Ticket",[]],"linear",false,[["value",["index"],null]],[],"zkl_resource_ticket"]],[],[["probe::Ticket",null]]]"#).isOk
#guard !(decoded r#"[[[["nominal","record","probe::Ticket",[]],"linear",false,[["value",["index"],null]],[],null]],[],[["probe::Ticket",null]]]"#).isOk
#guard (decoded r#"[[[["nominal","variant","probe::Choice",[]],"ordinary",false,[["empty",[]],["value",[["x",["bool"],null]]]],[],null]],[],[["probe::Choice",null]]]"#).isOk

-- Public admission remains reducible in the kernel, not just executable.
example : ({} : SourceDeclarations).checkShape = .ok () := by decide +kernel
example : SourceDeclarations.authorityOrder ["a", "b", "한"] = true := by decide +kernel

def ticket : OriginTerm := .nominal .record "probe::Ticket" []
def holder : OriginTerm := .nominal .record "probe::Holder" []
def chain : OriginTerm := .nominal .record "probe::Chain" []
def ticketSlot : String := "zkl_resource_ticket"
def chainSlot : String := "zkl_resource_chain"

def records (resource : String := "linear") (sealed : Bool := false) : SourceDeclarations :=
  { records := [
      ⟨ticket, resource, sealed, .fields [⟨"value", .index, none⟩], [],
        if resource == "ordinary" then none else some ticketSlot⟩,
      ⟨holder, "ordinary", false, .fields [⟨"inner", ticket, none⟩], [], none⟩,
      ⟨chain, "linear", true, .fields [⟨"first", ticket, none⟩,
        ⟨"empty", .array ticket "0", none⟩, ⟨"second", ticket, none⟩], [], some chainSlot⟩],
    authorities := [("probe::Chain", none), ("probe::Holder", none), ("probe::Ticket", none)] }

example : records.checkShape = .ok () := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resource_ticket" = true := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resources_ticket" = false := by decide +kernel
example : SourceDeclarations.slotValid "zkl_resource_한" = false := by decide +kernel

#guard (records.checkShape).isOk
#guard (records "affine").checkShape.isOk
#guard (records "ordinary").checkShape.isOk
#guard (records "linear" true).checkShape.isOk
#guard !( { records with authorities := [] } : SourceDeclarations).checkShape.isOk
#guard !( { records with authorities := records.authorities.reverse } : SourceDeclarations).checkShape.isOk
#guard !( { records with authorities := ("extra", none) :: records.authorities } : SourceDeclarations).checkShape.isOk
#guard !( { records with authorities := records.authorities.map fun (path, _) =>
  (path, some "not-a-revision") } : SourceDeclarations).checkShape.isOk
#guard !( { records with records := records.records.map fun row =>
  { row with slot := none } } : SourceDeclarations).checkShape.isOk
#guard !( { records with records := records.records.map fun row =>
  { row with roles := ["P"] } } : SourceDeclarations).checkShape.isOk

def kinds (source : SourceDeclarations) (type : OriginTerm) :=
  (source.leaves 8 type ["port"]).toOption.map (fun leaves => leaves.map (·.kind))
#guard kinds records holder == some [.custody ticket, .data .index]
#guard kinds (records "affine") holder == kinds records holder
#guard kinds (records "linear" true) holder == kinds records holder
#guard kinds (records "ordinary") holder == some [.data .index]
#guard kinds records chain == some [.custody chain, .custody ticket, .data .index,
  .custody ticket, .data .index]
#guard ((records.leaves 8 holder ["port"]).toOption.map fun leaves => leaves.map (·.path)) ==
  some [["port", "inner"], ["port", "inner", "value"]]

-- The association is declared before checking a port, including when a
-- different well-formed native slot appears in the same position.
def signature : ProtocolSignature :=
  ⟨"main", ["V"], [.resourceUnit ticketSlot, .index], [], [[0], [0]], []⟩
def port : SourcePort := ⟨"ticket", ticket, ["V"], 0, 2, .data ["V"]⟩
#guard (records.checkPorts signature [port] signature.inputs signature.inputScopes false).isOk
#guard !(records.checkPorts signature [port] [.resourceUnit chainSlot, .index]
  signature.inputScopes false).isOk
#guard !(records.checkPorts signature [{port with placement := .data ["P"]}]
  signature.inputs signature.inputScopes false).isOk

-- A helper-local custody type is justified by a declaration even when no
-- protocol port exhibits that type. A different slot remains unassociated.
def helperSnapshot (slot : String) : Snapshot :=
  { source := "sha256:" ++ String.ofList (List.replicate 64 '0'), entry := "main",
    domains := [], relations := [], bindings := [], catalogue := {nominals := [], services := []},
    definitions := [.function ⟨"helper", .local, .privateDef, [.resourceUnit slot], [],
      none, [], some (.local "helper" []), .block [] (.ret [])⟩] }
#guard (records.check (helperSnapshot ticketSlot) []).isOk
#guard !(records.check (helperSnapshot "zkl_resource_undeclared") []).isOk

-- Distributed declarations decode with ordered telescopes and placement trees;
-- placement admission checks their declaration-local formulas independently.
def logical : SourceDeclarations :=
  { records := [⟨.nominal .logicalRecord "probe::Claim" [], "ordinary", false,
      .fields [⟨"value", .boolean, some (.data ["receiver"])⟩], ["holder", "receiver"], none⟩],
    authorities := [("probe::Claim", none)] }
#guard logical.checkShape.isOk
#guard (logical.records.mapM logical.checkRecordPlacement).isOk
#guard !( { logical with records := logical.records.map fun row =>
  { row with roles := ["holder"] } } : SourceDeclarations).checkShape.isOk
#guard !( { logical with records := logical.records.map fun row =>
  { row with members := .fields [⟨"value", .boolean, none⟩] } } : SourceDeclarations).checkShape.isOk
#guard !(SourceDeclarations.SourcePlacement.check (some ["P", "V"]) 8
  (.product ["P", "P"] [])).isOk
#guard !(SourceDeclarations.SourcePlacement.check (some ["P", "V"]) 8
  (.product ["V", "P"] [.data ["X"]])).isOk
#guard (SourceDeclarations.SourcePlacement.check (some ["P", "V"]) 8
  (.product ["V", "P"] [.oracle "P" ["V"]])).isOk

-- A phantom module argument still requires its authority row.
def phantom : SourceDeclarations :=
  { records := [⟨.nominal .record "probe::Empty" [.nominal .moduleType "probe::Module" []],
      "ordinary", false, .fields [], [], none⟩],
    authorities := [("probe::Empty", none), ("probe::Module", none)] }
#guard phantom.checkShape.isOk
#guard !( {phantom with authorities := [("probe::Empty", none)]} : SourceDeclarations).checkShape.isOk

-- Test the semantic roster admission, beyond the parser, at both endpoints.
def run : IO Unit := do
  for size in [17, 1024, 1025] do
    let roles := (List.range size).map fun i => s!"role_{i}"
    let interface : ProtocolInterface := ⟨roles, [], []⟩
    unless (interface.resolve [] []).isOk == (size ≤ Limits.protocolRoles) do
      throw (IO.userError s!"protocol roster boundary failed at {size}")
  IO.println "structured declarations and protocol roster boundaries passed"

#eval run
end StructuredDeclarationsTests

import Zkc.IR.Source.Structured.ComponentDeclarations

/-! Placement and native association controls. The two nested distributed types
have different telescopes and orientations; no named protocol is privileged. -/
namespace StructuredDistributedDeclarationsTests
open Zkc.Source.Structured

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def ticket : OriginTerm := .nominal .record "test::Ticket" []
def ledger : OriginTerm := .nominal .logicalRecord "test::Ledger" []
def envelope : OriginTerm := .nominal .logicalRecord "test::Envelope" []
def brace : OriginTerm := .nominal .logicalRecord "test::Brace" []
def oracle : OriginTerm := .builtin "oracle" [.builtin "oracle.table" [.boolean]]
def sequence : OriginTerm :=
  .builtin "oracle_sequence" [.builtin "oracle.table" [.boolean], .natural "4"]
def kind : OracleKind := .table .boolean none

def ticketRow : SourceRecord :=
  ⟨ticket, "affine", false, .fields [⟨"value", .index, none⟩], [],
    some "zkl_resource_ticket"⟩
def ledgerFormula (issuer auditor : String) : SourcePlacement :=
  .product [issuer, auditor] [.oracle issuer [auditor], .data [auditor], .data [issuer]]
def ledgerRow : SourceRecord :=
  ⟨ledger, "affine", false, .fields [
    ⟨"table", oracle, some (.oracle "issuer" ["auditor"])⟩,
    ⟨"metadata", .index, some (.data ["auditor"])⟩,
    ⟨"ticket", ticket, some (.data ["issuer"])⟩], ["issuer", "auditor"],
    some "zkl_resource_ledger"⟩
def envelopeRow : SourceRecord :=
  ⟨envelope, "affine", true, .fields [
    ⟨"inner", ledger, some (ledgerFormula "right" "left")⟩,
    ⟨"reverse", oracle, some (.oracle "left" ["right"])⟩,
    ⟨"metadata", .tuple [.boolean, .index], some (.data ["left", "right"])⟩,
    ⟨"empty", .array ledger "0", some (.product ["left", "right"] [
      ledgerFormula "left" "right"])⟩], ["left", "right"],
    some "zkl_resource_envelope"⟩
def braceRow : SourceRecord :=
  ⟨brace, "ordinary", false, .fields [⟨"first", oracle, none⟩,
    ⟨"rest", sequence, none⟩, ⟨"metadata", .index, none⟩], [], none⟩
def source : SourceDeclarations :=
  { records := [ticketRow, ledgerRow, envelopeRow, braceRow],
    authorities := [("test::Brace", none), ("test::Envelope", none),
      ("test::Ledger", none), ("test::Ticket", none)] }

def placement : SourcePlacement :=
  .product ["V", "P"] [ledgerFormula "P" "V", .oracle "V" ["P"],
    .data ["P", "V"], .product ["P", "V"] [ledgerFormula "V" "P"]]
def port : SourcePort := ⟨"state", envelope, ["P", "V"], 0, 13, placement⟩
def native : List Ty :=
  [.resourceUnit "zkl_resource_envelope", .resourceUnit "zkl_resource_envelope",
    .resourceUnit "zkl_resource_ledger", .resourceUnit "zkl_resource_ledger",
    kind.data, .oracle kind, .index, .resourceUnit "zkl_resource_ticket", .index,
    kind.data, .oracle kind, .boolean, .index]
def scopes : List (List Nat) :=
  [[1], [0], [0], [1], [0], [1], [1], [0], [0], [1], [0], [0, 1], [0, 1]]
def signature : ProtocolSignature := ⟨"probe", ["P", "V"], native, [], scopes, []⟩
def association (p : SourcePort := port) (types : List Ty := native)
    (roles : List (List Nat) := scopes) : Except String (List (OriginTerm × String)) :=
  source.checkPorts signature [p] types roles false

def errorOf {α : Type} : Except String α → Option String
  | .error code => some code
  | .ok _ => none

#guard source.checkShape.isOk
#guard (source.checkRecordPlacement ledgerRow).isOk
#guard (source.checkRecordPlacement envelopeRow).isOk
#guard (association).isOk
#guard (source.placedLeaves signature.roles port).toOption.map (fun xs => xs.map (·.roles)) ==
  some [["V"], ["P"], ["P"], ["V"], ["P"], ["V"], ["V"], ["P"], ["P"],
    ["V"], ["P"], ["P", "V"], ["P", "V"]]
#guard (source.leaves 16 envelope []).toOption.map List.length == some 13

-- Wrong argument order is not silently sorted. A correct argument swap must
-- change every child formula and both distributed custody scopes.
#guard errorOf (association {port with placement :=
    (.product ["P", "V"] [ledgerFormula "P" "V", .oracle "V" ["P"],
      .data ["P", "V"], .product ["P", "V"] [ledgerFormula "V" "P"]])}) ==
  some "component-declaration-formula"
#guard errorOf (association {port with placement :=
    (.product ["V", "V"] [])}) == some "component-declaration-placement"
#guard errorOf (association {port with placement :=
    (.product ["V", "P"] [ledgerFormula "P" "V", .oracle "P" ["V"],
      .data ["P", "V"], .product ["P", "V"] [ledgerFormula "V" "P"]])}) ==
  some "component-declaration-formula"
#guard errorOf (association {port with roles := ["V", "P"]}) ==
  some "component-declaration-placement"
#guard errorOf (association {port with roles := ["P"]}) ==
  some "component-declaration-placement"
#guard errorOf (association {port with offset := 1}) == some "component-declaration-port"
#guard errorOf (association {port with count := 12}) == some "component-declaration-type"
#guard errorOf (association port (.boolean :: native.tail)) ==
  some "component-declaration-custody-identity"
#guard errorOf (association port (.resourceUnit "zkl_resource_forged" :: native.tail)) ==
  some "component-declaration-custody-identity"
#guard errorOf (association port (native.take 6 ++ [.boolean] ++ native.drop 7)) ==
  some "component-declaration-type"
#guard errorOf (association port native ([ [0] ] ++ scopes.tail)) ==
  some "component-declaration-role"
#guard errorOf (association port native ([ [0, 1] ] ++ scopes.tail)) ==
  some "component-declaration-role"
#guard errorOf (association port native scopes.tail) == some "component-declaration-role"

-- A zero array materializes no custody, but cannot erase a malformed child.
def zeroPort (child : SourcePlacement) : SourcePort :=
  ⟨"empty", .array ledger "0", ["P", "V"], 0, 0, .product ["P", "V"] [child]⟩
#guard (source.checkPorts signature [zeroPort (ledgerFormula "V" "P")] [] [] false).isOk
#guard !(source.checkPorts signature [zeroPort (.data ["P", "V"])] [] [] false).isOk
#guard !(source.checkPorts signature [zeroPort (.product ["P", "V"] [
  .oracle "P" ["V"], .data ["P"], .data ["P"]])] [] [] false).isOk
#guard !(source.checkPorts signature [zeroPort (.product ["P", "P"] [
  .oracle "P" ["V"], .data ["V"], .data ["P"]])] [] [] false).isOk

-- Structural products preserve ordered source fields and canonical child union.
def tuplePort : SourcePort :=
  ⟨"pair", .tuple [oracle, .boolean], ["P", "V"], 0, 3,
    .product ["P", "V"] [.oracle "V" ["P"], .data ["P", "V"]]⟩
#guard (source.checkPorts signature [tuplePort] [kind.data, .oracle kind, .boolean]
  [[1], [0], [0, 1]] false).isOk
#guard !(source.checkPorts signature [{tuplePort with placement :=
    (.product ["V", "P"] [.oracle "V" ["P"], .data ["P", "V"]])}]
  [kind.data, .oracle kind, .boolean] [[1], [0], [0, 1]] false).isOk

-- A declaration-local structural set is re-canonicalized after substitution.
def tupleRow : SourceRecord := { ledgerRow with members := .fields [
  ⟨"both", .tuple [oracle, .boolean], some (.product ["issuer", "auditor"] [
    .oracle "issuer" ["auditor"], .data ["issuer", "auditor"]])⟩] }
def tupleSource : SourceDeclarations := { source with records := [tupleRow] }
def tupleRecordPort : SourcePort :=
  ⟨"state", ledger, ["P", "V"], 0, 5, .product ["V", "P"] [
    .product ["P", "V"] [.oracle "V" ["P"], .data ["P", "V"]]]⟩
#guard (tupleSource.checkPorts signature [tupleRecordPort]
  [.resourceUnit "zkl_resource_ledger", .resourceUnit "zkl_resource_ledger",
    kind.data, .oracle kind, .boolean] [[1], [0], [1], [0], [0, 1]] false).isOk

-- Telescope-free records use one exact oriented family, including sequences.
def bracePort : SourcePort :=
  ⟨"brace", brace, ["P", "V"], 0, 5, .product ["P", "V"] [
    .oracle "V" ["P"], .oracle "V" ["P"], .data ["P", "V"]]⟩
def braceNative : List Ty :=
  [kind.data, .oracle kind, .sequence kind.data, .oracleSequence kind 4, .index]
#guard (source.checkPorts signature [bracePort] braceNative
  [[1], [0], [1], [0], [0, 1]] false).isOk
#guard errorOf (source.checkPorts signature [{bracePort with placement :=
    (.product ["P", "V"] [.oracle "V" ["P"], .oracle "P" ["V"], .data ["P", "V"]])}]
  braceNative [[1], [0], [0], [1], [0, 1]] false) ==
  some "component-declaration-logical-family"
#guard errorOf (source.checkPorts signature [{bracePort with placement :=
    (.product ["P", "V"] [.oracle "V" ["P"], .oracle "V" ["P"], .data ["P"]])}]
  braceNative [[1], [0], [1], [0], [0]] false) ==
  some "component-declaration-logical-family"
#guard !(source.checkPorts signature [{bracePort with placement := .data ["P", "V"]}]
  braceNative [[1], [0], [1], [0], [0, 1]] false).isOk
#guard !(source.checkPorts signature [{bracePort with placement := .oracle "V" ["P"]}]
  braceNative [[1], [0], [1], [0], [0, 1]] false).isOk

-- Declaration validation covers unused and phantom/zero-storage children.
def malformed : SourceDeclarations :=
  { source with records := source.records.map fun row =>
    if row.type == ledger then {row with members := .fields [
      ⟨"hidden", .boolean, some (.oracle "issuer" ["auditor"])⟩]} else row }
#guard !(malformed.checkRecordPlacement envelopeRow).isOk
#guard !(malformed.checkRecordPlacement {envelopeRow with members := .fields [
  ⟨"zero", .array ledger "0", some (.product ["left", "right"] [
    .product ["left", "right"] [.oracle "left" ["right"]]])⟩]}).isOk
def erasedOrdinary : SourceDeclarations :=
  { source with records := {ticketRow with members := .fields [
    ⟨"hidden", .array ledger "0", none⟩]} :: source.records.tail }
def cyclic : SourceDeclarations :=
  { source with records := {ledgerRow with members := .fields [
    ⟨"self", ledger, some (.product ["issuer", "auditor"] [])⟩]} :: source.records }
#guard !(erasedOrdinary.leaves 16 ticket []).isOk
#guard errorOf (cyclic.leaves 8 ledger []) == some "component-declaration-depth"
#guard errorOf (cyclic.leaves 8 (.array ledger "0") []) ==
  some "component-declaration-depth"
#guard !(source.leaves 0 ticket []).isOk
#guard errorOf (source.leaves 8 (.array .unit "513") []) ==
  some "component-declaration-limit"
#guard errorOf ((SourceDeclarations.chargePlacement).run' 0) ==
  some "component-declaration-limit"

-- Layout admission for affine distributed resources succeeds. Linear CLAIM
-- association remains explicitly unsupported until its holder law is supplied.
def linearSource : SourceDeclarations :=
  { source with records := source.records.map fun row =>
    if row.type == ledger then {row with resource := "linear"} else row }
#guard errorOf (linearSource.checkLinearHolders [port]) ==
  some "component-claim-distributed-custody-profile"
#guard (source.checkLinearHolders [port]).isOk
def linearTicketSource : SourceDeclarations :=
  { source with records := source.records.map fun row =>
    if row.type == ticket then {row with resource := "linear"} else row }
#guard (linearTicketSource.checkPorts signature [port] native scopes false).isOk
#guard errorOf (linearTicketSource.checkLinearHolders [port]) ==
  some "component-claim-fragmented-custody-profile"

-- Complete declaration admission uses every record, port, header and slot.
def boundarySource : SourceDeclarations :=
  { source with protocols := [⟨"probe", [port], []⟩] }
def snapshot : Snapshot :=
  { source := "sha256:" ++ String.ofList (List.replicate 64 '0'), entry := "probe",
    domains := [], relations := [], bindings := [], catalogue := {nominals := [], services := []},
    definitions := [], contracts := [⟨"probe", []⟩] }
#guard (boundarySource.check snapshot [signature]).isOk
#guard errorOf (({ boundarySource with records := boundarySource.records.map fun row =>
  if row.type == ledger then {row with slot := none} else row }
  : SourceDeclarations).check snapshot [signature]) == some "component-declaration-slot"
#guard errorOf (({ boundarySource with records := boundarySource.records.map fun row =>
  if row.type == ledger then {row with slot := some "zkl_resource_ticket"} else row }
  : SourceDeclarations).check snapshot [signature]) ==
  some "component-declaration-custody-identity"
#guard errorOf (({ boundarySource with records := linearSource.records }
  : SourceDeclarations).check snapshot [signature]) ==
  some "component-claim-distributed-custody-profile"
#guard (source.checkPorts signature [port] native.tail scopes.tail false).isOk == false
#guard (source.checkPorts signature [⟨"duplicate", oracle, ["P"], 0, 2,
  .oracle "P" ["P"]⟩] [kind.data, .oracle kind] [[0], [0]] false).isOk == false

-- Ordinary placement and direct Oracle placement retain their previous law.
#guard (source.checkPorts signature [⟨"data", .index, ["P", "V"], 0, 1,
  .data ["P", "V"]⟩] [.index] [[0, 1]] false).isOk
#guard !(source.checkPorts signature [⟨"data", .index, ["P", "V"], 0, 1,
  .data ["V", "P"]⟩] [.index] [[0, 1]] false).isOk
#guard (source.checkPorts signature [⟨"table", oracle, ["P", "V"], 0, 2,
  .oracle "V" ["P"]⟩] [kind.data, .oracle kind] [[1], [0]] false).isOk
#guard !(source.checkPorts signature [⟨"table", oracle, ["P", "V"], 0, 2,
  .oracle "V" ["P"]⟩] [.oracle kind, kind.data] [[0], [1]] false).isOk
#guard !(source.checkPorts signature [⟨"ticket", ticket, ["P", "V"], 0, 2,
  .data ["P", "V"]⟩] [.resourceUnit "zkl_resource_ticket", .index]
  [[0, 1], [0, 1]] false).isOk

-- Leaf paths retain source field order, custody prefixes and array positions.
#guard (source.placedLeaves signature.roles port).toOption.map
    (fun leaves => leaves.map (·.leaf.path)) == some [
  ["state"], ["state"], ["state", "inner"], ["state", "inner"],
  ["state", "inner", "table"], ["state", "inner", "table"],
  ["state", "inner", "metadata"], ["state", "inner", "ticket"],
  ["state", "inner", "ticket", "value"], ["state", "reverse"], ["state", "reverse"],
  ["state", "metadata", "0"], ["state", "metadata", "1"]]
def arrayPort : SourcePort :=
  ⟨"array", .array oracle "2", ["P", "V"], 0, 4,
    .product ["P", "V"] [.oracle "V" ["P"]]⟩
#guard (source.checkPorts signature [arrayPort]
  [kind.data, .oracle kind, kind.data, .oracle kind] [[1], [0], [1], [0]] false).isOk
#guard (source.placedLeaves signature.roles arrayPort).toOption.map
    (fun leaves => leaves.map (·.leaf.path)) ==
  some [["array", "0"], ["array", "0"], ["array", "1"], ["array", "1"]]
#guard !(association port native ([ [1], [1] ] ++ scopes.drop 2)).isOk

-- Receiver and data sets follow the full roster, unlike telescope arguments.
def threeRoles : ProtocolSignature := { signature with roles := ["P", "V", "W"] }
#guard (source.checkPorts threeRoles [⟨"table", oracle, ["P", "V", "W"], 0, 2,
  .oracle "V" ["P", "W"]⟩] [kind.data, .oracle kind] [[1], [0, 2]] false).isOk
#guard !(source.checkPorts threeRoles [⟨"table", oracle, ["P", "V", "W"], 0, 2,
  .oracle "V" ["W", "P"]⟩] [kind.data, .oracle kind] [[1], [2, 0]] false).isOk

-- An unused zero-array field still validates its declaration-local child.
def unusedType : OriginTerm := .nominal .logicalRecord "test::Unused" []
def unusedRow : SourceRecord :=
  ⟨unusedType, "ordinary", false, .fields [⟨"empty", .array .boolean "0",
    some (.product ["P", "V"] [.oracle "P" ["V"]])⟩], ["P", "V"], none⟩
def unusedSource : SourceDeclarations :=
  { records := [unusedRow], authorities := [("test::Unused", none)] }
#guard unusedSource.checkShape.isOk
#guard !(unusedSource.checkRecordPlacement unusedRow).isOk
#guard errorOf (unusedSource.check snapshot []) == some "component-declaration-placement"

-- Kernel readback for a concrete association (no native_decide).
theorem receiverAssociation : SourceDeclarations.associateLeaf {} ["P", "V"]
    ⟨⟨.receiverHandle (.oracle kind), ["table"]⟩, ["P"]⟩ (.oracle kind) [0] = .ok () := by
  decide +kernel
#print axioms SourceDeclarations.associateLeaf_readback
#print axioms receiverAssociation

end StructuredDistributedDeclarationsTests

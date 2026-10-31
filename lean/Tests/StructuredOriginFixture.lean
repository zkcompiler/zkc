module

public import Zkc.Source.Structured.Import
public import Zkc.Source.KernelRfl

@[expose] public section

/-! Small authored origins and bodies for decoder/admission/alias controls.
These are not captured native exports. -/
namespace Tests.StructuredOriginFixture
open Zkc.Source Zkc.Source.Structured

def terms : List OriginTerm := [
  .natural "0", .field "F", .group "G", .domain "Field" "D", .asset "Commitment" "A",
  .boolean, .index, .unit, .tuple [.boolean, .unit], .array (.field "F") "12",
  .nominal .record "test::T" [], .nominal .logicalRecord "test::T" [],
  .nominal .variant "test::T" [],
  .nominal .associated "test::T" [], .nominal .moduleType "test::T" [],
  .builtin "Vector" [.field "F"], .formal "Function" [.index, .boolean]]

def leafOrigin : ProtocolOrigin := ⟨"test::Leaf", [("T", .tuple terms)]⟩

def leaf : Function := ⟨"leaf", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], some (.protocol leafOrigin), .block [] (.ret [])⟩

def root : Function := ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], some (.protocol ⟨"test::Root", []⟩),
  .block [.instruction (.protocolApply "leaf" ["P"]) [] [] [] "use_leaf"] (.ret [])⟩

def helper : Function := ⟨"helper", .local, .privateDef, [], [], none, [],
  some (.local "test::helper" [("n", "1")]), .block [] (.ret [])⟩

-- Source order differs from the checked dependency order. The helper table
-- contains only helper; the checked protocol table is [leaf, main].
def snapshot : Snapshot := ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main",
  [], [], [], [.function root, .function helper, .function leaf],
  [⟨"main", []⟩, ⟨"leaf", []⟩], blsRows, {}⟩

def helperBody : Region dialect [] [] := .ret .nil
def leafBody : Region protocolDialect [] [] := .ret .nil
def leafSignature : ProtocolSignature := ⟨"leaf", ["P"], [], [], [], []⟩
def rootBody : Region protocolDialect [] [] :=
  .letOp (.mark "use_leaf") .nil .nil <|
  .letOp (.protocolApply leafSignature [0] "use_leaf") .nil .nil <|
  .ret .nil

def checkedHelper : CheckedDefinition := ⟨"helper", .local, [], [],
  helperBody.erase, helperBody, helperBody.elaborate_erase⟩
def checkedLeaf : CheckedProtocol := ⟨leafSignature,
  leafBody.erase, leafBody, leafBody.elaborate_erase⟩
def checkedRoot : CheckedProtocol := ⟨⟨"main", ["P"], [], [], [], []⟩,
  rootBody.erase, rootBody, rootBody.elaborate_erase⟩

def payload : UnitPayload where
  definitions := [checkedHelper]
  protocols := [checkedLeaf, checkedRoot]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨snapshot, payload⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def imported : Imported snapshot := ⟨program, by kernel_rfl⟩

end Tests.StructuredOriginFixture

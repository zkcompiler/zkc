#include "../lib/Compiler/ComponentContracts.h"
#include "../lib/Compiler/LanguageInterface.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Data/Layout.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/SourceTerms.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <filesystem>

using namespace llvm;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace iface = zkc::language::detail;
namespace {
using K = Type::Kind;
using F = InterfaceComponentFacet;
std::string digest(StringRef value) {
  return toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
}
std::shared_ptr<InterfaceSchema> schema(Type type,
                                        std::vector<std::string> leaves = {}) {
  auto result = std::make_shared<InterfaceSchema>();
  result->kind = type.kind;
  result->identity = digest(typeIdentity(type));
  result->type = spelling(type);
  result->permissions = {true, true};
  result->constructible = !isLogicalValue(type);
  result->leaves = std::move(leaves);
  return result;
}
struct Fixture {
  std::string native;
  json::Value document;
};
json::Object &protocolRecord(json::Value &value) {
  return *value.getAsObject()->getArray("protocols")->front().getAsObject();
}
json::Object &port(json::Value &value, bool output = false) {
  return *protocolRecord(value)
              .getArray(output ? "outputs" : "inputs")
              ->front()
              .getAsObject();
}
json::Object &shape(json::Value &value) {
  return *port(value).getObject("schema");
}
json::Object &field(json::Object &schema, unsigned index) {
  return *(*schema.getArray("fields"))[index].getAsObject();
}
const char *native = R"mlir(
#K = #protocol.oracle_kind<"table", [ui64, 4 : ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%leftData:!D, %leftAnchor:!H, %rightData:!D, %rightAnchor:!H, %flag:i1):
  %left = "protocol.oracle_input"(%leftData,%leftAnchor) {holder="role00000002",receivers=["role00000000","role00000001"],shape_bounds={}} : (!D,!H)->!H
  %right = "protocol.oracle_input"(%rightData,%rightAnchor) {holder="role00000001",receivers=["role00000000"],shape_bounds={}} : (!D,!H)->!H
  %first:2 = "protocol.oracle_components"(%left) {holder="role00000002",receivers=["role00000000","role00000001"]} : (!H)->(!D,!H)
  %second:2 = "protocol.oracle_components"(%right) {holder="role00000001",receivers=["role00000000"]} : (!H)->(!D,!H)
  "protocol.return"(%first#0,%first#1,%second#0,%second#1,%flag) : (!D,!H,!D,!H,i1)->()
 }) {sym_name="Relay", function_type=(!D,!H,!D,!H,i1)->(!D,!H,!D,!H,i1),
     roles=["role00000000","role00000001","role00000002"],
     input_roles=[["role00000002"],["role00000000","role00000001"],["role00000001"],["role00000000"],["role00000000"]],
     output_roles=[["role00000002"],["role00000000","role00000001"],["role00000001"],["role00000000"],["role00000000"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
Fixture fixture() {
  Type four(K::Natural);
  four.dimension = Natural::constant(4);
  Type kind(K::OracleKind, "table");
  kind.arguments = {Type(K::Index), four};
  Type handleType(K::Oracle);
  handleType.arguments = {kind};
  Type innerType(K::LogicalRecord, "sample::Sources");
  Type outerType(K::LogicalRecord, "sample::Envelope");
  Type arrayType(K::Array);
  arrayType.arguments = {innerType};
  arrayType.dimension = Natural::constant(0);
  auto data = schema(Type(K::Builtin, "indices"), {"indices"});
  auto handle = schema(handleType);
  handle->oracle =
      InterfaceOracle{"table",
                      {zkc::protocol::TypeArgument::typeArgument(
                           zkc::protocol::BoundType{"index", {}, {}, {}}),
                       zkc::protocol::TypeArgument::naturalArgument(4)}};
  handle->oracleData = data;
  auto flag = schema(Type(K::Boolean), {"bool"});
  auto inner = schema(innerType);
  inner->roles = {"A", "B", "C"};
  inner->fields = {{"left", 0, handle, {}, true, OraclePlacement{2, {0, 1}}},
                   {"right", 1, handle, {}, true, OraclePlacement{1, {0}}}};
  auto empty = schema(arrayType);
  empty->constructible = false;
  empty->element = inner;
  auto outer = schema(outerType);
  outer->roles = {"X", "Y", "Z"};
  ValuePlacement innerFormula =
      ProductPlacement{inner->identity,
                       {1, 2, 0},
                       {OraclePlacement{0, {1, 2}}, OraclePlacement{2, {1}}}};
  ValuePlacement elementFormula =
      ProductPlacement{inner->identity,
                       {0, 1, 2},
                       {OraclePlacement{2, {0, 1}}, OraclePlacement{1, {0}}}};
  ValuePlacement emptyFormula =
      ProductPlacement{empty->identity, {0, 1, 2}, {elementFormula}};
  outer->fields = {{"sources", 0, inner, {}, true, innerFormula},
                   {"flag", 2, flag, {}, true, DataPlacement{{1}}},
                   {"empty", 3, empty, {}, false, emptyFormula}};
  ValuePlacement innerPlacement =
      ProductPlacement{inner->identity,
                       {0, 1, 2},
                       {OraclePlacement{2, {0, 1}}, OraclePlacement{1, {0}}}};
  ValuePlacement phantomPlacement =
      ProductPlacement{empty->identity,
                       {0, 1, 2},
                       {ProductPlacement{inner->identity,
                                         {2, 0, 1},
                                         {OraclePlacement{1, {0, 2}},
                                          OraclePlacement{0, {2}}}}}};
  ValuePlacement placed =
      ProductPlacement{outer->identity,
                       {2, 0, 1},
                       {innerPlacement, DataPlacement{{0}}, phantomPlacement}};
  json::Array components;
  for (const auto &c :
       std::vector<InterfaceComponent>{{{0, 0}, 0, 0, F::OracleAnchor, 1},
                                       {{0, 0}, 0, 1, F::OracleAnchor, 1},
                                       {{0, 0}, 0, 2, F::OracleData, 0},
                                       {{0, 1}, 0, 0, F::OracleAnchor, 3},
                                       {{0, 1}, 0, 1, F::OracleData, 2},
                                       {{1}, 0, 0, F::Data, 4}}) {
    json::Array path;
    for (unsigned index : c.path)
      path.push_back(index);
    components.push_back(
        json::Object{{"path", std::move(path)},
                     {"leaf", c.leaf},
                     {"role", c.role},
                     {"facet", iface::componentFacetName(c.facet)},
                     {"native", c.native}});
  }
  json::Value logicalPort =
      json::Object{{"name", "state"},
                   {"index", 0},
                   {"type", outer->type},
                   {"native", json::Array{0, 1, 2, 3, 4}},
                   {"schema", iface::encodeInterfaceSchema(*outer)},
                   {"placement", iface::encodeInterfacePlacement(placed)},
                   {"components", std::move(components)}};
  // Retain actual native static declarations independently of source checking.
  // This fixture does not claim that a checked source constructed these
  // records.
  auto term = [](const Type &type) { return take(encodeStaticTerm(type)); };
  json::Value declarations = json::Array{
      json::Array{
          json::Array{term(innerType), "ordinary", false,
                      json::Array{json::Array{"left", term(handleType)},
                                  json::Array{"right", term(handleType)}}},
          json::Array{term(outerType), "ordinary", false,
                      json::Array{json::Array{"sources", term(innerType)},
                                  json::Array{"flag", term(Type(K::Boolean))},
                                  json::Array{"empty", term(arrayType)}}}},
      json::Array{}};
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(native, &context);
  require(bool(module), "independent native fixture does not parse");
  auto attrs = take(importDeclarationData(&context, declarations));
  module->getBody()->front().setAttr("source_declarations", attrs);
  std::string bytes;
  raw_string_ostream out(bytes);
  module->print(out);
  out.flush();
  json::Value document = json::Object{
      {"format", "zkc.language-interface/0"},
      {"capture", std::string(64, '0')},
      {"original", digest(bytes)},
      {"toolchain", compilerToolchainIdentity()},
      {"entry", "sample::Run"},
      {"protocol", "Relay"},
      {"relations", json::Array{}},
      {"setups", json::Array{}},
      {"job", json::Object{{"kind", "run"}}},
      {"protocols",
       json::Array{json::Object{{"symbol", "Relay"},
                                {"roles", json::Array{"V", "Q", "P"}},
                                {"inputs", json::Array{logicalPort}},
                                {"outputs", json::Array{logicalPort}},
                                {"services", json::Array{}},
                                {"common_input_requirements", json::Array{}},
                                {"clauses", json::Array{}}}}}};
  return {std::move(bytes), std::move(document)};
}
Fixture custodyFixture() {
  Type wrapperType(K::LogicalRecord, "sample::Ticket");
  Type tokenType(K::Record, "sample::Token");
  auto token = schema(tokenType, {"resource_unit:zkl_resource_" +
                                  digest(typeIdentity(tokenType))});
  token->custody = 1;
  token->permissions = {false, true};
  token->constructible = false;
  auto wrapper = schema(wrapperType);
  wrapper->custody = 2;
  wrapper->permissions = {false, true};
  wrapper->roles = {"P", "V"};
  wrapper->fields = {{"token", 2, token, {}, true, DataPlacement{{0}}}};
  ValuePlacement placed =
      ProductPlacement{wrapper->identity, {1, 0}, {DataPlacement{{1}}}};
  auto unit = [](StringRef identity) {
    return "!runtime.capability<resource_unit, \"zkl_resource_" +
           identity.str() + "\">";
  };
  auto parentUnit = unit(wrapper->identity), childUnit = unit(token->identity);
  std::string types = parentUnit + ", " + parentUnit + ", " + childUnit;
  std::string roles =
      "[[\"role00000001\"],[\"role00000000\"],[\"role00000001\"]]";
  std::string bytes =
      "module {\"protocol.module\"() ({\"protocol.func\"() ({^entry(%a: " +
      parentUnit + ", %b: " + parentUnit + ", %c: " + childUnit +
      "):\"protocol.return\"(%a,%b,%c) : (" + types +
      ")->()}) {sym_name=\"Relay\", function_type=(" + types + ")->(" + types +
      "), roles=[\"role00000000\",\"role00000001\"], input_roles=" + roles +
      ",output_roles=" + roles +
      "} : ()->()}) {profile=#protocol.profile<protocol>} : ()->()}";
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module), "custody fixture does not parse");
  json::Value declarations = json::Array{
      json::Array{json::Array{take(encodeStaticTerm(wrapperType)), "affine",
                              false,
                              json::Array{json::Array{
                                  "token", take(encodeStaticTerm(tokenType))}}},
                  json::Array{take(encodeStaticTerm(tokenType)), "affine",
                              false, json::Array{}}},
      json::Array{}};
  module->getBody()->front().setAttr(
      "source_declarations",
      take(importDeclarationData(&context, declarations)));
  bytes.clear();
  raw_string_ostream out(bytes);
  module->print(out);
  out.flush();
  json::Array components;
  for (const auto &c :
       std::vector<InterfaceComponent>{{{}, 0, 1, F::Custody, 0},
                                       {{}, 1, 0, F::Custody, 1},
                                       {{0}, 0, 1, F::Custody, 2}}) {
    json::Array path;
    for (unsigned index : c.path)
      path.push_back(index);
    components.push_back(
        json::Object{{"path", std::move(path)},
                     {"leaf", c.leaf},
                     {"role", c.role},
                     {"facet", iface::componentFacetName(c.facet)},
                     {"native", c.native}});
  }
  json::Value input =
      json::Object{{"name", "ticket"},
                   {"index", 0},
                   {"type", wrapper->type},
                   {"native", json::Array{0, 1, 2}},
                   {"schema", iface::encodeInterfaceSchema(*wrapper)},
                   {"placement", iface::encodeInterfacePlacement(placed)},
                   {"components", std::move(components)}};
  auto root = fixture().document;
  (*root.getAsObject())["original"] = digest(bytes);
  protocolRecord(root)["roles"] = json::Array{"P", "V"};
  protocolRecord(root)["inputs"] = json::Array{input};
  protocolRecord(root)["outputs"] = json::Array{input};
  return {std::move(bytes), std::move(root)};
}
void schemaHashParity() {
  Type elementType(K::Record, "sample::HiddenElement");
  Type arrayType(K::Array);
  arrayType.arguments = {elementType};
  arrayType.dimension = Natural::constant(0);
  Type rootType(K::Record, "sample::GeneratedInputs");
  auto scalar = std::make_shared<Layout>();
  scalar->type = Type(K::Boolean);
  scalar->permissions = {true, true};
  scalar->constructible = true;
  scalar->leaves = {"bool"};
  auto element = std::make_shared<Layout>();
  element->type = elementType;
  element->permissions = {true, true};
  element->constructible = false;
  element->leaves = {"bool"};
  element->fields = {{"hidden", scalar, 0, {}, false, {}}};
  auto array = std::make_shared<Layout>();
  array->type = arrayType;
  array->permissions = {true, true};
  array->constructible = false;
  array->element = element;
  Layout root;
  root.type = rootType;
  root.generatedIdentity = digest("captured generated family");
  root.permissions = {true, true};
  root.constructible = false;
  root.leaves = {"bool"};
  root.fields = {{"flag", scalar, 0, {}, true, {}},
                 {"empty", array, 1, {}, true, {}}};
  auto scalarSchema = schema(Type(K::Boolean), {"bool"});
  auto elementSchema = schema(elementType, {"bool"});
  elementSchema->constructible = false;
  elementSchema->fields = {{"hidden", 0, scalarSchema, {}, false, {}}};
  auto arraySchema = schema(arrayType);
  arraySchema->constructible = false;
  arraySchema->element = elementSchema;
  auto rootSchema = schema(rootType, {"bool"});
  rootSchema->constructible = false;
  rootSchema->generated = root.generatedIdentity;
  rootSchema->fields = {{"flag", 0, scalarSchema, {}, true, {}},
                        {"empty", 1, arraySchema, {}, true, {}}};
  auto compare = [&]() {
    uint64_t remaining = Limits{}.work;
    LayoutIdentities nativeHash(remaining);
    auto expected = take(nativeHash.get(root));
    auto actual = take(iface::interfaceSchemaIdentity(
        iface::encodeInterfaceSchema(*rootSchema), Limits{}));
    require(expected == actual,
            "source/native and independent full schema hashes differ");
    return actual;
  };
  auto baseline = compare();
  root.fields[0].isPublic = false;
  rootSchema->fields[0].isPublic = false;
  require(compare() != baseline, "field privacy missing from full schema hash");
  baseline = compare();
  element->fields[0].isPublic = true;
  elementSchema->fields[0].isPublic = true;
  require(compare() != baseline,
          "zero-array element privacy missing from full schema hash");
  baseline = compare();
  root.generatedIdentity = digest("another generated family");
  rootSchema->generated = root.generatedIdentity;
  require(compare() != baseline,
          "generated family missing from full schema hash");
}
void logicalSchemaHashParity() {
  Type childType(K::LogicalRecord, "sample::Distributed");
  Type arrayType(K::Array);
  arrayType.arguments = {childType};
  arrayType.dimension = Natural::constant(0);
  Type rootType(K::LogicalRecord, "sample::DistributedWrapper");
  auto scalar = std::make_shared<Layout>();
  scalar->type = Type(K::Boolean);
  scalar->permissions = {true, true};
  scalar->constructible = true;
  scalar->leaves = {"bool"};
  auto child = std::make_shared<Layout>();
  child->type = childType;
  child->roleParameters = {"A", "B"};
  child->permissions = {true, true};
  child->leaves = {"bool", "bool"};
  child->fields = {{"first", scalar, 0, {}, true, DataPlacement{{0}}},
                   {"second", scalar, 1, {}, false, DataPlacement{{1}}}};
  auto array = std::make_shared<Layout>();
  array->type = arrayType;
  array->element = child;
  array->permissions = {true, true};
  Layout root;
  root.type = rootType;
  root.roleParameters = {"P", "V"};
  root.permissions = {true, true};
  root.leaves = {"bool", "bool"};
  ValuePlacement childFormula =
      ProductPlacement{typeIdentity(childType),
                       {1, 0},
                       {DataPlacement{{1}}, DataPlacement{{0}}}};
  ValuePlacement emptyFormula = ProductPlacement{
      typeIdentity(arrayType),
      {0, 1},
      {ProductPlacement{typeIdentity(childType),
                        {0, 1},
                        {DataPlacement{{0}}, DataPlacement{{1}}}}}};
  root.fields = {{"child", child, 0, {}, true, childFormula},
                 {"empty", array, 2, {}, true, emptyFormula}};
  auto scalarSchema = schema(Type(K::Boolean), {"bool"});
  auto childSchema = schema(childType);
  childSchema->roles = {"A", "B"};
  childSchema->fields = {
      {"first", 0, scalarSchema, {}, true, DataPlacement{{0}}},
      {"second", 1, scalarSchema, {}, false, DataPlacement{{1}}}};
  auto arraySchema = schema(arrayType);
  arraySchema->constructible = false;
  arraySchema->element = childSchema;
  auto rootSchema = schema(rootType);
  rootSchema->roles = {"P", "V"};
  uint64_t remaining = Limits{}.work;
  auto externalChild =
      take(iface::externalPlacement(*child, childFormula, remaining, Limits{}));
  auto externalArray =
      take(iface::externalPlacement(*array, emptyFormula, remaining, Limits{}));
  rootSchema->fields = {{"child", 0, childSchema, {}, true, externalChild},
                        {"empty", 2, arraySchema, {}, true, externalArray}};
  LayoutIdentities nativeHash(remaining);
  auto expected = take(nativeHash.get(root));
  auto actual = take(iface::interfaceSchemaIdentity(
      iface::encodeInterfaceSchema(*rootSchema), Limits{}));
  require(expected == actual,
          "role telescope/product formula full schema hashes differ");
  require(std::get<ProductPlacement>(externalChild.value).instance ==
              childSchema->identity,
          "external product instance was hashed twice");
  auto repeated =
      iface::externalPlacement(*child, externalChild, remaining, Limits{});
  require(!repeated,
          "external digest was accepted as an internal source identity");
  consumeError(repeated.takeError());
}
Fixture publicFixture(bool verifierHolder) {
  auto reference = fixture();
  auto referenceView =
      take(readInterface(reference.native, printJson(reference.document)));
  auto handle = referenceView.selectedProtocol()
                    .inputs[0]
                    .schema->fields[0]
                    .schema->fields[0]
                    .schema;
  auto boolean = schema(Type(K::Boolean), {"bool"});
  Type stateType(K::LogicalRecord, "sample::ProofState");
  auto state = schema(stateType);
  state->roles = {"A", "B"};
  unsigned holder = verifierHolder ? 1 : 0, receiver = 1 - holder;
  ValuePlacement oriented = OraclePlacement{holder, {receiver}};
  state->fields = {{"handle", 0, handle, {}, true, oriented},
                   {"flag", 1, boolean, {}, true, DataPlacement{{0}}}};
  ValuePlacement placed =
      ProductPlacement{state->identity, {0, 1}, {oriented, DataPlacement{{0}}}};
  json::Array components;
  for (unsigned role : {0u, 1u})
    components.push_back(json::Object{
        {"path", json::Array{0}},
        {"leaf", 0},
        {"role", role},
        {"facet", role == holder ? "oracle_data" : "oracle_anchor"},
        {"native", role == holder ? 0 : 1}});
  components.push_back(json::Object{{"path", json::Array{1}},
                                    {"leaf", 0},
                                    {"role", 0},
                                    {"facet", "data"},
                                    {"native", 2}});
  json::Value input =
      json::Object{{"name", "state"},
                   {"index", 0},
                   {"type", state->type},
                   {"native", json::Array{0, 1, 2}},
                   {"schema", iface::encodeInterfaceSchema(*state)},
                   {"placement", iface::encodeInterfacePlacement(placed)},
                   {"components", std::move(components)}};
  json::Value output = json::Object{
      {"name", "accepted"},
      {"index", 0},
      {"type", "bool"},
      {"native", json::Array{0}},
      {"schema", iface::encodeInterfaceSchema(*boolean)},
      {"placement", iface::encodeInterfacePlacement(DataPlacement{{1}})},
      {"components", json::Array{json::Object{{"path", json::Array{}},
                                              {"leaf", 0},
                                              {"role", 1},
                                              {"facet", "data"},
                                              {"native", 0}}}}};
  std::string h = verifierHolder ? "role00000001" : "role00000000";
  std::string r = verifierHolder ? "role00000000" : "role00000001";
  std::string bytes = R"mlir(
#K = #protocol.oracle_kind<"table", [ui64,4:ui64]>
!H = !protocol.oracle<#K>
!D = !data.indices
module {"protocol.module"() ({
 "protocol.func"() ({^entry(%data:!D,%anchor:!H,%flag:i1):
  %handle = "protocol.oracle_input"(%data,%anchor) {holder="HOLDER",receivers=["RECEIVER"],shape_bounds={}} : (!D,!H)->!H
  %yes = arith.constant true
  "protocol.return"(%yes) : (i1)->()
 }) {sym_name="Relay",function_type=(!D,!H,i1)->i1,roles=["role00000000","role00000001"],
 input_roles=[["HOLDER"],["RECEIVER"],["role00000000"]],output_roles=[["role00000001"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->()}
)mlir";
  for (auto [from, to] :
       {std::pair<StringRef, StringRef>{"HOLDER", h}, {"RECEIVER", r}}) {
    for (size_t at = 0; (at = bytes.find(from.str(), at)) != std::string::npos;
         at += to.size())
      bytes.replace(at, from.size(), to.str());
  }
  Type four(K::Natural);
  four.dimension = Natural::constant(4);
  Type kind(K::OracleKind, "table");
  kind.arguments = {Type(K::Index), four};
  Type handleType(K::Oracle);
  handleType.arguments = {kind};
  json::Value declarations = json::Array{
      json::Array{json::Array{
          take(encodeStaticTerm(stateType)), "ordinary", false,
          json::Array{
              json::Array{"handle", take(encodeStaticTerm(handleType))},
              json::Array{"flag", take(encodeStaticTerm(Type(K::Boolean)))}}}},
      json::Array{}};
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module), "public fixture does not parse");
  module->getBody()->front().setAttr(
      "source_declarations",
      take(importDeclarationData(&context, declarations)));
  bytes.clear();
  raw_string_ostream out(bytes);
  module->print(out);
  out.flush();
  auto value = reference.document;
  (*value.getAsObject())["original"] = digest(bytes);
  (*value.getAsObject())["job"] =
      json::Object{{"kind", "proof"},
                   {"prover", "P"},
                   {"verifier", "V"},
                   {"public", json::Array{}},
                   {"gates", json::Array{}},
                   {"acceptance", json::Object{{"direction", "output"},
                                               {"port", 0},
                                               {"path", json::Array{}},
                                               {"role", "V"}}},
                   {"completion", nullptr},
                   {"target", nullptr},
                   {"construction", json::Object{{"kind", "authored"},
                                                 {"format", "zkc.framed/0"}}}};
  protocolRecord(value)["roles"] = json::Array{"P", "V"};
  protocolRecord(value)["inputs"] = json::Array{input};
  protocolRecord(value)["outputs"] = json::Array{output};
  return {std::move(bytes), std::move(value)};
}
void nativeHostMetadata() {
  auto boolean = schema(Type(K::Boolean), {"bool"});
  Type recordType(K::Record, "sample::Hidden");
  auto record = schema(recordType, {"bool"});
  record->constructible = false;
  record->sealed = true;
  record->generated = digest("generated family");
  record->fields = {{"hidden", 0, boolean, {}, false, {}}};
  Type arrayType(K::Array);
  arrayType.arguments = {recordType};
  arrayType.dimension = Natural::constant(0);
  auto array = schema(arrayType);
  array->constructible = false;
  array->element = record;
  auto value = iface::encodeInterfaceSchema(*array);
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto layout = data::importLayout(&context, value);
  require(layout && layout.getElement() && layout.getElement().getSealed() &&
              layout.getElement().getGenerated() &&
              layout.getElement().getGenerated().getValue() ==
                  record->generated &&
              !layout.getElement().getFields()[0].getIsPublic(),
          "Host native adapter erased zero-array element/privacy/generated "
          "identity");
  auto invalidGenerated = iface::encodeInterfaceSchema(*boolean);
  (*invalidGenerated.getAsObject())["generated"] =
      digest("not a generated scalar");
  mlir::ScopedDiagnosticHandler generatedSilence(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  require(!data::importLayout(&context, invalidGenerated),
          "native scalar acquired generated nominal authority");
  (*value.getAsObject())["element"] = nullptr;
  mlir::ScopedDiagnosticHandler silence(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  require(!data::importLayout(&context, value),
          "Host native adapter accepted an array without its element template");
}
void declarationCategories() {
  json::Value logical = json::Array{"nominal", "logical_record",
                                    "sample::Logical", json::Array{}};
  json::Value ordinary =
      json::Array{"nominal", "record", "sample::Ordinary", json::Array{}};
  json::Value value = json::Array{
      json::Array{json::Array{logical, "linear", false,
                              json::Array{json::Array{"child", ordinary}}},
                  json::Array{ordinary, "affine", false, json::Array{}}},
      json::Array{}};
  if (auto e = checkComponentDeclarations(value))
    throw std::runtime_error(toString(std::move(e)));
  auto missing = value;
  (*(*missing.getAsArray())[0].getAsArray()).pop_back();
  auto refusal = checkComponentDeclarations(missing);
  require(bool(refusal), "missing nested nominal declaration accepted");
  require(namesIdentifier(toString(std::move(refusal)),
                          "component-declaration-record"),
          "missing declaration lost its refusal identifier");
  for (bool phantom : {false, true}) {
    auto bad = value;
    auto &row = *(*(*bad.getAsArray())[0].getAsArray())[1].getAsArray();
    if (phantom) {
      (*row[0].getAsArray())[3] = json::Array{logical};
      auto &outer = *(*(*bad.getAsArray())[0].getAsArray())[0].getAsArray();
      (*(*outer[3].getAsArray())[0].getAsArray())[1] = row[0];
    } else
      row[3] = json::Array{
          json::Array{"hidden", json::Array{"array", logical, "0"}}};
    refusal = checkComponentDeclarations(bad);
    require(bool(refusal), "ordinary carrier erased logical category");
    require(namesIdentifier(toString(std::move(refusal)),
                            "component-declaration-record"),
            "logical category refusal lost its identifier");
  }
}
void sourceIntegration(StringRef path) {
  auto source = MemoryBuffer::getFile(path);
  require(bool(source), "source integration fixture is missing");
  CaptureOptions options;
  options.format = "zkc-layout";
  auto project = take(
      analyze(
          take(capture({{"sample", (*source)->getBuffer().str(), path.str()}},
                       options)))
          .checkedProject());
  auto closed = take(closeSubject(project, "sample::Relay"));
  auto original = take(prepareOriginal(closed));
  auto independent =
      take(readInterface(original.bytes(), original.interfaceJson()));
  if (auto e = compareInterface(closed, independent))
    throw std::runtime_error(toString(std::move(e)));
  take(admitOriginal(closed, original.bytes(), original.interfaceJson()));
  const auto &input = independent.selectedProtocol().inputs[0];
  require(input.native.size() == 5 && input.components.size() == 6 &&
              input.schema->roles.size() == 3 &&
              input.schema->fields.size() == 3 &&
              input.schema->fields[2].schema->element &&
              !input.schema->fields[2].isPublic,
          "checked source did not retain the complete recursive interface");
}
void structuralSourceIntegration(StringRef type, unsigned width) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto code =
      "module sample\npub protocol Run roles(P, V)(value: " + type.str() +
      ") -> " + type.str() + ":\n    return value\n";
  auto project = take(
      analyze(take(capture({{"sample", code, {}}}, options))).checkedProject());
  auto closed = take(closeNativeRun(project, "sample::Run"));
  auto original = take(prepareOriginal(closed));
  auto independent =
      take(readInterface(original.bytes(), original.interfaceJson()));
  if (auto error = compareInterface(closed, independent))
    throw std::runtime_error(toString(std::move(error)));
  const auto &input = independent.selectedProtocol().inputs[0];
  require(
      input.schema->kind != K::LogicalRecord && input.placement &&
          std::holds_alternative<ProductPlacement>(input.placement->value) &&
          input.native.size() == width && input.components.size() == width,
      "ordinary structural type lost its component placement");
  take(admitOriginal(closed, original.bytes(), original.interfaceJson()));
}
Fixture flagClauseFixture() {
  auto f = publicFixture(false);
  auto at = f.native.find("    \"protocol.func\"");
  require(at != std::string::npos, "native clause fixture function missing");
  f.native.insert(
      at,
      R"mlir(    "relation.declare"() <{sym_name="Flag",kind="fixture.flag/0",key="selected",revision="0",signature=(i1)->i1,purposes=["statement"]}> : ()->()
)mlir");
  at = f.native.find("function_type = ");
  require(at != std::string::npos, "native function properties missing");
  f.native.insert(
      at,
      R"mlir(contracts = [["input","selected",[@Flag,[["input",2:i64,"role00000000"]]],unit,unit]], )mlir");
  (*f.document.getAsObject())["original"] = digest(f.native);
  (*f.document.getAsObject())["relations"] = json::Array{json::Object{
      {"symbol", "Flag"},
      {"static_arguments", json::Array{}},
      {"definition", json::Object{{"kind", "opaque"}}},
      {"inputs", json::Array{json::Object{
                     {"name", "flag"},
                     {"purpose", "statement"},
                     {"native", json::Array{0}},
                     {"schema", iface::encodeInterfaceSchema(
                                    *schema(Type(K::Boolean), {"bool"}))}}}}}};
  protocolRecord(f.document)["clauses"] = json::Array{json::Object{
      {"name", "selected"},
      {"kind", "input"},
      {"subject", json::Object{{"relation", "Flag"},
                               {"operands", json::Array{json::Object{
                                                {"direction", "input"},
                                                {"port", 0},
                                                {"path", json::Array{1}},
                                                {"role", "P"}}}}}},
      {"residual", nullptr},
      {"decision", nullptr}}};
  return f;
}
Fixture setupFixture() {
  auto base = publicFixture(false);
  const std::string domain = "multilinear.kzg.bls12-381/0";
  Type verifierType(K::Builtin, "verifier_key"),
      proverType(K::Builtin, "prover_key");
  verifierType.arguments =
      proverType.arguments = {domainType("Commitment", domain)};
  auto verifier = schema(verifierType, {"verifier_key:" + domain});
  verifier->constructible = false;
  auto prover = schema(proverType, {"prover_key:" + domain});
  prover->constructible = false;
  auto boolean = schema(Type(K::Boolean), {"bool"});
  Type stateType(K::LogicalRecord, "sample::SetupState");
  auto state = schema(stateType);
  state->roles = {"P", "V"};
  state->fields = {{"verifier", 0, verifier, {}, true, DataPlacement{{1}}},
                   {"prover", 1, prover, {}, true, DataPlacement{{0}}},
                   {"flag", 2, boolean, {}, true, DataPlacement{{0}}}};
  ValuePlacement placed = ProductPlacement{
      state->identity,
      {0, 1},
      {DataPlacement{{1}}, DataPlacement{{0}}, DataPlacement{{0}}}};
  json::Array components;
  for (unsigned i = 0; i < 3; ++i)
    components.push_back(json::Object{{"path", json::Array{i}},
                                      {"leaf", 0},
                                      {"role", i == 0 ? 1 : 0},
                                      {"facet", "data"},
                                      {"native", i}});
  json::Value input =
      json::Object{{"name", "state"},
                   {"index", 0},
                   {"type", state->type},
                   {"native", json::Array{0, 1, 2}},
                   {"schema", iface::encodeInterfaceSchema(*state)},
                   {"placement", iface::encodeInterfacePlacement(placed)},
                   {"components", std::move(components)}};
  std::string bytes = R"mlir(
!VK = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "verifier_key">
!PK = !commitment.polynomial<"multilinear.kzg.bls12-381/0", "prover_key">
module {"protocol.module"() ({
 "protocol.func"() ({^entry(%vk:!VK,%pk:!PK,%flag:i1):
  %yes = arith.constant true
  "protocol.return"(%yes) : (i1)->()
 }) {sym_name="Relay",function_type=(!VK,!PK,i1)->i1,roles=["role00000000","role00000001"],
 input_roles=[["role00000001"],["role00000000"],["role00000000"]],output_roles=[["role00000001"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->()}
)mlir";
  json::Value declarations = json::Array{
      json::Array{json::Array{
          take(encodeStaticTerm(stateType)), "ordinary", false,
          json::Array{
              json::Array{"verifier", take(encodeStaticTerm(verifierType))},
              json::Array{"prover", take(encodeStaticTerm(proverType))},
              json::Array{"flag", take(encodeStaticTerm(Type(K::Boolean)))}}}},
      json::Array{}};
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(bytes, &context);
  require(bool(module), "setup fixture does not parse");
  module->getBody()->front().setAttr(
      "source_declarations",
      take(importDeclarationData(&context, declarations)));
  bytes.clear();
  raw_string_ostream out(bytes);
  module->print(out);
  out.flush();
  (*base.document.getAsObject())["original"] = digest(bytes);
  (*base.document.getAsObject()->getObject("job"))["public"] = json::Array{
      json::Object{{"port", 0}, {"path", json::Array{0}}, {"role", "V"}}};
  (*base.document.getAsObject())["setups"] = json::Array{json::Object{
      {"name", "pcs"},
      {"inputs",
       json::Array{json::Object{{"port", 0}, {"path", json::Array{0}}},
                   json::Object{{"port", 0}, {"path", json::Array{1}}}}}}};
  protocolRecord(base.document)["inputs"] = json::Array{input};
  return {std::move(bytes), std::move(base.document)};
}
void mutation(function_ref<void(json::Value &)> change) {
  auto f = fixture();
  change(f.document);
  refuses(readInterface(f.native, printJson(f.document)), "source.interface");
}
void mutateActual(StringRef from, StringRef to) {
  auto f = fixture();
  auto at = f.native.find(from.str());
  require(at != std::string::npos, "native mutation anchor missing");
  f.native.replace(at, from.size(), to.str());
  (*f.document.getAsObject())["original"] = digest(f.native);
  auto result = readInterface(f.native, printJson(f.document));
  require(!result, "changed actual transport was admitted");
  consumeError(result.takeError());
}
} // namespace
int main(int argc, char **argv) {
  Cases cases;
  for (bool sealed : {false, true})
    cases.run(
        sealed
            ? "sealed legacy family publishes complete current metadata"
            : "legacy generic family retains reversed multi-receiver placement",
        [=] {
          auto source = std::string(R"(module m;
type K=builtin("oracle.table",index,4);
type O=builtin("oracle",K);
type Os=builtin("oracle_sequence",K,0);
)") + (sealed ? "#[sealed] " : "") +
                        R"(
#[logical] struct State<N:nat>{secret:(),word:O,words:Os,pub tag:index}
protocol Forward roles(V,P,W)(state:State<9>@P->(V,W))
 ->(out:State<9>@P->(V,W)){return(out=state);}
protocol Run roles(W,V,P)(state:State<9>@P->(V,W))
 ->(out:State<9>@P->(V,W)){
 let out=Forward roles(V,P,W)(state);return(out=out);
})";
          auto captured =
              take(capture({{"m", source, "logical-transition.zkc"}}));
          auto checked = take(analyze(captured).checkedProject());
          auto subject = take(closeSubject(checked, "m::Run"));
          auto original = take(prepareOriginal(subject));
          auto view =
              take(readInterface(original.bytes(), original.interfaceJson()));
          if (auto e = compareInterface(original.entry(), view))
            throw std::runtime_error(toString(std::move(e)));
          const auto &input = view.selectedProtocol().inputs.front();
          require(input.schema->roles.empty() &&
                      input.schema->sealed == sealed &&
                      input.schema->fields.size() == 4 &&
                      !input.schema->fields[0].isPublic &&
                      input.schema->fields[0].schema->leaves.empty(),
                  "legacy schema lost its nominal or private empty metadata");
          require(input.placement.has_value(), "legacy placement is absent");
          const auto &placed =
              std::get<ProductPlacement>(input.placement->value);
          require(placed.arguments == std::vector<unsigned>({0, 1, 2}) &&
                      std::get<OraclePlacement>(placed.fields[1].value) ==
                          OraclePlacement{2, {0, 1}} &&
                      std::get<DataPlacement>(placed.fields[0].value).roles ==
                          placed.arguments,
                  "legacy family inferred a fixed first-role holder or dropped "
                  "empty metadata");
          for (unsigned change = 0; change < 4; ++change) {
            auto document = take(json::parse(original.interfaceJson()));
            auto &schema = shape(document);
            if (change == 0)
              schema.erase("roles");
            else if (change == 1)
              field(schema, 0)["placement"] = json::Object{
                  {"kind", "data"}, {"roles", json::Array{0, 1, 2}}};
            else if (change == 2)
              schema["permissions"] = json::Array{"Drop"};
            else
              schema["custody"] = 1;
            refuses(readInterface(original.bytes(), printJson(document)),
                    "source.interface");
          }
        });
  for (bool nested : {false, true})
    cases.run(
        nested ? "legacy category rejects nested distributed metadata"
               : "legacy category requires a direct handle",
        [=] {
          CaptureOptions options;
          options.format = "zkc-layout";
          std::string source = R"(module m
struct Payload roles(P,V):
    pub value: index @(P,V)
)";
          if (nested)
            source += R"(type K = builtin("oracle.table", index, 4)
type O = builtin("oracle", K)
struct State roles(P,V):
    pub nested: Payload roles(P,V)
    pub word: O @P -> V
)";
          auto type = nested ? "State" : "Payload";
          source += std::string("pub protocol Run roles(P,V)(state: ") + type +
                    " roles(P,V)) -> " + type +
                    " roles(P,V):\n    return state\n";
          auto project =
              take(analyze(take(capture({{"m", source, "logical-category.zkc"}},
                                        options)))
                       .checkedProject());
          auto original =
              take(prepareOriginal(take(closeSubject(project, "m::Run"))));
          take(readInterface(original.bytes(), original.interfaceJson()));
          auto document = take(json::parse(original.interfaceJson()));
          for (bool output : {false, true}) {
            auto &schema = *port(document, output).getObject("schema");
            schema["roles"] = json::Array{};
            for (auto &field : *schema.getArray("fields"))
              (*field.getAsObject())["placement"] = nullptr;
          }
          refuses(readInterface(original.bytes(), printJson(document)),
                  "source.interface");
        });
  if (argc == 3 && StringRef(argv[1]) == "--source") {
    cases.run("checked recursive source/interface/native correspondence",
              [&] { sourceIntegration(argv[2]); });
    return cases.result();
  }
  for (auto [type, width] :
       {std::pair<StringRef, unsigned>{"(index @V, index @P)", 2},
        {"[(index @V, index @P); 2]", 4},
        {"[(index @V, index @P); 0]", 0}})
    cases.run("ordinary structural schema preserves placement: " + type,
              [type = type, width = width] {
                structuralSourceIntegration(type, width);
              });
  cases.run(
      "nested independent holders, ordered applications, privacy and zero "
      "arrays",
      [] {
        auto f = fixture();
        auto view = take(readInterface(f.native, printJson(f.document)));
        const auto &input = view.selectedProtocol().inputs[0];
        require(input.components.size() == 6 &&
                    input.components[0].native == input.components[1].native &&
                    input.components[2].role == 2 &&
                    input.schema->fields[2].schema->element &&
                    input.schema->fields[2].schema->fields.empty() &&
                    !input.schema->fields[2].isPublic,
                "recursive metadata or shared anchor coordinate was erased");
      });
  for (StringRef name : {"missing", "extra", "reordered", "path", "leaf",
                         "role", "facet", "native"})
    cases.run("component map rejects " + name, [&] {
      mutation([&](auto &value) {
        auto &cs = *port(value).getArray("components");
        if (name == "missing")
          cs.pop_back();
        else if (name == "extra")
          cs.push_back(cs.front());
        else if (name == "reordered")
          std::swap(cs[0], cs[1]);
        else {
          auto &c = *cs.front().getAsObject();
          if (name == "path")
            c[name] = json::Array{0, 1};
          else if (name == "facet")
            c[name] = "data";
          else
            c[name] = 99;
        }
      });
    });
  for (StringRef name :
       {"identity", "role-arity", "role-alias", "field-order", "formula",
        "private", "element", "nullable", "custody", "boolean-custody"})
    cases.run("recursive schema rejects " + name, [&] {
      mutation([&](auto &value) {
        auto &s = shape(value);
        auto &p = *port(value).getObject("placement");
        if (name == "identity")
          p["instance"] = digest(*s.getString("identity"));
        else if (name == "role-arity")
          p["arguments"] = json::Array{0, 1};
        else if (name == "role-alias")
          p["arguments"] = json::Array{0, 0, 1};
        else if (name == "field-order")
          std::swap((*p.getArray("fields"))[0], (*p.getArray("fields"))[1]);
        else if (name == "formula")
          (*field(s, 0).getObject("placement"))["arguments"] =
              json::Array{0, 1, 2};
        else if (name == "private")
          field(s, 2)["public"] =
              true; // repeated identity must remain complete
        else if (name == "element")
          field(s, 2).getObject("schema")->erase("element");
        else if (name == "nullable")
          field(s, 1).erase("placement");
        else if (name == "custody")
          s["custody"] = 2;
        else
          s["custody"] = false;
      });
    });
  cases.run("zero array cannot replace its retained logical element with "
            "ordinary data",
            [] {
              auto f = fixture();
              auto boolean = iface::encodeInterfaceSchema(
                  *schema(Type(K::Boolean), {"bool"}));
              for (bool output : {false, true}) {
                auto &p = port(f.document, output);
                auto &s = *p.getObject("schema");
                field(s, 2).getObject("schema")->operator[]("element") =
                    boolean;
                field(s, 2)["placement"] =
                    iface::encodeInterfacePlacement(DataPlacement{{0}});
                (*p.getObject("placement")->getArray("fields"))[2] =
                    iface::encodeInterfacePlacement(DataPlacement{{2}});
              }
              refuses(readInterface(f.native, printJson(f.document)),
                      "source.interface");
            });
  cases.run(
      "distributed and nested ordinary custody prefixes retain separate "
      "coordinates",
      [] {
        auto f = custodyFixture();
        auto view = take(readInterface(f.native, printJson(f.document)));
        const auto &p = view.selectedProtocol().inputs[0];
        require(
            p.schema->custody == 2 && p.schema->fields[0].offset == 2 &&
                p.schema->fields[0].schema->custody == 1 &&
                p.components.size() == 3 && p.components[0].role == 1 &&
                p.components[1].role == 0 &&
                p.components[2].path == std::vector<unsigned>{0},
            "wrapper telescope custody collapsed into one aggregate fragment");
      });
  for (StringRef name :
       {"arity", "role-order", "child-prefix", "facet", "unit-identity"})
    cases.run("custody rejects " + name, [&] {
      auto f = custodyFixture();
      auto &s = shape(f.document);
      if (name == "arity")
        s["custody"] = 1;
      else if (name == "role-order")
        port(f.document).getObject("placement")->operator[]("arguments") =
            json::Array{0, 1};
      else if (name == "child-prefix")
        field(s, 0)["offset"] = 1;
      else if (name == "facet")
        (*port(f.document).getArray("components"))[0].getAsObject()->operator[](
            "facet") = "data";
      else
        field(s, 0).getObject("schema")->operator[]("identity") =
            std::string(64, 'a');
      refuses(readInterface(f.native, printJson(f.document)),
              "source.interface");
    });
  for (bool holder : {false, true})
    cases.run(
        "handle origins remain separate from ordinary public fields", [&] {
          auto f = publicFixture(holder);
          auto view = take(readInterface(f.native, printJson(f.document)));
          require(view.proof->publicInputs.empty(),
                  "handle data became an ordinary public selection");
          (*f.document.getAsObject()->getObject("job"))["public"] =
              json::Array{json::Object{
                  {"port", 0}, {"path", json::Array{}}, {"role", "V"}}};
          refuses(readInterface(f.native, printJson(f.document)),
                  "source.interface");
        });
  cases.run("Host native metadata retains complete zero-array element schemas",
            nativeHostMetadata);
  cases.run("component declarations retain nested resources and reject erased "
            "logical category",
            declarationCategories);
  cases.run(
      "ordinary logical subfield selection follows its own participant and "
      "native coordinate",
      [] {
        auto f = flagClauseFixture();
        auto view = take(readInterface(f.native, printJson(f.document)));
        const auto &operand =
            view.selectedProtocol().clauses[0].subject.operands[0];
        require(
            operand.native == std::vector<unsigned>{2} && operand.role == 0,
            "ordinary field selection used aggregate roles or body offsets");
        auto &selector = *protocolRecord(f.document)
                              .getArray("clauses")
                              ->front()
                              .getAsObject()
                              ->getObject("subject")
                              ->getArray("operands")
                              ->front()
                              .getAsObject();
        selector["role"] = "V";
        refuses(readInterface(f.native, printJson(f.document)),
                "source.interface");
        selector["role"] = "P";
        selector["path"] = json::Array{};
        refuses(readInterface(f.native, printJson(f.document)),
                "source.interface");
        selector["role"] = nullptr;
        selector["path"] = json::Array{1};
        refuses(readInterface(f.native, printJson(f.document)),
                "source.interface");
      });
  cases.run("setup and public key policy follow individual logical fields", [] {
    auto f = setupFixture();
    auto view = take(readInterface(f.native, printJson(f.document)));
    require(view.setups.size() == 1 && view.setups[0].inputs.size() == 2 &&
                view.setups[0].inputs[0].native == std::vector<unsigned>{0} &&
                view.setups[0].inputs[1].native == std::vector<unsigned>{1},
            "setup selection used aggregate role union or body slices");
  });
  for (StringRef name :
       {"private", "whole-logical", "omitted", "overlap", "non-setup"})
    cases.run("logical setup selection rejects " + name, [&] {
      auto f = setupFixture();
      auto &inputs = *f.document.getAsObject()
                          ->getArray("setups")
                          ->front()
                          .getAsObject()
                          ->getArray("inputs");
      if (name == "private")
        field(shape(f.document), 0)["public"] = false;
      else if (name == "whole-logical")
        inputs[0].getAsObject()->operator[]("path") = json::Array{};
      else if (name == "omitted")
        inputs.pop_back();
      else
        inputs[1].getAsObject()->operator[]("path") =
            name == "overlap" ? json::Array{0} : json::Array{2};
      refuses(readInterface(f.native, printJson(f.document)),
              "source.interface");
    });
  cases.run("verifier cannot acquire a prover key through a mixed-role record", [] {
    auto f = setupFixture();
    field(shape(f.document), 1)["placement"] =
        iface::encodeInterfacePlacement(DataPlacement{{1}});
    (*port(f.document).getObject("placement")->getArray("fields"))[1] =
        iface::encodeInterfacePlacement(DataPlacement{{1}});
    (*port(f.document).getArray("components"))[1].getAsObject()->operator[](
        "role") = 1;
    StringRef from =
        R"(input_roles = [["role00000001"], ["role00000000"], ["role00000000"]])";
    auto at = f.native.find(from.str());
    require(at != std::string::npos, "setup role mutation anchor missing");
    f.native.replace(
        at, from.size(),
        R"(input_roles = [["role00000001"], ["role00000001"], ["role00000000"]])");
    (*f.document.getAsObject())["original"] = digest(f.native);
    refuses(readInterface(f.native, printJson(f.document)), "source.interface");
  });
  cases.run("affine wrappers cannot grant Drop to a linear child", [] {
    auto f = custodyFixture();
    for (bool output : {false, true}) {
      auto &s = *port(f.document, output).getObject("schema");
      s["permissions"] = json::Array{};
      field(s, 0).getObject("schema")->operator[]("permissions") =
          json::Array{};
    }
    mlir::DialectRegistry registry;
    registerDialects(registry);
    mlir::MLIRContext context(registry);
    context.loadAllAvailableDialects();
    auto module = mlir::parseSourceString<mlir::ModuleOp>(f.native, &context);
    require(bool(module), "custody original no longer parses");
    auto &unit = module->getBody()->front();
    auto declarations =
        take(exportDeclarationData(unit.getAttr("source_declarations")));
    (*(*(*declarations.getAsArray())[0].getAsArray())[1].getAsArray())[1] =
        "linear";
    unit.setAttr("source_declarations",
                 take(importDeclarationData(&context, declarations)));
    f.native.clear();
    raw_string_ostream out(f.native);
    module->print(out);
    out.flush();
    (*f.document.getAsObject())["original"] = digest(f.native);
    take(readInterface(f.native, printJson(f.document)));
  });
  cases.run("actual equal typed anchor swap remains rejected",
            [] { mutateActual("%arg1)", "%arg3)"); });
  cases.run("actual equal typed output swap remains rejected", [] {
    mutateActual("\"protocol.return\"(%data, %anchor, %data_0, %anchor_1",
                 "\"protocol.return\"(%data_0, %anchor_1, %data, %anchor");
  });
  cases.run("independent schema hash binds generated family, privacy and zero "
            "elements",
            schemaHashParity);
  cases.run(
      "independent schema hash binds role telescopes and product formulas",
      logicalSchemaHashParity);
  cases.run("zero storage metadata still consumes bounded depth and work", [] {
    auto f = fixture();
    Limits limits;
    limits.work = 20;
    refuses(readInterface(f.native, printJson(f.document), limits),
            "source.limit");
    limits = Limits{};
    limits.typeDepth = 1;
    refuses(readInterface(f.native, printJson(f.document), limits),
            "source.limit");
  });
  if (argc == 2) {
    auto f = fixture();
    std::filesystem::create_directories(argv[1]);
    auto expected = take(iface::interfaceSchemaIdentity(
        *port(f.document).get("schema"), Limits{}));
    auto custody = custodyFixture();
    auto custodyExpected = take(iface::interfaceSchemaIdentity(
        *port(custody.document).get("schema"), Limits{}));
    for (auto [name, bytes] : std::vector<std::pair<std::string, std::string>>{
             {"recursive-records.mlir", f.native},
             {"recursive-records.json", printJson(f.document)},
             {"custody-records.mlir", custody.native},
             {"custody-records.json", printJson(custody.document)},
             {"schema-digests.json",
              printJson(json::Object{{"recursive-records", expected},
                                     {"custody-records", custodyExpected}})}}) {
      std::error_code error;
      raw_fd_ostream out(std::string(argv[1]) + "/" + name, error);
      require(!error, "cannot write fixture");
      out << bytes;
    }
  }
  return cases.result();
}

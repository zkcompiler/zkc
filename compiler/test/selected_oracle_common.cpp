#include "../lib/Transforms/OracleAccounting.h"
#include "../lib/Transforms/OracleCommonPlan.h"
#include "../lib/Transforms/OracleEmissionAccounting.h"
#include "../lib/Transforms/OracleNativeCommon.h"
#include "../lib/Transforms/OraclePublication.h"
#include "../lib/Transforms/OracleQuerySchedule.h"
#include "../lib/Transforms/OracleTableRead.h"
#include "../lib/Transforms/OracleVerificationContext.h"
#include "../lib/Transforms/OracleVirtualRecipe.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Protocol/OraclePorts.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/StructuredData.h"
#include "llvm/ADT/ScopeExit.h"
#include <filesystem>
#include <limits>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
// One static source contains both branch/repeat nestings, distinct
// constructors, enum payloads, equal-typed captures, repeated queries, a
// stopping guard and conditional participant completion. No test infers
// agreement from a type.
std::string fixture(unsigned trips, bool outerRepeat) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">, 2:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!Choice = !data.variant<#data.identity<["atom", "OracleChoice"]>, [#data.alternative<"left", [ui64]>, #data.alternative<"right", [ui64]>]>
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%choice:!Choice,%data:!D,%other:!D,%position:ui64,%allow:i1):
)mlir";
  text += " %trips = \"data.index\"() {value=" + std::to_string(trips) +
          ":ui64} : ()->ui64\n";
  if (outerRepeat)
    text += R"mlir(
 "protocol.repeat"(%trips,%choice,%data,%other,%position,%allow,%trips) ({
 ^outer(%iteration:ui64,%choice:!Choice,%data:!D,%other:!D,%position:ui64,%allow:i1,%trips:ui64):
)mlir";
  text += R"mlir(
 %chosen = "protocol.branch"(%choice,%data,%other,%position,%trips,%allow) ({
 ^left(%payload:ui64,%rows:!D,%other_rows:!D,%fallback:ui64,%count:ui64,%go:i1):
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %table = "protocol.oracle_send"(%rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="left_table"} : (!D,ui64)->!H
   "protocol.repeat"(%count,%table,%payload) ({
   ^inner(%i:ui64,%handle:!H,%index:ui64):
     %answer = "protocol.oracle_query"(%handle,%index) {site="left_inner",owner="V"} : (!H,ui64)->!F
     "protocol.yield"() : ()->()
   }) {site="left_rounds",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,!H,ui64)->()
   %first = "protocol.oracle_query"(%table,%payload) {site="left_first",owner="V"} : (!H,ui64)->!F
   %duplicate = "protocol.oracle_query"(%table,%payload) {site="left_duplicate",owner="V"} : (!H,ui64)->!F
   "protocol.guard"(%go) {owner="V",site="left_guard"} : (i1)->()
   "protocol.finish_if"(%go) {owner="V",site="left_finish"} : (i1)->()
   "protocol.yield"(%table) : (!H)->()
 }, {
 ^right(%payload:ui64,%rows:!D,%other_rows:!D,%fallback:ui64,%count:ui64,%go:i1):
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %table = "protocol.oracle_send"(%other_rows,%two) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="right_table"} : (!D,ui64)->!H
   %answer = "protocol.oracle_query"(%table,%payload) {site="right_read",owner="V"} : (!H,ui64)->!F
   "protocol.yield"(%table) : (!H)->()
 }) {site="choose",roles=["P","V"],output_roles=[["P","V"]],alternatives=["left","right"]} : (!Choice,!D,!D,ui64,ui64,i1)->!H
 %after = "protocol.oracle_query"(%chosen,%position) {site="after_join",owner="V"} : (!H,ui64)->!F
)mlir";
  if (outerRepeat)
    text += R"mlir(
 "protocol.yield"() : ()->()
 }) {site="outer_rounds",carried=0:i64,maximum=3:i64,roles=["P","V"],carried_roles=[]} : (ui64,!Choice,!D,!D,ui64,i1,ui64)->()
)mlir";
  text += R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(!Choice,!D,!D,ui64,i1)->(),roles=["P","V"],input_roles=[["P","V"],["P"],["P"],["V"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  if (outerRepeat) {
    auto begin = text.find("^outer(");
    auto end = text.find("}) {site=\"outer_rounds\"", begin);
    auto body = text.substr(begin, end - begin);
    for (StringRef name :
         {"choice", "data", "other", "position", "allow", "trips"}) {
      auto from = ("%" + name).str();
      auto to = ("%outer_" + name).str();
      size_t at = 0;
      while ((at = body.find(from, at)) != std::string::npos) {
        body.replace(at, from.size(), to);
        at += to.size();
      }
    }
    text.replace(begin, end - begin, body);
  }
  return text;
}
OwningOpRef<ModuleOp> source(MLIRContext &context, unsigned trips = 1,
                             bool outer = false) {
  auto module = parseSourceString<ModuleOp>(fixture(trips, outer), &context);
  require(bool(module) && succeeded(admitStage(*module)),
          "selected source admission");
  return module;
}
pir::BranchOp branch(ModuleOp module) {
  pir::BranchOp selected;
  module.walk([&](pir::BranchOp op) {
    if (op.getSite() == "choose")
      selected = op;
  });
  require(bool(selected), "missing actual selected region");
  return selected;
}
std::string printed(Operation *op) {
  std::string result;
  raw_string_ostream stream(result);
  op->print(stream);
  return result;
}
void checked(Error failure) {
  if (failure)
    throw std::runtime_error(toString(std::move(failure)));
}
// Exercise real production phases with a fresh exact allowance on every run.
// The final common-control completion keeps its own capacity identifier.
template <class Action> void cumulativeBoundary(Action action) {
  OracleNativeWork measured;
  const uint64_t measuredInitialWork = measured.remaining;
  const unsigned measuredInitialVisits = measured.operations;
  checked(action(measured));
  uint64_t cost = measuredInitialWork - measured.remaining;
  require(cost > 0 && !measured.exhausted, "missing production work debit");
  OracleNativeWork exact;
  exact.remaining = cost;
  checked(action(exact));
  require(exact.remaining == 0 && !exact.exhausted,
          "exact production allowance was insufficient");
  OracleNativeWork shortWork;
  shortWork.remaining = cost - 1;
  auto failure = action(shortWork);
  require(bool(failure), "one-less production allowance succeeded");
  auto code = toString(std::move(failure));
  require((namesIdentifier(code, "oracle-common-limit") ||
           namesIdentifier(code, "common-control-capacity")) &&
              shortWork.exhausted && !shortWork.charge(0),
          "production refusal lost its capacity identifier or stickiness");
  failure = action(shortWork);
  require(bool(failure), "production retry reset exhausted work");
  consumeError(std::move(failure));
  unsigned visits = measuredInitialVisits - measured.operations;
  if (visits) {
    // Keep work plentiful so this boundary independently exercises visits.
    OracleNativeWork exactVisits;
    exactVisits.operations = visits;
    checked(action(exactVisits));
    require(exactVisits.operations == 0 && !exactVisits.exhausted &&
                exactVisits.remaining == measured.remaining,
            "exact production visit allowance changed work accounting");
    OracleNativeWork shortVisits;
    shortVisits.operations = visits - 1;
    failure = action(shortVisits);
    require(bool(failure), "one-less production visit allowance succeeded");
    code = toString(std::move(failure));
    require((namesIdentifier(code, "oracle-common-limit") ||
             namesIdentifier(code, "common-control-capacity")) &&
                shortVisits.exhausted && !shortVisits.remaining &&
                !shortVisits.charge(0),
            "visit exhaustion lost its capacity identifier or stickiness");
    failure = action(shortVisits);
    require(bool(failure), "production retry reset exhausted visits");
    consumeError(std::move(failure));
  }
  OracleNativeWork retry;
  checked(action(retry));
}
Type sharedNestedType(MLIRContext &context, unsigned depth,
                      StringRef identityNamespace = "accounting.control") {
  Type type = IntegerType::get(&context, 64, IntegerType::Unsigned);
  for (unsigned i = 0; i < depth; ++i) {
    auto identity = data::importVariantIdentity(
        &context,
        VariantIdentity::Tuple{identityNamespace.str(), std::to_string(i)});
    auto arm = data::AlternativeAttr::get(&context,
                                          StringAttr::get(&context, "Record"),
                                          ArrayRef<Type>{type, type});
    type = data::VariantType::get(&context, identity,
                                  ArrayRef<data::AlternativeAttr>{arm});
  }
  return type;
}
void appendUnusedInput(ModuleOp module, Type type) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto entry =
      cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
  Builder builder(module.getContext());
  auto old = entry.getFunctionType();
  SmallVector<Type> inputs(old.getInputs());
  inputs.push_back(type);
  SmallVector<Attribute> owners(entry.getInputRoles().getValue());
  owners.push_back(builder.getArrayAttr({builder.getStringAttr("V")}));
  entry.getBody().front().addArgument(type, entry.getLoc());
  entry->setAttr("function_type", TypeAttr::get(builder.getFunctionType(
                                      inputs, old.getResults())));
  entry->setAttr("input_roles", builder.getArrayAttr(owners));
  require(succeeded(admitStage(module)),
          "unused structured input lost admission");
}
void rejected(ModuleOp original, OracleCommonRealization &actual,
              const OracleRealizationPolicy &policy = {}) {
  // The independently admitted candidate is still well-formed in these cases;
  // it must fail the original-to-candidate reader, not just its type verifier.
  require(succeeded(admitStage(*actual.module)), "mutation lost formation");
  refuses(checkOracleRealization(original, actual, policy),
          "oracle-common-body");
}
pir::LocalCallOp query(Block &arm) {
  for (auto call : arm.template getOps<pir::LocalCallOp>())
    if (call.getSite().ends_with("_query"))
      return call;
  throw std::runtime_error("missing direct selected query");
}
// Use the actual public realization fixture, retaining its virtual oracle
// reference and helpers while selecting just the main entry.
OwningOpRef<ModuleOp> commonEntrySource(MLIRContext &context) {
  auto path = std::filesystem::path(__FILE__).parent_path() /
              "fixtures/oracles/common-entries.mlir";
  auto module = parseSourceFile<ModuleOp>(path.string(), &context);
  require(bool(module), "common entry fixture parse");
  auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
  for (auto entry : make_early_inc_range(
           unit.getBody().front().getOps<pir::MathematicalOp>()))
    if (entry.getSymName() != "main")
      entry.erase();
  require(succeeded(admitStage(*module)), "common entry fixture admission");
  return module;
}
pir::MathematicalOp mainEntry(ModuleOp module) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  return cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
}
OwningOpRef<ModuleOp> sharedControlSource(MLIRContext &context,
                                          unsigned applications = 32) {
  auto module = commonEntrySource(context);
  std::string text = R"mlir(module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1):
)mlir";
  // The stored leaf occurs once; ordinary derivation reads it at each of the
  // wrapper's actual applications, with that invocation's role/input mapping.
  for (unsigned i = 0; i < 64; ++i)
    text += "%v" + std::to_string(i) + " = arith.xori %choice, %choice : i1\n";
  text += R"mlir(
 "protocol.branch"(%choice) ({ "protocol.yield"() : ()->()
 }, { "protocol.yield"() : ()->()
 }) {site="shared_choice",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1)->()
 "protocol.return"() : ()->()
 }) {sym_name="control_leaf",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
 "protocol.func"() ({ ^entry(%choice:i1):
)mlir";
  for (unsigned i = 0; i < applications; ++i)
    text += "protocol.apply @control_leaf(%choice) {site=\"apply_" +
            std::to_string(i) + "\",roles=[\"P\",\"V\"]} : (i1)->()\n";
  text += R"mlir(
 "protocol.return"() : ()->()
 }) {sym_name="control_wrapper",function_type=(i1)->(),roles=["P","V"],input_roles=[["P","V"]],output_roles=[]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() })mlir";
  auto shared = parseSourceString<ModuleOp>(text, &context);
  require(bool(shared), "shared control source parse");
  auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
  auto helpers = cast<pir::ProtocolModuleOp>(shared->getBody()->front());
  // Derive the wrapper first, so the quota control reaches actual helper
  // applications before the leaf's separate top-level derivation.
  for (auto &declaration : helpers.getBody().front())
    unit.getBody().front().push_front(declaration.clone());
  require(succeeded(admitStage(*module)),
          "shared control full source admission");
  return module;
}
void addDormantDeclarations(ModuleOp module, unsigned count,
                            unsigned nameWidth) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto *original = SymbolTable::lookupSymbolIn(unit, "admissible");
  require(bool(original), "missing dormant declaration prototype");
  for (unsigned i = 0; i < count; ++i) {
    auto *copy = original->clone();
    SymbolTable::setSymbolName(copy, "dormant_" + std::to_string(i) +
                                         std::string(nameWidth, 'x'));
    unit.getBody().front().push_back(copy);
  }
  require(succeeded(admitStage(module)), "dormant declarations lost admission");
}
OracleLocalRecipe constantRecipe(MLIRContext &context) {
  auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
  OracleNativeWork work;
  auto recipe = take(oracleLocalRecipe({}, index, work));
  recipe.name = "_local_setup_0";
  recipe.results = take(
      appendOracleLocalInstruction(recipe, {"index.constant", {}, ""}, index,
                                   {}, {IntegerAttr::get(index, 0)}, work));
  return recipe;
}
OracleLocalRecipe distinctBindingRecipe(MLIRContext &context) {
  auto recipe = constantRecipe(context);
  auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
  OracleNativeWork work;
  auto sum = take(appendOracleLocalInstruction(recipe, {"index.add", {}, ""},
                                               index, {0, 0}, {}, work));
  recipe.results = take(appendOracleLocalInstruction(
      recipe, {"index.mul", {}, ""}, index, {sum.front(), 0}, {}, work));
  return recipe;
}
// This lower bound follows MLIR's unsuccessful static lookup: each distinct
// binding must visit every dormant declaration, even before attribute costs.
uint64_t dormantBindingVisits(unsigned declarations, unsigned bindings) {
  return uint64_t(declarations) * bindings;
}
void expandOrdinaryResults(ModuleOp module, unsigned roleCount,
                           unsigned resultCount) {
  auto entry = mainEntry(module);
  Builder builder(module.getContext());
  SmallVector<Attribute> roles{builder.getStringAttr("P"),
                               builder.getStringAttr("V")};
  for (unsigned i = 2; i < roleCount; ++i)
    roles.push_back(builder.getStringAttr("unused_" + std::to_string(i)));
  entry->setAttr("roles", builder.getArrayAttr(roles));
  auto &returned = entry.getBody().front().back();
  require(isa<pir::MathematicalReturnOp>(returned) &&
              returned.getNumOperands() == 1,
          "expected one ordinary fixture result");
  Value answer = returned.getOperand(0);
  SmallVector<Value> values(resultCount, answer);
  SmallVector<Type> types(resultCount, answer.getType());
  SmallVector<Attribute> owners(
      resultCount, builder.getArrayAttr({builder.getStringAttr("V")}));
  returned.setOperands(values);
  entry->setAttr("function_type",
                 TypeAttr::get(builder.getFunctionType(
                     entry.getFunctionType().getInputs(), types)));
  entry->setAttr("output_roles", builder.getArrayAttr(owners));
}
OracleRealizationPolicy remotePolicy(OracleAuthentication authentication) {
  OracleRealizationPolicy policy;
  policy.roots = OracleTableRealization{
      "rows.merkle-keccak256.koala-bear.ext4-binomial3/0"};
  policy.authentication = authentication;
  return policy;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "closed identity regions reuse exact created bodies with live names",
      [&] {
        auto module = commonEntrySource(context);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        OracleNativeWork work;
        OracleEmissionSession session(work, unit);
        OracleEmissionListener listener(work);
        OpBuilder builder(&context, &listener);
        auto index = builder.getIntegerType(64, false);
        unsigned before = work.operations;
        auto first = session.identityRegion(builder, unit.getLoc(),
                                            TypeRange{index, index});
        // Exactly the function, exec.complete and func.return are inserted.
        require(before - work.operations == 3,
                "identity region inserted unexpected operations");
        before = work.operations;
        auto again = session.identityRegion(builder, unit.getLoc(),
                                            TypeRange{index, index});
        require(again == first && before == work.operations,
                "identity reuse rebuilt native IR");
        auto other =
            session.identityRegion(builder, unit.getLoc(), TypeRange{index});
        require(other != first && before - work.operations == 3,
                "identity types were conflated");
        session.finish();
        require(!work.emission && succeeded(verify(*module)),
                "identity session escaped its native scope");
      });
  cases.run(
      "native interface readers pay visits without expanding borrowed types",
      [&] {
        auto module = parseSourceString<ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]}:()->()
}) {profile=#protocol.profile<protocol>}:()->() }
)mlir",
                                                  &context);
        require(bool(module) && succeeded(admitStage(*module)),
                "empty interface admission");
        auto entry = mainEntry(*module);
        // Port reader: two eight-unit headers. Contract reader: eight-unit
        // header, eight-unit inventory header, and one scanned return
        // operation.
        constexpr uint64_t cost = 16 + 17;
        for (uint64_t allowance : {cost - 1, cost}) {
          OracleNativeWork work;
          work.remaining = allowance;
          SymbolTableCollection symbols;
          auto result = oracleVerificationWithWork(work, [&]() -> Error {
            unsigned remaining = 100000;
            if (failed(mathematical::readOraclePortLayout(entry, symbols,
                                                          remaining)) ||
                failed(pir::readContracts(entry, symbols)))
              return error("test-interface");
            return Error::success();
          });
          if (allowance < cost) {
            require(bool(result), "one-less interface allowance succeeded");
            require(namesIdentifier(toString(std::move(result)),
                                    "oracle-common-limit"),
                    "interface refusal identifier");
          } else {
            checked(std::move(result));
            require(!work.remaining && !work.exhausted,
                    "interface exact debit");
          }
        }
      });
  cases.run(
      "publication orders object keys with an independent comparison cost",
      [&] {
        constexpr StringLiteral expected = "{\"a\":null,\"b\":null}";
        // Ownership: three nodes, two fields and two copied key bytes.
        // Formatting: one visit per node, two local ordered-field slots,
        // two field-formatting reservations and two escaped key bytes.
        // Two keys need one comparison of width one, then actual output bytes.
        constexpr uint64_t cost =
            (3 + 2 + 2 * 2) + (3 + 4 * 2 + 2) + (1 + 1) + expected.size();
        for (uint64_t allowance : {cost - 1, cost}) {
          OracleNativeWork work;
          work.remaining = allowance;
          auto result = finishOraclePublication(
              json::Object{{"b", nullptr}, {"a", nullptr}}, work);
          if (allowance < cost)
            refuses(std::move(result), "oracle-common-limit");
          else {
            auto actual = take(std::move(result));
            require(actual.bytes == expected && !work.remaining &&
                        !work.exhausted,
                    "publication ordering escaped its exact debit");
          }
        }
      });
  cases.run(
      "publication streams once with an independent escaped-byte cost", [&] {
        constexpr StringLiteral expected = "{\"x\":\"a\\n\"}";
        // Two JSON nodes, one object field, one key byte, two input string
        // bytes and one local ordered-field slot, plus each byte of the
        // independently specified serialized spelling. Ownership costs seven
        // constant slots plus two copies/validation widths of key and value.
        constexpr uint64_t cost =
            (2 + 1 + 2 * 1 + 2 * 2) + (2 + 4 + 1 + 2) + expected.size();
        for (uint64_t allowance : {cost - 1, cost}) {
          OracleNativeWork work;
          work.remaining = allowance;
          auto result =
              finishOraclePublication(json::Object{{"x", "a\n"}}, work);
          if (allowance < cost)
            refuses(std::move(result), "oracle-common-limit");
          else {
            auto actual = take(std::move(result));
            require(actual.bytes == expected && work.remaining == 0 &&
                        !work.exhausted,
                    "publication changed spelling or omitted actual work");
          }
        }
      });
  // Pinned SmallVector starts at capacity zero and grows to 2*c+1. This
  // independent capacity sum counts relocated fixed-size decoding pieces.
  auto relocatedSlots = [](uint64_t count) {
    uint64_t total = 0;
    for (uint64_t capacity = 1; capacity < count; capacity = 2 * capacity + 1)
      total += capacity;
    return total;
  };
  auto pieceReservation = [&](uint64_t count) {
    // Piece insertion, fixed-size relocation and one assembly visit per piece.
    return 2 * count + relocatedSlots(count);
  };
  cases.run("borrowed record JSON has independent exact reservations", [&] {
    // Independent token/grammar counts. Each wire byte is lexed once;
    // every token and value gets one slot, every array element another.
    // Immediate array inventory occurs during the charged token insertion.
    // Strings separately pay UTF-8 construction, and object keys pay the
    // actual constructor/hash/comparison widths before insertion.
    std::vector<std::pair<std::string, uint64_t>> texts{
        {"0", 1 + (1) + 1},
        {std::string(64, '[') + "0" + std::string(64, ']'),
         129 + (129) + 65 + 64},
        {R"json({"x":"\uD83D\uDE00","n":18446744073709551615})json", 0},
        {" \n {\"x\":0} \t", 0},
        {"[0,0,0,0,0]", 11 + (11) + 6 + 5}};
    texts[2].second =
        texts[2].first.size() + (9) + 3 + 10 + 15 + pieceReservation(1);
    texts[3].second = texts[3].first.size() + (5) + 2 + 1 + 6;
    for (const auto &[text, cost] : texts) {
      for (uint64_t allowance : {cost - 1, cost}) {
        OracleNativeWork work;
        work.remaining = allowance;
        auto result = parseOracleRecordWithWork(text, work);
        if (allowance < cost)
          refuses(std::move(result), "oracle-common-limit");
        else {
          take(std::move(result));
          require(work.remaining == 0 && !work.exhausted,
                  "lexical reservation changed");
        }
      }
    }
    for (StringRef text : {R"json("\uD800")json", R"json("\uDC00")json",
                           R"json("\uD800\u0041")json", "\"\xc0\xaf\"",
                           R"json({"x":0,"\u0078":1})json", "01", "1e0"}) {
      OracleNativeWork work;
      refuses(parseOracleRecordWithWork(text, work),
              "oracle-realization-record");
    }
    for (StringRef text :
         {R"json({"a":[true,false,null,0,18446744073709551615]})json",
          R"json({"\u006bey":"a\b\f\n\r\t\/\\\""})json",
          "\"\xe2\x82\xac\xf0\x9f\x98\x80\"", "{}", "[]"}) {
      OracleNativeWork work;
      auto actual = take(parseOracleRecordWithWork(text, work));
      auto expected = take(
          parseNaturalJson(text, 32 * 1024 * 1024, 64, "invalid", "limit"));
      require(equalNaturalJson(actual, expected),
              "record JSON disagrees with independent natural parser");
    }
    for (StringRef text :
         {"[0,]", "{\"x\":0,}", "[true false]", "18446744073709551616", "-0",
          "+0", "1.0", "\"\xed\xa0\x80\"", "\"\xf4\x90\x80\x80\"",
          R"json({"x":0,"x":1})json"}) {
      OracleNativeWork work;
      refuses(parseOracleRecordWithWork(text, work),
              "oracle-realization-record");
    }
    auto invalidUTF8 = json::parse("\"\xc0\xaf\"");
    require(!invalidUTF8, "native JSON parser accepted invalid UTF-8");
    consumeError(invalidUTF8.takeError());
    OracleNativeWork work;
    refuses(parseOracleRecordWithWork("01" + std::string(65, '['), work),
            "oracle-realization-record-limit");
  });
  for (bool objectKey : {false, true})
    for (unsigned nesting : {0u, 3u})
      cases.run(
          std::string("65-element JSON array retains first owned ") +
              (objectKey ? "object key" : "string") +
              (nesting ? " in nested subtrees" : ""),
          [&] {
            const uint64_t width = objectKey ? 100000 : 180000;
            std::string spelling(width - 1, 'a');
            spelling += "\\u0061";
            std::string first =
                objectKey ? "{\"" + spelling + "\":0}" : "\"" + spelling + "\"";
            // Wrap the owned value in arrays: relocating an outer Value would
            // otherwise recursively copy every owned descendant.
            first =
                std::string(nesting, '[') + first + std::string(nesting, ']');
            std::string text = "[" + first;
            for (unsigned i = 0; i < 64; ++i)
              text += ",0";
            text += ']';
            const uint64_t tokens = (objectKey ? 135 : 131) + 2 * nesting;
            uint64_t cost = text.size() + (tokens) + (objectKey ? 67 : 66) +
                            nesting + 65 + nesting + 2 * width +
                            pieceReservation(2);
            if (objectKey)
              cost += 1 + 3 * width + 2 + width + 1;
            if (!nesting)
              require(text.size() == (objectKey ? 100141 : 180137) &&
                          cost == (objectKey ? 700417 : 540404),
                      "preserved 65-element JSON counterexample changed");
            for (uint64_t allowance : {cost - 1, cost, uint64_t(1000000)}) {
              OracleNativeWork work;
              const unsigned workInitialVisits = work.operations;
              work.remaining = allowance;
              auto result = parseOracleRecordWithWork(text, work);
              if (allowance < cost) {
                refuses(std::move(result), "oracle-common-limit");
                require(work.exhausted && !work.remaining && !work.charge(0),
                        "array reservation exhaustion was not sticky");
                refuses(parseOracleRecordWithWork("[]", work),
                        "oracle-common-limit");
                continue;
              }
              auto actual = take(std::move(result));
              auto *array = actual.getAsArray();
              require(array && array->size() == 65 &&
                          work.remaining == allowance - cost &&
                          !work.exhausted &&
                          work.operations == workInitialVisits,
                      "array reservation omitted independently counted work");
              const json::Value *owned = &array->front();
              for (unsigned i = 0; i < nesting; ++i) {
                auto *nested = owned->getAsArray();
                require(nested && nested->size() == 1,
                        "owned subtree shape changed");
                owned = &nested->front();
              }
              StringRef name;
              if (objectKey) {
                auto *object = owned->getAsObject();
                require(object && object->size() == 1,
                        "owned object disappeared during array assembly");
                name = object->begin()->first;
              } else {
                auto value = owned->getAsString();
                require(bool(value), "owned string disappeared");
                name = *value;
              }
              require(
                  name.size() == width && name == std::string(width, 'a'),
                  "owned array spelling did not survive parser destruction");
              // This mutation is after parsing: escaped spellings must own all
              // their bytes even when nested under a reserved array.
              text[objectKey ? nesting + 3 : nesting + 2] = 'b';
              require(name.front() == 'a',
                      "escaped array string borrowed input");
              text[objectKey ? nesting + 3 : nesting + 2] = 'a';
            }
          });
  for (unsigned elements : {0u, 1u, 2u, 3u, 4u, 7u, 8u, 15u, 16u, 31u, 32u, 63u,
                            64u, 65u, 127u, 128u})
    cases.run(
        "JSON token and array reservation at " + std::to_string(elements) +
            " elements",
        [&] {
          std::string text = "[";
          for (unsigned i = 0; i < elements; ++i)
            text += i ? ",0" : "0";
          text += ']';
          uint64_t tokens = elements ? 2 * elements + 1 : 2;
          uint64_t cost = text.size() + (tokens) + elements + 1 + elements;
          for (uint64_t allowance : {cost - 1, cost}) {
            OracleNativeWork work;
            const unsigned workInitialVisits = work.operations;
            work.remaining = allowance;
            auto result = parseOracleRecordWithWork(text, work);
            if (allowance < cost) {
              refuses(std::move(result), "oracle-common-limit");
              require(work.exhausted && !work.remaining && !work.charge(0),
                      "token or array exhaustion was not sticky");
            } else {
              auto actual = take(std::move(result));
              require(actual.getAsArray()->size() == elements &&
                          !work.remaining && !work.exhausted &&
                          work.operations == workInitialVisits,
                      "token growth or array inventory debit changed");
            }
          }
        });
  for (unsigned escapes : {1u, 2u, 3u, 4u, 8u, 16u, 65u})
    cases.run("escaped JSON assembles one decoded buffer for " +
                  std::to_string(escapes) + " escapes",
              [&] {
                std::string text = "\"", expected;
                for (unsigned i = 0; i < escapes; ++i) {
                  text += std::string(1024 + i, 'a') + "\\u0062";
                  expected += std::string(1024 + i, 'a') + 'b';
                }
                text += '\"';
                uint64_t cost = text.size() + (1) + 1 + 2 * expected.size() +
                                pieceReservation(2 * escapes);
                for (uint64_t allowance : {cost - 1, cost, uint64_t(1000000)}) {
                  OracleNativeWork work;
                  const unsigned workInitialVisits = work.operations;
                  work.remaining = allowance;
                  auto result = parseOracleRecordWithWork(text, work);
                  if (allowance < cost) {
                    refuses(std::move(result), "oracle-common-limit");
                    require(work.exhausted && !work.remaining &&
                                !work.charge(0),
                            "decoded-buffer exhaustion was not sticky");
                  } else {
                    auto actual = take(std::move(result));
                    require(actual.getAsString() == expected &&
                                work.remaining == allowance - cost &&
                                !work.exhausted &&
                                work.operations == workInitialVisits,
                            "decoded spans changed spelling or reservation");
                  }
                }
              });
  cases.run(
      "escaped JSON scalar boundaries have an exact decoded reservation", [&] {
        constexpr StringLiteral text =
            R"json("\u0000\u007f\u0080\u07ff\u0800\uffff\ud7ff\ue000\ud800\udc00\udbff\udfff")json";
        // Eight BMP scalars and two surrogate pairs encode to these exact
        // bytes. Spell the boundary scalar independently of a second parser.
        constexpr char expected[] =
            "\0\x7f\xc2\x80\xdf\xbf\xe0\xa0\x80\xef\xbf\xbf\xed\x9f\xbf"
            "\xee\x80\x80\xf0\x90\x80\x80\xf4\x8f\xbf\xbf";
        uint64_t cost = text.size() + 1 + 1 + 2 * 26 + pieceReservation(10);
        for (uint64_t allowance : {cost - 1, cost}) {
          OracleNativeWork work;
          const unsigned workInitialVisits = work.operations;
          work.remaining = allowance;
          auto result = parseOracleRecordWithWork(text, work);
          if (allowance < cost) {
            refuses(std::move(result), "oracle-common-limit");
            require(work.exhausted && !work.remaining && !work.charge(0),
                    "scalar decoding exhaustion was not sticky");
          } else {
            auto actual = take(std::move(result));
            require(actual.getAsString()->size() == 26 &&
                        *actual.getAsString() ==
                            StringRef(expected, sizeof(expected) - 1) &&
                        !work.remaining && !work.exhausted &&
                        work.operations == workInitialVisits,
                    "Unicode scalar assembly changed spelling or debit");
          }
        }
      });
  cases.run("reserved arrays preserve borrowed input addresses", [&] {
    std::string text = R"json([["first"],{"key":"second"}])json";
    OracleNativeWork work;
    const unsigned workInitialVisits = work.operations;
    auto actual = take(parseOracleRecordWithWork(text, work));
    auto *array = actual.getAsArray();
    auto first = array->front().getAsArray()->front().getAsString();
    auto *object = array->back().getAsObject();
    auto second = object->getString("key");
    require(first && second &&
                first->data() == text.data() + text.find("first") &&
                second->data() == text.data() + text.find("second") &&
                StringRef(object->begin()->first).data() ==
                    text.data() + text.find("key") &&
                !work.exhausted && work.operations == workInitialVisits,
            "array or stable-token construction detached borrowed input");
  });
  cases.run(
      "JSON inventory preserves wire depth and exhaustion precedence", [&] {
        for (const auto &prefix : {std::string("01"), std::string("\"\\q\""),
                                   std::string("// ignored [\n")}) {
          std::string text = prefix + std::string(65, '[');
          OracleNativeWork enough;
          refuses(parseOracleRecordWithWork(text, enough),
                  "oracle-realization-record-limit");
          OracleNativeWork shortWork;
          shortWork.remaining = text.size();
          refuses(parseOracleRecordWithWork(text, shortWork),
                  "oracle-common-limit");
          require(shortWork.exhausted && !shortWork.remaining &&
                      !shortWork.charge(0),
                  "lexical exhaustion lost precedence over later depth");
        }
        for (StringRef text : {"[0,]", "[0 0]", "[{]}", "[true,false,]",
                               "\"\\uD800\"", "\"\\q\""}) {
          OracleNativeWork work;
          refuses(parseOracleRecordWithWork(text, work),
                  "oracle-realization-record");
        }
        OracleNativeWork wire;
        wire.remaining = 0;
        refuses(parseOracleRecordWithWork(
                    std::string(32 * 1024 * 1024 + 1, ' '), wire),
                "oracle-realization-record-limit");
        require(!wire.exhausted,
                "wire ceiling consumed the cumulative allowance");
        refuses(parseOracleRecordWithWork("[]", wire), "oracle-common-limit");
        require(wire.exhausted && !wire.remaining && !wire.charge(0),
                "bounded-wire exhaustion was not sticky");
        constexpr StringLiteral text = "[0]";
        uint64_t cost = text.size() + (3) + 2 + 1;
        OracleNativeWork shared;
        shared.remaining = 2 * cost - 1;
        take(parseOracleRecordWithWork(text, shared));
        refuses(parseOracleRecordWithWork(text, shared), "oracle-common-limit");
        refuses(parseOracleRecordWithWork("0", shared), "oracle-common-limit");
        require(shared.exhausted && !shared.remaining && !shared.charge(0),
                "a subsequent parse refilled the shared allowance");
      });
  for (bool escaped : {false, true})
    for (unsigned fields : {47u, 48u, 95u, 96u})
      cases.run(
          "long first JSON key at " + std::to_string(fields) +
              (escaped ? " fields with owned spelling" : " fields"),
          [&] {
            const uint64_t width = escaped ? 100000 : 180000;
            std::string key(width, 'a');
            std::string text =
                "{\"" + (escaped ? key.substr(1) + "\\u0061" : key) + "\":0";
            for (unsigned i = 0; i + 1 < fields; ++i) {
              auto digits = std::to_string(i);
              text += ",\"k" + std::string(3 - digits.size(), '0') + digits +
                      "\":0";
            }
            text += '}';
            // Independent wire/token/value and constructor counts. The first
            // decoded key has the width above; every later key has width four.
            uint64_t keyBytes = width + 4 * (fields - 1);
            uint64_t ownedBytes = escaped ? width : 0;
            uint64_t cost = text.size() + (4 * fields + 1) + (fields + 1) +
                            keyBytes + ownedBytes + fields + keyBytes +
                            2 * ownedBytes +
                            (escaped ? pieceReservation(2) : 0);
            // First insertion: two initialized occupancy words, one hash and
            // one terminating lookup bucket. At fields 48/96, DenseMap rehashes
            // all prior keys, copies each owned spelling, and repeats the new
            // lookup.
            cost += 2 + width + 1;
            for (uint64_t prior = 1; prior < fields; ++prior) {
              uint64_t oldWords = prior < 48 ? 2 : 4;
              uint64_t lookup = 4 + prior + 1 + 4 * (prior - 1);
              cost += oldWords + prior + lookup;
              if (prior == 47 || prior == 95)
                cost += 3 * oldWords + prior + prior * (prior + 1) / 2 + width +
                        4 * (prior - 1) + ownedBytes + lookup;
            }
            for (uint64_t allowance : {cost - 1, cost}) {
              OracleNativeWork work;
              const unsigned workInitialVisits = work.operations;
              work.remaining = allowance;
              auto result = parseOracleRecordWithWork(text, work);
              if (allowance < cost) {
                refuses(std::move(result), "oracle-common-limit");
                require(work.exhausted && !work.remaining && !work.charge(0),
                        "JSON insertion exhaustion was not sticky");
                refuses(parseOracleRecordWithWork("{}", work),
                        "oracle-common-limit");
              } else {
                auto actual = take(std::move(result));
                auto *object = actual.getAsObject();
                require(
                    object && object->size() == fields &&
                        object->getInteger(key) == 0 && !work.remaining &&
                        !work.exhausted && work.operations == workInitialVisits,
                    "long-key JSON escaped its independent exact reservation");
                for (const auto &field : *object) {
                  StringRef name = field.first;
                  if (name.size() == width)
                    require((name.data() == text.data() + 2) == !escaped,
                            "JSON key ownership changed across parsing");
                }
              }
            }
            // Retain the original growth boundary under an explicit smaller
            // allowance, independently of the public default.
            constexpr uint64_t growthAllowance = 1000000;
            OracleNativeWork growth;
            growth.remaining = growthAllowance;
            auto result = parseOracleRecordWithWork(text, growth);
            if (fields == 96) {
              refuses(std::move(result), "oracle-common-limit");
              require(cost > growthAllowance && growth.exhausted &&
                          !growth.remaining && !growth.charge(0),
                      "second long-key growth escaped the smaller allowance");
              refuses(parseOracleRecordWithWork("{}", growth),
                      "oracle-common-limit");
            } else {
              take(std::move(result));
              require(growth.remaining == growthAllowance - cost &&
                          !growth.exhausted,
                      "long-key positive lost the smaller allowance");
            }
            OracleNativeWork defaults;
            const uint64_t initialWork = defaults.remaining;
            const unsigned initialVisits = defaults.operations;
            auto actual = take(parseOracleRecordWithWork(text, defaults));
            auto *object = actual.getAsObject();
            require(object && cost <= initialWork &&
                        defaults.remaining == initialWork - cost &&
                        !defaults.exhausted &&
                        defaults.operations == initialVisits &&
                        object->size() == fields &&
                        object->getInteger(key) == 0,
                    "default JSON parsing changed content or accounting");
            if (!escaped && fields == 96) {
              require(text.size() == 180861,
                      "long-key source-derived counterexample changed");
              OracleNativeWork work;
              work.remaining = 902959;
              refuses(parseOracleRecordWithWork(text, work),
                      "oracle-common-limit");
              require(work.exhausted && !work.remaining && !work.charge(0),
                      "long-key growth escaped the previous reservation");
            }
          });
  for (bool escaped : {false, true})
    cases.run(
        escaped ? "owned JSON keys survive colliding lookups and growth"
                : "JSON keys reserve worst-case colliding lookups",
        [&] {
          constexpr uint64_t fields = 96, width = 8;
          std::vector<std::string> keys;
          // All keys start in bucket zero at capacities 64, 128 and 256. This
          // realizes the full linear-probe and equal-length comparison bounds,
          // including both triangular growth-probe reservations.
          for (unsigned i = 0; i < 1000000 && keys.size() != fields; ++i) {
            auto digits = std::to_string(i);
            std::string key =
                "k" + std::string(7 - digits.size(), '0') + digits;
            if (!(llvm::DenseMapInfo<StringRef>::getHashValue(key) & 255))
              keys.push_back(std::move(key));
          }
          require(keys.size() == fields,
                  "could not construct colliding JSON keys");
          std::string text = "{";
          for (unsigned i = 0; i < fields; ++i) {
            if (i)
              text += ',';
            text += "\"" +
                    (escaped && !i ? "\\u006b" + keys[i].substr(1) : keys[i]) +
                    "\":0";
          }
          text += '}';
          uint64_t ownedBytes = escaped ? width : 0;
          uint64_t cost = text.size() + (4 * fields + 1) + (fields + 1) +
                          width * fields + ownedBytes + fields +
                          width * fields + 2 * ownedBytes + 2 + width + 1 +
                          (escaped ? pieceReservation(2) : 0);
          for (uint64_t prior = 1; prior < fields; ++prior) {
            uint64_t oldWords = prior < 48 ? 2 : 4;
            uint64_t lookup = width + prior + 1 + width * prior;
            cost += oldWords + prior + lookup;
            if (prior == 47 || prior == 95)
              cost += 3 * oldWords + prior + prior * (prior + 1) / 2 +
                      width * prior + ownedBytes + lookup;
          }
          for (uint64_t allowance : {cost - 1, cost}) {
            OracleNativeWork work;
            const unsigned workInitialVisits = work.operations;
            work.remaining = allowance;
            auto result = parseOracleRecordWithWork(text, work);
            if (allowance < cost) {
              refuses(std::move(result), "oracle-common-limit");
              require(work.exhausted && !work.remaining && !work.charge(0),
                      "colliding JSON insertion exhaustion was not sticky");
              refuses(parseOracleRecordWithWork("{}", work),
                      "oracle-common-limit");
            } else {
              auto actual = take(std::move(result));
              auto expected = take(json::parse(text));
              require(equalNaturalJson(actual, expected) && !work.remaining &&
                          !work.exhausted &&
                          work.operations == workInitialVisits,
                      "colliding JSON keys escaped their exact reservation");
            }
          }
          text.pop_back();
          text += ",\"\\u006b" + keys.front().substr(1) + "\":1}";
          OracleNativeWork work;
          refuses(parseOracleRecordWithWork(text, work),
                  "oracle-realization-record");
        });
  cases.run("local helper insertion count is independently eight", [&] {
    constexpr unsigned expectedOperations = 8;
    for (unsigned allowance :
         {2u, expectedOperations - 1, expectedOperations}) {
      auto module = commonEntrySource(context);
      auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
      unsigned before = 0;
      module->walk([&](Operation *) { ++before; });
      OracleNativeWork work;
      work.operations = allowance;
      auto result = emitOracleLocalHelper(unit, constantRecipe(context), work);
      if (allowance < expectedOperations) {
        refuses(std::move(result), "oracle-common-limit");
        require(work.exhausted && !work.charge(0),
                "missing sticky insertion refusal");
      } else {
        auto helper = take(std::move(result));
        unsigned after = 0, blocks = 0;
        module->walk([&](Operation *op) {
          ++after;
          for (auto &region : op->getRegions())
            blocks += region.getBlocks().size();
        });
        require(after - before == expectedOperations && work.operations == 0 &&
                    helper.getBody().getBlocks().size() == 3 && blocks >= 3,
                "native plumbing operation/block count changed");
        require(succeeded(admitStage(*module)),
                "exact operation allowance lost admission");
      }
    }
  });
  cases.run("Merkle operation debit equals actual inserted operations", [&] {
    auto original = source(context);
    pir::OracleKindAttr kind;
    original->walk([&](pir::OracleSendOp send) {
      kind = send.getHandle().getType().getKind();
    });
    constexpr StringLiteral scheme =
        "rows.merkle-keccak256.koala-bear.ext4-binomial3/0";
    auto emit = [&](ModuleOp module, OracleNativeWork &work) {
      return emitOracleMerkleWithWork(module, kind, scheme,
                                      OracleLeafGrouping::Individual,
                                      OracleLeafOrder::BitReversed, work);
    };
    auto count = [](ModuleOp module) {
      unsigned result = 0;
      module->walk([&](Operation *) { ++result; });
      return result;
    };
    auto probe = OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
    unsigned before = count(*probe);
    OracleNativeWork measured;
    const unsigned measuredInitialVisits = measured.operations;
    take(emit(*probe, measured));
    unsigned inserted = count(*probe) - before;
    require(inserted > 0 &&
                measuredInitialVisits - measured.operations == inserted,
            "Merkle retained a synthetic operation debit");
    // Repeat on the same candidate: both sets and new live symbol lookups
    // count.
    before = count(*probe);
    unsigned operations = measured.operations;
    take(emit(*probe, measured));
    require(operations - measured.operations == count(*probe) - before,
            "second Merkle set omitted or duplicated native insertions");
    for (unsigned allowance : {1u, 16u, 64u, inserted - 1, inserted}) {
      auto candidate =
          OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
      OracleNativeWork work;
      work.operations = allowance;
      auto frozen = printed(*candidate);
      if (allowance == inserted) {
        take(emit(*candidate, work));
        require(work.operations == 0 && !work.exhausted,
                "exact Merkle operation allowance");
      } else {
        refuses(emit(*candidate, work), "oracle-common-limit");
        require(work.exhausted && !work.emission &&
                    printed(*candidate) == frozen &&
                    succeeded(admitStage(*candidate)),
                "listener cancellation retained a malformed partial candidate");
      }
    }
  });
  cases.run("virtual empty slices pay query count times full inventory", [&] {
    auto fixture = [&](unsigned instructions, unsigned queries, bool nested) {
      std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [i1, 16:ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/slice-accounting",revision="0",
   signature=(!data.sequence<i1>)->i1,purposes=["witness"]}
 "protocol.oracle"() ({
 ^bb0(%source:!H,%position:ui64):
 %enabled = "data.index_equal"(%position,%position) : (ui64,ui64)->i1
)mlir";
      for (unsigned i = 0; i < instructions; ++i) {
        auto name = " %unused" + std::to_string(i);
        if (!nested)
          text += name + " = \"data.index\"() {value=0:ui64} : ()->ui64\n";
        else
          text += name + R"mlir( = "data.branch"(%enabled,%position) ({
          ^then(%p:ui64):
            %zero = "data.index"() {value=0:ui64} : ()->ui64
            "data.yield"(%p) : (ui64)->()
          }, {
          ^else(%p:ui64):
            %zero = "data.index"() {value=0:ui64} : ()->ui64
            "data.yield"(%p) : (ui64)->()
          }) {alternatives=["then","else"]} : (i1,ui64)->ui64
)mlir";
      }
      for (unsigned i = 0; i < queries; ++i)
        text +=
            " %answer" + std::to_string(i) +
            " = \"protocol.oracle_query\"(%source,%position) {site=\"query" +
            std::to_string(i) + "\"} : (!H,ui64)->i1\n";
      text += R"mlir(
 "protocol.oracle_yield"(%answer0) : (i1)->()
 }) {sym_name="many",function_type=(!H,ui64)->i1,kind=#K,
 shape_arguments={},shape_bounds={},admissibility=@admissible}:()->()
 }) {profile=#protocol.profile<protocol>}:()->() }
)mlir";
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module) && succeeded(verify(*module)),
              "slice fixture structure");
      // Exercise nested total-region copying at its private planner seam.
      // Public virtual-body admission still forbids regions; the flat case is
      // an admitted public subject.
      if (!nested)
        require(succeeded(admitStage(*module)), "slice fixture admission");
      return module;
    };
    for (bool nested : {false, true})
      for (auto [instructions, queries] :
           {std::pair{128u, 8u}, std::pair{4096u, 512u}}) {
        auto module = fixture(instructions, queries, nested);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        auto definition =
            *unit.getBody().front().getOps<pir::OracleDefinitionOp>().begin();
        OracleVirtualFunctionWork work;
        const uint64_t initialWork = work.getWork().remaining;
        auto plan = planOracleVirtualFunctions(definition, work);
        // Owners visit the branch and its four nested instructions. The
        // selection scan visits each outer instruction once per query.
        uint64_t lowerBound =
            (nested ? 6 : 2) * uint64_t(instructions) * queries;
        if (instructions == 4096) {
          require(lowerBound > initialWork,
                  "large slice inventory no longer exceeds the default");
          refuses(std::move(plan), "oracle-common-limit");
          require(work.getWork().exhausted,
                  "empty slices escaped their independent visit lower bound");
        } else {
          auto actual = take(std::move(plan));
          require(
              actual.queries.size() == queries &&
                  actual.queries.front().position.block.instructions.empty() &&
                  initialWork - work.getWork().remaining >= lowerBound,
              "empty dependency slices omitted full inventory scans");
        }
      }
  });
  cases.run(
      "ordinary admission charges native DAG formation before publication",
      [&] {
        auto module = commonEntrySource(context);
        appendUnusedInput(*module, sharedNestedType(context, 10));
        auto before = printed(*module);
        bool threading = context.isMultithreadingEnabled();
        cumulativeBoundary([&](OracleNativeWork &work) -> Error {
          auto preflight = OracleNativeSourcePreflight::read(*module, work);
          if (!preflight)
            return preflight.takeError();
          if (failed(preflight->admit()))
            return error(work.exhausted ? "oracle-common-limit"
                                        : "test-admission");
          return Error::success();
        });
        require(context.isMultithreadingEnabled() == threading,
                "admission did not restore threading after boundary checks");
        OracleNativeWork work;
        auto preflight = take(OracleNativeSourcePreflight::read(*module, work));
        // Give the operation traversal its independent structural width, then
        // only eight units for native formation. Reducing credit never refunds
        // work.
        uint64_t traversal = 0;
        module->walk([&](Operation *op) {
          traversal += 1 + op->getNumOperands() + op->getNumResults() +
                       op->getAttrs().size() + op->getNumRegions();
          for (auto &region : op->getRegions())
            for (auto &block : region)
              traversal += 1 + block.getNumArguments();
        });
        work.remaining = traversal + 1 + 8;
        require(failed(preflight.admit()) && work.exhausted && !work.charge(0),
                "ordinary admission escaped the formation allowance");
        require(context.isMultithreadingEnabled() == threading,
                "cancelled admission did not restore threading");
        require(printed(*module) == before,
                "formation cancellation mutated the admitted source");
      });
  cases.run("primitive reader kind formation uses the caller allowance", [&] {
    auto module = commonEntrySource(context);
    pir::OracleKindAttr ordinary;
    module->walk([&](pir::OracleSendOp send) {
      ordinary = send.getHandle().getType().getKind();
    });
    auto helper = take(emitOracleTableRead(*module, ordinary));
    OracleNativeWork work;
    auto borrow = take(OracleVerificationContext::read(*module, work));
    auto deep = pir::OracleKindAttr::get(
        &context, "table",
        ArrayAttr::get(&context,
                       {TypeAttr::get(sharedNestedType(context, 10))}));
    auto before = printed(*module);
    work.remaining = 8;
    auto failure = checkOracleTableRead(borrow, helper, deep);
    require(
        bool(failure) &&
            namesIdentifier(toString(std::move(failure)),
                            "oracle-common-limit") &&
            work.exhausted,
        "primitive kind formation continued outside the remaining allowance");
    require(printed(*module) == before,
            "reader cancellation changed its subject");
  });
  cases.run(
      "immutable primitive facts require their complete expected kind", [&] {
        auto module = commonEntrySource(context);
        pir::OracleKindAttr ordinary;
        module->walk([&](pir::OracleSendOp send) {
          ordinary = send.getHandle().getType().getKind();
        });
        auto helper = take(emitOracleTableRead(*module, ordinary));
        OracleNativeWork work;
        auto reader = take(OracleVerificationContext::read(*module, work));
        checked(checkOracleTableRead(reader, helper, ordinary));
        auto other = pir::OracleKindAttr::get(
            &context, "table",
            ArrayAttr::get(&context,
                           {TypeAttr::get(IntegerType::get(&context, 1))}));
        auto mismatch = checkOracleTableRead(reader, helper, other);
        require(bool(mismatch) && namesIdentifier(toString(std::move(mismatch)),
                                                  "oracle-table-read-body"),
                "a checked helper was reused for another expected kind");
        checked(checkOracleTableRead(reader, helper, ordinary));
      });
  for (bool outer : {false, true})
    for (unsigned trips : {0u, 1u, 3u})
      for (unsigned mode : {0u, 1u, 2u})
        cases.run(
            Twine("selected native source, outer=") + Twine(unsigned(outer)) +
                ", trips=" + Twine(trips) + ", policy=" + Twine(mode),
            [&] {
              auto original = source(context, trips, outer);
              auto before = printed(*original);
              auto policy =
                  mode ? remotePolicy(mode == 1
                                          ? OracleAuthentication::PerQuery
                                          : OracleAuthentication::AtomicBlocks)
                       : OracleRealizationPolicy{};
              auto actual = take(emitOracleRealization(*original, policy));
              auto facts =
                  take(checkOracleRealization(*original, actual, policy));
              require(printed(*original) == before,
                      "materialization changed original");
              require(actual.original && printed(*actual.original) == before,
                      "immutable admitted source was not retained");
              require(facts.entries.size() == 1,
                      "missing source-selected facts");
              auto selected = branch(*actual.module);
              require(selected->getNumRegions() == 2, "dormant arm was pruned");
              require(selected.getNumResults() > 1,
                      "selected stores were not joined");
              auto choices =
                  take(resolveOracleRealizationSelection(*original, policy));
              auto requirements =
                  take(oracleRequirements(*original, "main", choices));
              require(requirements.storage.constructors.size() == 2,
                      "lost alternate constructor");
              for (auto &constructor : requirements.storage.constructors)
                require(constructor.repeatDepth == unsigned(outer),
                        "branch arm became a dynamic coordinate");
              auto &entry = actual.entries.front();
              auto read = take(readOracleCommon(
                  *original, *actual.module, "main", requirements,
                  entry.controllers, entry.allocators, entry.merkle,
                  policy.authentication, entry.remotes, entry.batches));
              require(read.queryBlocks.size() ==
                          facts.entries.front().queryBlocks.size(),
                      "record reader lost actual source batches");
            });
  auto mutation =
      [&](StringRef name,
          llvm::function_ref<void(OracleCommonRealization &)> change) {
        cases.run(name, [&] {
          auto original = source(context);
          auto actual = take(emitOracleRealization(*original));
          take(checkOracleRealization(*original, actual));
          change(actual);
          rejected(*original, actual);
        });
      };
  mutation("same-type capture order does not grant source authority",
           [&](auto &actual) {
             auto selected = branch(*actual.module);
             Value left = selected->getOperand(1),
                   right = selected->getOperand(2);
             selected->setOperand(1, right);
             selected->setOperand(2, left);
           });
  mutation("dormant arm payload cannot be replaced by equal-typed capture",
           [&](auto &actual) {
             auto &arm = branch(*actual.module)->getRegion(1).front();
             auto call = query(arm);
             require(call->getOperand(1) == arm.getArgument(0),
                     "fixture lost selected payload");
             call->setOperand(1, arm.getArgument(3));
           });
  mutation(
      "arm query cannot move across the selected boundary", [&](auto &actual) {
        auto selected = branch(*actual.module);
        auto &left = selected->getRegion(0).front();
        auto &right = selected->getRegion(1).front();
        auto call = query(right);
        auto yielded = cast<pir::ProtocolYieldOp>(left.back());
        SmallVector<Value> operands{yielded.getOperand(0), left.getArgument(0)};
        // Controllers consume immutable stores in their declared order. The
        // left yield's appended successors provide the exact same types, but a
        // different arm and authority. Retain the moved operation's site and
        // callee.
        append_range(operands, yielded.getOperands().drop_front());
        SmallVector<Value> originalOperands(call.getInputs());
        for (unsigned i = 2; i < originalOperands.size(); ++i) {
          auto type = originalOperands[i].getType();
          auto found = llvm::find_if(
              operands, [&](Value value) { return value.getType() == type; });
          require(found != operands.end(), "missing typed moved store");
          originalOperands[i] = *found;
        }
        originalOperands[0] = operands[0];
        originalOperands[1] = operands[1];
        call->setOperands(originalOperands);
        call->moveBefore(&left.back());
      });
  mutation("construction, captures and queries cannot exchange arms",
           [&](auto &actual) {
             auto selected = branch(*actual.module);
             Region saved;
             saved.takeBody(selected->getRegion(0));
             selected->getRegion(0).takeBody(selected->getRegion(1));
             selected->getRegion(1).takeBody(saved);
           });
  mutation("an updated store cannot yield its incoming same-type seed",
           [&](auto &actual) {
             auto selected = branch(*actual.module);
             auto &arm = selected->getRegion(0).front();
             auto yielded = cast<pir::ProtocolYieldOp>(arm.back());
             for (unsigned i = 1; i < yielded.getNumOperands(); ++i)
               for (auto argument : arm.getArguments())
                 if (argument.getType() == yielded.getOperand(i).getType() &&
                     argument != yielded.getOperand(i)) {
                   yielded->setOperand(i, argument);
                   return;
                 }
             throw std::runtime_error("missing changed store successor");
           });
  mutation("query must read the updated store rather than its same-type seed",
           [&](auto &actual) {
             auto &arm = branch(*actual.module)->getRegion(1).front();
             auto call = query(arm);
             for (unsigned i = 2; i < call.getNumOperands(); ++i)
               for (auto argument : arm.getArguments())
                 if (argument.getType() == call.getOperand(i).getType() &&
                     argument != call.getOperand(i)) {
                   call->setOperand(i, argument);
                   return;
                 }
             throw std::runtime_error("missing queried store successor");
           });
  mutation(
      "selected query site is checked on the actual call", [&](auto &actual) {
        auto &arm = branch(*actual.module)->getRegion(1).front();
        query(arm)->setAttr("site", StringAttr::get(&context, "moved_query"));
      });
  mutation("conditional completion is not a source stop", [&](auto &actual) {
    auto &arm = branch(*actual.module)->getRegion(0).front();
    auto finish = *arm.template getOps<pir::FinishIfOp>().begin();
    finish.erase();
  });
  mutation("source stop cannot be omitted even after a completed query",
           [&](auto &actual) {
             auto &arm = branch(*actual.module)->getRegion(0).front();
             auto guard = *arm.template getOps<pir::GuardOp>().begin();
             guard.erase();
           });
  mutation("selected outcome ordering is exact", [&](auto &actual) {
    auto &arm = branch(*actual.module)->getRegion(0).front();
    auto guard = *arm.template getOps<pir::GuardOp>().begin();
    auto finish = *arm.template getOps<pir::FinishIfOp>().begin();
    finish->moveBefore(guard);
  });
  cases.run("a statically unselected arm is independently read", [&] {
    auto text = fixture(1, false);
    auto at = text.find(" %chosen =");
    require(at != std::string::npos, "missing static choice insertion point");
    text.insert(at, R"mlir(
 %zero = "data.index"() {value=0:ui64} : ()->ui64
 %fixed_choice = "data.make"(%zero) {alternative="left"} : (ui64)->!Choice
)mlir");
    at = text.find("\"protocol.branch\"(%choice,");
    require(at != std::string::npos, "missing static choice use");
    text.replace(at, std::string("\"protocol.branch\"(%choice,").size(),
                 "\"protocol.branch\"(%fixed_choice,");
    auto original = parseSourceString<ModuleOp>(text, &context);
    require(bool(original) && succeeded(admitStage(*original)),
            "static choice source admission");
    auto actual = take(emitOracleRealization(*original));
    take(checkOracleRealization(*original, actual));
    auto &unselected = branch(*actual.module)->getRegion(1).front();
    query(unselected)->setOperand(1, unselected.getArgument(3));
    rejected(*original, actual);
  });
  cases.run("Protocol arm still requires a structural yield", [&] {
    auto original = source(context);
    auto actual = take(emitOracleRealization(*original));
    branch(*actual.module)->getRegion(1).front().back().erase();
    require(failed(admitStage(*actual.module)),
            "yieldless Protocol arm admitted");
    refuses(checkOracleRealization(*original, actual), "oracle-common-body");
  });
  cases.run("native preflight charges environment work cumulatively", [&] {
    OracleNativeWork work;
    const uint64_t initialWork = work.remaining;
    require(initialWork > 1 && work.charge(initialWork - 1) &&
                work.remaining == 1 && !work.charge(2) && !work.charge(0),
            "exhausted work was reset or underflowed");
  });
  cases.run("native product accounting cannot overflow or reset", [&] {
    OracleNativeWork work;
    // Fixed operands exercise product arithmetic under an explicit allowance.
    work.remaining = 1000000;
    require(work.chargeProduct(1000, 1000) && work.remaining == 0 &&
                work.chargeProduct(0, std::numeric_limits<uint64_t>::max()) &&
                !work.chargeProduct(std::numeric_limits<uint64_t>::max(), 2) &&
                !work.chargeProduct(0, 0),
            "product accounting overflowed or reset exhaustion");
  });
  cases.run("recipe signature refuses before copying after exhaustion", [&] {
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    SmallVector<Type> inputs(128, index);
    OracleNativeWork limited;
    limited.remaining = inputs.size();
    refuses(oracleLocalRecipe(inputs, index, limited), "oracle-common-limit");
    require(limited.exhausted && !limited.charge(0),
            "signature copying reset the allowance");
    limited.remaining = 1000000;
    refuses(oracleLocalRecipe({}, {}, limited), "oracle-common-limit");
  });
  cases.run("ordered leaf recipe stops at its first failed append", [&] {
    auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
    SmallVector<Type> inputs(64, index);
    OracleNativeWork work;
    auto recipe = take(oracleLocalRecipe(inputs, index, work));
    require(recipe.nextResult == inputs.size(), "wrong initial result ordinal");
    // One constant (3 units), three additions (4 each), then an insufficient
    // allowance for the next addition. No later leaf is inspected or appended.
    work.remaining = 17;
    auto total = take(appendOracleLocalInstruction(
                          recipe, {"index.constant", {}, ""}, index, {},
                          {IntegerAttr::get(index, 0)}, work))
                     .front();
    unsigned completed = 0;
    for (unsigned leaf = 0; leaf < inputs.size(); ++leaf) {
      auto result = appendOracleLocalInstruction(
          recipe, {"index.add", {}, ""}, index, {total, leaf}, {}, work);
      if (!result) {
        auto message = toString(result.takeError());
        require(namesIdentifier(message, "oracle-common-limit"),
                "wrong recipe exhaustion diagnostic");
        break;
      }
      total = result->front();
      ++completed;
    }
    require(completed == 3 && recipe.instructions.size() == 4 &&
                recipe.nextResult == inputs.size() + 4 && work.exhausted,
            "recipe continued scanning/appending after the first failure");
    auto instructions = recipe.instructions.size();
    auto capacity = recipe.instructions.capacity();
    auto next = recipe.nextResult;
    // Even a zero-output instruction cannot be appended after exhaustion.
    work.remaining = 1000000;
    refuses(appendOracleLocalInstruction(recipe, {"control.require", {}, ""},
                                         {}, {total}, {}, work),
            "oracle-common-limit");
    require(recipe.instructions.size() == instructions &&
                recipe.instructions.capacity() == capacity &&
                recipe.nextResult == next && work.remaining == 0,
            "failed append mutated or allocated recipe storage");
  });
  cases.run("recipe ordinals survive zero-output instructions", [&] {
    auto bit = IntegerType::get(&context, 1);
    OracleNativeWork work;
    auto recipe = take(oracleLocalRecipe(bit, bit, work));
    take(appendOracleLocalInstruction(recipe, {"control.require", {}, ""}, {},
                                      {0}, {}, work));
    auto outputs = take(appendOracleLocalInstruction(
        recipe, {"bool.not", {}, ""}, bit, {0}, {}, work));
    require(outputs.size() == 1 && outputs.front() == 1 &&
                recipe.nextResult == 2,
            "zero-output instruction changed the next SSA ordinal");
  });
  for (bool contextRead : {false, true})
    cases.run(
        Twine("ordinary source admission charges shared helper expansion, "
              "context=") +
            Twine(unsigned(contextRead)),
        [&] {
          auto original = sharedControlSource(context);
          auto unit = cast<pir::ProtocolModuleOp>(original->getBody()->front());
          auto before = printed(*original);
          uint64_t stored = 0;
          original->walk([&](Operation *) { ++stored; });
          OracleNativeWork direct;
          const uint64_t directInitialWork = direct.remaining;
          facts::Work control(
              [&](uint64_t amount) { return direct.charge(amount); });
          auto requirements =
              take(zkc::detail::completeCommonControl(unit, control));
          uint64_t completionCost = directInitialWork - direct.remaining;
          auto single = sharedControlSource(context, 1);
          OracleNativeWork singleWork;
          const uint64_t singleWorkInitialWork = singleWork.remaining;
          facts::Work singleControl(
              [&](uint64_t amount) { return singleWork.charge(amount); });
          take(zkc::detail::completeCommonControl(
              cast<pir::ProtocolModuleOp>(single->getBody()->front()),
              singleControl));
          uint64_t partialCompletion =
              singleWorkInitialWork - singleWork.remaining + 4 * stored;
          require(!requirements.empty() && completionCost > partialCompletion,
                  "fixture did not expand a compact shared selected closure");
          auto operation =
              [&](OracleNativeWork &work,
                  const OracleNativeSourcePreflight &preflight) -> Error {
            if (contextRead) {
              auto result =
                  OracleVerificationContext::read(*original, work, preflight);
              if (!result)
                return result.takeError();
            } else {
              auto result = oracleEntries(*original, &work, &preflight);
              if (!result)
                return result.takeError();
              require(*result == std::vector<std::string>{"main"},
                      "dormant selected helpers changed the Oracle entry "
                      "inventory");
            }
            return Error::success();
          };
          OracleNativeWork prefix;
          const uint64_t prefixInitialWork = prefix.remaining;
          auto preflight =
              take(OracleNativeSourcePreflight::read(*original, prefix));
          checked(checkOracleNativePreflight(*original, prefix, &preflight));
          require(preflight.reserveTraversal(*original),
                  "admission reservation");
          uint64_t prefixCost = prefixInitialWork - prefix.remaining;
          checked(operation(prefix, preflight));
          // Cover more than the complete one-application module plus discovery,
          // but less than the actual repeated expansion. No independent
          // admission may complete first and refuse only afterwards.
          OracleNativeWork limited;
          limited.remaining = prefixCost + partialCompletion;
          auto bounded =
              take(OracleNativeSourcePreflight::read(*original, limited));
          bool capacityDiagnostic = false;
          ScopedDiagnosticHandler capture(
              &context, [&](Diagnostic &diagnostic) {
                capacityDiagnostic |= namesIdentifier(
                    diagnostic.str(), "common-control-capacity");
                return success();
              });
          auto failure = operation(limited, bounded);
          require(bool(failure) &&
                      namesIdentifier(toString(std::move(failure)),
                                      "oracle-common-limit") &&
                      capacityDiagnostic && limited.exhausted &&
                      limited.remaining == 0 && !limited.charge(0),
                  "source admission escaped the composed expansion allowance");
          failure = operation(limited, bounded);
          require(bool(failure), "repeated source admission reset exhaustion");
          consumeError(std::move(failure));
          require(printed(*original) == before,
                  "source admission mutated its owner");
        });
  cases.run(
      "local helper setup charges dormant declaration names after mutation",
      [&] {
        constexpr unsigned declarations = 128, extraWidth = 256;
        auto narrow = commonEntrySource(context);
        auto wide = commonEntrySource(context);
        addDormantDeclarations(*narrow, declarations, 0);
        addDormantDeclarations(*wide, declarations, extraWidth);
        auto recipe = constantRecipe(context);
        auto firstCost = [&](ModuleOp module) {
          OracleNativeWork work;
          const uint64_t workInitialWork = work.remaining;
          auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
          take(emitOracleLocalHelper(unit, recipe, work));
          return workInitialWork - work.remaining;
        };
        uint64_t narrowCost = firstCost(*narrow), wideCost = firstCost(*wide);
        require(wideCost - narrowCost == uint64_t(declarations) * extraWidth,
                "emitter setup did not reserve the actual copied symbol bytes");
        auto unit = cast<pir::ProtocolModuleOp>(wide->getBody()->front());
        OracleNativeWork cumulative;

        for (unsigned i = 1; i < 4; ++i) {
          recipe.name = "_local_setup_" + std::to_string(i);
          uint64_t inventory = 0;
          for (auto &declaration : unit.getBody().front()) {
            inventory += 2 + 2 * declaration.getAttrDictionary().size();
            if (auto name = SymbolTable::getSymbolName(&declaration))
              inventory += name.size();
          }
          uint64_t remaining = cumulative.remaining;
          take(emitOracleLocalHelper(unit, recipe, cumulative));
          uint64_t cost = remaining - cumulative.remaining;
          require(
              cost >= inventory,
              "next helper reused a stale inventory across candidate mutation");
        }
        require(succeeded(admitStage(*wide)),
                "emitted local helper lost full admission");
      });
  cases.run(
      "local helper setup and first instruction exhaust before binding "
      "emission",
      [&] {
        auto original = commonEntrySource(context);
        addDormantDeclarations(*original, 128, 256);
        auto recipe = constantRecipe(context);
        auto probe =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
        auto probeUnit = cast<pir::ProtocolModuleOp>(probe->getBody()->front());
        OracleNativeWork measured;
        const uint64_t measuredInitialWork = measured.remaining;
        take(emitOracleLocalHelper(probeUnit, recipe, measured));
        uint64_t cost = measuredInitialWork - measured.remaining;
        // These 128 dormant names alone copy 256 extra bytes each during
        // initial emitter inventory setup, before any binding can be created.
        constexpr uint64_t nameBytes = 128 * 256;
        for (uint64_t allowance : {nameBytes - 1, nameBytes}) {
          auto candidate =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
          auto unit =
              cast<pir::ProtocolModuleOp>(candidate->getBody()->front());
          OracleNativeWork limited;
          limited.remaining = allowance;
          refuses(emitOracleLocalHelper(unit, recipe, limited),
                  "oracle-common-limit");
          bool applied = false, bound = false;
          candidate->walk([&](exec::ApplyOp) { applied = true; });
          candidate->walk([&](runtime::BindingOp) { bound = true; });
          require(
              !applied && !bound && limited.exhausted &&
                  limited.remaining == 0 && !limited.charge(0),
              "exhausted setup emitted an instruction or reset its allowance");
          auto before = printed(*candidate);
          refuses(emitOracleLocalHelper(unit, recipe, limited),
                  "oracle-common-limit");
          require(printed(*candidate) == before,
                  "sticky exhaustion still created another helper");
        }
        OracleNativeWork exact;
        exact.remaining = cost;
        auto unit = cast<pir::ProtocolModuleOp>(original->getBody()->front());
        take(emitOracleLocalHelper(unit, recipe, exact));
        require(exact.remaining == 0 && !exact.exhausted,
                "exact setup and instruction allowance was not sufficient");
      });
  cases.run(
      "distinct local bindings charge each dormant inventory lookup", [&] {
        constexpr unsigned dormant = 128;
        auto one = constantRecipe(context);
        auto several = distinctBindingRecipe(context);
        auto cost = [&](const OracleLocalRecipe &recipe,
                        unsigned declarations) {
          auto module = commonEntrySource(context);
          addDormantDeclarations(*module, declarations, 0);
          auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
          OracleNativeWork work;
          const uint64_t workInitialWork = work.remaining;
          take(emitOracleLocalHelper(unit, recipe, work));
          require(succeeded(admitStage(*module)),
                  "distinct helper lost admission");
          return workInitialWork - work.remaining;
        };
        auto oneBase = cost(one, 0), oneDormant = cost(one, dormant);
        auto manyBase = cost(several, 0), manyDormant = cost(several, dormant);
        // Subtract common setup and recipe widths. The residual must account
        // for at least the two additional complete dormant-declaration
        // searches.
        uint64_t growth = (manyDormant - manyBase) - (oneDormant - oneBase);
        require(
            growth >= dormantBindingVisits(dormant, 2),
            "distinct bindings omitted their repeated dormant inventory scans");
        auto module = commonEntrySource(context);
        addDormantDeclarations(*module, dormant, 0);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        OracleNativeWork limited;
        limited.remaining = manyDormant - dormantBindingVisits(dormant, 2);
        refuses(emitOracleLocalHelper(unit, several, limited),
                "oracle-common-limit");
        unsigned applied = 0;
        module->walk([&](exec::ApplyOp) { ++applied; });
        require(applied < several.instructions.size() && limited.exhausted &&
                    !limited.charge(0),
                "inventory-dependent exhaustion still completed the helper");
      });
  cases.run(
      "metered bindings preserve late insertion, pins and deduplication", [&] {
        auto module = commonEntrySource(context);
        addDormantDeclarations(*module, 128, 0);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        constexpr StringLiteral prefix = "_late_binding_";
        mathematical::RealizationEmitter emitter(unit, prefix);
        OpBuilder builder(&context);
        builder.setInsertionPointToStart(&unit.getBody().front());
        auto inserted = runtime::BindingOp::create(
            builder, unit.getLoc(), "_late_binding_0", "index.constant",
            builder.getArrayAttr({}), "");
        auto before = printed(inserted);
        OracleNativeWork work;
        auto charge = [&](uint64_t amount) { return work.charge(amount); };
        NativeBindingApplication application{"index.add", {}, ""};
        auto first = emitter.bindingWithWork(builder, unit.getLoc(),
                                             application, charge);
        require(succeeded(first) && first->getValue() == "_late_binding_1",
                "late symbol insertion changed collision semantics");
        uint64_t reuseCost =
            2 + application.contract.size() + 1 + first->getValue().size() + 1;
        for (auto &declaration : unit.getBody().front())
          reuseCost += 2 + 2 * declaration.getAttrDictionary().size();
        uint64_t remaining = work.remaining;
        auto again = emitter.bindingWithWork(builder, unit.getLoc(),
                                             application, charge);
        require(succeeded(again) && *again == *first &&
                    remaining - work.remaining == reuseCost,
                "deduplication omitted its exact live inventory check");
        auto created = cast<runtime::BindingOp>(
            SymbolTable::lookupSymbolIn(unit, first->getValue()));
        auto attributes = created->getAttrDictionary();
        created.setImplementation("missing/implementation");
        require(failed(emitter.bindingWithWork(builder, unit.getLoc(),
                                               application, charge)),
                "emitter reused changed live attributes");
        created->setAttrs(attributes);
        require(succeeded(emitter.bindingWithWork(builder, unit.getLoc(),
                                                  application, charge)),
                "emitter lost restored exact created attributes");
        application.implementation = "native/index.add";
        auto pinned = emitter.bindingWithWork(builder, unit.getLoc(),
                                              application, charge);
        require(succeeded(pinned) && *pinned != *first &&
                    work.remaining < remaining && printed(inserted) == before,
                "explicit pin reused an unrelated binding or rewrote the late "
                "symbol");
      });
  cases.run("composite binding inventory observes every live insertion", [&] {
    auto module = commonEntrySource(context);
    auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
    OracleNativeWork work;
    OracleEmissionSession session(work, unit);
    OracleEmissionListener listener(work);
    OpBuilder builder(&context, &listener);
    builder.setInsertionPointToStart(&unit.getBody().front());
    // Construct the emitter before a sibling builder inserts the collision.
    OracleBindingEmitter emitter(unit, "unused", work);
    auto inserted = runtime::BindingOp::create(
        builder, unit.getLoc(), "_oracle_binding_0", "index.constant",
        builder.getArrayAttr({}), "");
    auto before = printed(inserted);
    NativeBindingApplication application{"index.add", {}, ""};
    auto first = emitter.binding(builder, unit.getLoc(), application);
    require(first.getValue() == "_oracle_binding_1",
            "composite inventory missed a late live collision");
    require(emitter.binding(builder, unit.getLoc(), application) == first,
            "composite emitter did not share its exact created application");
    application.implementation = "native/index.add";
    auto pinned = emitter.binding(builder, unit.getLoc(), application);
    require(pinned != first && printed(inserted) == before,
            "composite emitter reused an authored binding or changed a pin");
    session.finish();
    require(!work.emission, "composite session outlived its symbol owner");
    require(succeeded(admitStage(*module)), "live collision broke formation");
  });
  cases.run(
      "immutable native binding results recheck live attributes and owner",
      [&] {
        auto module = commonEntrySource(context);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        mathematical::RealizationEmitter emitter(unit, "_native_binding_");
        OpBuilder builder(&context);
        builder.setInsertionPointToStart(&unit.getBody().front());
        auto reference =
            emitter.binding(builder, unit.getLoc(), {"index.add", {}, ""});
        auto declaration = cast<runtime::BindingOp>(
            SymbolTable::lookupSymbolIn(unit, reference.getValue()));
        OracleNativeWork work;
        checked(oracleVerificationWithWork(work, [&]() -> Error {
          auto read = [&] {
            return readNativeBinding([&] { return declaration.emitOpError(); },
                                     declaration);
          };
          require(succeeded(read()) && succeeded(read()),
                  "exact binding read failed");
          auto attributes = declaration->getAttrDictionary();
          declaration.setImplementation("missing/native-implementation");
          {
            ScopedDiagnosticHandler handler(
                &context, [](Diagnostic &) { return success(); });
            require(failed(read()),
                    "immutable binding cache accepted changed live attributes");
          }
          declaration->setAttrs(attributes);
          require(succeeded(read()),
                  "restored exact immutable attributes were lost");
          auto &body = mainEntry(*module).getBody().front();
          declaration->moveBefore(&body, body.begin());
          {
            ScopedDiagnosticHandler handler(
                &context, [](Diagnostic &) { return success(); });
            require(failed(read()),
                    "immutable binding cache accepted a changed live owner");
          }
          return Error::success();
        }));
      });
  cases.run(
      "candidate local helpers share only exact emitted applications", [&] {
        auto module = commonEntrySource(context);
        addDormantDeclarations(*module, 64, 128);
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        auto recipe = constantRecipe(context);
        std::unique_ptr<mathematical::RealizationEmitter> emitter;
        OracleNativeWork work;
        auto first = take(emitOracleLocalHelper(unit, recipe, work, emitter));
        require(bool(emitter), "local emitter was not created lazily");
        auto firstApply =
            *first.getBody().front().getOps<exec::ApplyOp>().begin();
        auto firstBinding = firstApply.getBindingAttr();
        auto remaining = work.remaining;
        recipe.name = "_shared_local_1";
        uint64_t liveInventory = 2;
        for (auto &declaration : unit.getBody().front())
          liveInventory += 2 + 2 * declaration.getAttrDictionary().size();
        auto second = take(emitOracleLocalHelper(unit, recipe, work, emitter));
        auto secondApply =
            *second.getBody().front().getOps<exec::ApplyOp>().begin();
        require(secondApply.getBindingAttr() == firstBinding &&
                    remaining - work.remaining < liveInventory + 1024,
                "exact local application rebuilt more than its live inventory "
                "check");
        // A sibling inserts a colliding name after emitter construction. A new
        // exact pin must consult the live table and leave that declaration
        // alone.
        OpBuilder builder(&context);
        builder.setInsertionPointToStart(&unit.getBody().front());
        auto authored = runtime::BindingOp::create(
            builder, unit.getLoc(), "_oracle_common_binding_1",
            "index.constant", builder.getArrayAttr({}),
            "native/index.constant");
        auto authoredBefore = printed(authored);
        recipe.name = "_shared_local_pinned";
        recipe.instructions.front().binding.implementation =
            "native/index.constant";
        auto pinned = take(emitOracleLocalHelper(unit, recipe, work, emitter));
        auto pinnedApply =
            *pinned.getBody().front().getOps<exec::ApplyOp>().begin();
        require(
            pinnedApply.getBindingAttr() != firstBinding &&
                pinnedApply.getBindingAttr().getValue() !=
                    authored.getSymName() &&
                printed(authored) == authoredBefore,
            "local emitter reused authored authority or a stale name table");
        // Static arguments are part of the exact key too.
        recipe.name = "_shared_local_typed";
        recipe.instructions.front().binding = {
            "sequence.empty", {TypeAttr::get(builder.getI1Type())}, ""};
        recipe.instructions.front().parameters.clear();
        recipe.instructions.front().types = {
            data::SequenceType::get(&context, builder.getI1Type())};
        recipe.outputs = recipe.instructions.front().types;
        auto typed = take(emitOracleLocalHelper(unit, recipe, work, emitter));
        recipe.name = "_shared_local_other_type";
        auto index = builder.getIntegerType(64, false);
        recipe.instructions.front().binding.arguments = {TypeAttr::get(index)};
        recipe.instructions.front().types = {
            data::SequenceType::get(&context, index)};
        recipe.outputs = recipe.instructions.front().types;
        auto other = take(emitOracleLocalHelper(unit, recipe, work, emitter));
        require((*typed.getBody().front().getOps<exec::ApplyOp>().begin())
                        .getBindingAttr() !=
                    (*other.getBody().front().getOps<exec::ApplyOp>().begin())
                        .getBindingAttr(),
                "distinct static arguments shared one binding");
      });
  cases.run(
      "independent production reader accepts exact shared local pins", [&] {
        auto original = commonEntrySource(context);
        auto actual = take(emitOracleRealization(*original));
        llvm::DenseMap<Attribute, Operation *> seen;
        bool shared = false;
        for (auto helper : actual.entries.front().locals)
          helper.walk([&](exec::ApplyOp apply) {
            auto found =
                seen.try_emplace(apply.getBindingAttr(), helper.getOperation());
            shared |=
                !found.second && found.first->second != helper.getOperation();
          });
        require(shared,
                "production fixture did not share any exact local binding");
        take(checkOracleRealization(*original, actual));
      });
  cases.run(
      "nested resolution planning and schedule share the caller allowance",
      [&] {
        auto original = commonEntrySource(context);
        auto actual = take(emitOracleRealization(*original));
        auto before = printed(*original);
        cumulativeBoundary([&](OracleNativeWork &work) -> Error {
          auto preflight = OracleNativeSourcePreflight::read(*original, work);
          if (!preflight)
            return preflight.takeError();
          OracleRealizationPolicy policy;
          policy.order = OracleQueryOrder::AfterFinalDraw;
          auto selections = resolveOracleRealizationSelectionWithWork(
              *original, policy, work, *preflight);
          if (!selections)
            return selections.takeError();
          auto requirements = oracleRequirements(*original, "main", *selections,
                                                 &work, &*preflight);
          if (!requirements)
            return requirements.takeError();
          const auto &entry = actual.entries.front();
          auto schedule = planOracleQueryScheduleWithWork(
              *original, "main", *requirements, entry.controllers, entry.merkle,
              policy.authentication, work, *preflight);
          if (!schedule)
            return schedule.takeError();
          return Error::success();
        });
        require(printed(*original) == before,
                "nested planning mutated its source");
      });
  for (unsigned phase = 0; phase != 4; ++phase)
    cases.run(
        Twine("complete production accounting boundary ") + Twine(phase), [&] {
          auto original = commonEntrySource(context);
          auto actual = take(emitOracleRealization(*original));
          auto publication = take(exportOracleRealization(*original, actual));
          auto before = printed(*original),
               candidateBefore = printed(*actual.module);
          cumulativeBoundary([&](OracleNativeWork &work) -> Error {
            if (phase == 0) {
              auto emitted = emitOracleRealizationWithWork(*original, {}, work);
              if (!emitted)
                return emitted.takeError();
            } else if (phase == 1) {
              auto facts =
                  checkOracleRealizationWithWork(*original, actual, {}, work);
              if (!facts)
                return facts.takeError();
            } else if (phase == 2) {
              auto exported =
                  exportOracleRealizationWithWork(*original, actual, {}, work);
              if (!exported)
                return exported.takeError();
              require(exported->bytes == publication.bytes &&
                          equalNaturalJson(exported->data, publication.data),
                      "raw publication changed exact bytes or data");
            } else
              return checkOracleRealizationRecordWithWork(
                  *original, *actual.module, publication.bytes, {}, work);
            return Error::success();
          });
          require(printed(*original) == before &&
                      printed(*actual.module) == candidateBefore,
                  "production accounting refusal mutated a supplied owner");
        });
  cases.run(
      "wire whitespace syntax duplicate keys and limits remain distinct", [&] {
        auto original = commonEntrySource(context);
        auto actual = take(emitOracleRealization(*original));
        auto record = take(serializeOracleRealization(*original, actual));
        auto before = printed(*original),
             candidateBefore = printed(*actual.module);
        auto expect = [&](StringRef text, StringRef identifier) {
          auto failure =
              checkOracleRealization(*original, *actual.module, text);
          require(bool(failure), "invalid or oversized record accepted");
          auto message = toString(std::move(failure));
          require(namesIdentifier(message, identifier),
                  "wrong wire refusal: " + message);
        };
        OracleNativeWork defaults;
        expect(record + std::string(defaults.remaining + 1, ' '),
               "oracle-common-limit");
        expect("{", "oracle-realization-record");
        expect(R"json({"key":0,"\u006bey":1})json",
               "oracle-realization-record");
        expect("{}", "oracle-realization-record");
        expect(std::string(65, '[') + "0" + std::string(65, ']'),
               "oracle-realization-record-limit");
        expect(std::string(32 * 1024 * 1024 + 1, ' '),
               "oracle-realization-record-limit");
        checked(checkOracleRealization(*original, *actual.module, record));
        require(printed(*original) == before &&
                    printed(*actual.module) == candidateBefore,
                "wire refusal changed a source or candidate");
      });
  cases.run(
      "production type codecs charge repeated native descriptor expansion",
      [&] {
        Type type = sharedNestedType(context, 4);
        SmallVector<Type> types{type, data::SequenceType::get(&context, type)};
        auto jsonTypes = take(exportLogicalTypesData(types));
        cumulativeBoundary([&](OracleNativeWork &work) -> Error {
          auto written = writeOracleRecordedTypesWithWork(types, work);
          if (!written)
            return written.takeError();
          auto read = readOracleRecordedTypesWithWork(&context, *written, work);
          if (!read)
            return read.takeError();
          require(equal(*read, types),
                  "production type roundtrip changed native types");
          return Error::success();
        });
        OracleNativeWork duplicateWork;
        auto duplicate = jsonTypes;
        duplicate.push_back(jsonTypes.front());
        refuses(
            readOracleRecordedTypesWithWork(&context, duplicate, duplicateWork),
            "oracle-realization-record");
        // Compact immutable DAG, much larger recursive descriptor. The emitter
        // can retain native handles, while publication must pay every
        // expansion.
        auto original = commonEntrySource(context);
        // Preserve the originally admitted fixture: larger native types can
        // hit independent formation limits before publication is exercised.
        appendUnusedInput(*original, sharedNestedType(context, 12));
        auto actual = take(emitOracleRealization(*original));
        auto before = printed(*original),
             candidateBefore = printed(*actual.module);
        // The old explicit allowance still refuses. The larger public default
        // now publishes this same immutable input, with exact/one-less work
        // and visit boundaries checked against the real publication path.
        OracleNativeWork oldAllowance;
        oldAllowance.remaining = 1000000;
        refuses(exportOracleRealizationWithWork(*original, actual, {},
                                                oldAllowance),
                "oracle-common-limit");
        require(oldAllowance.exhausted && !oldAllowance.charge(0),
                "expanded descriptor exhaustion was not terminal");
        auto publication = take(exportOracleRealization(*original, actual));
        cumulativeBoundary([&](OracleNativeWork &work) -> Error {
          auto result =
              exportOracleRealizationWithWork(*original, actual, {}, work);
          if (!result)
            return result.takeError();
          require(result->bytes == publication.bytes &&
                      equalNaturalJson(result->data, publication.data),
                  "descriptor publication changed at its exact allowance");
          return Error::success();
        });
        require(printed(*original) == before &&
                    printed(*actual.module) == candidateBefore,
                "expanded type refusal mutated its immutable owners");
      });
  cases.run(
      "late primitive exhaustion discards partial helper and region ownership",
      [&] {
        auto original = source(context);
        pir::OracleKindAttr kind;
        original->walk([&](pir::OracleSendOp send) {
          kind = send.getHandle().getType().getKind();
        });
        require(bool(kind), "missing field-table kind");
        auto before = printed(*original);
        constexpr StringLiteral scheme =
            "rows.merkle-keccak256.koala-bear.ext4-binomial3/0";
        uint64_t cost = 0;
        unsigned inserted = 0;
        {
          auto scratch =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
          OracleNativeWork work;
          const unsigned workInitialVisits = work.operations;
          const uint64_t workInitialWork = work.remaining;
          take(emitOracleMerkleWithWork(*scratch, kind, scheme,
                                        OracleLeafGrouping::Individual,
                                        OracleLeafOrder::BitReversed, work));
          cost = workInitialWork - work.remaining;
          inserted = workInitialVisits - work.operations;
        }
        {
          auto scratch =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
          OracleNativeWork work;
          const unsigned workInitialVisits = work.operations;
          work.remaining = cost - 1;
          refuses(emitOracleMerkleWithWork(*scratch, kind, scheme,
                                           OracleLeafGrouping::Individual,
                                           OracleLeafOrder::BitReversed, work),
                  "oracle-common-limit");
          require(
              workInitialVisits - work.operations >= inserted - 1 &&
                  work.exhausted && !work.charge(0) && !work.emission &&
                  printed(*scratch) == before &&
                  succeeded(admitStage(*scratch)),
              "late cancellation failed to roll back linked helper/regions");
          auto partial = printed(*scratch);
          refuses(emitOracleMerkleWithWork(*scratch, kind, scheme,
                                           OracleLeafGrouping::Individual,
                                           OracleLeafOrder::BitReversed, work),
                  "oracle-common-limit");
          require(printed(*scratch) == partial,
                  "sticky retry appended private IR");
          // Generation performed essentially the whole helper set before
          // refusing. Rollback removes its cross-function region references;
          // no partial result is supplied as correspondence.
        }
        auto retry =
            OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
        OracleNativeWork exact;
        exact.remaining = cost;
        auto functions = take(emitOracleMerkleWithWork(
            *retry, kind, scheme, OracleLeafGrouping::Individual,
            OracleLeafOrder::BitReversed, exact));
        require(exact.remaining == 0 && !exact.exhausted,
                "fresh exact primitive retry failed");
        checked(checkOracleMerkle(*retry, functions, kind, scheme,
                                  OracleLeafGrouping::Individual,
                                  OracleLeafOrder::BitReversed));
        require(printed(*original) == before,
                "partial primitive changed its source");
      });
  cases.run(
      "primitive capacity reservations do not reset actual native work", [&] {
        auto original = commonEntrySource(context);
        auto program = mainEntry(*original);
        pir::OracleKindAttr kind;
        program.walk([&](pir::OracleSendOp send) {
          kind = send.getHandle().getType().getKind();
        });
        require(bool(kind), "missing primitive kind");
        OracleVirtualFunctionWork work;
        const uint64_t initialWork = work.getWork().remaining;
        require(work.reserveCapacity(4096, 4096 * 64),
                "primitive capacity reservation");
        require(work.operations == 100000 - 4096 &&
                    work.slots == 1000000 - 4096 * 64 &&
                    work.getWork().remaining == initialWork,
                "unused primitive upper bound became actual work");
        // The production builder listener still refuses at its first actual
        // node after any required live name inspection; capacity is not native
        // credit.
        OracleNativeWork limited;
        limited.operations = 0;
        refuses(emitOracleTableReadWithWork(*original, kind, limited),
                "oracle-common-limit");
        require(
            limited.exhausted && !limited.charge(0),
            "primitive generated IR outside the native operation allowance");
      });
  cases.run("recursive record equality debits the same allowance", [&] {
    auto original = commonEntrySource(context);
    auto actual = take(emitOracleRealization(*original));
    auto publication = take(exportOracleRealization(*original, actual));
    cumulativeBoundary([&](OracleNativeWork &work) -> Error {
      auto equal =
          equalOracleRecordWithWork(publication.data, publication.data, work);
      if (!equal)
        return equal.takeError();
      require(*equal, "exact publication equality failed");
      return Error::success();
    });
    auto changed = publication.data;
    (*changed.getAsObject())["format"] = "other";
    OracleNativeWork work;
    require(!take(equalOracleRecordWithWork(publication.data, changed, work)),
            "record equality ignored changed scalar");
  });
  cases.run(
      "zero shaped dense strings avoid logical element count iteration", [&] {
        auto module = commonEntrySource(context);
        auto tensor =
            RankedTensorType::get({std::numeric_limits<int64_t>::max(),
                                   std::numeric_limits<int64_t>::max(), 0},
                                  IntegerType::get(&context, 8));
        auto strings =
            DenseStringElementsAttr::get(tensor, ArrayRef<StringRef>{});
        module->getOperation()->setAttr("capacity_probe", strings);
        checked(boundOracleNativeIR(*module));
        module->getOperation()->removeAttr("capacity_probe");
      });
  cases.run(
      "publication byte reservation refuses before publishing a record", [&] {
        auto value = [] {
          return json::Value(json::Object{{"payload", std::string(4096, 'x')}});
        };
        // Node visits/string inspection fit; the output-byte append does not.
        // This bound comes from payload length, not measured debits.
        OracleNativeWork limited;
        limited.remaining = 4 * 4096;
        refuses(finishOraclePublication(value(), limited),
                "oracle-common-limit");
        require(limited.exhausted && !limited.charge(0),
                "serialization reset its cumulative allowance");
        OracleNativeWork sufficient;
        const uint64_t initialWork = sufficient.remaining;
        auto publication = take(finishOraclePublication(value(), sufficient));
        require(publication.bytes.size() > 4096 &&
                    sufficient.remaining <
                        initialWork - 2 * publication.bytes.size(),
                "publication omitted serialization or ownership work");
      });
  cases.run("source preflights share module and entry work cumulatively", [&] {
    auto original = source(context);
    auto unit = cast<pir::ProtocolModuleOp>(original->getBody()->front());
    auto first = mainEntry(*original);
    for (unsigned i = 1; i < 4; ++i) {
      auto *copy = first->clone();
      SymbolTable::setSymbolName(copy, "entry_" + std::to_string(i));
      unit.getBody().front().push_back(copy);
    }
    // Uncalled module metadata makes repeated whole-module scans
    // distinguishable from the reached entry closure. It supplies no admission
    // authority.
    original->getOperation()->setAttr(
        "protocol.preflight_probe",
        StringAttr::get(&context, std::string(8192, 'x')));
    require(succeeded(admitStage(*original)), "multi-entry source formation");
    auto before = printed(*original);
    OracleNativeWork measured;
    const uint64_t measuredInitialWork = measured.remaining;
    auto preflight =
        take(OracleNativeSourcePreflight::read(*original, measured));
    uint64_t moduleCost = measuredInitialWork - measured.remaining;
    auto names = take(oracleEntries(*original, &measured, &preflight));
    uint64_t discoveryCost =
        measuredInitialWork - measured.remaining - moduleCost;
    require(names.size() == 4, "multi-entry inventory changed");
    std::vector<uint64_t> closureCosts;
    for (const auto &name : names) {
      auto program =
          cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, name));
      auto remaining = measured.remaining;
      checked(
          checkOracleNativeSource(*original, program, &measured, &preflight));
      closureCosts.push_back(remaining - measured.remaining);
      require(closureCosts.back() > 0 && closureCosts.back() < moduleCost,
              "entry preflight rescanned the whole immutable module");
    }
    OracleNativeWork limited;
    limited.remaining = moduleCost + closureCosts[0] + closureCosts[1] - 1;
    auto bounded = take(OracleNativeSourcePreflight::read(*original, limited));
    checked(checkOracleNativeSource(*original, first, &limited, &bounded));
    auto second =
        cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, names[1]));
    auto failure =
        checkOracleNativeSource(*original, second, &limited, &bounded);
    require(bool(failure), "second entry reset its closure allowance");
    require(
        namesIdentifier(toString(std::move(failure)), "oracle-common-limit") &&
            limited.exhausted && !limited.charge(0),
        "wrong cumulative closure refusal");
    OracleNativeWork emission;
    emission.remaining =
        moduleCost + discoveryCost + closureCosts[0] + closureCosts[1] - 1;
    refuses(emitOracleRealizationWithWork(*original, {}, emission),
            "oracle-common-limit");
    require(emission.exhausted && printed(*original) == before,
            "multi-entry emission mutated the source or reset its allowance");
  });
  cases.run(
      "source preflight reuse belongs to the exact module and allowance", [&] {
        auto original = source(context);
        OracleNativeWork work;
        auto preflight =
            take(OracleNativeSourcePreflight::read(*original, work));
        OracleNativeWork otherWork;
        auto mismatch = checkOracleNativeSource(*original, mainEntry(*original),
                                                &otherWork, &preflight);
        require(bool(mismatch) && namesIdentifier(toString(std::move(mismatch)),
                                                  "oracle-common-body"),
                "preflight was reused with a different allowance");
        auto copy = OwningOpRef<ModuleOp>(cast<ModuleOp>((*original)->clone()));
        mismatch =
            checkOracleNativeSource(*copy, mainEntry(*copy), &work, &preflight);
        require(bool(mismatch) && namesIdentifier(toString(std::move(mismatch)),
                                                  "oracle-common-body"),
                "inspection clone inherited another module's preflight");
        // A new composed operation must preflight the actual current source
        // again.
        original->getOperation()->setAttr(
            "protocol.preflight_probe",
            StringAttr::get(&context, std::string(4096, 'x')));
        OracleNativeWork fresh;
        fresh.remaining = 4095;
        refuses(OracleNativeSourcePreflight::read(*original, fresh),
                "oracle-common-limit");
      });
  cases.run(
      "immutable symbol inventory preserves native walk order and work", [&] {
        auto original = source(context);
        auto unit = cast<pir::ProtocolModuleOp>(original->getBody()->front());
        auto *copy = mainEntry(*original)->clone();
        SymbolTable::setSymbolName(copy, "sibling");
        unit.getBody().front().push_back(copy);
        Builder builder(&context);
        auto main = FlatSymbolRefAttr::get(&context, "main");
        auto sibling = FlatSymbolRefAttr::get(&context, "sibling");
        auto references = builder.getArrayAttr(
            {main, builder.getArrayAttr({sibling, main}), sibling});
        original->getOperation()->setAttr("protocol.reference_probe",
                                          references);
        require(succeeded(admitStage(*original)),
                "symbol inventory source formation");
        SmallVector<SymbolRefAttr> native;
        references.walk(
            [&](SymbolRefAttr reference) { native.push_back(reference); });
        OracleNativeWork measured;
        const uint64_t measuredInitialWork = measured.remaining;
        auto preflight =
            take(OracleNativeSourcePreflight::read(*original, measured));
        uint64_t moduleCost = measuredInitialWork - measured.remaining;
        auto indexed = take(preflight.getReferences(references));
        uint64_t readCost =
            measuredInitialWork - measured.remaining - moduleCost;
        require(indexed == native && native.size() == 2 && native[0] == main &&
                    native[1] == sibling,
                "shared symbol nodes changed native postorder or multiplicity");
        auto remaining = measured.remaining;
        require(
            take(preflight.getReferences(references)) == native &&
                remaining - measured.remaining == readCost &&
                readCost == 1 + native.size(),
            "repeated symbol inventory rescanned the immutable attribute DAG");
        OracleNativeWork limited;
        limited.remaining = moduleCost + readCost - 1;
        auto bounded =
            take(OracleNativeSourcePreflight::read(*original, limited));
        refuses(bounded.getReferences(references), "oracle-common-limit");
        require(limited.exhausted && !limited.charge(0),
                "symbol inventory continued copying after exhaustion");
      });
  cases.run(
      "requirements closure shares its caller allowance across entries", [&] {
        auto original = source(context);
        auto unit = cast<pir::ProtocolModuleOp>(original->getBody()->front());
        auto *copy = mainEntry(*original)->clone();
        SymbolTable::setSymbolName(copy, "sibling");
        unit.getBody().front().push_back(copy);
        auto selections =
            take(resolveOracleRealizationSelection(*original, {}));
        OracleNativeWork measured;
        const uint64_t measuredInitialWork = measured.remaining;
        auto preflight =
            take(OracleNativeSourcePreflight::read(*original, measured));
        uint64_t moduleCost = measuredInitialWork - measured.remaining;
        take(oracleRequirements(*original, "main", selections, &measured,
                                &preflight));
        uint64_t firstCost =
            measuredInitialWork - measured.remaining - moduleCost;
        take(oracleRequirements(*original, "sibling", selections, &measured,
                                &preflight));
        uint64_t used = measuredInitialWork - measured.remaining;
        OracleNativeWork limited;
        limited.remaining = used - 1;
        auto bounded =
            take(OracleNativeSourcePreflight::read(*original, limited));
        take(oracleRequirements(*original, "main", selections, &limited,
                                &bounded));
        require(firstCost > 0, "requirements preflight was uncharged");
        refuses(oracleRequirements(*original, "sibling", selections, &limited,
                                   &bounded),
                "oracle-common-limit");
        require(limited.exhausted && !limited.charge(0),
                "requirements reset the composed allowance");
      });
  for (unsigned shape = 0; shape < 9; ++shape)
    cases.run(
        Twine("public oracle preflight bounds native fields ") + Twine(shape),
        [&] {
          auto original = commonEntrySource(context);
          auto before = printed(*original);
          auto actual = take(emitOracleRealization(*original));
          take(checkOracleRealization(*original, actual));
          auto candidateBefore = printed(*actual.module);
          Builder builder(&context);
          OracleNativeWork defaults;
          const uint64_t defaultWork = defaults.remaining;
          const unsigned width = defaultWork + 1;
          // Slots incur both their container width and each child visit.
          // Use that lower bound to avoid allocating twice as many handles.
          const unsigned slots = defaultWork / 2 + 1;
          Attribute oversized;
          switch (shape) {
          case 0: {
            SmallVector<Attribute> repeated(slots, builder.getStringAttr("x"));
            oversized = builder.getArrayAttr(repeated);
            break;
          }
          case 1: {
            SmallVector<Type> repeated(slots, builder.getI1Type());
            oversized = TypeAttr::get(builder.getFunctionType(repeated, {}));
            break;
          }
          case 2:
            oversized = TypeAttr::get(
                OpaqueType::get(builder.getStringAttr("capacity_test"),
                                std::string(width, 'x')));
            break;
          case 3:
            oversized = TypeAttr::get(IntegerType::get(&context, width));
            break;
          case 4: {
            // A dense byte array charges both elements and raw bytes.
            SmallVector<int8_t> bytes(slots, 0);
            oversized = builder.getDenseI8ArrayAttr(bytes);
            break;
          }
          case 5:
            oversized = builder.getDictionaryAttr({builder.getNamedAttr(
                std::string(width, 'x'), builder.getUnitAttr())});
            break;
          case 6: {
            const unsigned half = defaultWork / 4 + 1;
            SmallVector<Attribute> first(half, builder.getStringAttr("x"));
            SmallVector<Attribute> second(half, builder.getStringAttr("y"));
            oversized = builder.getArrayAttr(
                {builder.getArrayAttr(first), builder.getArrayAttr(second)});
            break;
          }
          case 7: {
            oversized = builder.getUnitAttr();
            for (unsigned i = 0; i < 128; ++i)
              oversized = builder.getArrayAttr({oversized});
            break;
          }
          default: {
            // Visit the same suffix shallowly first, then behind another path.
            // A cache that records only visited nodes misses the combined
            // depth.
            Attribute suffix = builder.getUnitAttr();
            for (unsigned i = 0; i < 40; ++i)
              suffix = builder.getArrayAttr({suffix});
            Attribute deep = suffix;
            for (unsigned i = 0; i < 40; ++i)
              deep = builder.getArrayAttr({deep});
            oversized = builder.getArrayAttr({suffix, deep});
            break;
          }
          }
          // Public emission must refuse before cloning/admitting an oversized
          // source. Removing only our mutation must restore the exact source.
          original->getOperation()->setAttr("capacity_probe", oversized);
          auto attributes = original->getOperation()->getAttrDictionary();
          refuses(emitOracleRealization(*original), "oracle-common-limit");
          require(original->getOperation()->getAttrDictionary() == attributes,
                  "capacity refusal changed source attributes");
          original->getOperation()->removeAttr("capacity_probe");
          require(printed(*original) == before,
                  "capacity refusal changed source");
          actual.module->getOperation()->setAttr("capacity_probe", oversized);
          attributes = actual.module->getOperation()->getAttrDictionary();
          refuses(checkOracleRealization(*original, actual),
                  "oracle-common-limit");
          require(actual.module->getOperation()->getAttrDictionary() ==
                      attributes,
                  "capacity reader changed candidate attributes");
          actual.module->getOperation()->removeAttr("capacity_probe");
          require(printed(*actual.module) == candidateBefore &&
                      printed(*original) == before,
                  "capacity reader changed source or candidate body");
        });
  cases.run("combined Oracle preflight precedes candidate admission", [&] {
    auto original = commonEntrySource(context);
    auto actual = take(emitOracleRealization(*original));
    take(checkOracleRealization(*original, actual));
    Builder builder(&context);
    OracleNativeWork defaults;
    const uint64_t width = defaults.remaining / 2 + 1;
    auto large = builder.getStringAttr(std::string(width, 'x'));
    original->getOperation()->setAttr("capacity_probe", large);
    actual.module->getOperation()->setAttr(
        "capacity_probe", builder.getStringAttr(std::string(width, 'y')));
    checked(boundOracleNativeIR(*original));
    checked(boundOracleNativeIR(*actual.module));
    // The two distinct spellings together exceed the default work allowance.
    // Each owner fits alone; exact immutable reuse cannot merge this pair.
    // A missing candidate terminator would diagnose during admission; the
    // combined size must refuse before reaching that unrelated malformed body.
    auto unit = cast<pir::ProtocolModuleOp>(actual.module->getBody()->front());
    auto program =
        *unit.getBody().front().getOps<pir::MathematicalOp>().begin();
    auto *terminal = program.getBody().front().getTerminator();
    terminal->remove();
    auto restore = llvm::scope_exit(
        [&] { program.getBody().front().getOperations().push_back(terminal); });
    const auto originalBefore = printed(*original);
    const auto candidateBefore = printed(*actual.module);
    unsigned diagnostics = 0;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &) {
      ++diagnostics;
      return success();
    });
    refuses(checkOracleRealization(*original, actual), "oracle-common-limit");
    require(!diagnostics, "combined capacity was checked after admission");
    require(printed(*original) == originalBefore &&
                printed(*actual.module) == candidateBefore,
            "combined capacity refusal mutated either supplied subject");
  });
  for (unsigned results : {1u, 4096u})
    cases.run(Twine("public oracle role/result work ") + Twine(results), [&] {
      auto original = commonEntrySource(context);
      auto actual = take(emitOracleRealization(*original));
      take(checkOracleRealization(*original, actual));
      expandOrdinaryResults(*original, 1024, results);
      expandOrdinaryResults(*actual.module, 1024, results);
      require(succeeded(admitStage(*original)) &&
                  succeeded(admitStage(*actual.module)),
              "role/result capacity fixture lost admission");
      auto before = printed(*original);
      auto candidateBefore = printed(*actual.module);
      // A small admitted pair is a positive control; the wide pair reaches
      // the independent reader without obtaining a wide emitter result.
      if (results == 1) {
        take(checkOracleRealization(*original, actual));
        auto emitted = take(emitOracleRealization(*original));
        take(checkOracleRealization(*original, emitted));
      } else {
        refuses(emitOracleRealization(*original), "oracle-common-limit");
        refuses(checkOracleRealization(*original, actual),
                "oracle-common-limit");
      }
      require(printed(*original) == before &&
                  printed(*actual.module) == candidateBefore,
              "role/result accounting changed source or candidate");
    });
  for (unsigned shapes : {16u, 2048u})
    cases.run(Twine("repeated Oracle shape role work ") + Twine(shapes), [&] {
      auto original = commonEntrySource(context);
      auto entry = mainEntry(*original);
      auto handle =
          *entry.getBody().front().getOps<pir::OracleVirtualOp>().begin();
      OpBuilder builder(&context);
      builder.setInsertionPoint(entry.getBody().front().getTerminator());
      for (unsigned i = 0; i < shapes; ++i)
        pir::OracleShapeOp::create(builder, entry.getLoc(),
                                   builder.getIntegerType(64, false),
                                   handle->getResult(0), "rows");
      require(succeeded(admitStage(*original)), "shape fixture admission");
      // With 1024 roles, each shape pays at least 1024 roster visits plus
      // 1024 receiver-membership checks: 2048 shapes exceed 4M work.
      // Obtain the independently read candidate with two roles, then widen
      // only both entry rosters. The actual handle still belongs to P and V.
      auto actual = take(emitOracleRealization(*original));
      expandOrdinaryResults(*original, 1024, 1);
      expandOrdinaryResults(*actual.module, 1024, 1);
      require(succeeded(admitStage(*original)) &&
                  succeeded(admitStage(*actual.module)),
              "wide shape fixture admission");
      auto before = printed(*original);
      auto candidateBefore = printed(*actual.module);
      if (shapes == 16) {
        take(checkOracleRealization(*original, actual));
        auto emitted = take(emitOracleRealization(*original));
        take(checkOracleRealization(*original, emitted));
      } else {
        refuses(emitOracleRealization(*original), "oracle-common-limit");
        refuses(checkOracleRealization(*original, actual),
                "oracle-common-limit");
      }
      require(printed(*original) == before &&
                  printed(*actual.module) == candidateBefore,
              "shape capacity refusal changed the original or candidate");
    });
  // Formation-arm boundary preflight, intentionally separate from admission.
  for (unsigned count : {512u, 513u})
    cases.run(Twine("selected arm preflight ") + Twine(count), [&] {
      OpBuilder builder(&context);
      auto module = ModuleOp::create(builder.getUnknownLoc());
      auto cleanup = llvm::scope_exit([&] { module.erase(); });
      builder.setInsertionPointToEnd(module.getBody());
      OperationState state(builder.getUnknownLoc(),
                           pir::BranchOp::getOperationName());
      for (unsigned i = 0; i < count; ++i)
        state.addRegion()->push_back(new Block);
      builder.create(state);
      auto failure = boundOracleNativeIR(module);
      if (count == 512)
        checked(std::move(failure));
      else {
        require(bool(failure), "513 selected arms escaped preflight");
        require(namesIdentifier(toString(std::move(failure)),
                                "oracle-common-limit"),
                "wrong arm capacity diagnostic");
      }
    });
  cases.run(
      "component captures stay lazy until the selected arm consumes Data", [&] {
        auto text = fixture(1, false);
        auto at = text.find(" %chosen =");
        require(at != std::string::npos, "missing selection insertion point");
        text.insert(at, R"mlir(
 %root_rows = "data.index"() {value=2:ui64} : ()->ui64
 %root = "protocol.oracle_send"(%data,%root_rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="root_table"} : (!D,ui64)->!H
 %view:2 = "protocol.oracle_components"(%root) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
)mlir");
        at = text.find("(%choice,%data,%other,%position,%trips,%allow)");
        require(at != std::string::npos, "missing capture insertion point");
        text.replace(
            at,
            std::string("(%choice,%data,%other,%position,%trips,%allow)")
                .size(),
            "(%choice,%view#0,%other,%position,%trips,%allow)");
        auto original = parseSourceString<ModuleOp>(text, &context);
        require(bool(original) && succeeded(admitStage(*original)),
                "lazy capture source admission");
        auto actual = take(emitOracleRealization(*original));
        take(checkOracleRealization(*original, actual));
        unsigned selectedReads = 0;
        actual.module->walk([&](pir::LocalCallOp call) {
          if (call.getSite().ends_with("_component_data")) {
            require(call->getParentOp() == branch(*actual.module),
                    "component lookup hoisted outside selection");
            require(call->getBlock() ==
                        &branch(*actual.module)->getRegion(0).front(),
                    "untaken arm acquired the other arm's component read");
            ++selectedReads;
          }
        });
        require(selectedReads == 1,
                "lazy holder view did not have one selected consumer");
      });
  cases.run(
      "selected record roundtrip and independently refused capture mutation",
      [&] {
        auto original = source(context);
        auto actual = take(emitOracleRealization(*original));
        auto record = take(serializeOracleRealization(*original, actual));
        checked(checkOracleRealization(*original, *actual.module, record));
        auto &arm = branch(*actual.module)->getRegion(1).front();
        query(arm)->setOperand(1, arm.getArgument(3));
        auto failure =
            checkOracleRealization(*original, *actual.module, record);
        require(bool(failure), "record replaced actual candidate reading");
        require(
            namesIdentifier(toString(std::move(failure)), "oracle-common-body"),
            "record mutation was not rejected by the actual body reader");
      });
  for (unsigned depth : {64u, 65u})
    cases.run(Twine("native control depth preflight ") + Twine(depth), [&] {
      OpBuilder builder(&context);
      auto module = ModuleOp::create(builder.getUnknownLoc());
      auto cleanup = llvm::scope_exit([&] { module.erase(); });
      Block *body = module.getBody();
      for (unsigned i = 0; i < depth; ++i) {
        builder.setInsertionPointToEnd(body);
        OperationState state(builder.getUnknownLoc(),
                             pir::BranchOp::getOperationName());
        auto *nested = new Block;
        state.addRegion()->push_back(nested);
        builder.create(state);
        body = nested;
      }
      builder.setInsertionPointToEnd(body);
      OperationState leaf(builder.getUnknownLoc(),
                          data::IndexOp::getOperationName());
      builder.create(leaf);
      auto failure = boundOracleNativeIR(module);
      if (depth == 64)
        checked(std::move(failure));
      else {
        require(bool(failure), "65 nested controls escaped preflight");
        require(namesIdentifier(toString(std::move(failure)),
                                "oracle-common-limit"),
                "wrong depth capacity diagnostic");
      }
    });
  return cases.result();
}

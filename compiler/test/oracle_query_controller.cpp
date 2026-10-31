#include "../lib/Transforms/OracleQueryController.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include <filesystem>
#include <fstream>
#include <functional>
#include <set>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
std::string source(bool noQueries = false, bool heterogeneous = false,
                   bool trailingZero = false, bool duplicate = false) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [ui64, 4 : ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
#B = #protocol.oracle_kind<"table", [ui64, 4 : ui64]>
!B = !protocol.oracle<#B>
!BD = !algebra.indices
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/controller",revision="0",
  signature=(!D,!BD,ui64)->i1,purposes=["witness","witness","parameter"]}
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!B,%mapped:ui64,%position:ui64):
)mlir";
  text += noQueries ? R"mlir(
   %answer = "data.index"() {value=9 : ui64} : ()->ui64
)mlir"
                    : R"mlir(
   %answer = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->ui64
   %unused = "protocol.oracle_query"(%b,%mapped) {site="right"} : (!B,ui64)->ui64
)mlir";
  text += R"mlir(
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="combine",function_type=(!H,!B,ui64,ui64)->ui64,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
  ^bb0(%left:!D,%right:!BD,%mapped:ui64,%position:ui64):
   %rows = "data.index"() {value=4 : ui64} : ()->ui64
   %a = "protocol.oracle_send"(%left,%rows) {shape_names=["rows"],shape_bounds={},
     sender="P",receivers=["V"],site="left"} : (!D,ui64)->!H
   %b = "protocol.oracle_send"(%right,%rows) {shape_names=["rows"],shape_bounds={},
     sender="P",receivers=["V"],site="right"} : (!BD,ui64)->!B
   %three = "data.index"() {value=3 : ui64} : ()->ui64
   %last = "protocol.repeat"(%three,%a,%b,%mapped) ({
    ^bb0(%iteration:ui64,%previous:!H,%other:!B,%map:ui64):
     %next = "protocol.oracle_virtual"(%previous,%other,%map) {callee=@combine,holder="P",receivers=["V"]} : (!H,!B,ui64)->!H
     "protocol.yield"(%next) : (!H)->()
   }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!B,ui64)->!H
   %answer = "protocol.oracle_query"(%last,%position) {owner="V",site="query"} : (!H,ui64)->ui64
   "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,!BD,ui64,ui64)->ui64,roles=["P","V"],
     input_roles=[["P"],["P"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  if (duplicate) {
    auto offset = text.find("oracle_query\"(%b,%mapped)");
    require(offset != std::string::npos, "duplicate query fragment missing");
    text.replace(offset, std::string("oracle_query\"(%b,%mapped)").size(),
                 "oracle_query\"(%a,%mapped)");
  }
  if (heterogeneous) {
    auto replace = [&](StringRef from, StringRef to) {
      auto i = text.find(from.str());
      require(i != std::string::npos, "missing heterogeneous fragment");
      text.replace(i, from.size(), to.str());
    };
    replace("#B = #protocol.oracle_kind<\"table\", [ui64,",
            "#B = #protocol.oracle_kind<\"table\", [i1,");
    replace("!BD = !algebra.indices", "!BD = !data.sequence<i1>");
    if (!noQueries)
      replace("(!B,ui64)->ui64", "(!B,ui64)->i1");
  }
  if (trailingZero) {
    auto replace = [&](StringRef from, StringRef to) {
      auto offset = text.find(from.str());
      require(offset != std::string::npos, "missing zero-query fragment");
      text.replace(offset, from.size(), to.str());
    };
    replace(" relation.declare @admissible", R"mlir(
 relation.declare @empty_admissible {kind="external",key="test/zero",revision="0",
  signature=()->i1,purposes=[]}
 "protocol.oracle"() ({ ^bb0(%position:ui64):
   %answer = "data.index"() {value=9 : ui64} : ()->ui64
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="zero",function_type=(ui64)->ui64,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@empty_admissible} : ()->()
 relation.declare @admissible)mlir");
    replace(
        "   %three =",
        R"mlir(   %zero = "protocol.oracle_virtual"() {callee=@zero,holder="P",receivers=["V"]} : ()->!H
   %three =)mlir");
    replace("(%three,%a,%b,%mapped)", "(%three,%a,%zero,%mapped)");
  }
  // The ordinary case consumes the saved first reference. The duplicate-source
  // case consumes the second reference, whose position may differ at every
  // level.
  if (duplicate) {
    auto at = text.find("protocol.oracle_yield\"(%answer)");
    require(at != std::string::npos, "second answer fragment missing");
    text.replace(at, std::string("protocol.oracle_yield\"(%answer)").size(),
                 "protocol.oracle_yield\"(%unused)");
  }
  return text;
}
std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text;
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    return success();
  });
  auto result =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(result), "parse: " + diagnostics);
  require(succeeded(zkc::admitStage(*result)), "formation: " + diagnostics);
  return result;
}
OwningOpRef<ModuleOp> fresh(MLIRContext &context) {
  return parse(context, R"mlir(
module { "protocol.module"() ({
 func.func private @placeholder()->i1 { %ok = arith.constant true
 return %ok : i1 }
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
}
void uniqueSites(ModuleOp module) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  for (auto function : unit.getBody().front().getOps<func::FuncOp>()) {
    if (function->hasAttr("runtime.region"))
      continue;
    std::set<std::string> sites;
    std::function<void(func::FuncOp, unsigned)> visit;
    visit = [&](func::FuncOp body, unsigned depth) {
      require(depth < 64, "cyclic generated control");
      body.walk([&](Operation *op) {
        auto site = op->getAttrOfType<StringAttr>("runtime.site");
        if (op->getName().getDialectNamespace() == "exec")
          site = op->getAttrOfType<StringAttr>("site");
        if (site)
          require(sites.insert(site.str()).second, "duplicate occurrence " +
                                                       function.getSymName() +
                                                       "/" + site.getValue());
        if (auto call = dyn_cast<func::CallOp>(op))
          if (!site) {
            auto nested = dyn_cast_or_null<func::FuncOp>(
                SymbolTable::lookupSymbolIn(unit, call.getCallee()));
            require(bool(nested), "missing generated control region");
            visit(nested, depth + 1);
          }
      });
    };
    visit(function, 0);
  }
}
std::string client(ModuleOp candidate, const OracleAnchorStorage &plan,
                   const OracleQueryController &controller,
                   const DialectRegistry &registry, bool resumeCheck,
                   bool prefixCheck) {
  auto unit = cast<pir::ProtocolModuleOp>(candidate.getBody()->front());
  SmallVector<func::FuncOp> allocators;
  for (auto item : controller.constructors)
    allocators.push_back(take(
        emitOracleAnchorAllocator(candidate, plan, item.source, item.role)));
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  SmallVector<Type> inputs{plan.constructors[0].kind.getDataType(),
                           plan.constructors[1].kind.getDataType()};
  // Actual virtual rows, mapped child position, selected constructor/instance,
  // outer position. Base rows follow their actual supplied table lengths.
  inputs.append(resumeCheck ? 11 : prefixCheck ? 6 : 5, index);
  auto owner = builder.getStrArrayAttr({"V"});
  OperationState main(loc, "protocol.func");
  main.addAttribute("sym_name", builder.getStringAttr("main"));
  main.addAttribute("function_type", TypeAttr::get(builder.getFunctionType(
                                         inputs, {index, index})));
  main.addAttribute("roles", prefixCheck
                                 ? builder.getStrArrayAttr({"V", "Observer"})
                                 : owner);
  main.addAttribute("input_roles", builder.getArrayAttr(SmallVector<Attribute>(
                                       inputs.size(), owner)));
  main.addAttribute("output_roles", builder.getArrayAttr({owner, owner}));
  auto *body = new Block;
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  main.addRegion()->push_back(body);
  builder.setInsertionPointToEnd(&unit.getBody().front());
  builder.create(main);
  builder.setInsertionPointToEnd(body);
  auto call = [&](func::FuncOp function, ValueRange inputs, StringRef site) {
    return pir::LocalCallOp::create(builder, loc,
                                    scopedDataSignature(function).getResults(),
                                    inputs, function.getSymName(), site, "V");
  };
  SmallVector<Value> stores, references;
  for (Type type : controller.stores)
    stores.push_back(data::SequenceEmptyOp::create(builder, loc, type));
  for (unsigned i = 0; i < 2; ++i) {
    auto input = body->getArgument(i);
    Value rows =
        isa<data::SequenceType>(input.getType())
            ? Value(data::SequenceLengthOp::create(builder, loc, index, input))
            : Value(data::DimOp::create(builder, loc, index, input, 0));
    auto count = call(controller.constructionCounts[i], stores,
                      "base_count_" + std::to_string(i));
    auto allocated =
        call(allocators[i],
             {stores[i], rows, count.getOutputs()[0], body->getArgument(i)},
             "base_" + std::to_string(i));
    references.push_back(allocated.getOutputs()[0]);
    stores[i] = allocated.getOutputs()[1];
  }
  unsigned virtualConstructor = 2;
  if (prefixCheck) {
    auto count = call(controller.constructionCounts[2], stores, "zero_count");
    auto zero =
        call(allocators[2],
             {stores[2], body->getArgument(2), count.getOutputs()[0]}, "zero");
    references[1] = zero.getOutputs()[0];
    stores[2] = zero.getOutputs()[1];
    virtualConstructor = 3;
  }
  Value previous = references[0];
  for (unsigned i = 0; i < 3; ++i) {
    auto iteration = data::IndexOp::create(builder, loc, index, i);
    Value rows = prefixCheck
                     ? Value(data::IndexOp::create(builder, loc, index, 4))
                     : body->getArgument(2);
    SmallVector<Value> counted{previous, references[1]};
    append_range(counted, stores);
    auto count = call(controller.constructionCounts[virtualConstructor],
                      counted, "virtual_count_" + std::to_string(i));
    auto allocated = call(allocators[virtualConstructor],
                          {stores[virtualConstructor], iteration, rows,
                           count.getOutputs()[0], previous, references[1],
                           body->getArgument(3)},
                          "virtual_" + std::to_string(i));
    previous = allocated.getOutputs()[0];
    stores[virtualConstructor] = allocated.getOutputs()[1];
  }
  auto root = data::MakeOp::create(
      builder, loc, previous.getType(),
      ValueRange{body->getArgument(4), body->getArgument(5)}, "Record");
  SmallVector<Value> counted{root};
  append_range(counted, stores);
  auto count = call(controller.leafCounts[0], counted, "root_count");
  SmallVector<Value> arguments{root, body->getArgument(6)};
  SmallVector<Value> output;
  if (resumeCheck || prefixCheck) {
    auto initial = call(controller.initialize, arguments, "initialize");
    arguments.assign(initial.getOutputs().begin(), initial.getOutputs().end());
    append_range(arguments, stores);
    auto request = call(controller.advance, arguments, "advance");
    arguments.assign(request.getOutputs().begin(), request.getOutputs().end());
    if (prefixCheck) {
      pir::ExchangeOp::create(
          builder, loc, index,
          request.getOutputs()[OracleQueryController::Position], "opening", "V",
          "Observer");
      append_range(arguments, request.getOutputs().take_front(5));
      arguments.push_back(body->getArgument(7));
    } else
      append_range(arguments, body->getArguments().slice(7, 6));
    auto resumed = call(controller.resume[0], arguments, "resume");
    arguments.assign(resumed.getOutputs().begin(), resumed.getOutputs().end());
    append_range(arguments, stores);
    auto complete = call(controller.advance, arguments, "complete");
    auto result = call(controller.finish, complete.getOutputs(), "finish");
    output.assign(result.getOutputs().begin(), result.getOutputs().end());
  } else {
    append_range(arguments, stores);
    auto result = call(controller.evaluate, arguments, "evaluate");
    output.assign(result.getOutputs().begin(), result.getOutputs().end());
  }
  output.push_back(count.getOutputs()[0]);
  pir::MathematicalReturnOp::create(builder, loc, output);
  std::string diagnostics;
  ScopedDiagnosticHandler capture(candidate.getContext(),
                                  [&](Diagnostic &message) {
                                    raw_string_ostream stream(diagnostics);
                                    message.print(stream);
                                    return success();
                                  });
  bool formed = succeeded(verify(candidate));
  require(formed, "controller client formation: " + diagnostics);
  return take(compileRun(print(candidate), "oracle-query-controller.mlir", {},
                         registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  if (argc > 3 || (argc == 3 && StringRef(argv[2]) != "checks" &&
                   (StringRef(argv[2]).size() != 1 || argv[2][0] < '0' ||
                    argv[2][0] > '5'))) {
    errs() << "usage: oracle-query-controller-test [output-directory "
              "[0..5|checks]]\n";
    return 1;
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    stream << '\n';
    return success();
  });
  Cases cases;
  for (unsigned variant = 0; variant < 6; ++variant)
    if (argc != 3 || std::to_string(variant) == argv[2])
      cases.run("generated continuation controller " + Twine(variant), [&] {
        auto original = parse(context, source(variant == 1, variant == 2,
                                              variant == 4, variant == 5));
        auto prepared = mathematical::prepareProtocol(*original, false);
        require(bool(prepared), "preparation: " + diagnostics);
        auto before = print(*prepared);
        auto plan = take(planOracleAnchorStorage(
            *prepared, "main", [](const auto &) -> Expected<std::string> {
              return std::string();
            }));
        auto bounds = take(analyzeOracleQueryCapacity(*prepared, "main"));
        OracleQuerySize capacity;
        for (const auto &query : bounds.queries) {
          capacity.leaves = std::max(capacity.leaves, query.second.leaves);
          capacity.nodes = std::max(capacity.nodes, query.second.nodes);
        }
        auto candidate = fresh(context);
        OracleVirtualFunctionWork work;
        auto controller = take(emitOracleQueryController(
            *candidate, *prepared, plan, "V", plan.constructors.back().kind,
            capacity, work));
        require(print(*prepared) == before,
                "controller emission mutated source");
        uniqueSites(*candidate);
        require(succeeded(verify(*candidate)),
                "controller formation: " + diagnostics);
        if (auto e = checkOracleQueryController(
                *candidate, *prepared, plan, "V", plan.constructors.back().kind,
                capacity, controller))
          throw std::runtime_error(toString(std::move(e)));
        require(bool(controller.evaluate), "ideal controller has no evaluator");
        auto bundle = client(*candidate, plan, controller, registry,
                             variant == 3, variant == 4);
        require(!bundle.empty(), "empty controller executable");
        if (argc >= 2) {
          std::filesystem::create_directories(argv[1]);
          std::ofstream out(
              std::filesystem::path(argv[1]) /
              ("controller-" + std::to_string(variant) + ".bundle"));
          out << bundle;
          require(bool(out), "controller fixture write failed");
        }
      });
  cases.run("a Merkle receiver suspends without a local table evaluator", [&] {
    auto original = parse(context, R"mlir(
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
#K = #protocol.oracle_kind<"table", [!F, 4 : ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({ ^bb0(%data:!D,%position:ui64):
  %rows = "data.index"() {value=4 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="clear"} : (!D,ui64)->!H
  %b = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="merkle"} : (!D,ui64)->!H
  %answer = "protocol.oracle_query"(%b,%position) {owner="V",site="query"} : (!H,ui64)->!F
  "protocol.return"(%answer) : (!F)->()
 }) {sym_name="main",function_type=(!D,ui64)->!F,roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
    auto prepared = mathematical::prepareProtocol(*original, false);
    require(bool(prepared), "Merkle preparation failed");
    auto plan = take(planOracleAnchorStorage(
        *prepared, "main",
        [](const auto &constructor) -> Expected<std::string> {
          return constructor.site == "clear"
                     ? std::string()
                     : std::string("rows.merkle-poseidon2-16.koala-bear.ext4-"
                                   "binomial3/0");
        }));
    for (StringRef role : {"P", "V"}) {
      auto candidate = fresh(context);
      OracleVirtualFunctionWork work;
      auto controller = take(emitOracleQueryController(
          *candidate, *prepared, plan, role, plan.constructors.back().kind,
          {1, 1}, work));
      if (auto e = checkOracleQueryController(*candidate, *prepared, plan, role,
                                              plan.constructors.back().kind,
                                              {1, 1}, controller))
        throw std::runtime_error(toString(std::move(e)));
      require(bool(controller.evaluate) == (role == "P"),
              "local evaluation did not respect table custody");
      if (role == "V")
        candidate->walk([&](func::FuncOp function) {
          require(
              !function.getSymName().starts_with("_oracle_query_read_leaf_"),
              "unavailable evaluator left dormant leaf helpers");
        });
    }
  });
  cases.run(
      "holder contents remain available beside unrelated Merkle receipts", [&] {
        auto original = parse(context, R"mlir(
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
#K = #protocol.oracle_kind<"table", [!F, 4 : ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({ ^bb0(%left:!D,%right:!D,%position:ui64):
  %rows = "data.index"() {value=4 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%left,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="held"} : (!D,ui64)->!H
  %b = "protocol.oracle_send"(%right,%rows) {shape_names=["rows"],shape_bounds={},sender="Q",receivers=["P"],site="received"} : (!D,ui64)->!H
  %answer = "protocol.oracle_query"(%b,%position) {owner="P",site="query"} : (!H,ui64)->!F
  "protocol.return"(%answer) : (!F)->()
 }) {sym_name="main",function_type=(!D,!D,ui64)->!F,roles=["P","Q","V"],input_roles=[["P"],["Q"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
        auto prepared = mathematical::prepareProtocol(*original, false);
        require(bool(prepared), "mixed custody preparation failed");
        auto plan = take(planOracleAnchorStorage(
            *prepared, "main", [](const auto &) -> Expected<std::string> {
              return std::string(
                  "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0");
            }));
        for (auto access : {OracleControllerAccess::Available,
                            OracleControllerAccess::Holder}) {
          auto candidate = fresh(context);
          OracleVirtualFunctionWork work;
          auto controller = take(emitOracleQueryController(
              *candidate, *prepared, plan, "P", plan.constructors[0].kind,
              {1, 1}, work, access));
          if (auto e = checkOracleQueryController(
                  *candidate, *prepared, plan, "P", plan.constructors[0].kind,
                  {1, 1}, controller, access))
            throw std::runtime_error(toString(std::move(e)));
          bool holder = access == OracleControllerAccess::Holder;
          require(
              bool(controller.evaluate) == holder &&
                  bool(controller.contents) == holder,
              "custody either hid held data or exposed received commitments");
          require(controller.constructors.size() == (holder ? 1 : 2),
                  "wrong controller domain");
        }
      });
  const char *mutations[] = {"root tag and instance",
                             "domain operands",
                             "domain relation",
                             "transition bound",
                             "request bound",
                             "resume coordinate",
                             "saved continuation",
                             "child continuation",
                             "frame instance",
                             "child position",
                             "dispatch partition",
                             "advance termination",
                             "answer kind",
                             "return phase",
                             "completion phase",
                             "answer slot",
                             "resume answer",
                             "finish phase",
                             "constructor inventory",
                             "continuation inventory",
                             "ordered queries",
                             "capacity record",
                             "state layout",
                             "missing resume",
                             "missing evaluator",
                             "role record",
                             "stored count",
                             "base count",
                             "virtual count seed",
                             "duplicate count operand",
                             "child count identity",
                             "missing count reader",
                             "missing count recurrence",
                             "previous answer reference",
                             "ordered child answer reference",
                             "answer arena append",
                             "previous answer kind"};
  for (unsigned mutation = 0; mutation < std::size(mutations); ++mutation)
    cases.run(
        "independent controller refusal: " + Twine(mutations[mutation]), [&] {
          auto original = parse(context, source());
          auto prepared = mathematical::prepareProtocol(*original, false);
          require(bool(prepared), "mutation preparation failed");
          auto plan = take(planOracleAnchorStorage(
              *prepared, "main", [](const auto &) -> Expected<std::string> {
                return std::string();
              }));
          auto candidate = fresh(context);
          OracleVirtualFunctionWork work;
          OracleQuerySize capacity{4, 7};
          auto controller = take(emitOracleQueryController(
              *candidate, *prepared, plan, "V", plan.constructors.back().kind,
              capacity, work));
          auto operation = [&](StringRef site) {
            Operation *found = nullptr;
            candidate->walk([&](Operation *op) {
              auto value = op->getAttrOfType<StringAttr>("site");
              if (!found && value && value.getValue() == site)
                found = op;
            });
            require(found != nullptr, "mutation site missing: " + site);
            return found;
          };
          auto constant = [&](StringRef site, StringRef value) {
            auto op = cast<exec::ApplyOp>(operation(site));
            uint64_t number;
            require(!value.getAsInteger(10, number), "invalid index mutation");
            op->setAttr(
                "parameters",
                ArrayAttr::get(
                    &context,
                    {IntegerAttr::get(
                        IntegerType::get(&context, 64, IntegerType::Unsigned),
                        number)}));
          };
          auto exchangeInputs = [&](StringRef site) {
            auto op = cast<exec::ApplyOp>(operation(site));
            SmallVector<Value> inputs(op.getInputs());
            std::swap(inputs[0], inputs[1]);
            op.getInputsMutable().assign(inputs);
          };
          switch (mutation) {
          case 0:
            controller.initialize.walk([&](exec::ReturnOp op) {
              SmallVector<Value> values(op.getValues());
              std::swap(values[0], values[1]);
              op.getValuesMutable().assign(values);
            });
            break;
          case 1:
            exchangeInputs("domain");
            break;
          case 2: {
            auto op = cast<exec::ApplyOp>(operation("domain"));
            SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                op, op.getBindingAttr())
                .setContract("index.equal");
            break;
          }
          case 3:
            constant("transition_bound", "1");
            break;
          case 4:
            constant("request_bound", "0");
            break;
          case 5: {
            auto op = cast<exec::ApplyOp>(operation("request_coordinate_0"));
            op.getInputsMutable()[1].set(op.getInputs()[0]);
            break;
          }
          case 6: {
            auto op = cast<exec::VariantOp>(operation("frame_record"));
            SmallVector<Value> values(op.getPayload());
            std::swap(values[0], values[1]);
            op.getPayloadMutable().assign(values);
            break;
          }
          case 7:
            constant("child_continuation", "0");
            break;
          case 8: {
            auto op = cast<exec::ApplyOp>(operation("load_frame"));
            auto owner = op->getParentOfType<func::FuncOp>();
            op.getInputsMutable()[1].set(owner.getArgument(2));
            break;
          }
          case 9: {
            auto op = cast<exec::ComputeOp>(operation("child_position"));
            op.getInputsMutable()[0].set(op.getInputs()[1]);
            break;
          }
          case 10:
            exchangeInputs("partition");
            break;
          case 11:
            exchangeInputs("stopped_advancing");
            break;
          case 12:
            // The answer kind reuses the exact checked literal. A same-type
            // input is not evidence for that value, even in a formed body.
            controller.resume[0].walk([&](exec::ReturnOp returned) {
              returned.getValuesMutable()[OracleQueryController::Kind].set(
                  controller.resume[0].getArgument(
                      1 + OracleQueryController::Phase));
            });
            break;
          case 13:
            constant("return", "3");
            break;
          case 14:
            constant("completed", "2");
            break;
          case 15: {
            auto op = cast<exec::ApplyOp>(operation("read_answer"));
            auto owner = op->getParentOfType<func::FuncOp>();
            op.getInputsMutable()[1].set(owner.getArgument(1));
            break;
          }
          case 16: {
            exec::ApplyOp value;
            controller.resume[0].walk([&](exec::ApplyOp op) {
              if (op.getSite() == "answer_value")
                value = op;
            });
            require(bool(value), "resume answer missing");
            value.getInputsMutable()[1].set(
                controller.resume[0].getArgument(1));
            break;
          }
          case 17:
            constant("completed_expected", "2");
            break;
          case 18:
            ++controller.constructors[0].source;
            break;
          case 19:
            controller.continuations.back().previousKinds.clear();
            break;
          case 20:
            std::swap(controller.constructors.back().functions.queries[0],
                      controller.constructors.back().functions.queries[1]);
            break;
          case 21:
            ++controller.capacity.leaves;
            break;
          case 22:
            controller.state.pop_back();
            break;
          case 23:
            controller.resume[0] = {};
            break;
          case 24:
            controller.evaluate = {};
            break;
          case 25:
            controller.role = "P";
            break;
          case 26: {
            bool changed = false;
            candidate->walk([&](func::FuncOp function) {
              if (!changed && function.getSymName().starts_with(
                                  "_oracle_query_stored_count_")) {
                function.walk([&](exec::ReturnOp op) {
                  op.getValuesMutable()[0].set(function.getArgument(1));
                });
                changed = true;
              }
            });
            require(changed, "count leaf missing");
            break;
          }
          case 27:
          case 28: {
            auto function =
                controller.constructionCounts[mutation == 27 ? 0 : 2];
            function.walk([&](exec::ApplyOp op) {
              if (op.getSite() == "initial_count")
                op->setAttr(
                    "parameters",
                    ArrayAttr::get(&context,
                                   {IntegerAttr::get(
                                       IntegerType::get(&context, 64,
                                                        IntegerType::Unsigned),
                                       mutation == 27 ? 0 : 1)}));
            });
            break;
          }
          case 29: {
            auto op = cast<exec::ApplyOp>(operation("sum_count_1"));
            op.getInputsMutable()[1].set(op.getInputs()[0]);
            break;
          }
          case 30:
            controller.constructionCounts[2].walk([&](func::CallOp op) {
              auto site = op->getAttrOfType<StringAttr>("runtime.site");
              if (site && site.getValue() == "child_count_1")
                op.setOperand(1,
                              controller.constructionCounts[2].getArgument(1));
            });
            break;
          case 31:
            controller.leafCounts[0] = {};
            break;
          case 32:
            controller.constructionCounts[0] = {};
            break;
          case 33: {
            exec::VariantOp saved;
            candidate->walk([&](exec::VariantOp op) {
              if (op.getSite() == "frame_record" && op.getPayload().size() > 4)
                saved = op;
            });
            require(bool(saved), "saved answer reference missing");
            saved.getPayloadMutable()[4].set(saved.getPayload()[3]);
            break;
          }
          case 34: {
            auto op = cast<exec::ApplyOp>(operation("child_answer_0"));
            auto owner = op->getParentOfType<func::FuncOp>();
            op.getInputsMutable()[1].set(
                owner.getArgument(1 + OracleQueryController::AnswerIndex));
            break;
          }
          case 35:
            controller.resume[0].walk([&](exec::ReturnOp op) {
              op.getValuesMutable()[OracleQueryController::HeaderSize].set(
                  controller.resume[0].getArgument(
                      1 + OracleQueryController::HeaderSize));
            });
            break;
          case 36:
            ++controller.continuations.back().previousKinds[0];
            break;
          }
          require(succeeded(verify(*candidate)),
                  "mutation only failed formation");
          auto refusal = checkOracleQueryController(
              *candidate, *prepared, plan, "V", plan.constructors.back().kind,
              capacity, controller);
          require(bool(refusal),
                  "changed controller passed the actual-body reader");
          require(namesIdentifier(toString(std::move(refusal)),
                                  "oracle-controller-body"),
                  "unexpected controller refusal");
        });
  cases.run(
      "controller generation refuses unsupported capacity and malformed inputs",
      [&] {
        auto original = parse(context, source());
        auto before = print(*original);
        auto plan = take(planOracleAnchorStorage(
            *original, "main", [](const auto &) -> Expected<std::string> {
              return std::string();
            }));
        for (auto capacity :
             {OracleQuerySize{0, 0}, OracleQuerySize{2, 1},
              OracleQuerySize{0, 1048576}, OracleQuerySize{1048576, 1048576}}) {
          auto candidate = fresh(context);
          OracleVirtualFunctionWork work;
          refuses(emitOracleQueryController(*candidate, *original, plan, "V",
                                            plan.constructors.back().kind,
                                            capacity, work),
                  "oracle-controller-capacity");
        }
        auto candidate = fresh(context);
        OracleVirtualFunctionWork work;
        refuses(emitOracleQueryController(*candidate, *original, plan, "V", {},
                                          {4, 7}, work),
                "oracle-controller-source");
        refuses(emitOracleQueryController(*original, *original, plan, "V",
                                          plan.constructors.back().kind, {4, 7},
                                          work),
                "oracle-controller-source");
        refuses(emitOracleQueryController(
                    *candidate, *original, plan, "Missing",
                    plan.constructors.back().kind, {4, 7}, work),
                "oracle-controller-layout");
        work.operations = 0;
        refuses(emitOracleQueryController(*candidate, *original, plan, "V",
                                          plan.constructors.back().kind, {4, 7},
                                          work),
                "oracle-controller-limit");
        require(before == print(*original), "refusal modified the source");
      });
  return cases.result();
}

#include "../lib/Transforms/OracleQueryDemand.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
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
using Demand = OracleQueryDemand;
namespace {
std::string print(Operation *operation) {
  std::string text;
  raw_string_ostream stream(text);
  operation->print(stream);
  return text;
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module) && succeeded(admitStage(*module)), "source admission");
  return module;
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
void checked(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
std::string replace(std::string text, StringRef before, StringRef after) {
  auto offset = text.find(before.str());
  require(offset != std::string::npos, "missing fixture fragment: " + before);
  text.replace(offset, before.size(), after.str());
  return text;
}
std::string fixture(unsigned variant) {
  auto name = variant == 1 ? "query-constructors" : "common-recurrence";
  std::ifstream input(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                      (std::string(name) + ".mlir"));
  require(bool(input), "cannot read demand source fixture");
  std::string text((std::istreambuf_iterator<char>(input)), {});
  if (variant == 2)
    text = replace(text, "oracle_query\"(%b,%mapped)",
                   "oracle_query\"(%a,%mapped)");
  if (variant == 3) {
    auto begin = text.find("   %answer = \"protocol.oracle_query\"");
    auto end = text.find("   \"protocol.oracle_yield\"", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "missing empty virtual fixture fragment");
    text.replace(begin, end - begin,
                 "   %answer = \"data.index\"() {value=9 : ui64} : ()->ui64\n");
  }
  if (variant == 4) {
    text = replace(text, " relation.declare @admissible", R"mlir(
 relation.declare @empty_admissible {kind="external",key="test/demand-empty",revision="0",
  signature=()->i1,purposes=[]}
 "protocol.oracle"() ({ ^bb0(%position:ui64):
   %answer = "data.index"() {value=9 : ui64} : ()->ui64
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="empty",function_type=(ui64)->ui64,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@empty_admissible} : ()->()
 relation.declare @admissible)mlir");
    text = replace(
        text, "   %last =",
        R"mlir(   %empty = "protocol.oracle_virtual"() {callee=@empty,holder="P",receivers=["V"]} : ()->!H
   %last =)mlir");
    text =
        replace(text, "(%trips,%a,%b,%mapped)", "(%trips,%a,%empty,%mapped)");
  }
  return text;
}
OwningOpRef<ModuleOp> fresh(MLIRContext &context) {
  return parse(context, R"mlir(
module { "protocol.module"() ({
 func.func private @placeholder()->i1 { %ok = arith.constant true
 return %ok : i1 }
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
}
struct Input {
  OwningOpRef<ModuleOp> source, prepared, candidate;
  OracleAnchorStorage storage;
  OracleQueryController controller;
  Demand demand;
  pir::OracleKindAttr root;
};
Input emitted(MLIRContext &context, unsigned variant = 0) {
  Input result;
  result.source = parse(context, fixture(variant));
  auto frozenSource = print(*result.source);
  result.prepared = mathematical::prepareProtocol(*result.source, false);
  require(bool(result.prepared), "demand source preparation");
  auto frozenPrepared = print(*result.prepared);
  result.storage = take(planOracleAnchorStorage(
      *result.prepared, "main",
      [](const auto &) -> Expected<std::string> { return std::string(); }));
  auto capacity = take(analyzeOracleQueryCapacity(*result.prepared, "main"));
  OracleQuerySize bound;
  for (const auto &query : capacity.queries) {
    bound.leaves = std::max(bound.leaves, query.second.leaves);
    bound.nodes = std::max(bound.nodes, query.second.nodes);
  }
  result.candidate = fresh(context);
  OracleVirtualFunctionWork work;
  auto controllerRoot = result.storage.constructors[0].kind;
  result.controller = take(emitOracleQueryController(
      *result.candidate, *result.prepared, result.storage, "V", controllerRoot,
      bound, work));
  checked(checkOracleQueryController(*result.candidate, *result.prepared,
                                     result.storage, "V", controllerRoot, bound,
                                     result.controller));
  // The heterogeneous base is intentionally not the controller's root kind.
  result.root = result.storage.constructors[variant == 1 ? 1 : 0].kind;
  auto mathematicalHelpers = [&] {
    unsigned count = 0;
    for (auto function :
         unit(*result.candidate).getBody().front().getOps<func::FuncOp>())
      count += !isScopedExecutionFunction(function);
    return count;
  };
  auto helpersBefore = mathematicalHelpers();
  auto before = work;
  result.demand = take(emitOracleQueryDemand(
      *result.candidate, result.storage, result.controller, result.root, work));
  require(work.operations < before.operations && work.slots < before.slots,
          "demand emission did not debit shared work");
  require(mathematicalHelpers() == helpersBefore,
          "demand emission regenerated mathematical helpers");
  require(succeeded(admitStage(*result.candidate)),
          "demand emission failed source admission");
  checked(checkOracleQueryDemand(*result.candidate, *result.prepared,
                                 result.storage, result.controller, result.root,
                                 result.demand));
  require(print(*result.source) == frozenSource &&
              print(*result.prepared) == frozenPrepared,
          "emission or checking mutated source");
  return result;
}
void rebind(ModuleOp candidate, OracleQueryController &controller,
            Demand &demand) {
  auto bind = [&](func::FuncOp &function) {
    if (function) {
      function = dyn_cast_or_null<func::FuncOp>(
          SymbolTable::lookupSymbolIn(unit(candidate), function.getSymName()));
      require(bool(function), "textual helper was lost");
    }
  };
  for (auto &item : controller.constructors) {
    bind(item.lookup);
    bind(item.functions.answer);
    for (auto &query : item.functions.queries)
      bind(query.position);
  }
  for (auto *inventory : {&controller.leafCounts, &controller.rowCounts,
                          &controller.constructionCounts, &controller.resume})
    for (auto &function : *inventory)
      bind(function);
  for (auto *function :
       {&controller.initialize, &controller.advance, &controller.finish,
        &controller.evaluate, &controller.contents, &demand.initialize,
        &demand.advance, &demand.consume})
    bind(*function);
}
void refusesDemand(Input &input) {
  auto frozenSource = print(*input.prepared);
  auto check = [&](ModuleOp candidate) {
    require(succeeded(verify(candidate)), "mutation failed ordinary formation");
    auto frozenCandidate = print(candidate);
    auto error =
        checkOracleQueryDemand(candidate, *input.prepared, input.storage,
                               input.controller, input.root, input.demand);
    require(bool(error), "mutated demand passed actual-body checking");
    require(namesIdentifier(toString(std::move(error)), "oracle-demand-body"),
            "unexpected demand refusal");
    require(print(candidate) == frozenCandidate &&
                print(*input.prepared) == frozenSource,
            "refusal mutated candidate or prepared source");
  };
  check(*input.candidate);
  // Some adversaries intentionally fail source admission. Parse without
  // admission so the independent reader must refuse the fresh actual body.
  auto freshCandidate = parseSourceString<ModuleOp>(
      print(*input.candidate),
      ParserConfig(input.candidate->getContext(), false));
  require(bool(freshCandidate), "mutated demand text did not parse");
  rebind(*freshCandidate, input.controller, input.demand);
  check(*freshCandidate);
}
// Follow only actual discovery edges. Pure computations must be existing
// checked position maps, even though the evaluator's answer helpers coexist.
void noAnswers(ModuleOp candidate, const OracleQueryController &controller,
               const Demand &demand) {
  auto closure = take(readSourceExecutionClosure(unit(candidate)));
  std::set<std::string> positions, visited;
  for (const auto &item : controller.constructors)
    for (const auto &query : item.functions.queries)
      positions.insert(
          SymbolTable::getSymbolName(query.position).getValue().str());
  std::function<void(func::FuncOp)> visit = [&](func::FuncOp function) {
    if (!visited.insert(function.getSymName().str()).second)
      return;
    auto found = closure.bodies.find(function.getSymName().str());
    require(found != closure.bodies.end(), "discovery closure is missing");
    for (const auto &step : found->second) {
      if (auto compute = dyn_cast<exec::ComputeOp>(step.operation)) {
        auto callee = dyn_cast_or_null<func::FuncOp>(
            SymbolTable::lookupSymbolIn(unit(candidate), compute.getCallee()));
        require(callee && positions.count(callee.getSymName().str()),
                "demand called an answer or unrecognized computation");
      }
      if (auto call = dyn_cast<func::CallOp>(step.operation)) {
        auto callee = dyn_cast_or_null<func::FuncOp>(
            SymbolTable::lookupSymbolIn(unit(candidate), call.getCallee()));
        require(bool(callee), "discovery callee is missing");
        visit(callee);
      }
      for (auto region : step.regions)
        visit(region);
    }
  };
  visit(demand.initialize);
  visit(demand.advance);
  visit(demand.consume);
  for (auto function : unit(candidate).getBody().front().getOps<func::FuncOp>())
    if (function.getSymName().starts_with("_oracle_demand_"))
      require(isScopedExecutionFunction(function),
              "demand regenerated a mathematical helper");
}
Operation *operation(ModuleOp candidate, StringRef site,
                     StringRef name = "exec.apply") {
  Operation *found = nullptr;
  candidate.walk([&](Operation *op) {
    auto owner = op->getParentOfType<func::FuncOp>();
    auto label = op->getAttrOfType<StringAttr>(
        name == "func.call" ? "runtime.site" : "site");
    if (!found && owner && owner.getSymName().starts_with("_oracle_demand_") &&
        op->getName().getStringRef() == name && label &&
        label.getValue() == site)
      found = op;
  });
  require(found != nullptr, "missing demand mutation site: " + site);
  return found;
}
void constant(ModuleOp candidate, StringRef site, uint64_t value) {
  auto op = operation(candidate, site);
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  op->setAttr("parameters", ArrayAttr::get(candidate.getContext(),
                                           {IntegerAttr::get(index, value)}));
}
void emptyStore(ModuleOp candidate) {
  auto call =
      cast<func::CallOp>(operation(candidate, "load_anchor", "func.call"));
  auto owner = call->getParentOfType<func::FuncOp>();
  auto store = call.getOperand(3);
  auto element = cast<data::SequenceType>(store.getType()).getElementType();
  auto *previous = call->getBlock();
  auto *continuation = previous->splitBlock(call->getIterator());
  OpBuilder builder(candidate.getContext());
  builder.setInsertionPointToEnd(previous);
  mathematical::RealizationEmitter bindings(unit(candidate),
                                            "_demand_mutation_");
  auto binding = bindings.binding(
      builder, call.getLoc(), {"sequence.empty", {TypeAttr::get(element)}, ""});
  exec::ScopedExecutionBuilder control(builder, owner);
  auto empty =
      control
          .invoke("exec.apply", store.getType(), control.scoped({}),
                  {builder.getNamedAttr("binding", binding),
                   builder.getNamedAttr("parameters", builder.getArrayAttr({})),
                   builder.getNamedAttr("site",
                                        builder.getStringAttr("empty_store"))})
          .front();
  cf::BranchOp::create(builder, call.getLoc(), continuation, ValueRange{});
  call.setOperand(3, empty);
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  for (unsigned variant = 0; variant < 5; ++variant)
    cases.run("actual demand and fresh text " + Twine(variant), [&] {
      auto input = emitted(context, variant);
      require(input.demand.state.size() == Demand::HeaderSize + 1,
              "demand retained answer arenas");
      if (variant == 1)
        require(!sameOracleReferenceKind(input.controller.kinds[0], input.root),
                "nonzero root-kind case lost");
      noAnswers(*input.candidate, input.controller, input.demand);
      auto freshCandidate = parse(context, print(*input.candidate));
      rebind(*freshCandidate, input.controller, input.demand);
      checked(checkOracleQueryDemand(*freshCandidate, *input.prepared,
                                     input.storage, input.controller,
                                     input.root, input.demand));
      noAnswers(*freshCandidate, input.controller, input.demand);
    });
  const char *mutations[] = {
      "domain branch",    "domain predicate",   "cut phase",
      "child position",   "child order",        "immutable store",
      "child reference",  "saved continuation", "consume guard",
      "empty transition", "root position",      "transition bound",
      "parent position",  "next child",         "frame reference",
      "kind association", "return phase",       "completion phase",
      "state layout",     "missing consume",    "duplicate domain occurrence"};
  for (unsigned mutation = 0; mutation < std::size(mutations); ++mutation)
    cases.run("independent demand refusal: " + Twine(mutations[mutation]), [&] {
      auto input = emitted(context, mutation == 9 ? 3 : 0);
      auto candidate = *input.candidate;
      switch (mutation) {
      case 0: {
        auto test = operation(candidate, "domain_branch", "exec.test");
        auto dispatch =
            cast<exec::DispatchOp>(test->getBlock()->getTerminator());
        auto branch =
            cast<cf::CondBranchOp>(dispatch->getSuccessor(0)->getTerminator());
        auto *left = branch->getSuccessor(0);
        branch->setSuccessor(branch->getSuccessor(1), 0);
        branch->setSuccessor(left, 1);
        break;
      }
      case 1: {
        auto op = cast<exec::ApplyOp>(operation(candidate, "domain"));
        SmallVector<Value> inputs(op.getInputs());
        std::swap(inputs[0], inputs[1]);
        op.getInputsMutable().assign(inputs);
        break;
      }
      case 2:
        constant(candidate, "domain_cut", Demand::Request);
        break;
      case 3: {
        auto op = cast<exec::ComputeOp>(
            operation(candidate, "child_position", "exec.compute"));
        op.getInputsMutable()[0].set(op.getInputs()[1]);
        break;
      }
      case 4: {
        auto op = operation(candidate, "child_position", "exec.compute");
        op->setAttr("callee",
                    FlatSymbolRefAttr::get(input.controller.constructors.back()
                                               .functions.queries[1]
                                               .position));
        break;
      }
      case 5:
        emptyStore(candidate);
        break;
      case 6: {
        auto op = operation(candidate, "child_reference", "exec.match");
        auto owner = op->getParentOfType<func::FuncOp>();
        const auto &item = input.controller.constructors.back();
        const auto &fields =
            input.storage.constructors[item.source].roles[item.role].fields;
        auto other = find_if(
            fields, [](const auto &field) { return field.name == "source.1"; });
        require(other != fields.end(), "missing alternate source reference");
        op->setOperand(1, owner.getArgument(1 + input.demand.state.size() +
                                            input.controller.stores.size() +
                                            (other - fields.begin())));
        break;
      }
      case 7: {
        auto op = cast<exec::VariantOp>(
            operation(candidate, "frame_record", "exec.variant"));
        op.getPayloadMutable()[Demand::ParentContinuation].set(
            op.getPayload()[Demand::ParentPosition]);
        break;
      }
      case 8:
        constant(candidate, "suspended_expected", Demand::Return);
        break;
      case 9:
        constant(candidate, "empty_return", Demand::Request);
        break;
      case 10:
        input.demand.initialize.walk([&](exec::ReturnOp op) {
          op.getValuesMutable()[Demand::Position].set(
              op.getValues()[Demand::Instance]);
        });
        break;
      case 11:
        constant(candidate, "transition_bound", 1);
        break;
      case 12: {
        auto op = operation(candidate, "restore_parent", "func.call");
        op->setOperand(1 + Demand::Position,
                       op->getOperand(1 + Demand::Instance));
        break;
      }
      case 13:
        constant(candidate, "next_child", 2);
        break;
      case 14: {
        auto op = cast<exec::ApplyOp>(operation(candidate, "load_frame"));
        op.getInputsMutable()[1].set(
            op->getParentOfType<func::FuncOp>().getArgument(1 +
                                                            Demand::Instance));
        break;
      }
      case 15:
        constant(candidate, "child_kind", 1);
        break;
      case 16:
        constant(candidate, "return_parent", Demand::Completed);
        break;
      case 17:
        constant(candidate, "completed", Demand::DomainCut);
        break;
      case 18:
        input.demand.state.pop_back();
        break;
      case 19:
        input.demand.consume = {};
        break;
      case 20: {
        auto test = operation(candidate, "domain_branch", "exec.test");
        auto owner = test->getParentOfType<func::FuncOp>();
        auto site = StringAttr::get(&context, "domain");
        test->setAttr("site", site);
        owner.walk([&](runtime::EnterScopeOp enter) {
          if (enter.getSite() == "domain_branch")
            enter->setAttr("site", site);
        });
        require(failed(admitStage(candidate)),
                "duplicate domain occurrence passed source admission");
        break;
      }
      }
      refusesDemand(input);
    });
  const char *dependencies[] = {"source query reference",
                                "source query position",
                                "controller position map", "controller body"};
  for (unsigned mutation = 0; mutation < std::size(dependencies); ++mutation)
    cases.run(
        "independent dependency refusal: " + Twine(dependencies[mutation]),
        [&] {
          auto input = emitted(context);
          if (mutation < 2) {
            auto definition = cast<pir::OracleDefinitionOp>(
                SymbolTable::lookupSymbolIn(unit(*input.prepared), "combine"));
            SmallVector<pir::OracleQueryOp> queries(
                definition.getBody().front().getOps<pir::OracleQueryOp>());
            require(queries.size() == 2, "missing source query pair");
            if (mutation == 0)
              queries[1].getHandleMutable().assign(queries[0].getHandle());
            else
              queries[1].getPositionMutable().assign(queries[0].getPosition());
          } else if (mutation == 2) {
            auto position = input.controller.constructors.back()
                                .functions.queries[0]
                                .position;
            auto returned = cast<func::ReturnOp>(position.front().back());
            require(returned.getOperand(0) != position.getArgument(0),
                    "missing distinct position-map parameter");
            returned.setOperand(0, position.getArgument(0));
          } else {
            input.controller.advance.walk([&](exec::ReturnOp returned) {
              returned.getValuesMutable()[OracleQueryController::Position].set(
                  returned.getValues()[OracleQueryController::Instance]);
            });
          }
          require(succeeded(admitStage(*input.prepared)) &&
                      succeeded(admitStage(*input.candidate)),
                  "dependency mutation failed source admission");
          refusesDemand(input);
        });
  cases.run("capacity and shared-work refusal preserve source", [&] {
    auto input = emitted(context);
    auto frozen = print(*input.prepared);
    auto refuse = [&](OracleQueryController controller,
                      OracleVirtualFunctionWork work, pir::OracleKindAttr root,
                      StringRef identifier) {
      // Even a refused producer receives its own disposable candidate.
      auto discarded = parse(context, print(*input.candidate));
      auto demand = input.demand;
      rebind(*discarded, controller, demand);
      refuses(emitOracleQueryDemand(*discarded, input.storage, controller, root,
                                    work),
              identifier);
    };
    for (auto capacity :
         {OracleQuerySize{0, 0}, OracleQuerySize{2, 1},
          OracleQuerySize{0, 1048576}, OracleQuerySize{1048576, 1048576}}) {
      auto controller = input.controller;
      controller.capacity = capacity;
      refuse(controller, {}, input.root, "oracle-demand-capacity");
    }
    for (bool operations : {false, true}) {
      OracleVirtualFunctionWork work;
      if (operations)
        work.operations = 0;
      else
        work.slots = 0;
      refuse(input.controller, work, input.root, "oracle-demand-limit");
    }
    refuse(input.controller, {}, {}, "oracle-demand-layout");
    OracleVirtualFunctionWork work;
    refuses(emitOracleQueryDemand({}, input.storage, input.controller,
                                  input.root, work),
            "oracle-demand-source");
    require(print(*input.prepared) == frozen,
            "refusal mutated prepared source");
  });
  return cases.result();
}

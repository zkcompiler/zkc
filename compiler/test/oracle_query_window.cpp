#include "../lib/Transforms/OracleQueryWindow.h"
#include "../lib/Transforms/OracleVerificationContext.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
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
using Controller = OracleQueryController;
using Demand = OracleQueryDemand;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
std::string print(Operation *operation) {
  std::string text;
  raw_string_ostream stream(text);
  operation->print(stream);
  return text;
}
void checked(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refused(Error error, StringRef code = "oracle-window-body") {
  require(bool(error), "expected window refusal");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module) && succeeded(admitStage(*module)), "source admission");
  return module;
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
  OracleQuerySize capacity;
  OracleQueryController receiver, holder;
  std::vector<OracleMerkleFunctions> merkle;
  OracleQueryExchange exchange;
  OracleQueryResponse response;
  Demand demand;
  pir::OracleKindAttr root;
  OracleQueryWindow window;
  OracleVirtualFunctionWork work;
};
std::string scheme(const OracleAnchorConstructor &anchor) {
  auto field = cast<algebra::FieldType>(anchor.kind.getAnswerType());
  return "rows.merkle-poseidon2-16." + field.getDomain().str() + "/0";
}
Error checkWindow(const Input &input) {
  auto context = OracleVerificationContext::read(*input.candidate);
  if (!context)
    return context.takeError();
  return checkOracleQueryWindow(*context, input.receiver, input.demand,
                                input.exchange, input.response, input.window);
}
void checkModel(const Input &input) {
  auto target = take(OracleVerificationContext::read(*input.candidate));
  auto source = take(OracleVerificationContext::read(*input.prepared));
  auto root = input.storage.constructors[0].kind;
  checked(checkOracleQueryController(target, source, input.storage, "V", root,
                                     input.capacity, input.receiver,
                                     OracleControllerAccess::Available));
  checked(checkOracleQueryController(target, source, input.storage, "P", root,
                                     input.capacity, input.holder,
                                     OracleControllerAccess::Holder));
  for (auto [ordinal, anchor] : enumerate(input.storage.constructors)) {
    if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual)
      continue;
    checked(checkOracleMerkle(target, input.merkle[ordinal], anchor.kind,
                              anchor.scheme, OracleLeafGrouping::Individual,
                              OracleLeafOrder::Natural));
  }
}
Input emitted(MLIRContext &context, unsigned variant = 0,
              uint64_t packetCapacity = 2) {
  Input input;
  auto path = std::filesystem::path(ZKC_ORACLE_FIXTURES) / "query-constructors.mlir";
  std::ifstream fixture(path);
  require(bool(fixture), "cannot read window source fixture");
  std::string text((std::istreambuf_iterator<char>(fixture)), {});
  auto replace = [&](StringRef before, StringRef after) {
    auto offset = text.find(before.str());
    require(offset != std::string::npos,
            "missing window fixture fragment: " + before);
    text.replace(offset, before.size(), after.str());
  };
  // Same-kind variants permit duplicate occurrences and a zero-query child.
  if (variant >= 2) {
    replace("!BF = !algebra.field<\"koala-bear\">",
            "!BF = !algebra.field<\"koala-bear.ext4-binomial3\">");
    replace("!BD = !algebra.field_vector<\"koala-bear\">",
            "!BD = !algebra.field_vector<\"koala-bear.ext4-binomial3\">");
  }
  if (variant == 2)
    replace("oracle_query\"(%b,%mapped)", "oracle_query\"(%a,%position)");
  if (variant == 3) {
    auto begin = text.find("   %answer = \"protocol.oracle_query\"");
    auto end = text.find("   \"protocol.oracle_yield\"", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "empty virtual source");
    text.replace(begin, end - begin,
                 "   %answer = \"algebra.constant\"() "
                 "{value=#algebra.literal<!F, 9 : ui31>} : ()->!F\n");
  }
  if (variant == 4) {
    replace(" relation.declare @admissible", R"mlir(
 relation.declare @empty_admissible {kind="external",key="test/window-empty",revision="0",
  signature=()->i1,purposes=[]}
 "protocol.oracle"() ({ ^bb0(%position:ui64):
   %answer = "algebra.constant"() {value=#algebra.literal<!F, 9 : ui31>} : ()->!F
   "protocol.oracle_yield"(%answer) : (!F)->()
 }) {sym_name="empty",function_type=(ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@empty_admissible} : ()->()
 relation.declare @admissible)mlir");
    replace(
        "   %last =",
        R"mlir(   %empty = "protocol.oracle_virtual"() {callee=@empty,holder="P",receivers=["V"]} : ()->!H
   %last =)mlir");
    replace("(%trips,%a,%b,%mapped)", "(%trips,%a,%empty,%mapped)");
  }
  input.source = parse(context, text);
  auto frozenSource = print(*input.source);
  input.prepared = mathematical::prepareProtocol(*input.source, false);
  require(bool(input.prepared), "source preparation");
  auto frozenPrepared = print(*input.prepared);
  input.storage = take(planOracleAnchorStorage(
      *input.prepared, "main", [](const auto &anchor) -> Expected<std::string> {
        return scheme(anchor);
      }));
  auto bounds = take(analyzeOracleQueryCapacity(*input.prepared, "main"));
  for (const auto &query : bounds.queries) {
    input.capacity.leaves =
        std::max(input.capacity.leaves, query.second.leaves);
    input.capacity.nodes = std::max(input.capacity.nodes, query.second.nodes);
  }
  input.candidate = fresh(context);
  input.work.operations = 1000000;
  input.work.slots = 100000000;
  auto root = input.storage.constructors[0].kind;
  input.receiver = take(emitOracleQueryController(
      *input.candidate, *input.prepared, input.storage, "V", root,
      input.capacity, input.work));
  input.holder = take(emitOracleQueryController(
      *input.candidate, *input.prepared, input.storage, "P", root,
      input.capacity, input.work, OracleControllerAccess::Holder));
  input.merkle.resize(input.storage.constructors.size());
  for (auto [ordinal, anchor] : enumerate(input.storage.constructors))
    if (anchor.constructor != OracleAnchorConstructor::Kind::Virtual)
      input.merkle[ordinal] = take(emitOracleMerkle(
          *input.candidate, anchor.kind, anchor.scheme,
          OracleLeafGrouping::Individual, OracleLeafOrder::Natural));
  input.exchange = take(planOracleQueryExchange(input.storage, input.receiver,
                                                input.holder, input.merkle));
  checkModel(input);
  input.response = take(
      emitOracleQueryResponse(*input.candidate, input.exchange, input.work));
  input.root = input.storage.constructors[variant == 1 ? 1 : 0].kind;
  input.demand = take(emitOracleQueryDemand(
      *input.candidate, input.storage, input.receiver, input.root, input.work));
  checked(checkOracleQueryDemand(*input.candidate, *input.prepared,
                                 input.storage, input.receiver, input.root,
                                 input.demand));
  auto before = input.work;
  input.window = take(emitOracleQueryWindow(
      *input.candidate, input.receiver, input.demand, input.exchange,
      input.response, packetCapacity, input.work));
  require(input.work.operations < before.operations &&
              input.work.slots < before.slots,
          "window emission did not debit shared work");
  checked(checkWindow(input));
  require(print(*input.source) == frozenSource &&
              print(*input.prepared) == frozenPrepared,
          "window emission or checking mutated source");
  return input;
}
void rebind(Input &input) {
  auto bind = [&](func::FuncOp &function) {
    if (!function)
      return;
    function = dyn_cast_or_null<func::FuncOp>(SymbolTable::lookupSymbolIn(
        unit(*input.candidate), function.getSymName()));
    require(bool(function), "serialized helper was lost");
  };
  for (auto *controller : {&input.receiver, &input.holder}) {
    for (auto &item : controller->constructors) {
      bind(item.lookup);
      bind(item.functions.answer);
      for (auto &query : item.functions.queries)
        bind(query.position);
    }
    for (auto *inventory :
         {&controller->resume, &controller->leafCounts, &controller->rowCounts,
          &controller->constructionCounts})
      for (auto &function : *inventory)
        bind(function);
    for (auto *function :
         {&controller->initialize, &controller->advance, &controller->finish,
          &controller->evaluate, &controller->contents})
      bind(*function);
  }
  for (auto &helpers : input.merkle)
    for (auto *function : {&helpers.position, &helpers.commit, &helpers.open,
                           &helpers.authenticate})
      bind(*function);
  for (auto &arm : input.exchange.arms)
    for (auto *function : {&arm.holderLookup, &arm.receiverLookup, &arm.open,
                           &arm.authenticate, &arm.resume})
      bind(*function);
  bind(input.response.authenticate);
  bind(input.response.resume);
  for (auto *function :
       {&input.demand.initialize, &input.demand.advance, &input.demand.consume,
        &input.window.collect, &input.window.replay, &input.window.finish})
    bind(*function);
}
Operation *site(Input &input, StringRef name, bool windowOnly = true) {
  Operation *found = nullptr;
  input.candidate->walk([&](Operation *op) {
    if (op->getName().getDialectNamespace() == "runtime")
      return; // Scope bookkeeping shares the semantic operation's site.
    auto owner = op->getParentOfType<func::FuncOp>();
    if (!owner ||
        (windowOnly && !owner.getSymName().starts_with("_oracle_window_")))
      return;
    auto actual = op->getAttrOfType<StringAttr>(
        isa<func::CallOp>(op) ? "runtime.site" : "site");
    if (actual && actual.getValue() == name) {
      require(!found, "ambiguous mutation site: " + name);
      found = op;
    }
  });
  require(found, "missing mutation site: " + name);
  return found;
}
void constant(Input &input, StringRef name, uint64_t value) {
  auto index = IntegerType::get(input.candidate->getContext(), 64,
                                IntegerType::Unsigned);
  site(input, name)
      ->setAttr("parameters", ArrayAttr::get(index.getContext(),
                                             {IntegerAttr::get(index, value)}));
}
void insertBefore(
    Operation *before,
    llvm::function_ref<void(exec::ScopedExecutionBuilder &, OpBuilder &)> emit) {
  auto owner = before->getParentOfType<func::FuncOp>();
  auto *head = before->getBlock();
  auto *tail = head->splitBlock(Block::iterator(before));
  OpBuilder builder(before->getContext());
  builder.setInsertionPointToEnd(head);
  exec::ScopedExecutionBuilder control(builder, owner);
  emit(control, builder);
  cf::BranchOp::create(builder, before->getLoc(), tail, ValueRange{});
}
void invoke(exec::ScopedExecutionBuilder &c, OpBuilder &b, func::FuncOp helper,
            ValueRange inputs, StringRef name) {
  c.invoke("func.call", scopedDataSignature(helper).getResults(),
           c.scoped(inputs),
           {b.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
            b.getNamedAttr("runtime.site", b.getStringAttr(name))});
}
func::FuncOp branch(Input &input, StringRef name, unsigned ordinal) {
  auto closure = take(readSourceExecutionClosure(unit(*input.candidate)));
  auto *op = site(input, name);
  auto owner = op->getParentOfType<func::FuncOp>();
  for (const auto &step : closure.bodies.at(owner.getSymName().str()))
    if (step.operation == op) {
      require(ordinal < step.regions.size(), "missing actual region ordinal");
      return step.regions[ordinal];
    }
  throw std::runtime_error("missing actual branch association");
}
// Substitute a formed helper that omits the original source work. Checking
// must bind the exact expected helper, not accept a matching signature.
func::FuncOp bypass(Input &input, func::FuncOp original,
                    bool fakeFinish = false) {
  OpBuilder b(input.candidate->getContext());
  b.setInsertionPointToEnd(&unit(*input.candidate).getBody().front());
  auto loc = input.candidate->getLoc();
  auto helper = func::FuncOp::create(b, loc, "_window_bypass",
                                     original.getFunctionType());
  helper.setPrivate();
  helper.setNoInline(true);
  helper->setAttr("runtime.origin",
                  b.getArrayAttr({b.getStringAttr(helper.getSymName()),
                                  b.getArrayAttr({})}));
  b.setInsertionPointToEnd(helper.addEntryBlock());
  exec::ScopedExecutionBuilder c(b, helper);
  auto a = helper.getArguments().drop_front();
  if (!fakeFinish) {
    unsigned n = scopedDataSignature(original).getNumResults();
    c.returned(a.take_front(n));
  } else {
    // Extract the arena value while skipping controller.finish's completion
    // and root-kind guards. This is a well-typed but invalid finalization.
    mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                              "_window_attack_binding_");
    Type answer = scopedDataSignature(original).getResult(0);
    auto binding =
        bindings.binding(b, loc, {"sequence.at", {TypeAttr::get(answer)}, ""});
    auto value = c.invoke(
        "exec.apply", answer,
        c.scoped({a[Controller::HeaderSize], a[Controller::AnswerIndex]}),
        {b.getNamedAttr("binding", binding),
         b.getNamedAttr("parameters", b.getArrayAttr({})),
         b.getNamedAttr("site", b.getStringAttr("skip_completion_guards"))});
    c.returned(value);
  }
  return helper;
}
void emptyStore(Input &input, StringRef name, unsigned operand) {
  auto call = cast<func::CallOp>(site(input, name));
  auto store = call.getOperand(operand);
  insertBefore(call, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
    mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                              "_window_empty_binding_");
    auto element = cast<data::SequenceType>(store.getType()).getElementType();
    auto binding = bindings.binding(
        b, call.getLoc(), {"sequence.empty", {TypeAttr::get(element)}, ""});
    auto empty = c.invoke(
        "exec.apply", store.getType(), c.scoped({}),
        {b.getNamedAttr("binding", binding),
         b.getNamedAttr("parameters", b.getArrayAttr({})),
         b.getNamedAttr("site", b.getStringAttr("wrong_immutable_store"))})[0];
    call.setOperand(operand, empty);
  });
}
void omitGuard(Input &input, StringRef name) {
  auto *op = site(input, name);
  OpBuilder b(op);
  OperationState replacement(op->getLoc(), "exec.returned");
  replacement.addTypes(op->getResultTypes());
  auto *returned = b.create(replacement);
  op->replaceAllUsesWith(returned->getResults());
  op->erase();
}
void injectDiscovery(Input &input, StringRef name, unsigned ordinal) {
  auto region = branch(input, name, ordinal);
  exec::CompleteOp complete;
  region.walk([&](exec::CompleteOp op) { complete = op; });
  require(bool(complete), "identity branch lacks completion");
  auto a = region.getArguments().drop_front();
  Values inputs(a.take_front(input.demand.state.size()));
  append_range(inputs, a.drop_front(input.demand.state.size() + 2));
  insertBefore(complete, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
    invoke(c, b, input.demand.advance, inputs, "unwanted_discovery");
  });
}
void reorderReplay(Input &input) {
  auto region = branch(input, "window_replay_loop", 0);
  region.getBody().dropAllReferences();
  region.getBody().getBlocks().clear();
  OpBuilder b(input.candidate->getContext());
  b.setInsertionPointToEnd(region.addEntryBlock());
  exec::ScopedExecutionBuilder c(b, region);
  mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                            "_reordered_window_binding_");
  auto a = region.getArguments().drop_front();
  unsigned n = input.receiver.state.size();
  auto at = [&](Value sequence, Type element, StringRef name) {
    auto binding = bindings.binding(
        b, region.getLoc(), {"sequence.at", {TypeAttr::get(element)}, ""});
    return c.invoke("exec.apply", element, c.scoped({sequence, a[0]}),
                    {b.getNamedAttr("binding", binding),
                     b.getNamedAttr("parameters", b.getArrayAttr({})),
                     b.getNamedAttr("site", b.getStringAttr(name))})[0];
  };
  auto request = at(a[n + 1], input.exchange.request, "window_replay_request");
  auto answer = at(a[n + 2], input.response.answer, "window_replay_answer");
  Values resume{request, answer};
  append_range(resume, a.slice(1, n));
  auto resumed = c.invoke(
      "func.call", input.receiver.state, c.scoped(resume),
      {b.getNamedAttr("callee", FlatSymbolRefAttr::get(input.response.resume)),
       b.getNamedAttr("runtime.site",
                      b.getStringAttr("window_replay_resume"))});
  append_range(resumed, a.drop_front(n + 3));
  auto advanced = c.invoke(
      "func.call", input.receiver.state, c.scoped(resumed),
      {b.getNamedAttr("callee", FlatSymbolRefAttr::get(input.receiver.advance)),
       b.getNamedAttr("runtime.site",
                      b.getStringAttr("window_replay_advance"))});
  c.complete(advanced);
}
void rejects(Input &input) {
  auto check = [&] {
    require(succeeded(verify(*input.candidate)),
            "mutation failed ordinary MLIR formation");
    auto frozen = print(*input.candidate);
    auto current = OracleVerificationContext::read(*input.candidate);
    if (!current) {
      // Missing guards or broken native control may already be refused by
      // admission. Never turn that refusal into a positive window result.
      consumeError(current.takeError());
    } else {
      refused(checkOracleQueryWindow(*current, input.receiver, input.demand,
                                     input.exchange, input.response,
                                     input.window));
    }
    require(print(*input.candidate) == frozen, "reader mutated candidate");
  };
  check();
  auto copy = parseSourceString<ModuleOp>(
      print(*input.candidate),
      ParserConfig(input.candidate->getContext(), false));
  require(bool(copy), "mutated text failed to parse");
  auto old = std::move(input.candidate);
  input.candidate = std::move(copy);
  rebind(input);
  check();
}
// Audit the actual local window closure without descending into the separately
// checked demand/controller/response bodies. No hidden source work is ignored.
void effects(const Input &input) {
  auto closure = take(readSourceExecutionClosure(unit(*input.candidate)));
  auto inspect = [&](func::FuncOp entry, std::set<std::string> expected) {
    std::set<std::string> visited, calls;
    std::function<void(func::FuncOp)> visit = [&](func::FuncOp helper) {
      require(visited.insert(helper.getSymName().str()).second,
              "cyclic window regions");
      for (const auto &step : closure.bodies.at(helper.getSymName().str())) {
        require(!isa<exec::ComputeOp>(step.operation),
                "window evaluated an unowned source helper");
        if (auto call = dyn_cast<func::CallOp>(step.operation)) {
          require(expected.count(call.getCallee().str()),
                  "unexpected window call");
          calls.insert(call.getCallee().str());
        }
        for (auto region : step.regions)
          visit(region);
      }
    };
    visit(entry);
    require(calls == expected, "window omitted a required call");
  };
  inspect(input.window.collect, {func::FuncOp(input.demand.advance).getSymName().str(),
                                 func::FuncOp(input.demand.consume).getSymName().str()});
  inspect(input.window.replay, {func::FuncOp(input.receiver.advance).getSymName().str(),
                                func::FuncOp(input.response.resume).getSymName().str()});
  inspect(input.window.finish, {func::FuncOp(input.receiver.advance).getSymName().str(),
                                func::FuncOp(input.receiver.finish).getSymName().str()});
}
// Optional production compiler client for this primitive, with caller-supplied
// stores and authenticated answers. It deliberately makes no complete-window
// authentication/transport claim. The test only emits it when given a path.
std::string client(Input &input, DialectRegistry &registry) {
  auto candidate = *input.candidate;
  OpBuilder b(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  auto reference = scopedDataSignature(input.receiver.initialize).getInput(0);
  Types inputs{reference,
               index,
               input.window.requestSequence,
               input.window.answerSequence,
               index,
               index,
               b.getI1Type()};
  append_range(inputs, input.receiver.stores);
  Types outputs{input.window.requestSequence, b.getI1Type()};
  append_range(outputs,
               scopedDataSignature(input.receiver.finish).getResults());
  auto owner = b.getArrayAttr({b.getStringAttr("V")});
  OperationState entry(loc, "protocol.func");
  entry.addAttribute("sym_name", b.getStringAttr("main"));
  entry.addAttribute("function_type",
                     TypeAttr::get(b.getFunctionType(inputs, outputs)));
  entry.addAttribute("roles", owner);
  entry.addAttribute("input_roles", b.getArrayAttr(SmallVector<Attribute>(
                                        inputs.size(), owner)));
  entry.addAttribute("output_roles", b.getArrayAttr(SmallVector<Attribute>(
                                         outputs.size(), owner)));
  auto *body = new Block;
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  entry.addRegion()->push_back(body);
  b.setInsertionPointToEnd(&unit(candidate).getBody().front());
  b.create(entry);
  b.setInsertionPointToEnd(body);
  auto a = body->getArguments();
  auto call = [&](func::FuncOp function, ValueRange args, StringRef name) {
    return pir::LocalCallOp::create(b, loc,
                                    scopedDataSignature(function).getResults(),
                                    args, function.getSymName(), name, "V")
        .getOutputs();
  };
  auto discovery =
      call(input.demand.initialize, a.take_front(2), "demand_initialize");
  auto evaluator =
      call(input.receiver.initialize, a.take_front(2), "controller_initialize");
  Values collect(discovery);
  append_range(collect, Values{a[2], a[6]});
  append_range(collect, a.drop_front(7));
  auto collected = call(input.window.collect, collect, "collect");
  Values replay(evaluator);
  append_range(replay,
               Values{collected[input.demand.state.size()], a[3], a[4], a[5]});
  append_range(replay, a.drop_front(7));
  auto resumed = call(input.window.replay, replay, "replay");
  Values finish(resumed);
  append_range(finish, a.drop_front(7));
  auto answer = call(input.window.finish, finish, "finish");
  Values returned{collected[input.demand.state.size()],
                  collected[input.demand.state.size() + 1]};
  append_range(returned, answer);
  pir::MathematicalReturnOp::create(b, loc, returned);
  require(succeeded(verify(candidate)), "window client formation");
  return take(compileRun(print(candidate), "oracle-query-window.mlir", {},
                         registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  if (argc > 2) {
    errs() << "usage: oracle-query-window-test [output-directory]\n";
    return 1;
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  for (unsigned variant = 0; variant < 5; ++variant)
    cases.run("fresh actual window: " + Twine(variant), [&] {
      auto input = emitted(context, variant);
      if (variant == 1)
        require(!sameOracleReferenceKind(input.receiver.kinds[0], input.root),
                "nonzero demand root kind was lost");
      if (variant == 2) {
        auto &queries = input.receiver.constructors.back().functions.queries;
        require(queries.size() == 2 && queries[0].source == queries[1].source,
                "duplicate source occurrence was lost");
      }
      effects(input);
      auto copy = parse(context, print(*input.candidate));
      auto old = std::move(input.candidate);
      input.candidate = std::move(copy);
      refused(checkWindow(input)); // Foreign handles cannot authorize fresh IR.
      rebind(input);
      checkModel(input);
      checked(checkOracleQueryDemand(*input.candidate, *input.prepared,
                                     input.storage, input.receiver, input.root,
                                     input.demand));
      checked(checkWindow(input));
      effects(input);
    });
  cases.run("capacity one and repeated emission share work", [&] {
    auto input = emitted(context, 0, 1);
    auto before = input.work;
    auto second = take(emitOracleQueryWindow(*input.candidate, input.receiver,
                                             input.demand, input.exchange,
                                             input.response, 3, input.work));
    require(second.requestSequence == input.window.requestSequence &&
                second.answerSequence == input.window.answerSequence &&
                second.collect != input.window.collect &&
                input.work.operations < before.operations &&
                input.work.slots < before.slots,
            "window reused helpers or reset work");
    auto current = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryWindow(current, input.receiver, input.demand,
                                   input.exchange, input.response, second));
    checked(checkWindow(input));
  });
  const char *mutations[] = {"request constructor",
                             "request instance",
                             "request position",
                             "transition allowance",
                             "advance after last capacity slot",
                             "full prefix discovers",
                             "reached cut propagation",
                             "pending cut propagation",
                             "blocked cut value",
                             "omitted consume",
                             "discovery stores",
                             "replay stores",
                             "answer index",
                             "request index",
                             "replay begin",
                             "replay end",
                             "range order guard",
                             "range end guard",
                             "sequence length equality",
                             "replay capacity guard",
                             "stale continuation",
                             "stale advanced state",
                             "response continuation coordinates",
                             "skip finish",
                             "finish coordinates",
                             "skip finish advance",
                             "blocked branch discovering",
                             "completed branch discovering",
                             "full branch discovering",
                             "missing prefix guard",
                             "missing range guard",
                             "retained heterogeneous kind",
                             "wrong origin",
                             "public helper",
                             "request sequence type",
                             "answer sequence type",
                             "wrong continuation predicate",
                             "missing phase guard",
                             "missing request-entry guard",
                             "missing length guard",
                             "advance after replay resume",
                             "resume before advance",
                             "wrong region captures"};
  for (auto [mutation, name] : enumerate(mutations))
    cases.run("actual window mutation: " + Twine(name), [&, mutation = mutation] {
      auto input = emitted(context);
      auto call = [&](StringRef name) {
        return cast<func::CallOp>(site(input, name));
      };
      auto apply = [&](StringRef name) {
        return cast<exec::ApplyOp>(site(input, name));
      };
      if (mutation < 3) {
        auto op = cast<exec::VariantOp>(site(input, "window_request"));
        op.getPayloadMutable()[mutation].set(
            op.getPayload()[(mutation + 1) % 3]);
      } else if (mutation == 3)
        constant(input, "window_collect_upper", input.window.capacity + 2);
      else if (mutation == 4)
        constant(input, "window_packet_capacity", input.window.capacity + 1);
      else if (mutation == 5)
        constant(input, "window_seed_capacity", input.window.capacity + 1);
      else if (mutation == 6)
        constant(input, "window_cut_phase", Demand::Completed);
      else if (mutation == 7)
        constant(input, "window_pending_cut_phase", Demand::Request);
      else if (mutation == 8)
        constant(input, "window_blocked_phase", Demand::Completed);
      else if (mutation == 9)
        call("window_consume")
            .setCalleeAttr(
                FlatSymbolRefAttr::get(bypass(input, input.demand.consume)));
      else if (mutation == 10)
        emptyStore(input, "window_discover", 1 + input.demand.state.size());
      else if (mutation == 11)
        emptyStore(input, "window_replay_advance",
                   1 + input.receiver.state.size());
      else if (mutation == 12 || mutation == 13) {
        auto op = apply(mutation == 12 ? "window_replay_answer"
                                       : "window_replay_request");
        op.getInputsMutable()[1].set(
            op->getParentOfType<func::FuncOp>().getArgument(
                2 + Controller::Position));
      } else if (mutation == 14 || mutation == 15) {
        auto *op = site(input, "window_replay_loop");
        op->setOperand(mutation == 14 ? 1 : 2,
                       op->getOperand(mutation == 14 ? 2 : 1));
      } else if (mutation == 16 || mutation == 17) {
        auto op = apply(mutation == 16 ? "window_reversed_range"
                                       : "window_range_outside");
        auto a = Values(op.getInputs());
        std::swap(a[0], a[1]);
        op.getInputsMutable().assign(a);
      } else if (mutation == 18) {
        auto op = apply("window_equal_lengths");
        op.getInputsMutable()[1].set(op.getInputs()[0]);
      } else if (mutation == 19)
        constant(input, "window_replay_bound", input.window.capacity + 2);
      else if (mutation == 20 || mutation == 21) {
        auto op = call("window_replay_resume");
        auto owner = op->getParentOfType<func::FuncOp>();
        if (mutation == 20)
          op.setOperand(3 + Controller::Continuation,
                        owner.getArgument(2 + Controller::Continuation));
        else
          for (unsigned i = 0; i < input.receiver.state.size(); ++i)
            op.setOperand(3 + i, owner.getArgument(2 + i));
      } else if (mutation == 22) {
        auto prefix = "constructor_" +
                      std::to_string(input.exchange.arms[0].constructor) +
                      "_resume";
        auto op = cast<func::CallOp>(site(input, prefix, false));
        op.setOperand(1 + input.receiver.state.size() + 4,
                      op.getOperand(1 + Controller::Position));
      } else if (mutation == 23)
        call("window_finish_payload")
            .setCalleeAttr(FlatSymbolRefAttr::get(
                bypass(input, input.receiver.finish, true)));
      else if (mutation == 24) {
        auto op = call("window_finish_advance");
        op.setOperand(1 + Controller::Position,
                      op.getOperand(1 + Controller::Instance));
      } else if (mutation == 25)
        call("window_finish_advance")
            .setCalleeAttr(
                FlatSymbolRefAttr::get(bypass(input, input.receiver.advance)));
      else if (mutation == 26)
        injectDiscovery(input, "window_blocked", 0);
      else if (mutation == 27)
        injectDiscovery(input, "window_terminal", 0);
      else if (mutation == 28)
        injectDiscovery(input, "window_room", 1);
      else if (mutation == 29)
        omitGuard(input, "window_admit_prefix");
      else if (mutation == 30)
        omitGuard(input, "window_admit_range_order");
      else if (mutation == 31) {
        auto region = branch(input, "window_room", 1);
        region.walk([&](exec::CompleteOp op) {
          op.getValuesMutable()[Demand::Kind].set(
              op.getValues()[Demand::Position]);
        });
      } else if (mutation == 32) {
        input.window.collect->setAttr("runtime.origin",
                                      ArrayAttr::get(&context, {}));
      } else if (mutation == 33)
        input.window.replay.setPublic();
      else if (mutation == 34)
        input.window.requestSequence = input.window.answerSequence;
      else if (mutation == 35)
        input.window.answerSequence =
            data::SequenceType::get(&context, input.exchange.response);
      else if (mutation == 36) {
        auto op = apply("window_continue");
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            op, op.getBindingAttr());
        binding.setContract("bool.or");
      } else if (mutation == 37)
        omitGuard(input, "window_admit_phase");
      else if (mutation == 38)
        omitGuard(input, "window_admit_consumed");
      else if (mutation == 39)
        omitGuard(input, "window_admit_lengths");
      else if (mutation == 40) {
        auto resume = call("window_replay_resume");
        auto region = resume->getParentOfType<func::FuncOp>();
        auto a = region.getArguments().drop_front();
        exec::CompleteOp complete;
        region.walk([&](exec::CompleteOp op) { complete = op; });
        Values inputs(complete.getValues());
        append_range(inputs, a.drop_front(input.receiver.state.size() + 3));
        insertBefore(complete, [&](exec::ScopedExecutionBuilder &c,
                                   OpBuilder &b) {
          invoke(c, b, input.receiver.advance, inputs, "advance_after_resume");
        });
      } else if (mutation == 41)
        reorderReplay(input);
      else {
        auto left = branch(input, "window_room", 0);
        auto right = branch(input, "window_room", 1);
        auto owner =
            site(input, "window_room")->getParentOfType<func::FuncOp>();
        owner.walk([&](runtime::EnterScopeOp enter) {
          if (enter.getSite() == "window_room")
            enter.getInputsMutable()[Demand::Instance].set(
                enter.getInputs()[Demand::Constructor]);
        });
        owner.walk([&](func::CallOp call) {
          auto target = SymbolTable::lookupSymbolIn(unit(*input.candidate),
                                                    call.getCallee());
          if (target == left.getOperation() || target == right.getOperation())
            call.setOperand(1 + Demand::Instance,
                            call.getOperand(1 + Demand::Constructor));
        });
      }
      rejects(input);
    });
  cases.run("capacity, work and exact model refusals are atomic", [&] {
    auto input = emitted(context);
    auto frozen = print(*input.candidate);
    auto frozenSource = print(*input.prepared);
    for (unsigned test = 0; test < 12; ++test) {
      auto controller = input.receiver;
      auto demand = input.demand;
      auto exchange = input.exchange;
      auto response = input.response;
      auto work = input.work;
      uint64_t capacity = 2;
      StringRef code = "oracle-window-layout";
      if (test < 4) {
        const uint64_t values[] = {0, 1048576, 1048577, UINT64_MAX};
        capacity = values[test];
        code = "oracle-window-capacity";
      } else if (test == 4) {
        work.operations = 0;
        code = "oracle-window-limit";
      } else if (test == 5) {
        work.slots = 0;
        code = "oracle-window-limit";
      } else if (test == 6)
        demand.consume = {};
      else if (test == 7)
        exchange.state.pop_back();
      else if (test == 8)
        exchange.receiverStores.pop_back();
      else if (test == 9)
        response.answer = exchange.response;
      else if (test == 10)
        exchange.arms[0].kind = 1;
      auto before = work;
      // A same-signature foreign controller is refused by its request/resume
      // association, rather than accepting coincidentally equal kind numbers.
      if (test == 11)
        controller = input.holder;
      refuses(emitOracleQueryWindow(*input.candidate, controller, demand,
                                    exchange, response, capacity, work),
              code);
      require(
          work.operations == before.operations && work.slots == before.slots &&
              print(*input.candidate) == frozen &&
              print(*input.prepared) == frozenSource,
          "refused window emission changed candidate, source or shared work");
    }
    auto empty =
        OwningOpRef<ModuleOp>(ModuleOp::create(UnknownLoc::get(&context)));
    refuses(emitOracleQueryWindow(*empty, input.receiver, input.demand,
                                  input.exchange, input.response, 2,
                                  input.work),
            "oracle-window-source");
  });
  cases.run("maximum representable packet allowance", [&] {
    auto input = emitted(context);
    OracleVirtualFunctionWork work;
    work.operations = 1000000;
    work.slots = 100000000;
    auto maximum = take(emitOracleQueryWindow(*input.candidate, input.receiver,
                                              input.demand, input.exchange,
                                              input.response, 1048575, work));
    require(maximum.capacity == 1048575, "packet maximum changed");
    auto current = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryWindow(current, input.receiver, input.demand,
                                   input.exchange, input.response, maximum));
  });
  if (argc == 2)
    cases.run("production runtime client emission", [&] {
      auto input = emitted(context);
      auto bundle = client(input, registry);
      require(!bundle.empty(), "empty window client bundle");
      std::filesystem::create_directories(argv[1]);
      std::ofstream output(std::filesystem::path(argv[1]) / "window.bundle");
      output << bundle;
      require(bool(output), "cannot retain window client bundle");
    });
  else
    outs() << "Production runtime client emission was not requested.\n";
  return cases.result();
}

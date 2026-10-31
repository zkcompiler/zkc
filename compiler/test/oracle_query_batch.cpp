#include "../lib/Transforms/OracleQueryBatch.h"
#include "../lib/Transforms/OracleVerificationContext.h"
#include "../lib/Transforms/RealizationEmission.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include <algorithm>
#include <filesystem>
#include <fstream>
#include <optional>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
using Values = SmallVector<Value>;
using Control = exec::ScopedExecutionBuilder;

std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text;
}
void checked(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
void refused(Error e) {
  require(bool(e), "expected batch body refusal");
  auto message = toString(std::move(e));
  require(namesIdentifier(message, "oracle-batch-body"), message);
}
pir::ProtocolModuleOp unit(ModuleOp module) {
  return cast<pir::ProtocolModuleOp>(module.getBody()->front());
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module) && succeeded(admitStage(*module)),
          "batch test admission");
  return module;
}
struct Root {
  OracleQueryController controller;
  OracleQueryDemand demand;
  OracleQueryExchange exchange;
  OracleQueryResponse response;
  OracleQueryWindow window;
  pir::OracleKindAttr kind;
};
struct Input {
  OwningOpRef<ModuleOp> candidate;
  OracleAnchorStorage storage;
  OracleQuerySize capacity;
  OracleQueryController holder;
  std::vector<OracleMerkleFunctions> merkle;
  std::vector<Root> entries;
  OracleQueryBatch batch;
  OracleVirtualFunctionWork work;
  SmallVector<OracleQueryBatchRoot> roots() const {
    SmallVector<OracleQueryBatchRoot> result;
    for (const auto &root : entries)
      result.push_back({&root.controller, &root.demand, &root.window});
    return result;
  }
};
struct Fixture {
  OwningOpRef<ModuleOp> source, prepared;
  Input input;
};
Error checkBatch(const Input &input) {
  auto context = OracleVerificationContext::read(*input.candidate);
  if (!context)
    return context.takeError();
  return checkOracleQueryBatch(*context, input.roots(), input.batch);
}
void checkModels(const Input &input, ModuleOp prepared) {
  auto candidate = take(OracleVerificationContext::read(*input.candidate));
  auto source = take(OracleVerificationContext::read(prepared));
  checked(checkOracleQueryController(
      candidate, source, input.storage, "P", input.storage.constructors[0].kind,
      input.capacity, input.holder, OracleControllerAccess::Holder));
  for (auto [i, anchor] : enumerate(input.storage.constructors))
    if (anchor.constructor != OracleAnchorConstructor::Kind::Virtual)
      checked(checkOracleMerkle(candidate, input.merkle[i], anchor.kind,
                                anchor.scheme, OracleLeafGrouping::Individual,
                                OracleLeafOrder::Natural));
  for (const auto &root : input.entries) {
    checked(checkOracleQueryController(
        candidate, source, input.storage, "V", root.kind, input.capacity,
        root.controller, OracleControllerAccess::Available));
    checked(checkOracleQueryDemand(candidate, source, input.storage,
                                   root.controller, root.kind, root.demand));
    checked(checkOracleQueryResponse(candidate, root.exchange, root.response));
    checked(checkOracleQueryWindow(candidate, root.controller, root.demand,
                                   root.exchange, root.response, root.window));
  }
}
Fixture emitted(MLIRContext &context, uint64_t capacity = 2,
                bool emptyVirtual = false) {
  Fixture fixture;
  auto path =
      std::filesystem::path(ZKC_ORACLE_FIXTURES) / "query-constructors.mlir";
  std::ifstream file(path);
  require(bool(file), "cannot read batch source fixture");
  std::string text((std::istreambuf_iterator<char>(file)), {});
  // Retain three actual ordered source occurrences, including unused answers.
  // The first and third use independently emitted, equal-signature helpers;
  // the middle controller has a different local kind numbering and answer.
  auto at = text.find("   \"protocol.return\"(%answer)");
  require(at != std::string::npos, "missing entry return");
  text.insert(at, R"mlir(
   %second = "protocol.oracle_query"(%b,%position) {owner="V",site="second"} : (!B,ui64)->!BF
   %third = "protocol.oracle_query"(%a,%position) {owner="V",site="third"} : (!H,ui64)->!F
)mlir");
  if (emptyVirtual) {
    auto begin = text.find("   %answer = \"protocol.oracle_query\"");
    auto end = text.find("   \"protocol.oracle_yield\"", begin);
    require(begin != std::string::npos && end != std::string::npos,
            "missing virtual source body");
    text.replace(begin, end - begin,
                 "   %answer = \"algebra.constant\"() "
                 "{value=#algebra.literal<!F, 9 : ui31>} : ()->!F\n");
  }
  fixture.source = parse(context, text);
  fixture.prepared = mathematical::prepareProtocol(*fixture.source, false);
  require(bool(fixture.prepared), "batch source preparation");
  auto frozenSource = print(*fixture.source);
  auto frozenPrepared = print(*fixture.prepared);
  auto &input = fixture.input;
  input.storage = take(planOracleAnchorStorage(
      *fixture.prepared, "main",
      [](const auto &anchor) -> Expected<std::string> {
        auto field = cast<algebra::FieldType>(anchor.kind.getAnswerType());
        return "rows.merkle-poseidon2-16." + field.getDomain().str() + "/0";
      }));
  auto bounds = take(analyzeOracleQueryCapacity(*fixture.prepared, "main"));
  for (const auto &query : bounds.queries) {
    input.capacity.leaves =
        std::max(input.capacity.leaves, query.second.leaves);
    input.capacity.nodes = std::max(input.capacity.nodes, query.second.nodes);
  }
  input.candidate = parse(context, R"mlir(
module { "protocol.module"() ({
 func.func private @placeholder()->i1 { %ok = arith.constant true
 return %ok : i1 }
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
  input.work.operations = 1000000;
  input.work.slots = 100000000;
  input.holder = take(emitOracleQueryController(
      *input.candidate, *fixture.prepared, input.storage, "P",
      input.storage.constructors[0].kind, input.capacity, input.work,
      OracleControllerAccess::Holder));
  input.merkle.resize(input.storage.constructors.size());
  for (auto [i, anchor] : enumerate(input.storage.constructors))
    if (anchor.constructor != OracleAnchorConstructor::Kind::Virtual)
      input.merkle[i] = take(emitOracleMerkle(
          *input.candidate, anchor.kind, anchor.scheme,
          OracleLeafGrouping::Individual, OracleLeafOrder::Natural));
  for (unsigned i = 0; i < 3; ++i) {
    Root root;
    root.kind = input.storage.constructors[i == 1 ? 1 : 0].kind;
    root.controller = take(emitOracleQueryController(
        *input.candidate, *fixture.prepared, input.storage, "V", root.kind,
        input.capacity, input.work));
    root.exchange = take(planOracleQueryExchange(input.storage, root.controller,
                                                 input.holder, input.merkle));
    root.response = take(
        emitOracleQueryResponse(*input.candidate, root.exchange, input.work));
    root.demand =
        take(emitOracleQueryDemand(*input.candidate, input.storage,
                                   root.controller, root.kind, input.work));
    root.window = take(emitOracleQueryWindow(
        *input.candidate, root.controller, root.demand, root.exchange,
        root.response, capacity, input.work));
    input.entries.push_back(std::move(root));
  }
  checkModels(input, *fixture.prepared);
  auto before = input.work;
  input.batch =
      take(emitOracleQueryBatch(*input.candidate, input.roots(), input.work));
  require(input.work.operations < before.operations &&
              input.work.slots < before.slots,
          "batch emission did not debit shared work");
  checked(checkBatch(input));
  require(print(*fixture.source) == frozenSource &&
              print(*fixture.prepared) == frozenPrepared,
          "batch construction changed source");
  return fixture;
}

void rebind(Input &input) {
  auto bind = [&](func::FuncOp &function) {
    if (!function)
      return;
    function = dyn_cast_or_null<func::FuncOp>(SymbolTable::lookupSymbolIn(
        unit(*input.candidate), function.getSymName()));
    require(bool(function), "serialized helper missing");
  };
  auto controller = [&](OracleQueryController &model) {
    for (auto &item : model.constructors) {
      bind(item.lookup);
      bind(item.functions.answer);
      for (auto &query : item.functions.queries)
        bind(query.position);
    }
    for (auto *inventory : {&model.resume, &model.leafCounts, &model.rowCounts,
                            &model.constructionCounts})
      for (auto &helper : *inventory)
        bind(helper);
    for (auto *helper : {&model.initialize, &model.advance, &model.finish,
                         &model.evaluate, &model.contents})
      bind(*helper);
  };
  controller(input.holder);
  for (auto &helpers : input.merkle)
    for (auto *helper : {&helpers.position, &helpers.commit, &helpers.open,
                         &helpers.authenticate})
      bind(*helper);
  for (auto &root : input.entries) {
    controller(root.controller);
    for (auto &arm : root.exchange.arms)
      for (auto *helper : {&arm.holderLookup, &arm.receiverLookup, &arm.open,
                           &arm.authenticate, &arm.resume})
        bind(*helper);
    for (auto *helper :
         {&root.demand.initialize, &root.demand.advance, &root.demand.consume,
          &root.response.authenticate, &root.response.resume,
          &root.window.collect, &root.window.replay, &root.window.finish})
      bind(*helper);
  }
  for (auto *helper : {&input.batch.collect, &input.batch.checkAvailable,
                       &input.batch.replay, &input.batch.finish})
    bind(*helper);
}
Input copyInput(const Input &original, MLIRContext &context, bool bind = true) {
  Input input;
  input.candidate = parse(context, print(*original.candidate));
  input.storage = original.storage;
  input.capacity = original.capacity;
  input.holder = original.holder;
  input.merkle = original.merkle;
  input.entries = original.entries;
  input.batch = original.batch;
  input.work = original.work;
  if (bind)
    rebind(input);
  return input;
}
Operation *site(Input &input, StringRef name) {
  Operation *found = nullptr;
  input.candidate->walk([&](Operation *op) {
    if (op->getName().getDialectNamespace() == "runtime")
      return; // Scope bookkeeping shares the semantic operation's site.
    auto owner = op->getParentOfType<func::FuncOp>();
    if (!owner || !owner.getSymName().starts_with("_oracle_batch_"))
      return;
    auto tag = op->getAttrOfType<StringAttr>(
        isa<func::CallOp>(op) ? "runtime.site" : "site");
    if (tag && tag.getValue() == name) {
      require(!found, "ambiguous batch site: " + name);
      found = op;
    }
  });
  require(found, "missing batch site: " + name);
  return found;
}
func::FuncOp branch(Input &input, unsigned ordinal) {
  auto context = take(OracleVerificationContext::read(*input.candidate));
  auto *op = site(input, "batch_empty_round");
  auto owner = op->getParentOfType<func::FuncOp>();
  for (const auto &step :
       context.getClosure().bodies.at(owner.getSymName().str()))
    if (step.operation == op) {
      require(ordinal < step.regions.size(), "missing empty round branch");
      return step.regions[ordinal];
    }
  throw std::runtime_error("missing conditional association");
}
void insertBefore(Operation *before,
                  llvm::function_ref<void(Control &, OpBuilder &)> emit) {
  auto owner = before->getParentOfType<func::FuncOp>();
  auto *head = before->getBlock();
  auto *tail = head->splitBlock(Block::iterator(before));
  OpBuilder builder(before->getContext());
  builder.setInsertionPointToEnd(head);
  Control control(builder, owner);
  emit(control, builder);
  cf::BranchOp::create(builder, before->getLoc(), tail, ValueRange{});
}
void invoke(Control &c, OpBuilder &b, func::FuncOp helper, ValueRange inputs,
            StringRef name) {
  c.invoke("func.call", scopedDataSignature(helper).getResults(),
           c.scoped(inputs),
           {b.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
            b.getNamedAttr("runtime.site", b.getStringAttr(name))});
}
Values evaluation(const Input &input, ValueRange arguments, unsigned root) {
  unsigned first = 0;
  for (unsigned i = 0; i < root; ++i)
    first += input.entries[i].controller.state.size();
  Values values(
      arguments.slice(first, input.entries[root].controller.state.size()));
  append_range(values, arguments.take_back(
                           input.entries[root].controller.stores.size()));
  return values;
}
exec::ReturnOp returned(func::FuncOp helper) {
  exec::ReturnOp result;
  helper.walk([&](exec::ReturnOp op) {
    require(!result, "ambiguous successful return");
    result = op;
  });
  require(bool(result), "missing successful return");
  return result;
}
void emptyStore(Input &input, StringRef name, unsigned operand) {
  auto call = cast<func::CallOp>(site(input, name));
  Type store = call.getOperand(operand).getType();
  insertBefore(call, [&](Control &c, OpBuilder &b) {
    mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                              "_batch_attack_binding_");
    auto element = cast<data::SequenceType>(store).getElementType();
    auto binding = bindings.binding(
        b, call.getLoc(), {"sequence.empty", {TypeAttr::get(element)}, ""});
    auto empty = c.invoke(
        "exec.apply", store, c.scoped({}),
        {b.getNamedAttr("binding", binding),
         b.getNamedAttr("parameters", b.getArrayAttr({})),
         b.getNamedAttr("site", b.getStringAttr("batch_replaced_store"))})[0];
    call.setOperand(operand, empty);
  });
}
void omitGuard(Input &input, StringRef name) {
  auto *op = site(input, name);
  OpBuilder b(op);
  OperationState state(op->getLoc(), "exec.returned");
  state.addTypes(op->getResultTypes());
  auto *replacement = b.create(state);
  op->replaceAllUsesWith(replacement->getResults());
  op->erase();
}
void rejects(Input &input) {
  auto check = [&] {
    require(succeeded(verify(*input.candidate)),
            "mutation failed MLIR formation");
    auto frozen = print(*input.candidate);
    auto context = OracleVerificationContext::read(*input.candidate);
    if (!context)
      consumeError(context.takeError());
    else
      refused(checkOracleQueryBatch(*context, input.roots(), input.batch));
    require(print(*input.candidate) == frozen,
            "batch reader changed candidate");
  };
  check();
  auto fresh = parseSourceString<ModuleOp>(
      print(*input.candidate),
      ParserConfig(input.candidate->getContext(), false));
  require(bool(fresh), "mutation textual parse");
  auto old = std::move(input.candidate);
  input.candidate = std::move(fresh);
  rebind(input);
  check();
}
void effects(const Input &input) {
  auto context = take(OracleVerificationContext::read(*input.candidate));
  const auto &closure = context.getClosure();
  auto calls = [&](func::FuncOp helper) {
    std::vector<std::string> result;
    for (const auto &step : closure.bodies.at(helper.getSymName().str()))
      if (auto call = dyn_cast<func::CallOp>(step.operation))
        result.push_back(call.getCallee().str());
    return result;
  };
  std::vector<std::string> collect, replay, finish;
  for (const auto &root : input.entries) {
    collect.push_back(func::FuncOp(root.window.collect).getSymName().str());
    replay.push_back(func::FuncOp(root.window.replay).getSymName().str());
    finish.push_back(func::FuncOp(root.window.finish).getSymName().str());
  }
  require(calls(input.batch.collect) == collect,
          "normal discovery calls an evaluator");
  require(calls(input.batch.replay) == replay,
          "replay advances beyond its root segments");
  require(calls(input.batch.finish) == finish, "finish changes source order");
  SmallVector<Type> collectionInputs(input.batch.demandState.begin(),
                                     input.batch.demandState.end());
  append_range(collectionInputs, input.entries.front().controller.stores);
  require(equal(scopedDataSignature(input.batch.collect).getInputs(),
                collectionInputs),
          "collection retains evaluator inputs");
  require(scopedDataSignature(input.batch.checkAvailable).getNumResults() == 0,
          "availability check returns request dependencies");
  for (const auto &step :
       closure.bodies.at(func::FuncOp(input.batch.collect).getSymName().str()))
    require(!isa<exec::TestOp>(step.operation),
            "collection retains the evaluator-dependent empty branch");
  unsigned decisions = 0;
  for (const auto &step : closure.bodies.at(
           func::FuncOp(input.batch.checkAvailable).getSymName().str()))
    if (isa<exec::TestOp>(step.operation)) {
      ++decisions;
      require(step.regions.size() == 2 && calls(step.regions[0]) == finish &&
                  calls(step.regions[1]).empty(),
              "empty-only evaluator calls were lost");
      auto &empty =
          closure.bodies.at(func::FuncOp(step.regions[0]).getSymName().str());
      require(empty.size() == input.entries.size() + 4 &&
                  isa<exec::ApplyOp>(empty[empty.size() - 2].operation),
              "empty failure guard does not follow every finish");
    }
  require(decisions == 1, "missing batch emptiness decision");
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
  // Construct the real source/controller/demand/response/window closure once;
  // each mutation gets a separately parsed candidate and rebound handles.
  std::optional<Fixture> fixture;
  cases.run("real ordered roots with independent kind numbering", [&] {
    fixture.emplace(emitted(context));
    auto &input = fixture->input;
    require(
        input.entries[0].controller.state !=
                input.entries[1].controller.state &&
            !sameOracleReferenceKind(input.entries[0].controller.kinds[0],
                                     input.entries[1].controller.kinds[0]) &&
            input.entries[0].controller.stores ==
                input.entries[1].controller.stores,
        "test did not retain independent controllers with common stores");
    effects(input);
  });
  if (!fixture)
    return cases.result();
  const auto &base = fixture->input;
  cases.run("fresh text requires rebinding every helper", [&] {
    auto input = copyInput(base, context, false);
    refused(checkBatch(input));
    rebind(input);
    checkModels(input, *fixture->prepared);
    checked(checkBatch(input));
    effects(input);
  });
  cases.run("single-root and repeated emission use shared work", [&] {
    auto input = copyInput(base, context);
    auto roots = input.roots();
    roots.resize(1);
    auto before = input.work;
    auto single =
        take(emitOracleQueryBatch(*input.candidate, roots, input.work));
    auto again =
        take(emitOracleQueryBatch(*input.candidate, roots, input.work));
    require(single.collect != again.collect &&
                single.checkAvailable != again.checkAvailable &&
                single.replay != again.replay &&
                input.work.operations < before.operations &&
                input.work.slots < before.slots,
            "batch reset work or reused helper names");
    auto current = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryBatch(current, roots, single));
    checked(checkOracleQueryBatch(current, roots, again));
    checked(checkOracleQueryBatch(current, input.roots(), input.batch));
  });
  cases.run("capacity one and zero-leaf virtual composition", [&] {
    auto empty = emitted(context, 1, true);
    checked(checkBatch(empty.input));
    effects(empty.input);
    require(empty.input.storage.constructors.back().constructor ==
                OracleAnchorConstructor::Kind::Virtual,
            "missing zero-leaf virtual constructor");
    auto parsed = copyInput(empty.input, context);
    checked(checkBatch(parsed));
  });
  cases.run("maximum window capacity composes without resetting work", [&] {
    auto input = copyInput(base, context);
    for (auto &root : input.entries)
      root.window = take(emitOracleQueryWindow(
          *input.candidate, root.controller, root.demand, root.exchange,
          root.response, 1048575, input.work));
    checkModels(input, *fixture->prepared);
    input.batch =
        take(emitOracleQueryBatch(*input.candidate, input.roots(), input.work));
    checked(checkBatch(input));
  });

  const char *mutations[] = {"equal-signature root order",
                             "collect target",
                             "replay target",
                             "finish target",
                             "demand coordinates",
                             "empty finish coordinates",
                             "returned end order",
                             "end measured from previous prefix",
                             "replay begin loses previous end",
                             "replay end loses root association",
                             "first begin is not zero",
                             "last end guard is tautological",
                             "last end guard checks previous root",
                             "omitted last end guard",
                             "omitted empty guard",
                             "finish before emptiness decision",
                             "finish on nonempty branch",
                             "extra call",
                             "discovery stores",
                             "replay stores",
                             "finish stores",
                             "empty finish stores",
                             "blocked propagation",
                             "stale demand return",
                             "answer return order",
                             "public batch helper",
                             "wrong origin",
                             "wrong sequence model",
                             "unequal capacities",
                             "unequal store types",
                             "wrong state model",
                             "empty finish uses another root state",
                             "finish during replay",
                             "empty guard accepts",
                             "stale evaluator return",
                             "duplicate end replaces a root end",
                             "wrong region capture",
                             "empty root finish order",
                             "empty guard precedes source finish",
                             "public root window helper",
                             "batch helper marked as region",
                             "missing availability helper",
                             "substituted availability helper",
                             "availability length from another sequence",
                             "availability emptiness is tautological",
                             "public availability helper"};
  for (auto [mutation, name] : enumerate(mutations))
    cases.run("batch mutation: " + Twine(name), [&, mutation = mutation] {
      auto input = copyInput(base, context);
      auto call = [&](StringRef siteName) {
        return cast<func::CallOp>(site(input, siteName));
      };
      auto apply = [&](StringRef siteName) {
        return cast<exec::ApplyOp>(site(input, siteName));
      };
      unsigned d = input.batch.demandState.size();
      unsigned e = input.batch.evaluatorState.size();
      unsigned n = input.entries[0].controller.state.size();
      unsigned dn = input.entries[0].demand.state.size();
      if (mutation == 0) {
        auto roots = input.roots();
        std::swap(roots[0], roots[2]);
        auto current = take(OracleVerificationContext::read(*input.candidate));
        refused(checkOracleQueryBatch(current, roots, input.batch));
        return;
      } else if (mutation >= 1 && mutation <= 3) {
        auto helper = mutation == 1   ? input.entries[2].window.collect
                      : mutation == 2 ? input.entries[2].window.replay
                                      : input.entries[2].window.finish;
        call(mutation == 1   ? "batch_collect_0"
             : mutation == 2 ? "batch_replay_0"
                             : "batch_finish_0")
            .setCalleeAttr(FlatSymbolRefAttr::get(helper));
      } else if (mutation == 4 || mutation == 5) {
        auto op =
            call(mutation == 4 ? "batch_collect_0" : "batch_empty_finish_0");
        op.setOperand(1, op.getOperand(2));
      } else if (mutation == 6) {
        auto op = returned(input.batch.collect);
        auto first = op->getOperand(d + 1);
        op->setOperand(d + 1, op->getOperand(d + 3));
        op->setOperand(d + 3, first);
      } else if (mutation == 7)
        apply("batch_end_1")
            .getInputsMutable()[0]
            .set(apply("batch_end_0").getInputs()[0]);
      else if (mutation == 8)
        call("batch_replay_1")
            .setOperand(n + 3, call("batch_replay_0").getOperand(n + 3));
      else if (mutation == 9)
        call("batch_replay_1")
            .setOperand(n + 4, call("batch_replay_0").getOperand(n + 4));
      else if (mutation == 10)
        call("batch_replay_0")
            .setOperand(n + 3, call("batch_replay_0").getOperand(n + 4));
      else if (mutation == 11)
        apply("batch_last_end")
            .getInputsMutable()[0]
            .set(apply("batch_last_end").getInputs()[1]);
      else if (mutation == 12)
        apply("batch_last_end")
            .getInputsMutable()[0]
            .set(input.batch.replay.getArgument(1 + e + 3));
      else if (mutation == 13 || mutation == 14)
        omitGuard(input, mutation == 13 ? "batch_admit_last_end"
                                        : "batch_reject_empty");
      else if (mutation == 15) {
        auto *before = site(input, "batch_available_length");
        auto a = input.batch.checkAvailable.getArguments().drop_front(2);
        auto args = evaluation(input, a, 0);
        insertBefore(before, [&](Control &c, OpBuilder &b) {
          invoke(c, b, input.entries[0].window.finish, args,
                 "unwanted_early_finish");
        });
      } else if (mutation == 16) {
        auto region = branch(input, 1);
        exec::CompleteOp last;
        region.walk([&](exec::CompleteOp op) { last = op; });
        require(bool(last), "missing nonempty completion");
        auto args = evaluation(input, region.getArguments().drop_front(), 0);
        insertBefore(last, [&](Control &c, OpBuilder &b) {
          invoke(c, b, input.entries[0].window.finish, args, "nonempty_finish");
        });
      } else if (mutation == 17 || mutation == 32) {
        auto *before = mutation == 17 ? site(input, "batch_finish_0")
                                      : site(input, "batch_replay_0");
        auto owner = before->getParentOfType<func::FuncOp>();
        auto args = evaluation(input, owner.getArguments().drop_front(), 0);
        insertBefore(before, [&](Control &c, OpBuilder &b) {
          invoke(c, b, input.entries[0].window.finish, args, "extra_finish");
        });
      } else if (mutation >= 18 && mutation <= 21) {
        const char *names[] = {"batch_collect_0", "batch_replay_0",
                               "batch_finish_0", "batch_empty_finish_0"};
        unsigned operands[] = {1 + dn + 2, 1 + n + 4, 1 + n, 1 + n};
        emptyStore(input, names[mutation - 18], operands[mutation - 18]);
      } else if (mutation == 22)
        call("batch_collect_1")
            .setOperand(1 + dn + 1,
                        call("batch_collect_0").getOperand(1 + dn + 1));
      else if (mutation == 23)
        returned(input.batch.collect)
            ->setOperand(0, input.batch.collect.getArgument(1));
      else if (mutation == 24) {
        auto op = returned(input.batch.finish);
        auto first = op->getOperand(0);
        op->setOperand(0, op->getOperand(2));
        op->setOperand(2, first);
      } else if (mutation == 25)
        input.batch.collect.setPublic();
      else if (mutation == 26)
        input.batch.finish->setAttr("runtime.origin",
                                    ArrayAttr::get(&context, {}));
      else if (mutation == 27)
        input.batch.requestSequence = input.batch.answerSequence;
      else if (mutation == 28)
        ++input.entries[1].window.capacity;
      else if (mutation == 29)
        input.entries[1].controller.stores.pop_back();
      else if (mutation == 30)
        input.batch.demandState.pop_back();
      else if (mutation == 31) {
        auto op = call("batch_empty_finish_0");
        auto region = op->getParentOfType<func::FuncOp>();
        unsigned third = input.entries[0].controller.state.size() +
                         input.entries[1].controller.state.size();
        op.setOperand(1, region.getArgument(1 + third));
      } else if (mutation == 33) {
        auto op = apply("batch_impossible_empty");
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            op, op.getBindingAttr());
        binding.setContract("index.equal");
      } else if (mutation == 34)
        returned(input.batch.replay)
            ->setOperand(0, input.batch.replay.getArgument(1));
      else if (mutation == 35)
        returned(input.batch.collect)
            ->setOperand(d + 2,
                         returned(input.batch.collect)->getOperand(d + 1));
      else if (mutation == 36) {
        input.batch.checkAvailable.walk([&](runtime::EnterScopeOp enter) {
          if (enter.getSite() == "batch_empty_round")
            enter.getInputsMutable()[OracleQueryController::Position].set(
                enter.getInputs()[OracleQueryController::Instance]);
        });
      } else if (mutation == 37) {
        call("batch_empty_finish_0")
            .setCalleeAttr(
                FlatSymbolRefAttr::get(input.entries[2].window.finish));
        call("batch_empty_finish_2")
            .setCalleeAttr(
                FlatSymbolRefAttr::get(input.entries[0].window.finish));
      } else if (mutation == 38) {
        auto *before = site(input, "batch_empty_finish_0");
        auto coordinate =
            before->getParentOfType<func::FuncOp>().getArgument(1);
        insertBefore(before, [&](Control &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(
              unit(*input.candidate), "_batch_early_guard_binding_");
          auto binding =
              bindings.binding(b, before->getLoc(), {"index.less", {}, ""});
          auto no = c.invoke(
              "exec.apply", b.getI1Type(), c.scoped({coordinate, coordinate}),
              {b.getNamedAttr("binding", binding),
               b.getNamedAttr("parameters", b.getArrayAttr({})),
               b.getNamedAttr("site", b.getStringAttr("early_false"))})[0];
          auto guard = bindings.binding(b, before->getLoc(),
                                        {"control.require", {}, ""});
          c.invoke("exec.apply", {}, c.scoped(no),
                   {b.getNamedAttr("binding", guard),
                    b.getNamedAttr("parameters", b.getArrayAttr({})),
                    b.getNamedAttr("site", b.getStringAttr("early_guard"))});
        });
      } else if (mutation == 39)
        input.entries[0].window.collect.setPublic();
      else if (mutation == 40)
        input.batch.collect->setAttr("runtime.region", UnitAttr::get(&context));
      else if (mutation == 41) {
        input.batch.checkAvailable = {};
        refused(checkBatch(input));
        return;
      } else if (mutation == 42) {
        input.batch.checkAvailable = input.batch.finish;
        refused(checkBatch(input));
        return;
      } else if (mutation == 43) {
        auto op = apply("batch_available_length");
        insertBefore(op, [&](Control &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(
              unit(*input.candidate), "_batch_empty_sequence_binding_");
          auto element = cast<data::SequenceType>(input.batch.requestSequence)
                             .getElementType();
          auto binding = bindings.binding(
              b, op.getLoc(), {"sequence.empty", {TypeAttr::get(element)}, ""});
          auto empty = c.invoke(
              "exec.apply", input.batch.requestSequence, c.scoped({}),
              {b.getNamedAttr("binding", binding),
               b.getNamedAttr("parameters", b.getArrayAttr({})),
               b.getNamedAttr("site", b.getStringAttr("unrelated_empty"))})[0];
          op.getInputsMutable()[0].set(empty);
        });
      } else if (mutation == 44) {
        auto op = apply("batch_is_empty");
        op.getInputsMutable()[0].set(op.getInputs()[1]);
      } else
        input.batch.checkAvailable.setPublic();
      rejects(input);
    });

  cases.run(
      "fail-closed bounds and layouts leave candidate and work intact", [&] {
        auto input = copyInput(base, context);
        auto frozen = print(*input.candidate);
        for (unsigned test = 0; test < 20; ++test) {
          auto entries = input.entries;
          SmallVector<OracleQueryBatchRoot> roots;
          for (const auto &entry : entries)
            roots.push_back({&entry.controller, &entry.demand, &entry.window});
          auto work = input.work;
          StringRef code = "oracle-batch-layout";
          if (test == 0 || test == 1) {
            roots.resize(test == 0 ? 0 : 33, roots[0]);
            code = "oracle-batch-capacity";
          } else if (test >= 2 && test <= 5) {
            const uint64_t capacities[] = {0, 1048576, 1048577, UINT64_MAX};
            entries[0].window.capacity = capacities[test - 2];
            code = "oracle-batch-capacity";
          } else if (test == 6 || test == 7) {
            if (test == 6)
              work.operations = 0;
            else
              work.slots = 0;
            code = "oracle-batch-limit";
          } else if (test == 8)
            roots[0].window = nullptr;
          else if (test == 9)
            entries[1].window.capacity = entries[0].window.capacity + 1;
          else if (test == 10)
            entries[1].controller.stores.pop_back();
          else if (test == 11)
            entries[0].window.collect = {};
          else if (test == 12)
            entries[0].window.requestSequence =
                entries[0].window.answerSequence;
          else if (test == 13)
            entries[0].demand.state[0] = {};
          else if (test == 14) {
            entries[0].controller.state.resize(513,
                                               entries[0].controller.state[0]);
            code = "oracle-batch-capacity";
          } else if (test == 15)
            entries[0].window.finish = entries[0].controller.finish;
          else if (test == 16)
            roots[0].controller = nullptr;
          else if (test == 17)
            roots[0].demand = nullptr;
          else if (test == 18)
            entries[1].window.answerSequence =
                entries[1].window.requestSequence;
          else
            entries[0].window.replay = entries[0].window.finish;
          auto before = work;
          refuses(emitOracleQueryBatch(*input.candidate, roots, work), code);
          require(work.operations == before.operations &&
                      work.slots == before.slots &&
                      print(*input.candidate) == frozen,
                  "refused batch changed candidate or shared work");
        }
        auto empty =
            OwningOpRef<ModuleOp>(ModuleOp::create(UnknownLoc::get(&context)));
        refuses(emitOracleQueryBatch(*empty, input.roots(), input.work),
                "oracle-batch-source");
      });
  cases.run("helper placement must remain in the checked protocol unit", [&] {
    auto input = copyInput(base, context);
    input.batch.finish->moveBefore(unit(*input.candidate));
    auto current = OracleVerificationContext::read(*input.candidate);
    require(!current, "misplaced helper admitted a batch context");
    consumeError(current.takeError());
  });
  cases.run("batch root and aggregate widths refuse before construction", [&] {
    auto input = copyInput(base, context);
    auto first = input.roots()[0];
    size_t stores = first.controller->stores.size();
    // Demand collection and receiver evaluation have separate signatures.
    // The receiver replay also carries the request/answer/cursor ports.
    unsigned admitted =
        std::min({size_t(32), size_t(511 - stores) / first.demand->state.size(),
                  size_t(509 - stores) / (first.controller->state.size() + 1),
                  size_t(511) / (first.demand->state.size() + 1)});
    require(admitted > 0 && admitted <= 32,
            "test must reach the aggregate width boundary");
    SmallVector<OracleQueryBatchRoot> roots(admitted, first);
    auto widest =
        take(emitOracleQueryBatch(*input.candidate, roots, input.work));
    auto current = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryBatch(current, roots, widest));
    auto frozen = print(*input.candidate);
    auto before = input.work;
    roots.push_back(first);
    refuses(emitOracleQueryBatch(*input.candidate, roots, input.work),
            "oracle-batch-capacity");
    roots.resize(33, first);
    refuses(emitOracleQueryBatch(*input.candidate, roots, input.work),
            "oracle-batch-capacity");
    require(print(*input.candidate) == frozen &&
                input.work.operations == before.operations &&
                input.work.slots == before.slots,
            "aggregate width refusal changed candidate or work");
  });
  return cases.result();
}

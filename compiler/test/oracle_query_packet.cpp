#include "../lib/Transforms/OracleQueryPacket.h"
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
#include "llvm/ADT/DenseMap.h"
#include <filesystem>
#include <fstream>
#include <functional>
#include <limits>
#include <set>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = zkc::protocol_ir;
namespace {
using Controller = OracleQueryController;
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
void refused(Error error, StringRef code = "oracle-packet-body") {
  require(bool(error), "expected packet refusal");
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
  OracleQueryPacket packet;
  func::FuncOp openOne;
  pir::OracleKindAttr root;
  OracleLeafGrouping grouping = OracleLeafGrouping::Individual;
  OracleLeafOrder order = OracleLeafOrder::Natural;
  uint64_t packetCapacity = 8;
  OracleVirtualFunctionWork work;
};
std::string scheme(const OracleAnchorConstructor &anchor) {
  auto field = cast<algebra::FieldType>(anchor.kind.getAnswerType());
  return "rows.merkle-poseidon2-16." + field.getDomain().str() + "/0";
}
Error checkPacket(const Input &input) {
  auto context = OracleVerificationContext::read(*input.candidate);
  if (!context)
    return context.takeError();
  return checkOracleQueryPacket(*context, input.exchange, input.response,
                                input.openOne, input.merkle,
                                input.packetCapacity, input.packet);
}
void checkModel(const Input &input) {
  auto target = take(OracleVerificationContext::read(*input.candidate));
  auto source = take(OracleVerificationContext::read(*input.prepared));
  auto root = input.root;
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
                              anchor.scheme, input.grouping, input.order));
  }
}
OracleExchangeRecipe openingRecipe(const Input &input) {
  OracleExchangeRecipe recipe;
  recipe.name = "_packet_fixture_open_one";
  recipe.inputs = {input.exchange.request};
  append_range(recipe.inputs, input.exchange.holderStores);
  recipe.outputs = {input.exchange.response};
  recipe.action = OracleExchangeAction::Open;
  recipe.exchange = std::make_shared<const OracleQueryExchange>(input.exchange);
  return recipe;
}
Input emitted(MLIRContext &context, bool sameKind = false,
              OracleLeafGrouping grouping = OracleLeafGrouping::Individual,
              OracleLeafOrder order = OracleLeafOrder::Natural) {
  Input input;
  input.grouping = grouping;
  input.order = order;
  // This is the existing source fixture with a recurrent virtual and two
  // distinct committed base constructors, including an unused child answer.
  auto path =
      std::filesystem::path(ZKC_ORACLE_FIXTURES) / "query-constructors.mlir";
  std::ifstream fixture(path);
  require(bool(fixture), "cannot read constructor source fixture");
  std::string text((std::istreambuf_iterator<char>(fixture)), {});
  if (sameKind) {
    for (StringRef fragment : {"!BF = !algebra.field<\"koala-bear\">",
                               "!BD = !data.field_vector<\"koala-bear\">"}) {
      auto offset = text.find(fragment.str());
      require(offset != std::string::npos, "same-kind fixture fragment");
      auto replacement = fragment.str();
      replacement.replace(replacement.find("koala-bear"), 10,
                          "koala-bear.ext4-binomial3");
      text.replace(offset, fragment.size(), replacement);
    }
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
  // Start the controller's kind order at the OTHER base field. Source
  // constructor ordinals and controller kind ordinals deliberately disagree.
  input.root = input.storage.constructors[1].kind;
  auto root = input.root;
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
          *input.candidate, anchor.kind, anchor.scheme, grouping, order));
  input.exchange = take(planOracleQueryExchange(input.storage, input.receiver,
                                                input.holder, input.merkle));
  checkModel(input);
  auto before = input.work;
  input.response = take(
      emitOracleQueryResponse(*input.candidate, input.exchange, input.work));
  require(input.work.operations < before.operations &&
              input.work.slots < before.slots,
          "response emission did not debit shared work");
  input.openOne =
      emitOracleQueryExchange(*input.candidate, openingRecipe(input));
  {
    auto target = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryResponse(target, input.exchange, input.response));
    require(
        checkOracleQueryExchange(target, input.openOne, openingRecipe(input)),
        "openOne independent reader refused fixture");
  }
  before = input.work;
  input.packet = take(emitOracleQueryPacket(
      *input.candidate, input.exchange, input.response, input.openOne,
      input.merkle, input.packetCapacity, input.work));
  require(input.work.operations < before.operations &&
              input.work.slots < before.slots,
          "packet did not debit shared work");
  checked(checkPacket(input));
  require(print(*input.source) == frozenSource &&
              print(*input.prepared) == frozenPrepared,
          "packet emission or reading mutated source");
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
  bind(input.openOne);
  bind(input.packet.group);
  bind(input.packet.open);
  bind(input.packet.authenticate);
}
Operation *site(const Input &input, StringRef name) {
  Operation *found = nullptr;
  auto candidate = *input.candidate;
  candidate.walk([&](Operation *op) {
    auto actual = op->getAttrOfType<StringAttr>("runtime.site");
    if (op->getName().getDialectNamespace() == "exec")
      actual = op->getAttrOfType<StringAttr>("site");
    if ((isa<func::CallOp>(op) ||
         op->getName().getDialectNamespace() == "exec") &&
        actual && actual.getValue() == name) {
      require(!found, "ambiguous mutation site: " + name);
      found = op;
    }
  });
  require(found, "missing mutation site: " + name);
  return found;
}
// Execute the recovered packet control, sequence operations, actual lookups
// and actual Merkle position functions. Opening/authentication are explicit
// abstract effect adapters with traces, NOT cryptographic verification or VM
// execution. The optional native client below uses the normal compiler tools.
struct Datum {
  uint64_t number = 0;
  std::string alternative;
  std::vector<Datum> items;
  static Datum scalar(uint64_t n) { return {n, {}, {}}; }
  static Datum sequence(std::vector<Datum> items = {}) {
    return {0, {}, std::move(items)};
  }
  static Datum record(std::vector<Datum> fields, StringRef name = "Record") {
    return {0, name.str(), std::move(fields)};
  }
  bool operator==(const Datum &other) const {
    return number == other.number && alternative == other.alternative &&
           items == other.items;
  }
};
using Data = std::vector<Datum>;
struct ModelStop : std::runtime_error {
  ModelStop() : std::runtime_error("modeled native stop") {}
};
struct Execution {
  const Input &input;
  OracleVerificationContext context;
  Data receiverStores, holderStores, openedRequests, authenticatedRequests;
  unsigned work = 100000;
  unsigned failAuthentication = std::numeric_limits<unsigned>::max();
  explicit Execution(const Input &input)
      : input(input),
        context(take(OracleVerificationContext::read(*input.candidate))) {
    receiverStores.resize(input.exchange.receiverStores.size(),
                          Datum::sequence());
    holderStores.resize(input.exchange.holderStores.size(), Datum::sequence());
    for (const auto &arm : input.exchange.arms) {
      auto item = find_if(input.receiver.constructors, [&](const auto &item) {
        return item.source == arm.constructor;
      });
      require(item != input.receiver.constructors.end(),
              "missing receiver constructor");
      Data records;
      for (unsigned instance = 0; instance < 3; ++instance) {
        Data fields;
        for (const auto &field : input.storage.constructors[arm.constructor]
                                     .roles[item->role]
                                     .fields) {
          // Equal abstract roots deliberately do not merge distinct anchors.
          fields.push_back(Datum::scalar(field.name == "shape.rows" ? 4
                                         : field.name == "root"     ? 77
                                                                    : 1));
        }
        records.push_back(Datum::record(std::move(fields)));
      }
      receiverStores[arm.receiverSlot] = Datum::sequence(std::move(records));
    }
  }
  Datum request(unsigned arm, uint64_t instance, uint64_t position) {
    return Datum::record({Datum::scalar(input.exchange.arms[arm].constructor),
                          Datum::scalar(instance), Datum::scalar(position)});
  }
  const OracleQueryExchange::Arm &arm(const Datum &request) {
    if (request.alternative != "Record" || request.items.size() != 3)
      throw ModelStop();
    auto found = find_if(input.exchange.arms, [&](const auto &arm) {
      return arm.constructor == request.items[0].number;
    });
    if (found == input.exchange.arms.end())
      throw ModelStop();
    return *found;
  }
  Datum key(const Datum &request, ArrayRef<Datum> stores) {
    const auto &selected = arm(request);
    auto stored =
        run(selected.receiverLookup, {request.items[0], request.items[1],
                                      stores[selected.receiverSlot]});
    auto position = run(input.merkle[selected.constructor].position,
                        {stored[selected.receiverRows], request.items[2]});
    return Datum::record({request.items[0], request.items[1], position[1]});
  }
  Data run(func::FuncOp function, ArrayRef<Datum> arguments,
           unsigned depth = 0) {
    require(depth < 64, "modeled call depth");
    if (function == input.openOne) {
      openedRequests.push_back(arguments[0]);
      const auto &selected = arm(arguments[0]);
      auto physicalKey = key(arguments[0], receiverStores);
      // Abstract row/proof stand-ins; no claim about field arithmetic or
      // hashes.
      return {Datum::record({physicalKey, Datum::scalar(77)},
                            selected.alternative)};
    }
    if (function == input.response.authenticate) {
      auto ordinal = authenticatedRequests.size();
      authenticatedRequests.push_back(arguments[0]);
      if (ordinal == failAuthentication)
        throw ModelStop();
      const auto &selected = arm(arguments[0]);
      auto expected = key(arguments[0], arguments.drop_front(2));
      const auto &response = arguments[1];
      if (response.alternative != selected.alternative ||
          response.items.size() != 2 || !(response.items[0] == expected))
        throw ModelStop();
      return {Datum::record({arguments[0].items[2]}, selected.alternative)};
    }
    require(arguments.size() + 1 == function.getNumArguments(),
            "modeled signature");
    llvm::DenseMap<Value, Datum> values;
    for (auto [formal, value] :
         zip(function.getArguments().drop_front(), arguments))
      values[formal] = value;
    auto found = context.getClosure().bodies.find(function.getSymName().str());
    require(found != context.getClosure().bodies.end(), "missing modeled body");
    for (const auto &step : found->second) {
      require(work-- != 0, "modeled work exhausted");
      Data args;
      for (auto value : step.inputs) {
        auto found = values.find(value);
        require(found != values.end(), "unbound modeled SSA operand");
        args.push_back(found->second);
      }
      auto *op = step.operation;
      Data results;
      if (isa<exec::ReturnOp, exec::CompleteOp>(op))
        return args;
      if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            apply, apply.getBindingAttr());
        auto contract = binding.getContract();
        if (contract == "index.constant") {
          results = {Datum::scalar(cast<IntegerAttr>(apply.getParameters()[0])
                                       .getValue()
                                       .getZExtValue())};
        } else if (contract == "control.require") {
          if (!args[0].number)
            throw ModelStop();
        } else if (contract == "sequence.empty") {
          results = {Datum::sequence()};
        } else if (contract == "sequence.length") {
          results = {Datum::scalar(args[0].items.size())};
        } else if (contract == "sequence.append") {
          auto sequence = args[0];
          sequence.items.push_back(args[1]);
          results = {std::move(sequence)};
        } else if (contract == "sequence.at") {
          if (args[1].number >= args[0].items.size())
            throw ModelStop();
          results = {args[0].items[args[1].number]};
        } else {
          auto a = args[0].number;
          auto b = args.size() > 1 ? args[1].number : 0;
          uint64_t value;
          if (contract == "index.equal")
            value = a == b;
          else if (contract == "index.less")
            value = a < b;
          else if (contract == "bool.and")
            value = bool(a) && bool(b);
          else if (contract == "bool.not")
            value = !a;
          else if (contract == "index.wrapping_sub")
            value = a - b;
          else if (contract == "index.bit_and")
            value = a & b;
          else if (contract == "index.add") {
            if (b > std::numeric_limits<uint64_t>::max() - a)
              throw ModelStop();
            value = a + b;
          } else if (contract == "index.sub") {
            if (a < b)
              throw ModelStop();
            value = a - b;
          } else if (contract == "index.mul") {
            if (a && b > std::numeric_limits<uint64_t>::max() / a)
              throw ModelStop();
            value = a * b;
          } else if (contract == "index.div" || contract == "index.mod") {
            if (!b)
              throw ModelStop();
            value = contract == "index.div" ? a / b : a % b;
          } else
            throw std::runtime_error("unmodeled binding: " + contract.str());
          results = {Datum::scalar(value)};
        }
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = cast<func::FuncOp>(SymbolTable::lookupSymbolIn(
            unit(*input.candidate), call.getCallee()));
        results = run(callee, args, depth + 1);
      } else if (auto variant = dyn_cast<exec::VariantOp>(op)) {
        results = {Datum::record(std::move(args), variant.getAlternative())};
      } else if (auto match = dyn_cast<exec::MatchOp>(op)) {
        unsigned branch = 0;
        for (; branch < match.getAlternatives().size(); ++branch)
          if (cast<StringAttr>(match.getAlternatives()[branch]).getValue() ==
              args[0].alternative)
            break;
        if (branch == match.getAlternatives().size())
          throw ModelStop();
        Data captures(args[0].items);
        append_range(captures, ArrayRef<Datum>(args).drop_front());
        results = run(step.regions[branch], captures, depth + 1);
      } else if (isa<exec::TestOp>(op)) {
        results = run(step.regions[args[0].number ? 0 : 1],
                      ArrayRef<Datum>(args).drop_front(), depth + 1);
      } else if (isa<exec::RangeOp>(op)) {
        auto count = step.outputs.size();
        results.assign(args.begin() + 2, args.begin() + 2 + count);
        for (uint64_t i = args[0].number; i < args[1].number; ++i) {
          Data captures{Datum::scalar(i)};
          append_range(captures, results);
          append_range(captures, ArrayRef<Datum>(args).drop_front(2 + count));
          auto next = run(step.regions[0], captures, depth + 1);
          auto first = step.conditional ? 1 : 0;
          results.assign(next.begin() + first, next.end());
          if (step.conditional && !next[0].number)
            break;
        }
      } else
        throw std::runtime_error("unmodeled execution operation");
      require(results.size() == step.outputs.size(), "modeled result arity");
      for (auto [value, datum] : zip(step.outputs, results))
        values[value] = datum;
    }
    throw std::runtime_error("modeled body had no completion");
  }
  Data group(const Datum &logical) {
    Data args{logical};
    append_range(args, receiverStores);
    return run(input.packet.group, args);
  }
  Datum open(const Datum &physical) {
    Data args{physical};
    append_range(args, holderStores);
    return run(input.packet.open, args)[0];
  }
  Datum authenticate(const Datum &logical, const Datum &physical,
                     const Datum &groups, const Datum &responses) {
    Data args{logical, physical, groups, responses};
    append_range(args, receiverStores);
    return run(input.packet.authenticate, args)[0];
  }
};
void stopped(llvm::function_ref<void()> body) {
  bool didStop = false;
  try {
    body();
  } catch (const ModelStop &) {
    didStop = true;
  }
  require(didStop, "expected modeled native stop");
}
SourceExecutionStep stepAt(const Input &input, StringRef name) {
  auto target = take(OracleVerificationContext::read(*input.candidate));
  for (const auto &entry : target.getClosure().bodies)
    for (const auto &step : entry.second)
      if (step.operation == site(input, name))
        return step;
  throw std::runtime_error("missing execution step");
}
func::FuncOp cloneHelper(Input &input, func::FuncOp function) {
  auto clone = cast<func::FuncOp>(function->clone());
  clone.setSymName("_packet_unrelated_correct_helper");
  OpBuilder b(clone.getContext());
  clone->setAttr("runtime.origin",
                 b.getArrayAttr({b.getStringAttr(clone.getSymName()),
                                 b.getArrayAttr({})}));
  unit(*input.candidate).getBody().front().push_back(clone);
  return clone;
}
// Add a real scoped action, preserving the existing ordinary failure edge.
void insertBefore(
    Operation *before,
    llvm::function_ref<void(exec::ScopedExecutionBuilder &, OpBuilder &)>
        emit) {
  auto function = before->getParentOfType<func::FuncOp>();
  auto *head = before->getBlock();
  auto *tail = head->splitBlock(Block::iterator(before));
  OpBuilder builder(before->getContext());
  builder.setInsertionPointToEnd(head);
  exec::ScopedExecutionBuilder control(builder, function);
  emit(control, builder);
  cf::BranchOp::create(builder, before->getLoc(), tail, ValueRange{});
}
// Optional normal compiler client. Its explicit ordinary stores deliberately
// make caller binding visible; it does not pretend to realize a source window.
std::string nativeClient(Input &input, const DialectRegistry &registry) {
  auto candidate = *input.candidate;
  OpBuilder b(candidate.getContext());
  auto loc = candidate.getLoc();
  Types inputs{input.packet.requestSequence};
  append_range(inputs, input.exchange.receiverStores);
  append_range(inputs, input.exchange.holderStores);
  Types outputs{input.packet.requestSequence, input.packet.groupsSequence,
                input.packet.responseSequence, input.packet.answerSequence};
  auto owner = b.getStrArrayAttr({"V"});
  OperationState main(loc, "protocol.func");
  main.addAttribute("sym_name", b.getStringAttr("main"));
  main.addAttribute("function_type",
                    TypeAttr::get(b.getFunctionType(inputs, outputs)));
  main.addAttribute("roles", owner);
  main.addAttribute("input_roles", b.getArrayAttr(SmallVector<Attribute>(
                                       inputs.size(), owner)));
  main.addAttribute("output_roles", b.getArrayAttr(SmallVector<Attribute>(
                                        outputs.size(), owner)));
  auto *body = new Block;
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  main.addRegion()->push_back(body);
  b.setInsertionPointToEnd(&unit(candidate).getBody().front());
  b.create(main);
  b.setInsertionPointToEnd(body);
  auto a = body->getArguments();
  auto call = [&](func::FuncOp helper, ValueRange args, StringRef site) {
    return pir::LocalCallOp::create(b, loc,
                                    scopedDataSignature(helper).getResults(),
                                    args, helper.getSymName(), site, "V")
        .getOutputs();
  };
  auto receiver = a.slice(1, input.exchange.receiverStores.size());
  Values groupArgs{a[0]};
  append_range(groupArgs, receiver);
  auto grouped = call(input.packet.group, groupArgs, "group");
  Values openArgs{grouped[0]};
  append_range(openArgs, a.drop_front(1 + receiver.size()));
  auto opened = call(input.packet.open, openArgs, "open");
  Values authArgs{a[0], grouped[0], grouped[1], opened[0]};
  append_range(authArgs, receiver);
  auto answers = call(input.packet.authenticate, authArgs, "authenticate");
  pir::MathematicalReturnOp::create(
      b, loc, ValueRange{grouped[0], grouped[1], opened[0], answers[0]});
  require(succeeded(verify(candidate)), "packet client formation");
  return take(compileRun(print(candidate), "oracle-query-packet.mlir", {},
                         registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  if (argc > 2) {
    errs() << "usage: oracle-query-packet-test [output-directory]\n";
    return 1;
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  for (auto grouping :
       {OracleLeafGrouping::Individual, OracleLeafGrouping::AntipodalPairs})
    for (auto order : {OracleLeafOrder::Natural, OracleLeafOrder::BitReversed})
      for (bool sameKind : {false, true})
        cases.run(
            "fresh textual packet, modeled order/anchors/layout " +
                Twine(unsigned(grouping)) + "/" + Twine(unsigned(order)) + "/" +
                Twine(sameKind),
            [&] {
              auto input = emitted(context, sameKind, grouping, order);
              auto parsed = parse(context, print(*input.candidate));
              auto old = std::move(input.candidate);
              input.candidate = std::move(parsed);
              // Equal names do not bind model handles to a different module.
              refused(checkPacket(input));
              rebind(input);
              checkModel(input);
              {
                auto target =
                    take(OracleVerificationContext::read(*input.candidate));
                checked(checkOracleQueryResponse(target, input.exchange,
                                                 input.response));
                require(checkOracleQueryExchange(target, input.openOne,
                                                 openingRecipe(input)),
                        "parsed openOne body");
              }
              checked(checkPacket(input));
              if (!sameKind)
                require(input.exchange.arms[0].constructor !=
                            input.exchange.arms[0].kind,
                        "kind/constructor independence was not exercised");
              auto answer = cast<data::VariantType>(input.response.answer);
              require(
                  cast<data::SequenceType>(input.packet.answerSequence)
                          .getElementType() == input.response.answer,
                  "packet answer type differs from detached response answer");
              require(sameKind ||
                          answer.getAlternatives()[0].getPayload()[0] !=
                              answer.getAlternatives()[1].getPayload()[0],
                      "heterogeneous field answers were erased");
              Execution execution(input);
              auto logical = Datum::sequence(
                  {execution.request(0, 0, 1), execution.request(0, 0, 1),
                   execution.request(0, 1, 1), execution.request(1, 0, 1),
                   execution.request(0, 0, 3), execution.request(0, 1, 1)});
              auto grouped = execution.group(logical);
              bool paired = grouping == OracleLeafGrouping::AntipodalPairs;
              std::vector<uint64_t> expected{0, 0, 1, 2, paired ? 0u : 3u, 1};
              require(grouped[0].items.size() == (paired ? 3 : 4),
                      "physical representative count");
              for (auto [i, ordinal] : enumerate(expected))
                require(grouped[1].items[i].number == ordinal,
                        "first-use group order or multiplicity");
              require(grouped[0].items[0] == logical.items[0] &&
                          grouped[0].items[1] == logical.items[2] &&
                          grouped[0].items[2] == logical.items[3],
                      "physical representative order");
              auto layout = take(OracleTableLayout::create(4, grouping, order));
              auto actualPosition = execution.run(
                  input.merkle[input.exchange.arms[0].constructor].position,
                  {Datum::scalar(4), Datum::scalar(1)});
              require(actualPosition[1].number == take(layout.locate(1)).leaf,
                      "actual position differs from selected layout");
              auto responses = execution.open(grouped[0]);
              auto answers = execution.authenticate(logical, grouped[0],
                                                    grouped[1], responses);
              require(execution.openedRequests == grouped[0].items &&
                          execution.authenticatedRequests == logical.items &&
                          answers.items.size() == logical.items.size(),
                      "opening or authentication did not execute once in its "
                      "required order");
              for (unsigned i = 0; i < answers.items.size(); ++i)
                require(answers.items[i].items[0].number ==
                            logical.items[i].items[2].number,
                        "logical answer position was replaced by the "
                        "representative position");
              auto empty = Datum::sequence();
              auto groupedEmpty = execution.group(empty);
              require(groupedEmpty[0].items.empty() &&
                          groupedEmpty[1].items.empty() &&
                          execution.open(empty).items.empty() &&
                          execution.authenticate(empty, empty, empty, empty)
                              .items.empty(),
                      "empty packet");
              require(execution.openedRequests == grouped[0].items &&
                          execution.authenticatedRequests == logical.items,
                      "empty packet performed an opening or authentication");
            });
  cases.run("exact capacity, singleton capacity and repeated shared work", [&] {
    auto input = emitted(context);
    Datum request;
    {
      Execution execution(input);
      request = execution.request(0, 0, 1);
      auto logical = Datum::sequence(Data(input.packetCapacity, request));
      auto grouped = execution.group(logical);
      auto responses = execution.open(grouped[0]);
      require(
          grouped[0].items.size() == 1 &&
              grouped[1].items.size() == input.packetCapacity &&
              execution.authenticate(logical, grouped[0], grouped[1], responses)
                      .items.size() == input.packetCapacity,
          "exact-capacity repeated packet");
    }
    auto before = input.work;
    auto prior = input.packet;
    input.packetCapacity = 1;
    input.packet = take(emitOracleQueryPacket(
        *input.candidate, input.exchange, input.response, input.openOne,
        input.merkle, input.packetCapacity, input.work));
    require(input.packet.key == prior.key &&
                input.packet.answerSequence == prior.answerSequence &&
                input.packet.group != prior.group &&
                input.packet.open != prior.open &&
                input.packet.authenticate != prior.authenticate &&
                input.work.operations < before.operations &&
                input.work.slots < before.slots,
            "repeated packet emission reset work or reused functions");
    checked(checkPacket(input));
    Execution singleton(input);
    auto logical = Datum::sequence({request});
    auto grouped = singleton.group(logical);
    auto responses = singleton.open(grouped[0]);
    require(singleton.authenticate(logical, grouped[0], grouped[1], responses)
                    .items.size() == 1,
            "singleton capacity");
    stopped([&] { singleton.group(Datum::sequence({request, request})); });
  });
  cases.run(
      "modeled finite bounds, exact lookups and per-occurrence stops", [&] {
        auto input = emitted(context);
        auto empty = Datum::sequence();
        Execution execution(input);
        auto request = execution.request(0, 0, 1);
        auto logical = Datum::sequence({request, request, request});
        auto grouped = execution.group(logical);
        auto responses = execution.open(grouped[0]);
        auto oversized =
            Datum::sequence(Data(input.packetCapacity + 1, request));
        stopped([&] { execution.group(oversized); });
        stopped([&] { execution.open(oversized); });
        auto oversizedGroups =
            Datum::sequence(Data(input.packetCapacity + 1, Datum::scalar(0)));
        stopped([&] {
          execution.authenticate(oversized, grouped[0], oversizedGroups,
                                 responses);
        });
        auto oversizedResponses =
            Datum::sequence(Data(input.packetCapacity + 1, responses.items[0]));
        stopped([&] {
          execution.authenticate(logical, oversized, grouped[1],
                                 oversizedResponses);
        });
        stopped([&] {
          execution.authenticate(logical, grouped[0], empty, responses);
        });
        stopped([&] {
          execution.authenticate(logical, grouped[0], grouped[1], empty);
        });
        auto invalidGroups = grouped[1];
        invalidGroups.items[2] = Datum::scalar(1);
        stopped([&] {
          execution.authenticate(logical, grouped[0], invalidGroups, responses);
        });
        auto distinct = Datum::sequence({request, execution.request(0, 1, 1)});
        auto distinctGroups = execution.group(distinct);
        auto distinctResponses = execution.open(distinctGroups[0]);
        auto wrongPairing = distinctGroups[1];
        wrongPairing.items[1] = Datum::scalar(0);
        stopped([&] {
          execution.authenticate(distinct, distinctGroups[0], wrongPairing,
                                 distinctResponses);
        });
        auto unknown = request;
        unknown.items[0] = Datum::scalar(10000);
        stopped([&] { execution.group(Datum::sequence({unknown})); });
        stopped([&] {
          execution.group(Datum::sequence({execution.request(0, 99, 1)}));
        });
        stopped([&] {
          execution.group(Datum::sequence({execution.request(0, 0, 4)}));
        });
        Execution nonPowerOfTwo(input);
        const auto &arm = input.exchange.arms[0];
        nonPowerOfTwo.receiverStores[arm.receiverSlot]
            .items[0]
            .items[arm.receiverRows] = Datum::scalar(3);
        stopped([&] { nonPowerOfTwo.group(Datum::sequence({request})); });
        Execution invalidLastOccurrence(input);
        invalidLastOccurrence.failAuthentication = 2;
        stopped([&] {
          invalidLastOccurrence.authenticate(logical, grouped[0], grouped[1],
                                             responses);
        });
        require(
            invalidLastOccurrence.authenticatedRequests == logical.items,
            "shared physical response skipped a later logical authentication");
        // This primitive deliberately checks lengths and logical
        // authentication, not equality between arbitrary caller-supplied
        // physical descriptors and an earlier grouping result. The complete
        // window must bind that call.
        auto unrelatedPhysical = grouped[0];
        unrelatedPhysical.items[0] = execution.request(1, 2, 3);
        require(execution
                        .authenticate(logical, unrelatedPhysical, grouped[1],
                                      responses)
                        .items.size() == 3,
                "packet silently widened its source-window binding contract");
      });
  const std::vector<std::string> attacks{
      "constructor dispatch",
      "reference instance",
      "key constructor",
      "key instance",
      "key leaf",
      "actual rows",
      "logical position",
      "receiver store",
      "scan order",
      "scan key index",
      "key constructor equality",
      "key instance equality",
      "key leaf equality",
      "first match group ordinal",
      "new group ordinal",
      "logical sequence read",
      "physical sequence read",
      "opening order",
      "logical group length",
      "physical response length",
      "capacity",
      "authentication bound",
      "logical authentication request",
      "group ordinal read",
      "physical response pairing",
      "answer sequence append",
      "skipped length guard",
      "correct unrelated position helper",
      "correct unrelated opening helper",
      "correct unrelated authentication helper",
      "key call captures",
      "lookup reference",
      "exact native comparison binding",
      "helper preconditions",
      "helper origin",
      "helper visibility"};
  for (auto [attack, name] : enumerate(attacks))
    cases.run("formed packet attack: " + name, [&, attack = attack] {
      auto input = emitted(context, true);
      auto prefix = "packet_constructor_" +
                    std::to_string(input.exchange.arms[0].constructor) + "_";
      auto apply = [&](StringRef name) {
        return cast<exec::ApplyOp>(site(input, name));
      };
      auto call = [&](StringRef name) {
        return cast<func::CallOp>(site(input, name));
      };
      auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
      auto parameter = [&](StringRef name, uint64_t value) {
        apply(name).setParametersAttr(
            ArrayAttr::get(&context, {IntegerAttr::get(index, value)}));
      };
      if (attack == 0) {
        parameter(prefix + "tag", input.exchange.arms[1].constructor);
      } else if (attack == 1) {
        auto op = call(prefix + "lookup");
        op.setOperand(2, op.getOperand(1));
      } else if (attack >= 2 && attack <= 4) {
        auto op = cast<exec::VariantOp>(site(input, prefix + "key"));
        unsigned field = attack - 2;
        auto wrong = field == 2 ? stepAt(input, prefix + "position").outputs[2]
                                : op.getPayload()[(field + 1) % 3];
        op.getPayloadMutable()[field].set(wrong);
      } else if (attack == 5 || attack == 6) {
        auto op = call(prefix + "position");
        op.setOperand(attack == 5 ? 1 : 2, op.getOperand(attack == 5 ? 2 : 1));
      } else if (attack == 7) {
        auto op = call(prefix + "lookup");
        auto store = op.getOperand(3).getType();
        insertBefore(op, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                    "_packet_attack_binding_");
          auto binding = bindings.binding(
              b, op.getLoc(),
              {"sequence.empty",
               {TypeAttr::get(
                   cast<data::SequenceType>(store).getElementType())},
               ""});
          auto replacement = c.invoke(
              "exec.apply", store, c.scoped({}),
              {b.getNamedAttr("binding", binding),
               b.getNamedAttr("parameters", b.getArrayAttr({})),
               b.getNamedAttr("site", b.getStringAttr("packet_wrong_store"))});
          op.setOperand(3, replacement[0]);
        });
      } else if (attack == 8) {
        auto op = cast<exec::RangeOp>(site(input, "packet_scan"));
        op->setOperand(1, op.getUpper());
      } else if (attack == 9) {
        auto op = apply("packet_scan_key");
        auto function = op->getParentOfType<func::FuncOp>();
        op.getInputsMutable()[1].set(function.getArgument(2));
      } else if (attack >= 10 && attack <= 12) {
        auto name = attack == 10   ? "packet_same_constructor"
                    : attack == 11 ? "packet_same_instance"
                                   : "packet_same_leaf";
        auto op = apply(name);
        op.getInputsMutable()[1].set(op.getInputs()[0]);
      } else if (attack == 13) {
        auto found = stepAt(input, "packet_found");
        auto function = found.regions[0];
        function.walk([&](exec::CompleteOp op) {
          op->setOperand(1, function.getArgument(2));
        });
      } else if (attack == 14) {
        auto op = apply("packet_add_new_group");
        insertBefore(op, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                    "_packet_attack_binding_");
          auto binding =
              bindings.binding(b, op.getLoc(), {"index.constant", {}, ""});
          auto zero = c.invoke(
              "exec.apply", index, c.scoped({}),
              {b.getNamedAttr("binding", binding),
               b.getNamedAttr("parameters",
                              b.getArrayAttr({b.getIntegerAttr(index, 0)})),
               b.getNamedAttr("site", b.getStringAttr("packet_wrong_group"))});
          op.getInputsMutable()[1].set(zero[0]);
        });
      } else if (attack == 15 || attack == 16) {
        auto op = apply(attack == 15 ? "packet_logical_request"
                                     : "packet_physical_request");
        // Same collection type; replace the sequence with an empty one at its
        // reached occurrence, without relying on an ill-typed operand swap.
        auto sequence = op.getInputs()[0].getType();
        insertBefore(op, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                    "_packet_attack_binding_");
          auto binding = bindings.binding(
              b, op.getLoc(),
              {"sequence.empty", {TypeAttr::get(input.exchange.request)}, ""});
          auto empty =
              c.invoke("exec.apply", sequence, c.scoped({}),
                       {b.getNamedAttr("binding", binding),
                        b.getNamedAttr("parameters", b.getArrayAttr({})),
                        b.getNamedAttr(
                            "site", b.getStringAttr("packet_wrong_requests"))});
          op.getInputsMutable()[0].set(empty[0]);
        });
      } else if (attack == 17) {
        parameter("packet_open_lower", 1);
      } else if (attack == 18 || attack == 19) {
        auto op =
            apply(attack == 18 ? "packet_logical_group_lengths_equal"
                               : "packet_physical_response_lengths_equal");
        op.getInputsMutable()[1].set(op.getInputs()[0]);
      } else if (attack == 20) {
        parameter("packet_group_capacity", input.packetCapacity + 2);
      } else if (attack == 21) {
        auto op = cast<exec::RangeOp>(site(input, "packet_authenticate"));
        op->setOperand(2,
                       stepAt(input, "packet_auth_physical_length").outputs[0]);
      } else if (attack == 22) {
        auto op = apply("packet_auth_request");
        auto function = op->getParentOfType<func::FuncOp>();
        op.getInputsMutable()[0].set(function.getArgument(4));
      } else if (attack == 23) {
        parameter("packet_auth_lower", 1);
      } else if (attack == 24) {
        auto op = apply("packet_auth_response");
        op.getInputsMutable()[1].set(
            op->getParentOfType<func::FuncOp>().getArgument(1));
      } else if (attack == 25) {
        auto op = apply("packet_add_answer");
        auto function = op->getParentOfType<func::FuncOp>();
        auto completed = stepAt(input, "packet_authenticate").regions[0];
        require(function == completed, "answer append iteration");
        function.walk([&](exec::CompleteOp complete) {
          complete->setOperand(1, function.getArgument(2));
        });
      } else if (attack == 26) {
        auto op = apply("packet_group_within_capacity");
        OpBuilder b(&context);
        mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                  "_packet_attack_binding_");
        op.setBindingAttr(
            bindings.binding(b, op.getLoc(), {"index.equal", {}, ""}));
        op.getInputsMutable()[1].set(op.getInputs()[0]);
      } else if (attack >= 27 && attack <= 29) {
        auto op = call(attack == 27   ? prefix + "position"
                       : attack == 28 ? "packet_open_one"
                                      : "packet_authenticate_one");
        auto expected =
            attack == 27
                ? input.merkle[input.exchange.arms[0].constructor].position
            : attack == 28 ? input.openOne
                           : input.response.authenticate;
        op.setCalleeAttr(FlatSymbolRefAttr::get(cloneHelper(input, expected)));
      } else if (attack == 30) {
        // Constructor/instance captures entering the exact selected arm.
        auto op = cast<exec::TestOp>(site(input, prefix + "dispatch"));
        auto function = op->getParentOfType<func::FuncOp>();
        function.walk([&](runtime::EnterScopeOp enter) {
          if (enter.getSite() == prefix + "dispatch") {
            auto values = Values(enter.getInputs());
            std::swap(values[0], values[1]);
            enter.getInputsMutable().assign(values);
          }
        });
      } else if (attack == 31) {
        auto op = call(prefix + "lookup");
        op.setOperand(1, op.getOperand(2));
      } else if (attack == 32) {
        auto op = apply("packet_same_leaf");
        OpBuilder b(&context);
        mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                  "_packet_attack_binding_");
        op.setBindingAttr(
            bindings.binding(b, op.getLoc(), {"index.less", {}, ""}));
      } else if (attack == 33) {
        input.packet.authenticate->setAttr("data.preconditions",
                                           ArrayAttr::get(&context, {}));
      } else if (attack == 34) {
        OpBuilder b(&context);
        input.packet.group->setAttr(
            "runtime.origin",
            b.getArrayAttr(
                {b.getStringAttr("unrelated_origin"), b.getArrayAttr({})}));
      } else {
        input.packet.open.setPublic();
      }
      require(succeeded(verify(*input.candidate)),
              "attack only failed MLIR formation");
      // The whole-candidate admission boundary may reject malformed scoped
      // control before the independent helper grammar is read.
      if (auto context = OracleVerificationContext::read(*input.candidate))
        refused(checkPacket(input));
      else
        refused(context.takeError(), "oracle-verification-source");
    });
  cases.run(
      "capacity, layout, overflow and shared budget refusal preserve inputs",
      [&] {
        auto input = emitted(context);
        auto source = print(*input.source), prepared = print(*input.prepared),
             candidate = print(*input.candidate);
        for (unsigned refusal = 0; refusal < 15; ++refusal) {
          auto model = input.exchange;
          auto response = input.response;
          auto merkle = input.merkle;
          auto opening = input.openOne;
          auto capacity = input.packetCapacity;
          auto work = input.work;
          StringRef code = "oracle-packet-layout";
          if (refusal == 0 || refusal == 1) {
            if (refusal == 0)
              work.operations = 0;
            else
              work.slots = 0;
            code = "oracle-packet-limit";
          } else if (refusal >= 2 && refusal <= 4) {
            capacity = refusal == 2   ? 0
                       : refusal == 3 ? 1048576
                                      : std::numeric_limits<uint64_t>::max();
            code = "oracle-packet-capacity";
          } else if (refusal == 5) {
            capacity = 1048575;
            code = "oracle-packet-limit";
          } else if (refusal == 6) {
            model.arms.resize(33, model.arms[0]);
            code = "oracle-packet-capacity";
          } else if (refusal == 7) {
            model.receiverStores.resize(481, model.receiverStores[0]);
            code = "oracle-packet-capacity";
          } else if (refusal == 8) {
            model.holderStores.resize(481, model.holderStores[0]);
            code = "oracle-packet-capacity";
          } else if (refusal == 9) {
            opening = response.authenticate;
          } else if (refusal == 10) {
            response.answer = model.response;
          } else if (refusal == 11) {
            merkle[model.arms[0].constructor].position = {};
          } else if (refusal == 12) {
            model.arms[0].receiverRows = 999;
          } else if (refusal == 13) {
            model.arms[0].receiverSlot = model.arms[1].receiverSlot;
          } else {
            model.request = model.response;
          }
          auto before = work;
          refuses(emitOracleQueryPacket(*input.candidate, model, response,
                                        opening, merkle, capacity, work),
                  code);
          require(work.operations == before.operations &&
                      work.slots == before.slots,
                  "refused packet debited shared work");
          require(print(*input.source) == source &&
                      print(*input.prepared) == prepared &&
                      print(*input.candidate) == candidate,
                  "refused packet mutated inputs");
        }
        auto empty =
            OwningOpRef<ModuleOp>(ModuleOp::create(UnknownLoc::get(&context)));
        refuses(emitOracleQueryPacket(*empty, input.exchange, input.response,
                                      input.openOne, input.merkle,
                                      input.packetCapacity, input.work),
                "oracle-packet-source");
        refuses(emitOracleQueryPacket(*input.prepared, input.exchange,
                                      input.response, input.openOne,
                                      input.merkle, input.packetCapacity,
                                      input.work),
                "oracle-packet-layout");
        require(print(*input.prepared) == prepared,
                "foreign model modified prepared source");
      });
  cases.run(
      "reader rederives packet layout, capacity and exact source helpers", [&] {
        auto input = emitted(context);
        auto target = take(OracleVerificationContext::read(*input.candidate));
        auto packet = input.packet;
        packet.key = input.exchange.request;
        refused(checkOracleQueryPacket(target, input.exchange, input.response,
                                       input.openOne, input.merkle,
                                       input.packetCapacity, packet));
        packet = input.packet;
        packet.answerSequence = input.packet.responseSequence;
        refused(checkOracleQueryPacket(target, input.exchange, input.response,
                                       input.openOne, input.merkle,
                                       input.packetCapacity, packet));
        refused(checkOracleQueryPacket(target, input.exchange, input.response,
                                       input.openOne, input.merkle,
                                       input.packetCapacity + 1, input.packet));
        auto helpers = input.merkle;
        helpers[0] = helpers[1];
        refused(checkOracleQueryPacket(target, input.exchange, input.response,
                                       input.openOne, helpers,
                                       input.packetCapacity, input.packet));
        checked(checkPacket(input));
      });
  if (argc == 2)
    for (auto grouping :
         {OracleLeafGrouping::Individual, OracleLeafGrouping::AntipodalPairs})
      for (auto order :
           {OracleLeafOrder::Natural, OracleLeafOrder::BitReversed})
        cases.run("optional native compiler client " +
                      Twine(unsigned(grouping)) + "/" + Twine(unsigned(order)),
                  [&] {
                    auto input = emitted(context, false, grouping, order);
                    auto bundle = nativeClient(input, registry);
                    require(!bundle.empty(), "empty packet bundle");
                    std::filesystem::create_directories(argv[1]);
                    auto name = "packet-" + std::to_string(unsigned(grouping)) +
                                "-" + std::to_string(unsigned(order)) +
                                ".bundle";
                    std::ofstream output(std::filesystem::path(argv[1]) / name);
                    output << bundle;
                    require(bool(output), "cannot save packet bundle");
                  });
  return cases.result();
}

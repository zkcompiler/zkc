#include "../lib/Transforms/OracleQueryResponse.h"
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
void refused(Error error, StringRef code = "oracle-response-body") {
  require(bool(error), "expected response refusal");
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
  OracleVirtualFunctionWork work;
};
std::string scheme(const OracleAnchorConstructor &anchor) {
  auto field = cast<algebra::FieldType>(anchor.kind.getAnswerType());
  return "rows.merkle-poseidon2-16." + field.getDomain().str() + "/0";
}
Error checkResponse(const Input &input) {
  auto context = OracleVerificationContext::read(*input.candidate);
  if (!context)
    return context.takeError();
  return checkOracleQueryResponse(*context, input.exchange, input.response);
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
Input emitted(MLIRContext &context, bool sameKind = false) {
  Input input;
  // This is the existing source fixture with a recurrent virtual and two
  // distinct committed base constructors, including an unused child answer.
  auto path = std::filesystem::path(ZKC_ORACLE_FIXTURES) /
              "query-constructors.mlir";
  std::ifstream fixture(path);
  require(bool(fixture), "cannot read constructor source fixture");
  std::string text((std::istreambuf_iterator<char>(fixture)), {});
  if (sameKind) {
    for (StringRef fragment : {"!BF = !algebra.field<\"koala-bear\">",
                               "!BD = !algebra.field_vector<\"koala-bear\">"}) {
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
  auto before = input.work;
  input.response = take(
      emitOracleQueryResponse(*input.candidate, input.exchange, input.work));
  require(input.work.operations < before.operations &&
              input.work.slots < before.slots,
          "response emission did not debit shared work");
  checked(checkResponse(input));
  require(print(*input.source) == frozenSource &&
              print(*input.prepared) == frozenPrepared,
          "response emission or reading mutated source");
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
}
Operation *site(Input &input, StringRef name) {
  Operation *found = nullptr;
  input.candidate->walk([&](Operation *op) {
    auto actual = op->getAttrOfType<StringAttr>("runtime.site");
    if (op->getName().getDialectNamespace() == "exec")
      actual = op->getAttrOfType<StringAttr>("site");
    if (actual && actual.getValue() == name) {
      require(!found, "ambiguous mutation site: " + name);
      found = op;
    }
  });
  require(found, "missing mutation site: " + name);
  return found;
}
// Insert a real scoped effect before existing control, preserving its native
// stop edge. The original tail continues only if the injected effect succeeds.
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
void noPrematureEffects(const Input &input) {
  auto closure = take(readSourceExecutionClosure(unit(*input.candidate)));
  auto inspect = [&](func::FuncOp entry, bool authenticating) {
    std::set<std::string> visited;
    unsigned calls = 0;
    std::function<void(func::FuncOp)> visit = [&](func::FuncOp function) {
      require(visited.insert(function.getSymName().str()).second,
              "response control was cyclic or reused an arm");
      auto found = closure.bodies.find(function.getSymName().str());
      require(found != closure.bodies.end(), "missing response body");
      for (const auto &step : found->second) {
        require(!isa<exec::ComputeOp>(step.operation),
                "response primitive recomputed an answer");
        if (auto call = dyn_cast<func::CallOp>(step.operation)) {
          auto target = SymbolTable::lookupSymbolIn(unit(*input.candidate),
                                                    call.getCallee());
          require(
              any_of(input.exchange.arms,
                     [&](auto arm) {
                       return authenticating
                                  ? target == arm.authenticate.getOperation() ||
                                        target ==
                                            arm.receiverLookup.getOperation()
                                  : target == arm.resume.getOperation();
                     }),
              "response crossed the authentication/resume boundary");
          ++calls;
        }
        for (auto region : step.regions)
          visit(region);
      }
    };
    visit(entry);
    require(calls == input.exchange.arms.size() * (authenticating ? 2 : 1),
            "a constructor skipped its own authentication or resume");
  };
  inspect(input.response.authenticate, true);
  inspect(input.response.resume, false);
}
// A native client of the detached boundary, following oracle_merkle.cpp's
// optional bundle convention. The independently supplied state is deliberate:
// phase/kind/coordinate attacks must be stopped by this primitive. The window
// checker, rather than this client, owns validity of the source root
// occurrence.
std::string client(Input &input, unsigned ordinal,
                   const DialectRegistry &registry) {
  auto candidate = *input.candidate;
  const auto &arm = input.exchange.arms[ordinal];
  const auto &anchor = input.storage.constructors[arm.constructor];
  auto selected = find_if(input.receiver.constructors, [&](const auto &item) {
    return item.source == arm.constructor;
  });
  require(selected != input.receiver.constructors.end(), "missing receiver");
  auto allocate = take(emitOracleAnchorAllocator(
      candidate, input.storage, arm.constructor, selected->role));
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto index =
      IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned);
  // proof table, stored-root table, rows, stored rows, opening position,
  // request ctor/instance/position, state ctor/instance/position/phase/kind.
  Types inputs{anchor.kind.getDataType(), anchor.kind.getDataType()};
  append_range(inputs, Types(11, index));
  Types outputs{index, index, index,
                input.exchange.state[Controller::HeaderSize + arm.kind]};
  auto owner = builder.getStrArrayAttr({"V"});
  OperationState main(loc, "protocol.func");
  main.addAttribute("sym_name", builder.getStringAttr("main"));
  main.addAttribute("function_type",
                    TypeAttr::get(builder.getFunctionType(inputs, outputs)));
  main.addAttribute("roles", owner);
  main.addAttribute("input_roles", builder.getArrayAttr(SmallVector<Attribute>(
                                       inputs.size(), owner)));
  main.addAttribute("output_roles", builder.getArrayAttr(SmallVector<Attribute>(
                                        outputs.size(), owner)));
  auto *body = new Block;
  body->addArguments(inputs, SmallVector<Location>(inputs.size(), loc));
  main.addRegion()->push_back(body);
  builder.setInsertionPointToEnd(&unit(candidate).getBody().front());
  builder.create(main);
  builder.setInsertionPointToEnd(body);
  auto a = body->getArguments();
  auto call = [&](func::FuncOp function, ValueRange args, StringRef name) {
    return pir::LocalCallOp::create(builder, loc,
                                    scopedDataSignature(function).getResults(),
                                    args, function.getSymName(), name, "V")
        .getOutputs();
  };
  auto number = [&](unsigned n) -> Value {
    return data::IndexOp::create(builder, loc, index, n);
  };
  auto proofRoot =
      call(input.merkle[arm.constructor].commit, {a[0], a[2]}, "proof_root");
  auto storedRoot =
      call(input.merkle[arm.constructor].commit, {a[1], a[2]}, "stored_root");
  auto opened = call(arm.open, {proofRoot[1], a[2], a[4]}, "open");
  Values stores;
  for (auto type : input.exchange.receiverStores)
    stores.push_back(data::SequenceEmptyOp::create(builder, loc, type));
  auto request = data::MakeOp::create(builder, loc, input.exchange.request,
                                      ValueRange{a[5], a[6], a[7]}, "Record");
  auto response = data::MakeOp::create(builder, loc, input.exchange.response,
                                       opened, arm.alternative);
  Value answer;
  // Reuse exactly one physical response for two logical occurrences. The
  // second call independently checks its supplied immutable store; a valid
  // first authentication cannot authorize a different second root or shape.
  for (unsigned occurrence = 0; occurrence < 2; ++occurrence) {
    Value empty = data::SequenceEmptyOp::create(
        builder, loc, input.exchange.receiverStores[arm.receiverSlot]);
    Values allocateArgs{empty};
    for (const auto &field : anchor.roles[selected->role].fields) {
      if (field.name == "shape.rows")
        allocateArgs.push_back(a[occurrence == 0 ? 2 : 3]);
      else if (field.name == "query.leaves")
        allocateArgs.push_back(number(1));
      else {
        require(field.name == "root", "unexpected receiver storage field");
        allocateArgs.push_back(occurrence == 0 ? proofRoot[0] : storedRoot[0]);
      }
    }
    auto allocated =
        call(allocate, allocateArgs, "allocate_" + std::to_string(occurrence));
    stores[arm.receiverSlot] = allocated[1];
    Values authArgs{request, response};
    append_range(authArgs, stores);
    answer = call(input.response.authenticate, authArgs,
                  "authenticate_" + std::to_string(occurrence))[0];
  }
  auto root = data::MakeOp::create(
      builder, loc, input.exchange.arms[0].reference,
      ValueRange{number(input.exchange.arms[0].constructor), number(0)},
      "Record");
  auto initial = call(input.receiver.initialize, {root, a[10]}, "initialize");
  Values state(initial);
  state[Controller::Constructor] = a[8];
  state[Controller::Instance] = a[9];
  state[Controller::Position] = a[10];
  state[Controller::Phase] = a[11];
  state[Controller::Kind] = a[12];
  Values resumeArgs{request, answer};
  append_range(resumeArgs, state);
  auto resumed = call(input.response.resume, resumeArgs, "resume");
  pir::MathematicalReturnOp::create(
      builder, loc,
      ValueRange{resumed[Controller::Phase], resumed[Controller::Kind],
                 resumed[Controller::AnswerIndex],
                 resumed[Controller::HeaderSize + arm.kind]});
  require(succeeded(verify(candidate)), "response client formation");
  return take(compileRun(print(candidate), "oracle-query-response.mlir", {},
                         registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  if (argc > 2) {
    errs() << "usage: oracle-query-response-test [output-directory]\n";
    return 1;
  }
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  cases.run("detached effects, heterogeneous answers and nonzero kind", [&] {
    auto input = emitted(context);
    noPrematureEffects(input);
    auto answer = cast<data::VariantType>(input.response.answer);
    require(answer.getAlternatives().size() == 2, "base constructor inventory");
    for (auto [ordinal, alternative] : enumerate(answer.getAlternatives())) {
      const auto &arm = input.exchange.arms[ordinal];
      require(alternative.getLabel().getValue() == arm.alternative &&
                  alternative.getPayload().size() == 1 &&
                  alternative.getPayload()[0] ==
                      input.storage.constructors[arm.constructor]
                          .kind.getAnswerType(),
              "checked answer did not preserve the source constructor's "
              "logical answer");
    }
    require(answer.getAlternatives()[0].getPayload()[0] !=
                answer.getAlternatives()[1].getPayload()[0],
            "heterogeneous answers were coerced");
    require(input.exchange.arms[1].kind != 0, "nonzero kind was not exercised");
    auto work = input.work;
    auto second = take(
        emitOracleQueryResponse(*input.candidate, input.exchange, input.work));
    require(second.answer == input.response.answer &&
                second.authenticate != input.response.authenticate &&
                second.resume != input.response.resume &&
                input.work.operations < work.operations &&
                input.work.slots < work.slots,
            "repeated emission reused helpers or reset shared work");
    checked(checkResponse(input));
    auto target = take(OracleVerificationContext::read(*input.candidate));
    checked(checkOracleQueryResponse(target, input.exchange, second));
  });
  for (bool sameKind : {false, true})
    cases.run("fresh serialized readback " + Twine(sameKind), [&] {
      auto input = emitted(context, sameKind);
      auto copy = parse(context, print(*input.candidate));
      auto old = std::move(input.candidate);
      input.candidate = std::move(copy);
      // Candidate-local handles are mandatory even when all names are equal.
      refused(checkResponse(input));
      rebind(input);
      checkModel(input);
      checked(checkResponse(input));
      noPrematureEffects(input);
    });
  const std::vector<std::string> mutations{"wrong request constructor",
                                           "wrong request instance",
                                           "wrong logical position",
                                           "unbound replay constructor",
                                           "unbound replay instance",
                                           "unbound replay position",
                                           "wrong phase",
                                           "wrong kind",
                                           "wrong state constructor",
                                           "invented continuation",
                                           "wrong stored rows",
                                           "recomputed root",
                                           "skipped authentication",
                                           "wrong checked answer payload",
                                           "wrong checked answer constructor",
                                           "premature resume before guards",
                                           "substituted authentication helper",
                                           "substituted resume helper",
                                           "wrong response capture",
                                           "wrong binding contract",
                                           "wrong helper origin",
                                           "wrong helper visibility",
                                           "wrong receiver store",
                                           "added helper preconditions"};
  for (auto [mutation, name] : enumerate(mutations))
    cases.run("formed response attack: " + name, [&, mutation = mutation] {
      auto input = emitted(context, true);
      auto prefix = "constructor_" +
                    std::to_string(input.exchange.arms[0].constructor) + "_";
      auto apply = [&](StringRef suffix) {
        return cast<exec::ApplyOp>(site(input, prefix + suffix.str()));
      };
      auto call = [&](StringRef suffix) {
        return cast<func::CallOp>(site(input, prefix + suffix.str()));
      };
      if (mutation == 0) {
        auto op = apply("request_constructor_equal");
        auto function = op->getParentOfType<func::FuncOp>();
        op.getInputsMutable()[0].set(function.getArgument(4));
      } else if (mutation == 1) {
        auto op = cast<exec::VariantOp>(site(input, prefix + "anchor"));
        op.getPayloadMutable()[1].set(op.getPayload()[0]);
      } else if (mutation == 2) {
        auto op = call("authenticate");
        auto function = op->getParentOfType<func::FuncOp>();
        op.setOperand(3, function.getArgument(4));
      } else if (mutation >= 3 && mutation <= 5) {
        auto op =
            apply("request_field_" + std::to_string(mutation - 3) + "_equal");
        op.getInputsMutable()[1].set(op.getInputs()[0]);
      } else if (mutation >= 6 && mutation <= 8) {
        auto suffix = mutation == 6   ? "request_phase_expected"
                      : mutation == 7 ? "request_kind_expected"
                                      : "state_constructor_expected";
        auto op = apply(suffix);
        auto index = IntegerType::get(&context, 64, IntegerType::Unsigned);
        op.setParametersAttr(ArrayAttr::get(
            &context,
            {IntegerAttr::get(index, mutation == 6 ? Controller::Enter : 1)}));
      } else if (mutation == 9) {
        auto op = call("resume");
        auto count = input.exchange.state.size();
        // Keep state itself intact, but pass a different fifth continuation
        // coordinate. All header fields share the same native type.
        op.setOperand(1 + count + 4, op.getOperand(1 + Controller::Position));
      } else if (mutation == 10) {
        auto op = call("authenticate");
        op.setOperand(2, op.getOperand(3));
      } else if (mutation == 11) {
        auto op = call("authenticate");
        insertBefore(op, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
          auto commit = input.merkle[0].commit;
          auto values = c.invoke(
              "func.call", scopedDataSignature(commit).getResults(),
              c.scoped({op.getOperand(4), op.getOperand(2)}),
              {b.getNamedAttr("callee", FlatSymbolRefAttr::get(commit)),
               b.getNamedAttr("runtime.site",
                              b.getStringAttr("unbound_root"))});
          op.setOperand(1, values[0]);
        });
      } else if (mutation == 12) {
        auto op = call("authenticate");
        auto field = cast<algebra::FieldType>(
            scopedDataSignature(input.exchange.arms[0].authenticate)
                .getResult(0));
        OpBuilder b(op);
        mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                  "_attack_binding_");
        auto binding = bindings.binding(
            b, op.getLoc(),
            {"vector.get", {b.getStringAttr(field.getDomain())}, ""});
        OperationState replacement(op.getLoc(), "exec.apply");
        replacement.addTypes(op.getResultTypes());
        replacement.addOperands(
            {op.getOperand(0), op.getOperand(4), op.getOperand(3)});
        replacement.addAttribute("binding", binding);
        replacement.addAttribute("parameters", b.getArrayAttr({}));
        replacement.addAttribute("site", op->getAttr("runtime.site"));
        auto *fake = b.create(replacement);
        op->replaceAllUsesWith(fake->getResults());
        op.erase();
      } else if (mutation == 13) {
        auto op = cast<exec::VariantOp>(site(input, prefix + "checked_answer"));
        auto owner = op->getParentOfType<func::FuncOp>();
        auto field = cast<algebra::FieldType>(op.getPayload()[0].getType());
        insertBefore(op, [&](exec::ScopedExecutionBuilder &c, OpBuilder &b) {
          mathematical::RealizationEmitter bindings(unit(*input.candidate),
                                                    "_attack_binding_");
          auto binding = bindings.binding(
              b, op.getLoc(),
              {"vector.get", {b.getStringAttr(field.getDomain())}, ""});
          auto wrong = c.invoke(
              "exec.apply", field,
              c.scoped({owner.getArgument(1), owner.getArgument(3)}),
              {b.getNamedAttr("binding", binding),
               b.getNamedAttr("parameters", b.getArrayAttr({})),
               b.getNamedAttr("site", b.getStringAttr("unbound_answer"))});
          op.getPayloadMutable()[0].set(wrong[0]);
        });
      } else if (mutation == 14) {
        auto op = cast<exec::VariantOp>(site(input, prefix + "checked_answer"));
        op.setAlternative(input.exchange.arms[1].alternative);
      } else if (mutation == 15) {
        auto before = site(input, prefix + "request_phase_expected");
        auto function = before->getParentOfType<func::FuncOp>();
        auto state = function.getArguments().drop_front(5);
        Values args(state);
        append_range(args, state.take_front(5));
        args.push_back(function.getArgument(1));
        insertBefore(before, [&](exec::ScopedExecutionBuilder &c,
                                 OpBuilder &b) {
          auto resume = input.exchange.arms[0].resume;
          c.invoke("func.call", input.exchange.state, c.scoped(args),
                   {b.getNamedAttr("callee", FlatSymbolRefAttr::get(resume)),
                    b.getNamedAttr("runtime.site",
                                   b.getStringAttr("premature_resume"))});
        });
      } else if (mutation == 16 || mutation == 17) {
        auto op = call(mutation == 16 ? "authenticate" : "resume");
        auto expected = mutation == 16 ? input.exchange.arms[0].authenticate
                                       : input.exchange.arms[0].resume;
        auto clone = cast<func::FuncOp>(expected->clone());
        clone.setSymName("_substituted_helper");
        OpBuilder b(&context);
        clone->setAttr("runtime.origin",
                       b.getArrayAttr({b.getStringAttr(clone.getSymName()),
                                       b.getArrayAttr({})}));
        unit(*input.candidate).getBody().front().push_back(clone);
        op.setCalleeAttr(FlatSymbolRefAttr::get(clone));
      } else if (mutation == 18) {
        auto op = cast<exec::MatchOp>(site(input, "authenticate_response"));
        // Scope, response, then the three request coordinates.
        auto values = Values(op->getOperands());
        auto width = (values.size() - 2) / op.getAlternatives().size();
        for (unsigned arm = 0; arm < op.getAlternatives().size(); ++arm)
          std::swap(values[2 + arm * width], values[3 + arm * width]);
        op->setOperands(values);
      } else if (mutation == 19) {
        auto op = apply("request_field_1_equal");
        auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
            op, op.getBindingAttr());
        binding.setContract("index.less");
      } else if (mutation == 20) {
        OpBuilder b(&context);
        input.response.authenticate->setAttr(
            "runtime.origin",
            b.getArrayAttr(
                {b.getStringAttr("different_origin"), b.getArrayAttr({})}));
      } else if (mutation == 21) {
        input.response.resume.setPublic();
      } else if (mutation == 22) {
        input.exchange.arms[0].receiverSlot =
            input.exchange.arms[1].receiverSlot;
      } else {
        input.response.resume->setAttr("data.preconditions",
                                       ArrayAttr::get(&context, {}));
      }
      require(succeeded(verify(*input.candidate)),
              "attack only failed MLIR formation");
      // The whole-candidate admission boundary may reject malformed scoped
      // control before the independent helper grammar is read.
      if (auto context = OracleVerificationContext::read(*input.candidate))
        refused(checkResponse(input));
      else
        refused(context.takeError(), "oracle-verification-source");
    });
  cases.run(
      "capacity and shared budget refusal preserve source and candidate", [&] {
        auto input = emitted(context);
        auto frozenSource = print(*input.source);
        auto frozenPrepared = print(*input.prepared);
        auto frozenCandidate = print(*input.candidate);
        for (unsigned refusal = 0; refusal < 8; ++refusal) {
          auto model = input.exchange;
          auto work = input.work;
          StringRef code = "oracle-response-layout";
          if (refusal == 0) {
            work.operations = 0;
            code = "oracle-response-limit";
          } else if (refusal == 1) {
            work.slots = 0;
            code = "oracle-response-limit";
          } else if (refusal == 2) {
            model.arms.resize(33, model.arms[0]);
            code = "oracle-response-capacity";
          } else if (refusal == 3) {
            model.state.resize(513, model.state[0]);
            code = "oracle-response-capacity";
          } else if (refusal == 4) {
            model.receiverStores.resize(513, model.receiverStores[0]);
            code = "oracle-response-capacity";
          } else if (refusal == 5) {
            model.arms[0].authenticate = model.arms[0].open;
          } else if (refusal == 6) {
            model.request = model.response;
          } else {
            model.arms[0].resume = {};
          }
          auto before = work;
          refuses(emitOracleQueryResponse(*input.candidate, model, work), code);
          require(work.operations == before.operations &&
                      work.slots == before.slots,
                  "refused emission debited work");
          require(print(*input.candidate) == frozenCandidate &&
                      print(*input.source) == frozenSource &&
                      print(*input.prepared) == frozenPrepared,
                  "refused emission mutated an input module");
        }
        auto empty =
            OwningOpRef<ModuleOp>(ModuleOp::create(UnknownLoc::get(&context)));
        refuses(emitOracleQueryResponse(*empty, input.exchange, input.work),
                "oracle-response-source");
        refuses(emitOracleQueryResponse(*input.prepared, input.exchange,
                                        input.work),
                "oracle-response-layout");
        require(print(*input.prepared) == frozenPrepared,
                "foreign-model refusal mutated source");
      });
  cases.run("answer identity and exact model are read independently", [&] {
    auto input = emitted(context);
    auto answer = input.response.answer;
    input.response.answer = input.exchange.response;
    refused(checkResponse(input));
    input.response.answer = answer;
    auto first = input.exchange.arms[0];
    input.exchange.arms[0].kind = 511;
    refused(checkResponse(input));
    input.exchange.arms[0] = first;
    input.exchange.arms[0].root = 511;
    refused(checkResponse(input));
    input.exchange.arms[0] = first;
    checked(checkResponse(input));
  });
  if (argc == 2)
    for (unsigned ordinal = 0; ordinal < 2; ++ordinal)
      cases.run("native boundary client " + Twine(ordinal), [&] {
        auto input = emitted(context);
        auto bundle = client(input, ordinal, registry);
        require(!bundle.empty(), "empty response bundle");
        std::filesystem::create_directories(argv[1]);
        std::ofstream output(
            std::filesystem::path(argv[1]) /
            ("response-" + std::to_string(ordinal) + ".bundle"));
        output << bundle;
        require(bool(output), "response client retention failed");
      });
  return cases.result();
}

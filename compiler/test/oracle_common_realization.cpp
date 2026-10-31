#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/RealizedProtocol.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include <filesystem>
#include <fstream>
#include <set>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace pir = protocol_ir;
namespace {
Error checkCandidate(ModuleOp prepared, const OracleCommonRealization &actual) {
  auto record = serializeOracleRealization(prepared, actual);
  if (!record)
    return record.takeError();
  return checkOracleRealization(prepared, actual.module.get(), *record);
}
void checked(Error error) {
  if (error)
    throw std::runtime_error(toString(std::move(error)));
}
void refused(Error error, StringRef code) {
  require(bool(error), "expected refusal");
  auto message = toString(std::move(error));
  require(namesIdentifier(message, code), "unexpected refusal: " + message);
}
std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text;
}
std::string fixtureText(StringRef name) {
  std::ifstream input(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                      (name.str() + ".mlir"));
  require(bool(input), "missing oracle fixture: " + name.str());
  return std::string((std::istreambuf_iterator<char>(input)), {});
}
void replace(std::string &text, StringRef before, StringRef after) {
  auto at = text.find(before);
  require(at != std::string::npos, "missing dynamic fixture slot");
  text.replace(at, before.size(), after.str());
}
pir::LocalCallOp commonCall(ModuleOp module, StringRef purpose) {
  pir::LocalCallOp found;
  module.walk([&](pir::LocalCallOp call) {
    if (!found && call.getSite().ends_with(purpose))
      found = call;
  });
  require(bool(found), "missing common call: " + purpose.str());
  return found;
}
func::FuncOp helper(ModuleOp module, func::FuncOp original) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto found = dyn_cast_or_null<func::FuncOp>(
      SymbolTable::lookupSymbolIn(unit, original.getSymName()));
  require(bool(found), "fresh candidate lost helper");
  return found;
}
// Follow actual call/region references from each constructed participant. A
// declaration remaining in the shared module says nothing about role work.
std::set<std::string> reachableHelpers(ModuleOp module, StringRef role) {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  SmallVector<Operation *> pending;
  for (auto participant : unit.getBody().front().getOps<pir::ParticipantOp>())
    if (participant.getRole() == role)
      pending.push_back(participant);
  require(pending.size() == 1, "missing constructed participant");
  std::set<std::string> result;
  while (!pending.empty()) {
    auto uses = SymbolTable::getSymbolUses(pending.pop_back_val());
    require(bool(uses), "cannot read actual helper references");
    for (const auto &use : *uses)
      if (auto function = dyn_cast_or_null<func::FuncOp>(
              SymbolTable::lookupSymbolIn(unit, use.getSymbolRef())))
        if (result.insert(function.getSymName().str()).second)
          pending.push_back(function);
  }
  return result;
}
void requestIsolation(Cases &cases, MLIRContext &context) {
  cases.run("native requests exclude verifier evaluator closures", [&] {
    auto source = parseSourceString<ModuleOp>(fixtureText("query-constructors"),
                                              &context);
    require(bool(source), "request isolation source");
    auto unit = cast<pir::ProtocolModuleOp>(source->getBody()->front());
    auto program =
        *unit.getBody().front().getOps<pir::MathematicalOp>().begin();
    auto &body = program.getBody().front();
    OpBuilder b(&context);
    auto random =
        pir::ServiceReferenceType::get(&context, "random.bls12-381.fr/0");
    auto coins = body.addArgument(random, program.getLoc());
    auto first = *body.getOps<pir::OracleQueryOp>().begin();
    b.setInsertionPoint(first);
    auto draw = pir::QueryOp::create(
        b, program.getLoc(), algebra::FieldType::get(&context, "bls12-381.fr"),
        coins, ValueRange{}, "draw", "V", "draw");
    pir::ExchangeOp::create(b, program.getLoc(), draw.getResult(0), "challenge",
                            "V", "P");
    auto returned = cast<pir::MathematicalReturnOp>(body.back());
    b.setInsertionPoint(returned);
    auto ok = algebra::FieldEqualOp::create(b, program.getLoc(), b.getI1Type(),
                                            returned.getOperand(0),
                                            returned.getOperand(0));
    returned->setOperands(ValueRange{ok.getResult()});
    SmallVector<Type> inputs(program.getFunctionType().getInputs());
    inputs.push_back(random);
    program.setFunctionType(b.getFunctionType(inputs, {b.getI1Type()}));
    SmallVector<Attribute> owners(program.getInputRoles().begin(),
                                  program.getInputRoles().end());
    owners[3] = b.getStrArrayAttr({"P", "V"});
    owners.push_back(b.getStrArrayAttr({"V"}));
    program.setInputRolesAttr(b.getArrayAttr(owners));
    program.setOutputRolesAttr(b.getArrayAttr({b.getStrArrayAttr({"V"})}));
    NativeProofPolicy policy;
    policy.entry = "main";
    policy.producer = "P";
    policy.validator = "V";
    policy.suite = "merlin3.bls12-381.fr64be/0";
    policy.services = {5};
    policy.publicInputs = {2, 3, 4};
    policy.draws = {{"draw", "challenge"}};
    OracleRealizationPolicy oracle;
    oracle.authentication = OracleAuthentication::PerQuery;
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "request isolation preparation");
    auto roots = take(resolveOracleRealizationSelection(*prepared, oracle));
    for (auto [i, root] : enumerate(roots))
      root.realization = {
          i == 0 ? "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"
                 : "rows.merkle-keccak256.koala-bear/0",
          OracleLeafGrouping::Individual, OracleLeafOrder::Natural};
    oracle.roots = std::move(roots);
    auto built = take(constructNativeProof(*source, policy, {}, oracle));
    checked(checkNativeProof(*source, *built.module, policy, {}, oracle));
    auto producer = reachableHelpers(*built.module, "P");
    auto verifier = reachableHelpers(*built.module, "V");
    auto record = take(json::parse(built.realization->realizationRecord()));
    auto &entry =
        *record.getAsObject()->getArray("entries")->front().getAsObject();
    for (auto &row : *entry.getArray("batches")) {
      auto &batch = *row.getAsObject()->getObject("body");
      auto collect = batch.getString("collect")->str();
      require(producer.count(collect) && verifier.count(collect),
              "actual collect was not reconstructed");
      for (StringRef field : {"check_available", "replay", "finish"}) {
        auto name = batch.getString(field)->str();
        require(!producer.count(name) && verifier.count(name),
                "verifier-only evaluator helper is a producer dependency: " +
                    name);
      }
    }
    for (auto &row : *entry.getArray("remotes")) {
      auto &window = *row.getAsObject()->getObject("window");
      for (StringRef field : {"replay", "finish"}) {
        auto name = window.getString(field)->str();
        require(!producer.count(name) && verifier.count(name),
                "root evaluator remains a producer dependency: " + name);
      }
      auto authenticate = row.getAsObject()
                              ->getObject("packet")
                              ->getString("authenticate")
                              ->str();
      require(!producer.count(authenticate) && verifier.count(authenticate),
              "packet authentication remains a producer request dependency");
    }
  });
}
// These are whole-candidate checks: every mutation is read from a fresh parsed
// candidate under the frozen original, without reusing producer-owned handles.
void dynamicWindows(Cases &cases, MLIRContext &context) {
  constexpr StringLiteral scheme =
      "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0";
  for (StringRef mode :
       {"paired", "individual", "reversed", "unknown-first", "unknown-later",
        "guard", "unused-answer-call", "per-query"}) {
    auto text = fixtureText("query-blocks");
    if (mode == "unknown-first")
      replace(text, "\"protocol.oracle_query\"(%a,%zero)",
              "\"protocol.oracle_query\"(%a,%position)");
    if (mode == "unknown-later")
      replace(text, "\"protocol.oracle_query\"(%a,%four)",
              "\"protocol.oracle_query\"(%a,%position)");
    if (mode == "guard")
      replace(text, "  %y = ",
              "  \"protocol.guard\"(%allow) "
              "{owner=\"V\",site=\"early_barrier\"} : (i1)->()\n  %y = ");
    if (mode == "unused-answer-call") {
      replace(text, " \"protocol.func\"()", R"mlir(
 func.func private @choose_position(%answer:!F,%position:ui64)->ui64 {
  return %position : ui64
 }
 "protocol.func"())mlir");
      replace(text, "  %y = ",
              "  %nextPosition = func.call @choose_position(%x,%position) : "
              "(!F,ui64)->ui64\n  %y = ");
      replace(text, "\"protocol.oracle_query\"(%a,%four)",
              "\"protocol.oracle_query\"(%a,%nextPosition)");
    }
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source), "dynamic source did not parse");
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "dynamic source did not prepare");
    OracleRealizationPolicy policy;
    policy.authentication = mode == "per-query"
                                ? OracleAuthentication::PerQuery
                                : OracleAuthentication::AtomicBlocks;
    policy.roots = take(resolveOracleRealizationSelection(*prepared, policy));
    for (auto &root : std::get<std::vector<OracleRootSelection>>(policy.roots))
      root.realization = {scheme.str(),
                          mode == "individual"
                              ? OracleLeafGrouping::Individual
                              : OracleLeafGrouping::AntipodalPairs,
                          mode == "reversed" ? OracleLeafOrder::BitReversed
                                             : OracleLeafOrder::Natural};
    auto candidate = take(emitOracleRealization(*prepared, policy));
    auto record =
        take(serializeOracleRealization(*prepared, candidate, policy));
    auto candidateText = print(*candidate.module);
    require(candidate.entries.size() == 1, "dynamic entry inventory changed");
    const auto &entry = candidate.entries.front();
    bool barrier = mode == "guard";
    unsigned count = mode == "per-query" ? 5 : barrier ? 3 : 2;
    uint64_t capacity = mode == "per-query" ? 1 : barrier ? 3 : 4;
    cases.run("dynamic " + mode + " source order and fresh record", [&] {
      auto fresh = parseSourceString<ModuleOp>(candidateText, &context);
      require(bool(fresh), "dynamic candidate did not parse");
      checked(checkOracleRealization(*prepared, *fresh, record, policy));
      require(entry.remotes.size() == 1 && entry.batches.size() == count &&
                  entry.remotes.front().window.capacity == capacity,
              "wrong dynamic inventory or global capacity");
      auto encoded = take(json::parse(record));
      auto &row =
          *encoded.getAsObject()->getArray("entries")->front().getAsObject();
      auto &blocks = *row.getArray("query_blocks");
      require(blocks.size() == count, "wrong dynamic barrier partition");
      unsigned occurrences = 0;
      for (auto [block, batch] : zip(blocks, entry.batches)) {
        auto &fields = *block.getAsObject();
        auto &paths = *fields.getArray("queries");
        require(fields.size() == 2 && !fields.get("request_groups") &&
                    fields.get("packet_capacity") &&
                    fields.get("packet_capacity")->getAsUINT64() == capacity &&
                    paths.size() == batch.remotes.size(),
                "dynamic row lost capacity or logical occurrence coverage");
        for (unsigned remote : batch.remotes)
          require(remote == 0, "repeated roots lost their remote association");
        occurrences += paths.size();
      }
      require(occurrences == 5, "repeated or unused source query disappeared");
    });
    if (mode != "paired")
      continue;
    auto mutate = [&](StringRef name, llvm::function_ref<void(ModuleOp)> change,
                      StringRef code = "oracle-common-body") {
      cases.run("dynamic refuses " + name, [&] {
        auto fresh = parseSourceString<ModuleOp>(candidateText, &context);
        require(bool(fresh), "mutation candidate did not parse");
        change(*fresh);
        require(succeeded(verify(*fresh)), "dynamic mutation lost formation");
        refused(checkOracleRealization(*prepared, *fresh, record, policy),
                code);
      });
    };
    auto changeRecord = [&](StringRef name,
                            llvm::function_ref<void(json::Object &)> change,
                            StringRef code = "oracle-realization-record") {
      cases.run("dynamic record refuses " + name, [&] {
        auto encoded = take(json::parse(record));
        auto &row =
            *encoded.getAsObject()->getArray("entries")->front().getAsObject();
        change(row);
        std::string changed;
        raw_string_ostream(changed) << encoded;
        refused(checkOracleRealization(*prepared, *candidate.module, changed,
                                       policy),
                code);
      });
    };
    changeRecord("derived capacity", [&](auto &row) {
      (*row.getArray("query_blocks")
            ->front()
            .getAsObject())["packet_capacity"] = 1;
    });
    changeRecord("old physical group schema", [&](auto &row) {
      auto &block = *row.getArray("query_blocks")->front().getAsObject();
      block.erase("packet_capacity");
      block["request_groups"] = json::Array{0, 0, 0, 1};
    });
    changeRecord(
        "window capacity",
        [&](auto &row) {
          (*row.getArray("remotes")->front().getAsObject()->getObject(
              "window"))["capacity"] = 1;
        },
        "oracle-common-body");
    changeRecord(
        "remote controller substitution",
        [&](auto &row) {
          auto &remote = *row.getArray("remotes")->front().getAsObject();
          remote["receiver"] = *remote.get("holder");
        },
        "oracle-common-body");
    changeRecord(
        "missing remote", [&](auto &row) { row.getArray("remotes")->clear(); },
        "oracle-common-body");
    changeRecord(
        "missing batch",
        [&](auto &row) { row.getArray("batches")->pop_back(); },
        "oracle-common-body");
    changeRecord(
        "changed root index",
        [&](auto &row) {
          (*row.getArray("batches")->front().getAsObject()->getArray(
              "remotes"))[0] = 1;
        },
        "oracle-common-body");
    changeRecord(
        "lost repeated root",
        [&](auto &row) {
          row.getArray("batches")
              ->front()
              .getAsObject()
              ->getArray("remotes")
              ->pop_back();
        },
        "oracle-common-body");
    changeRecord("reordered source paths", [&](auto &row) {
      auto &paths = *row.getArray("query_blocks")
                         ->front()
                         .getAsObject()
                         ->getArray("queries");
      std::swap(paths[0], paths[1]);
    });
    changeRecord("helper model override", [&](auto &row) {
      (*row.getArray("remotes")->front().getAsObject())["exchange"] =
          json::Object{};
    });
    changeRecord("missing fresh helper", [&](auto &row) {
      (*row.getArray("batches")->front().getAsObject()->getObject(
          "body"))["collect"] = "absent";
    });
    changeRecord("old batch helper inventory", [&](auto &row) {
      row.getArray("batches")->front().getAsObject()->getObject("body")->erase(
          "check_available");
    });
    changeRecord("missing availability helper", [&](auto &row) {
      (*row.getArray("batches")->front().getAsObject()->getObject(
          "body"))["check_available"] = "absent";
    });
    mutate("missing actual availability check", [&](ModuleOp fresh) {
      commonCall(fresh, "query_check_available")->erase();
    });
    mutate("availability check after grouping", [&](ModuleOp fresh) {
      commonCall(fresh, "query_check_available")
          ->moveAfter(commonCall(fresh, "opening_group"));
    });
    mutate("availability check after exchange", [&](ModuleOp fresh) {
      pir::ExchangeOp exchange;
      fresh.walk([&](pir::ExchangeOp op) {
        if (!exchange && op.getSite().ends_with("_opening_request"))
          exchange = op;
      });
      require(bool(exchange), "missing request exchange");
      commonCall(fresh, "query_check_available")->moveAfter(exchange);
    });
    mutate(
        "substituted check beside unused correct helper", [&](ModuleOp fresh) {
          auto good = helper(fresh, entry.batches.front().body.checkAvailable);
          auto bad = cast<func::FuncOp>(good->clone());
          bad.setSymName("substituted_availability_check");
          Builder builder(&context);
          bad->setAttr(
              "runtime.origin",
              builder.getArrayAttr({builder.getStringAttr(bad.getSymName()),
                                    builder.getArrayAttr({})}));
          good->getBlock()->push_back(bad);
          commonCall(fresh, "query_check_available")
              ->setAttr("callee", FlatSymbolRefAttr::get(bad));
        });
    mutate("availability request substitution", [&](ModuleOp fresh) {
      auto check = commonCall(fresh, "query_check_available");
      auto group = commonCall(fresh, "opening_group");
      check->moveAfter(group);
      check.getInputsMutable()[0].set(group.getResult(0));
    });
    mutate("availability evaluator root substitution", [&](ModuleOp fresh) {
      auto check = commonCall(fresh, "query_check_available");
      unsigned state =
          entry.controllers[entry.remotes.front().receiver].body.state.size();
      check.getInputsMutable()[1].set(check.getInputs()[1 + state]);
    });
    mutate("availability store substitution", [&](ModuleOp fresh) {
      auto check = commonCall(fresh, "query_check_available");
      auto original = cast<BlockArgument>(check.getInputs().back());
      auto repeat = check->getParentOfType<pir::RepeatOp>();
      auto incoming = repeat.getInputs()[original.getArgNumber()];
      Value stale;
      for (auto &op : *repeat->getBlock()) {
        if (&op == repeat.getOperation())
          break;
        for (Value value : op.getResults())
          if (!stale && value != incoming &&
              value.getType() == incoming.getType())
            stale = value;
      }
      require(bool(stale), "missing distinct immutable store");
      auto &body = repeat.getBody().front();
      body.addArgument(stale.getType(), check.getLoc());
      repeat->insertOperands(repeat->getNumOperands(), stale);
      check.getInputsMutable()[check.getInputs().size() - 1].set(
          body.getArguments().back());
    });
    mutate("wrong source position", [&](ModuleOp fresh) {
      auto call = commonCall(fresh, "query_initialize");
      require(call.getInputs().size() == 2 &&
                  call.getInputs()[1].getDefiningOp(),
              "missing source position");
      auto original = call.getInputs()[1];
      Value alternative;
      for (auto &operation : *call->getBlock()) {
        if (&operation == call.getOperation())
          break;
        for (Value value : operation.getResults())
          if (value != original && value.getType() == original.getType())
            alternative = value;
      }
      require(bool(alternative), "missing another actual source position");
      call.getInputsMutable()[1].set(alternative);
    });
    mutate("another actual source anchor", [&](ModuleOp fresh) {
      SmallVector<pir::LocalCallOp> initializers;
      fresh.walk([&](pir::LocalCallOp call) {
        if (call.getSite().ends_with("_query_initialize"))
          initializers.push_back(call);
      });
      require(initializers.size() == 5 && initializers[0].getInputs()[0] !=
                                              initializers[3].getInputs()[0],
              "missing distinct source anchors");
      initializers[0].getInputsMutable()[0].set(initializers[3].getInputs()[0]);
    });
    mutate("reordered collected root states", [&](ModuleOp fresh) {
      auto call = commonCall(fresh, "query_collect");
      unsigned width = entry.remotes.front().demand.state.size();
      SmallVector<Value> first(call.getInputs().take_front(width));
      for (unsigned i = 0; i < width; ++i) {
        call.getInputsMutable()[i].set(call.getInputs()[width + i]);
        call.getInputsMutable()[width + i].set(first[i]);
      }
    });
    mutate("stale immutable store", [&](ModuleOp fresh) {
      auto call = commonCall(fresh, "query_collect");
      auto repeat = call->getParentOfType<pir::RepeatOp>();
      require(bool(repeat), "collect lost structural rounds");
      // The captured stores follow iteration and carried demand/evaluator
      // states. Substitute a well-typed store from before its allocation.
      auto original = call.getInputs().back();
      auto argument = cast<BlockArgument>(original);
      auto incoming = repeat.getInputs()[argument.getArgNumber()];
      Value stale;
      for (auto &operation : *repeat->getBlock()) {
        if (&operation == repeat.getOperation())
          break;
        for (Value value : operation.getResults())
          if (!stale && value != incoming &&
              value.getType() == incoming.getType())
            stale = value;
      }
      require(bool(stale), "missing pre-allocation immutable store");
      repeat.getInputsMutable()[argument.getArgNumber()].set(stale);
    });
    mutate("request substitution", [&](ModuleOp fresh) {
      auto group = commonCall(fresh, "opening_group");
      auto authenticate = commonCall(fresh, "opening_authenticate");
      authenticate.getInputsMutable()[0].set(group->getResult(0));
    });
    mutate("root end-range substitution", [&](ModuleOp fresh) {
      auto replay = commonCall(fresh, "query_replay");
      unsigned ends = entry.batches.front().body.evaluatorState.size() + 2;
      replay.getInputsMutable()[ends + 1].set(replay.getInputs()[ends]);
    });
    mutate(
        "correct unused helper beside a bad actual call", [&](ModuleOp fresh) {
          auto group = commonCall(fresh, "opening_group");
          auto good = helper(fresh, entry.remotes.front().packet.group);
          auto bad = cast<func::FuncOp>(good->clone());
          bad.setSymName("bad_actual_group");
          Builder builder(&context);
          bad->setAttr(
              "runtime.origin",
              builder.getArrayAttr({builder.getStringAttr("bad_actual_group"),
                                    builder.getArrayAttr({})}));
          good->getBlock()->push_back(bad);
          exec::ApplyOp lower;
          bad.walk([&](exec::ApplyOp op) {
            if (op.getSite() == "packet_group_lower")
              lower = op;
          });
          require(bool(lower), "missing actual packet grouping lower bound");
          // Skip the first logical request in the forged implementation. The
          // original recorded helper remains present and independently
          // checkable.
          lower.setParametersAttr(builder.getArrayAttr({builder.getIntegerAttr(
              IntegerType::get(&context, 64, IntegerType::Unsigned), 1)}));
          group->setAttr("callee", FlatSymbolRefAttr::get(bad));
        });
    mutate(
        "logical authentication replaced by physical grouping",
        [&](ModuleOp fresh) {
          auto packet =
              helper(fresh, entry.remotes.front().packet.authenticate);
          exec::ApplyOp length;
          packet.walk([&](exec::ApplyOp op) {
            if (op.getSite() == "packet_auth_logical_length")
              length = op;
          });
          require(bool(length), "missing logical authentication length");
          length.getInputsMutable()[0].set(packet.getArgument(2));
        },
        "oracle-packet-body");
    mutate(
        "physical key drops actual instance identity",
        [&](ModuleOp fresh) {
          exec::VariantOp key;
          fresh.walk([&](exec::VariantOp op) {
            if (!key && op.getSite().starts_with("packet_constructor_") &&
                op.getSite().ends_with("_key"))
              key = op;
          });
          require(bool(key) && key.getPayload().size() == 3,
                  "missing physical opening key");
          key.getPayloadMutable()[1].set(key.getPayload()[0]);
        },
        "oracle-packet-body");
    mutate("authentication after a replay call", [&](ModuleOp fresh) {
      auto replay = commonCall(fresh, "query_replay");
      auto authenticate = commonCall(fresh, "opening_authenticate");
      auto *early = authenticate->clone();
      authenticate->getBlock()->getOperations().insert(
          authenticate->getIterator(), early);
      auto partial = cast<pir::LocalCallOp>(early);
      partial.setSite("partial_authentication");
      // A first call authenticates only physical requests. Replay takes those
      // answers while the actual complete logical authentication runs later.
      partial.getInputsMutable()[0].set(authenticate.getInputs()[1]);
      unsigned answer = entry.batches.front().body.evaluatorState.size() + 1;
      replay.getInputsMutable()[answer].set(partial->getResult(0));
      authenticate->moveAfter(replay);
    });
    cases.run("dynamic refuses reordered frozen source queries", [&] {
      auto changed = parseSourceString<ModuleOp>(print(*prepared), &context);
      SmallVector<pir::OracleQueryOp> queries;
      changed->walk(
          [&](pir::OracleQueryOp query) { queries.push_back(query); });
      require(queries.size() == 5, "missing ordered source queries");
      queries[1]->moveBefore(queries[0]);
      require(succeeded(verify(*changed)), "reordered source lost formation");
      refused(
          checkOracleRealization(*changed, *candidate.module, record, policy),
          "oracle-common-body");
    });
  }
  for (bool sameKind : {false, true})
    cases.run(
        sameKind ? "dynamic recurrent queries keep constructor identity"
                 : "dynamic recurrent mixed kinds retain logical answers",
        [&] {
          auto text = fixtureText("query-constructors");
          if (sameKind) {
            replace(text, "!BF = !algebra.field<\"koala-bear\">",
                    "!BF = !algebra.field<\"koala-bear.ext4-binomial3\">");
            replace(
                text, "!BD = !algebra.field_vector<\"koala-bear\">",
                "!BD = !algebra.field_vector<\"koala-bear.ext4-binomial3\">");
          }
          replace(text, "   \"protocol.return\"(%answer)",
                  "   %unusedRoot = \"protocol.oracle_query\"(%b,%mapped) "
                  "{owner=\"V\",site=\"sibling_root\"} : (!B,ui64)->!BF\n"
                  "   \"protocol.return\"(%answer)");
          auto source = parseSourceString<ModuleOp>(text, &context);
          require(bool(source), "virtual dynamic source did not parse");
          auto prepared = mathematical::prepareProtocol(*source, false);
          require(bool(prepared), "virtual dynamic source did not prepare");
          OracleRealizationPolicy policy;
          policy.authentication = OracleAuthentication::AtomicBlocks;
          policy.roots =
              take(resolveOracleRealizationSelection(*prepared, policy));
          auto &roots =
              std::get<std::vector<OracleRootSelection>>(policy.roots);
          require(roots.size() == 2, "wrong mixed constructor inventory");
          for (auto [ordinal, root] : enumerate(roots))
            root.realization = {
                ordinal == 0 || sameKind ? scheme.str()
                                         : "rows.merkle-keccak256.koala-bear/0",
                OracleLeafGrouping::AntipodalPairs, OracleLeafOrder::Natural};
          auto candidate = take(emitOracleRealization(*prepared, policy));
          auto record =
              take(serializeOracleRealization(*prepared, candidate, policy));
          auto fresh =
              parseSourceString<ModuleOp>(print(*candidate.module), &context);
          require(bool(fresh), "mixed dynamic candidate did not parse");
          checked(checkOracleRealization(*prepared, *fresh, record, policy));
          const auto &entry = candidate.entries.front();
          require(entry.remotes.size() == (sameKind ? 1u : 2u) &&
                      entry.batches.size() == 1 &&
                      entry.batches.front().remotes ==
                          std::vector<unsigned>({0, sameKind ? 0u : 1u}) &&
                      entry.remotes.front().window.capacity > 1,
                  "recurrent expansion did not use the bounded dynamic route");
          if (!sameKind) {
            auto encoded = take(json::parse(record));
            auto &roots = *encoded.getAsObject()
                               ->getArray("entries")
                               ->front()
                               .getAsObject()
                               ->getArray("batches")
                               ->front()
                               .getAsObject()
                               ->getArray("remotes");
            std::swap(roots[0], roots[1]);
            std::string changed;
            raw_string_ostream(changed) << encoded;
            refused(checkOracleRealization(*prepared, *fresh, changed, policy),
                    "oracle-common-body");
          }
          exec::VariantOp request;
          fresh->walk([&](exec::VariantOp op) {
            if (!request && op.getSite() == "window_request")
              request = op;
          });
          require(bool(request) && request.getPayload().size() == 3,
                  "virtual discovery lost retained request coordinates");
          request.getPayloadMutable()[1].set(request.getPayload()[2]);
          require(succeeded(verify(*fresh)),
                  "request coordinate mutation lost formation");
          refused(checkOracleRealization(*prepared, *fresh, record, policy),
                  "oracle-window-body");
        });
  cases.run("dynamic zero-leaf batches retain actual evaluator finish", [&] {
    auto source = parseSourceString<ModuleOp>(R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">,8:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
module { "protocol.module"() ({
 relation.declare @empty_ok {kind="external",key="test/empty",revision="0",
  signature=(!D,!F)->i1,purposes=["witness","parameter"]}
 "protocol.oracle"() ({
 ^entry(%a:!H,%constant:!F,%position:ui64):
  "protocol.oracle_yield"(%constant) : (!F)->()
 }) {sym_name="empty",function_type=(!H,!F,ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@empty_ok} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%constant:!F,%position:ui64):
  %rows = "data.index"() {value=8:ui64} : ()->ui64
  %base = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="base"} : (!D,ui64)->!H
  %empty = "protocol.oracle_virtual"(%base,%constant) {callee=@empty,holder="P",receivers=["V"]} : (!H,!F)->!H
  %answer = "protocol.oracle_query"(%empty,%position) {owner="V",site="read"} : (!H,ui64)->!F
  "protocol.return"(%answer) : (!F)->()
 }) {sym_name="main",function_type=(!D,!F,ui64)->!F,roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir",
                                              &context);
    require(bool(source), "empty virtual source did not parse");
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "empty virtual source did not prepare");
    OracleRealizationPolicy policy;
    policy.authentication = OracleAuthentication::AtomicBlocks;
    policy.roots = take(resolveOracleRealizationSelection(*prepared, policy));
    for (auto &root : std::get<std::vector<OracleRootSelection>>(policy.roots))
      root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                          OracleLeafOrder::Natural};
    auto candidate = take(emitOracleRealization(*prepared, policy));
    auto record =
        take(serializeOracleRealization(*prepared, candidate, policy));
    auto fresh =
        parseSourceString<ModuleOp>(print(*candidate.module), &context);
    require(bool(fresh), "empty virtual candidate did not parse");
    checked(checkOracleRealization(*prepared, *fresh, record, policy));
    const auto &entry = candidate.entries.front();
    require(entry.remotes.size() == 1 && entry.batches.size() == 1 &&
                entry.remotes.front().window.capacity == 1,
            "zero leaves lost the positive global packet capacity");
    auto finish = commonCall(*fresh, "query_finish");
    require(finish.getCallee() ==
                func::FuncOp(entry.batches.front().body.finish).getSymName(),
            "zero-leaf batch did not use actual checked finish");
    auto original = finish.getInputs()[0];
    require(finish.getInputs().size() > 1 &&
                original.getType() == finish.getInputs()[1].getType(),
            "missing zero-leaf evaluator coordinates");
    finish.getInputsMutable()[0].set(finish.getInputs()[1]);
    require(succeeded(verify(*fresh)),
            "finish coordinate mutation lost formation");
    refused(checkOracleRealization(*prepared, *fresh, record, policy),
            "oracle-common-body");
  });
  requestIsolation(cases, context);
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    return success();
  });
  Cases cases;
  bool compile = argc > 1 && (argc < 3 || StringRef(argv[2]) != "checks");
  bool mutations = argc < 3 || StringRef(argv[2]) != "compile";
  bool selectedFixture = false;
  for (StringRef fixture :
       {"common-recurrence", "common-holders", "common-input", "common-shape",
        "common-contents", "common-views", "common-entries", "common-return",
        "common-empty", "common-clauses"}) {
    if (argc > 3 && fixture != argv[3])
      continue;
    selectedFixture = true;
    std::ifstream in(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                     (fixture.str() + ".mlir"));
    std::string text((std::istreambuf_iterator<char>(in)), {});
    auto source =
        parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
    require(bool(source) && succeeded(verify(*source)),
            "source: " + diagnostics);
    auto prepared = mathematical::prepareProtocol(*source, false);
    require(bool(prepared), "prepare: " + diagnostics);
    auto frozen = print(*prepared);
    auto emitted = emitOracleRealization(*prepared);
    require(bool(emitted),
            "emission: " +
                (emitted ? std::string() : toString(emitted.takeError())) +
                "\n" + diagnostics);
    auto candidate = std::move(*emitted);
    unsigned expectedEntries =
        fixture == "common-return"                                   ? 3
        : (fixture == "common-entries" || fixture == "common-empty") ? 2
                                                                     : 1;
    require(candidate.entries.size() == expectedEntries,
            "wrong oracle entry inventory");
    auto mainEntry = find_if(candidate.entries, [](const auto &item) {
      return item.entry == "main";
    });
    require(mainEntry != candidate.entries.end(), "missing main entry");
    auto &entry = *mainEntry;
    cases.run(fixture + " actual common body", [&] {
      checked(checkCandidate(*prepared, candidate));
      require(print(*prepared) == frozen,
              "emission or reading changed original");
      bool leftover = false;
      candidate.module->walk([&](Operation *op) {
        leftover |=
            op->getName().getStringRef().starts_with("protocol.oracle_") ||
            isa<pir::OracleDefinitionOp>(op);
        for (Type type : op->getOperandTypes())
          leftover |= isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
        for (Type type : op->getResultTypes())
          leftover |= isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
      });
      require(!leftover, "logical oracle survived common realization");
    });
    auto unit =
        cast<pir::ProtocolModuleOp>(candidate.module->getBody()->front());
    auto program =
        cast<pir::MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
    if (mutations) {
      cases.run(fixture + " independent record and fresh candidate read", [&] {
        auto record = take(serializeOracleRealization(*prepared, candidate));
        auto copy = parseSourceString<ModuleOp>(print(*candidate.module),
                                                ParserConfig(&context, false));
        require(bool(copy), "candidate text did not parse");
        checked(checkOracleRealization(*prepared, *copy, record));
        require(record ==
                    take(serializeOracleRealization(*prepared, candidate)),
                "record is not deterministic");
      });
    }
    if (mutations && fixture == "common-input") {
      auto record = take(serializeOracleRealization(*prepared, candidate));
      auto changed = [&](StringRef name,
                         llvm::function_ref<void(json::Object &)> change,
                         StringRef refusal = "oracle-realization-record") {
        cases.run("record refuses " + name, [&] {
          auto parsed = take(json::parse(record));
          change(*parsed.getAsObject());
          std::string text;
          raw_string_ostream(text) << parsed;
          refused(checkOracleRealization(*prepared, *candidate.module, text),
                  refusal);
        });
      };
      changed("missing contract", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        entry.getObject("contracts")->getArray("clauses")->pop_back();
      });
      changed("contract component port", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[0]
                            .getAsObject();
        auto &operand = *(*clause.getObject("subject")->getArray("operands"))[0]
                             .getAsObject();
        (*operand.getObject("component"))["port"] = 1;
      });
      changed("contract relation", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[0]
                            .getAsObject();
        (*clause.getObject("subject"))["relation"] = "other";
      });
      changed("continuation residual direction", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &clause = *(*entry.getObject("contracts")->getArray("clauses"))[2]
                            .getAsObject();
        auto &operand =
            *(*clause.getObject("residual")->getArray("operands"))[0]
                 .getAsObject();
        (*operand.getObject("component"))["direction"] = "input";
      });
      changed("invented statement selection", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        entry.getObject("contracts")
            ->getArray("statements")
            ->push_back(json::Object{{"operation", 0}, {"target", 0}});
      });
      changed("unknown root field",
              [&](auto &value) { value["extra"] = true; });
      changed("other version", [&](auto &value) {
        value["format"] = "zkc.oracle-realization/1";
      });
      changed("unknown envelope field",
              [&](auto &value) { value["mode"] = "merkle"; });
      changed("unknown entry field", [&](auto &value) {
        (*value.getArray("entries"))[0].getAsObject()->insert({"extra", true});
      });
      changed("duplicate type", [&](auto &value) {
        auto &types = *value.getArray("types");
        types.push_back(types.front());
      });
      changed("unused type", [&](auto &value) {
        value.getArray("types")->push_back(
            json::Array{"apply", "bytes", json::Array{}});
      });
      changed("old printed type schema", [&](auto &value) {
        (*value.getArray("types"))[0] = "field:koala-bear";
      });
      changed("old type-specific array", [&](auto &value) {
        (*value.getArray("types"))[0] = json::Array{"field", "koala-bear"};
      });
      changed("wrong nominal argument kind", [&](auto &value) {
        (*value.getArray("types"))[0] = json::Array{
            "apply", "field",
            json::Array{json::Array{"domain", "Group", "koala-bear"}}};
      });
      changed("service is not ordinary type table data", [&](auto &value) {
        (*value.getArray("types"))[0] =
            json::Array{"service", "random.koala-bear/0"};
      });
      changed("oracle is not ordinary type table data", [&](auto &value) {
        (*value.getArray("types"))[0] = json::Array{
            "oracle", "table",
            json::Array{json::Array{
                "type", json::Array{"apply", "bool", json::Array{}}}}};
      });
      changed(
          "reordered type inventory",
          [&](auto &value) {
            auto &types = *value.getArray("types");
            require(types.size() > 1, "missing distinct type references");
            std::swap(types[0], types[1]);
          },
          "oracle-common-body");
      changed("missing helper", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &controller = *(*entry.getArray("controllers"))[0].getAsObject();
        (*controller.getObject("body"))["initialize"] =
            "not_a_generated_helper";
      });
      changed("foreign type index", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        auto &controller = *(*entry.getArray("controllers"))[0].getAsObject();
        (*controller.getObject("body")->getArray("state"))[0] = 999999;
      });
      changed("changed source constructor", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*(*entry.getArray("constructors"))[0]
              .getAsObject())["maximum_instances"] = 2;
      });
      changed("changed occurrence path", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*(*entry.getArray("occurrences"))[0].getAsObject())["path"] =
            json::Array{999};
      });
      changed("changed output role", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*entry.getObject("interface"))["output_roles"] =
            json::Array{json::Array{"P"}};
      });
      auto inputPair = [&](json::Object &value) -> json::Object & {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        return *(*entry.getObject("logical_interface")->getArray("inputs"))[0]
                    .getAsObject();
      };
      changed("holder and receiver data ports swapped", [&](auto &value) {
        auto &pair = inputPair(value);
        std::swap(*pair.get("data"), *pair.get("anchor"));
      });
      changed("logical holder changed",
              [&](auto &value) { inputPair(value)["holder"] = "V"; });
      changed("logical receiver changed", [&](auto &value) {
        inputPair(value)["receivers"] = json::Array{"P"};
      });
      changed("logical input association dropped", [&](auto &value) {
        auto &entry = *(*value.getArray("entries"))[0].getAsObject();
        (*entry.getObject("logical_interface"))["inputs"] = json::Array{};
      });
      changed("declaration order", [&](auto &value) {
        auto &declarations = *value.getArray("declarations");
        std::swap(declarations[0], declarations[1]);
      });
      cases.run("record producer enforces its reader lexical depth", [&] {
        auto &state = entry.controllers.front().body.state;
        auto saved = state;
        auto restore = llvm::scope_exit([&] { state = std::move(saved); });
        Type nested = IntegerType::get(&context, 1);
        for (unsigned depth = 0; depth != 22; ++depth)
          nested = data::SequenceType::get(&context, nested);
        state.push_back(nested);
        refuses(serializeOracleRealization(*prepared, candidate),
                "oracle-realization-record-limit");
      });
      cases.run("record refuses an oversized type table", [&] {
        auto parsed = take(json::parse(record));
        auto &types = *parsed.getAsObject()->getArray("types");
        while (types.size() <= 4096)
          types.push_back("ui64");
        std::string text;
        raw_string_ostream(text) << parsed;
        refused(checkOracleRealization(*prepared, *candidate.module, text),
                "oracle-realization-record-limit");
      });
      cases.run("record refuses duplicate decoded keys", [&] {
        std::string duplicate = record;
        duplicate.insert(1, "\"format\":\"zkc.oracle-realization/0\",");
        refused(checkOracleRealization(*prepared, *candidate.module, duplicate),
                "oracle-realization-record");
      });
      cases.run("record binds generated binding names", [&] {
        runtime::BindingOp binding;
        unit.walk([&](runtime::BindingOp op) {
          if (!binding && op.getSymName().starts_with("_oracle_"))
            binding = op;
        });
        require(bool(binding), "missing generated binding");
        auto original = binding.getSymNameAttr();
        auto replacement = StringAttr::get(&context, "changed_binding");
        require(succeeded(SymbolTable::replaceAllSymbolUses(binding,
                                                            replacement, unit)),
                "could not rename binding uses");
        binding->setAttr("sym_name", replacement);
        auto restore = llvm::scope_exit([&] {
          (void)SymbolTable::replaceAllSymbolUses(binding, original, unit);
          binding->setAttr("sym_name", original);
        });
        require(succeeded(verify(*candidate.module)),
                "renamed binding is malformed");
        refused(checkOracleRealization(*prepared, *candidate.module, record),
                "oracle-realization-record");
      });
    }
    if (mutations && fixture == "common-empty") {
      cases.run("uninhabited handle uses retain a refusing controller", [&] {
        const auto &selected = candidate.entries[1];
        require(selected.entry == "at" && selected.controllers.size() == 1 &&
                    selected.allocators.empty(),
                "uninhabited entry layout");
        require(selected.controllers[0].body.constructors.empty() &&
                    selected.controllers[0].body.stores.empty(),
                "manufactured anchor or store");
        exec::RejectOp rejection;
        unit.walk([&](exec::RejectOp op) {
          if (!rejection && op.getSite() == "no_constructor")
            rejection = op;
        });
        require(bool(rejection), "missing uninhabited dispatch refusal");
        auto reason = rejection.getReasonAttr();
        auto restore =
            llvm::scope_exit([&] { rejection.setReasonAttr(reason); });
        rejection.setReason("abort");
        require(succeeded(verify(*candidate.module)),
                "changed cause malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("empty sequence has no allocated anchor or controller", [&] {
        require(entry.controllers.empty() && entry.allocators.empty() &&
                    entry.locals.empty(),
                "invented an anchor for an empty collection");
      });
      cases.run("empty length cannot become an unrelated input", [&] {
        auto returned =
            cast<pir::MathematicalReturnOp>(program.getBody().front().back());
        Value original = returned->getOperand(0);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(0, original); });
        returned->setOperand(0, program.getBody().front().getArgument(0));
        require(succeeded(verify(*candidate.module)),
                "empty mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-return") {
      cases.run(
          "returned logical pairs use distinct actual holder leaves", [&] {
            auto record = take(json::parse(
                take(serializeOracleRealization(*prepared, candidate))));
            auto &entries = *record.getAsObject()->getArray("entries");
            auto found = find_if(entries, [](const auto &item) {
              return item.getAsObject()->getString("entry") == "main";
            });
            require(found != entries.end(), "missing main record");
            auto &outputs = *found->getAsObject()
                                 ->getObject("logical_interface")
                                 ->getArray("outputs");
            require(outputs.size() == 3, "wrong returned logical inventory");
            for (unsigned i = 0; i < outputs.size(); ++i) {
              auto &pair = *outputs[i].getAsObject();
              require(pair.getInteger("data") == 2 * i &&
                          pair.getInteger("anchor") == 2 * i + 1 &&
                          pair.getString("holder") == "P",
                      "logical aliases lost canonical pairing");
            }
            (*outputs[0].getAsObject())["data"] = 2;
            std::string changed;
            raw_string_ostream(changed) << record;
            refused(
                checkOracleRealization(*prepared, *candidate.module, changed),
                "oracle-realization-record");
          });
      cases.run("returned aliases share role-specific support stores", [&] {
        require(entry.resultStores == std::vector<OracleResultStore>(
                                          {{0, 1, 7}, {1, 1, 8}, {2, 1, 9}}),
                "result store layout differs from source custody");
        require(entry.resultReferences ==
                    std::vector<OracleResultReference>({{1, "V", {7, 8, 9}},
                                                        {3, "V", {7, 8, 9}},
                                                        {5, "V", {7, 8, 9}}}),
                "result reference layout lost aliases or source positions");
      });
      cases.run("changed logical result position refuses", [&] {
        auto original = entry.resultReferences[0].result;
        auto restore = llvm::scope_exit(
            [&] { entry.resultReferences[0].result = original; });
        entry.resultReferences[0].result = 3;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("changed support role refuses", [&] {
        auto original = entry.resultStores[0].role;
        auto restore =
            llvm::scope_exit([&] { entry.resultStores[0].role = original; });
        entry.resultStores[0].role = 0;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("changed native store position refuses", [&] {
        auto original = entry.resultStores[0].port;
        auto restore =
            llvm::scope_exit([&] { entry.resultStores[0].port = original; });
        entry.resultStores[0].port = 8;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("missing support association refuses", [&] {
        auto &ports = entry.resultReferences[0].storePorts;
        auto original = ports.back();
        ports.pop_back();
        auto restore = llvm::scope_exit([&] { ports.push_back(original); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("same-typed returned reference substitution refuses", [&] {
        auto *returned = program.getBody().front().getTerminator();
        auto original = returned->getOperand(1);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(1, original); });
        returned->setOperand(1, returned->getOperand(5));
        require(succeeded(verify(*candidate.module)),
                "returned reference mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("stale returned store refuses", [&] {
        auto *returned = program.getBody().front().getTerminator();
        auto original = returned->getOperand(9);
        Value empty;
        for (auto &op : program.getBody().front())
          if (auto call = dyn_cast<protocol_ir::LocalCallOp>(op);
              call && call.getNumOperands() == 0 && call.getNumResults() == 1 &&
              call.getResult(0).getType() == original.getType() &&
              is_contained(cast<ArrayAttr>(program.getOutputRoles()[9]),
                           call.getRoleAttr()))
            empty = call.getResult(0);
        require(bool(empty), "missing initial virtual store");
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(9, original); });
        returned->setOperand(9, empty);
        require(succeeded(verify(*candidate.module)),
                "returned store mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-entries") {
      cases.run("shared virtual entries have distinct generated locals", [&] {
        require(candidate.entries[0].entry == "main" &&
                    candidate.entries[1].entry == "companion",
                "source entry order changed");
        require(candidate.entries[0].locals[0].getSymName() !=
                    candidate.entries[1].locals[0].getSymName(),
                "entry-local symbol collision");
        require(candidate.entries[0].locals[0].getSymName() !=
                        "_oracle_common_local_0_0" &&
                    candidate.entries[0].allocators[0][0].getSymName() !=
                        "_oracle_allocate_0_0",
                "authored symbol was reused");
        auto repeated = emitOracleRealization(*prepared);
        require(bool(repeated), "repeat emission failed");
        require(print(*repeated->module) == print(*candidate.module),
                "emission depends on mutable naming state");
      });
      cases.run("reordered entry records refuse", [&] {
        std::swap(candidate.entries[0], candidate.entries[1]);
        auto restore = llvm::scope_exit(
            [&] { std::swap(candidate.entries[0], candidate.entries[1]); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("missing entry records refuse", [&] {
        auto missing = std::move(candidate.entries.back());
        candidate.entries.pop_back();
        auto restore = llvm::scope_exit(
            [&] { candidate.entries.push_back(std::move(missing)); });
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("duplicate entry identities refuse", [&] {
        auto original = candidate.entries[1].entry;
        auto restore =
            llvm::scope_exit([&] { candidate.entries[1].entry = original; });
        candidate.entries[1].entry = candidate.entries[0].entry;
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("same-typed entry body substitution refuses", [&] {
        auto companion = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit, "companion"));
        auto exchange = [&] {
          Region temporary;
          temporary.takeBody(program.getBody());
          program.getBody().takeBody(companion.getBody());
          companion.getBody().takeBody(temporary);
        };
        exchange();
        auto restore = llvm::scope_exit(exchange);
        require(succeeded(verify(*candidate.module)),
                "entry body swap is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("ordinary sibling body remains checked", [&] {
        auto ordinary = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(unit, "ordinary"));
        auto *returned = ordinary.getBody().front().getTerminator();
        auto original = returned->getOperand(0);
        auto restore =
            llvm::scope_exit([&] { returned->setOperand(0, original); });
        returned->setOperand(0, ordinary.getBody().front().getArgument(1));
        require(succeeded(verify(*candidate.module)),
                "ordinary sibling mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("ordinary-only modules use the same complete reader", [&] {
        OwningOpRef<ModuleOp> plain(cast<ModuleOp>(prepared->clone()));
        auto owner = cast<pir::ProtocolModuleOp>(plain->getBody()->front());
        for (auto &op : make_early_inc_range(owner.getBody().front()))
          if (isa<pir::OracleDefinitionOp>(op) ||
              (isa<pir::MathematicalOp>(op) &&
               SymbolTable::getSymbolName(&op).getValue() != "ordinary"))
            op.erase();
        auto realized = emitOracleRealization(*plain);
        require(bool(realized), "ordinary emission failed");
        require(realized->entries.empty(), "invented oracle entry");
        checked(checkCandidate(*plain, *realized));
        require(print(*plain) == print(*realized->module),
                "ordinary declarations changed");
        auto after =
            cast<pir::ProtocolModuleOp>(realized->module->getBody()->front());
        auto ordinary = cast<pir::MathematicalOp>(
            SymbolTable::lookupSymbolIn(after, "ordinary"));
        ordinary.getBody().front().getTerminator()->setOperand(
            0, ordinary.getBody().front().getArgument(1));
        refused(checkCandidate(*plain, *realized), "oracle-common-body");
      });
    }
    if (mutations && fixture == "common-views") {
      cases.run("rebindings preserve the actual selected anchor", [&] {
        SmallVector<pir::RestrictRolesOp> rebindings;
        program.walk([&](pir::RestrictRolesOp op) {
          if (op.getRoles().size() == 2)
            rebindings.push_back(op);
        });
        require(rebindings.size() == 2, "expected two component rebindings");
        auto original = rebindings[1].getInput();
        auto restore = llvm::scope_exit(
            [&] { rebindings[1].getInputMutable().set(original); });
        rebindings[1].getInputMutable().set(rebindings[0].getInput());
        require(succeeded(verify(*candidate.module)),
                "rebind mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run("pair-only component views do not materialize data", [&] {
        unsigned materializations = 0;
        program.walk([&](pir::LocalCallOp op) {
          materializations += op.getSite().ends_with("_component_data");
        });
        require(materializations == 1,
                "unused component data was materialized");
      });
    }
    if (mutations && fixture == "common-contents") {
      auto holder = find_if(entry.controllers, [](const auto &item) {
        return item.access == OracleControllerAccess::Holder;
      });
      require(holder != entry.controllers.end(), "missing holder controller");
      cases.run("holder domain excludes unrelated received anchors", [&] {
        require(holder->body.constructors.size() == 3,
                "holder domain includes unrelated received data");
      });
      cases.run("holder access metadata cannot widen custody", [&] {
        auto restore = llvm::scope_exit(
            [&] { holder->body.access = OracleControllerAccess::Holder; });
        holder->body.access = OracleControllerAccess::Available;
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("contents checks actual materialization upper bound", [&] {
        exec::RangeOp rows;
        candidate.module->walk([&](exec::RangeOp op) {
          if (op.getSite() == "rows" && !rows)
            rows = op;
        });
        require(bool(rows), "missing contents loop");
        // Range operands begin with scope, lower, upper. Changing the upper
        // to zero is formed but would silently drop the virtual table.
        auto upper = rows->getOperand(2);
        auto restore = llvm::scope_exit([&] { rows->setOperand(2, upper); });
        rows->setOperand(2, rows->getOperand(1));
        require(succeeded(verify(*candidate.module)),
                "loop mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
      cases.run("shape observers cannot substitute structural leaf count", [&] {
        auto available = find_if(entry.controllers, [](const auto &item) {
          return item.access == OracleControllerAccess::Available &&
                 item.role == "P";
        });
        auto original = available->body.rowCounts[0];
        auto restore =
            llvm::scope_exit([&] { available->body.rowCounts[0] = original; });
        available->body.rowCounts[0] = available->body.leafCounts[0];
        refused(checkCandidate(*prepared, candidate), "oracle-controller-body");
      });
    }
    if (mutations && fixture != "common-empty") {
      SmallVector<pir::LocalCallOp> calls;
      program.walk([&](pir::LocalCallOp call) { calls.push_back(call); });
      cases.run(fixture + " changed query occurrence", [&] {
        auto found = find_if(calls, [](auto call) {
          return call.getSite().ends_with("_query");
        });
        require(found != calls.end(), "missing query call");
        auto original = found->getSiteAttr();
        auto restore = llvm::scope_exit([&] { found->setSiteAttr(original); });
        found->setSite("changed");
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
        found->setSiteAttr(original);
      });
      if (fixture == "common-recurrence" || fixture == "common-holders")
        cases.run(fixture + " substituted same-typed actual anchor", [&] {
          auto found = find_if(calls, [](auto call) {
            return call.getSite().ends_with("_query");
          });
          auto original = found->getInputs()[0];
          Value replacement;
          for (auto assembly :
               program.getBody().front().getOps<pir::AssembleRolesOp>())
            if (assembly.getOutput().getType() == original.getType() &&
                assembly.getOutput() != original) {
              replacement = assembly.getOutput();
              break;
            }
          require(bool(replacement), "missing alternative anchor");
          auto restore = llvm::scope_exit(
              [&] { found->getInputsMutable()[0].set(original); });
          found->getInputsMutable()[0].set(replacement);
          require(succeeded(verify(*candidate.module)),
                  "anchor mutation is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          found->getInputsMutable()[0].set(original);
        });
      if (fixture != "common-input" && fixture != "common-clauses")
        cases.run(fixture + " changed delivery occurrence", [&] {
          pir::ExchangeOp exchange;
          program.walk([&](pir::ExchangeOp op) {
            if (!exchange)
              exchange = op;
          });
          require(bool(exchange), "missing delivery");
          auto original = exchange.getSiteAttr();
          auto restore =
              llvm::scope_exit([&] { exchange.setSiteAttr(original); });
          exchange.setSite("other_delivery");
          require(succeeded(verify(*candidate.module)),
                  "mutation is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          exchange.setSiteAttr(original);
        });
      cases.run(fixture + " changed shape predicate", [&] {
        exec::ApplyOp predicate;
        for (auto helper : entry.locals)
          helper.walk([&](exec::ApplyOp op) {
            auto binding =
                SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                    op, op.getBindingAttr());
            if (binding && binding.getContract() == "index.equal" && !predicate)
              predicate = op;
          });
        require(bool(predicate), "missing predicate");
        auto first = predicate.getInputs()[0],
             second = predicate.getInputs()[1];
        auto restore = llvm::scope_exit(
            [&] { predicate.getInputsMutable()[1].set(second); });
        predicate.getInputsMutable()[1].set(first);
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
        predicate.getInputsMutable()[1].set(second);
      });
      cases.run(fixture + " extra body refuses", [&] {
        auto extra = cast<func::FuncOp>(entry.locals.front()->clone());
        extra.setSymName("unrelated");
        unit.getBody().front().push_back(extra);
        auto restore = llvm::scope_exit([&] { extra.erase(); });
        require(succeeded(verify(*candidate.module)), "mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      cases.run(fixture + " changed helper occurrence origin", [&] {
        auto helper = entry.locals.front();
        auto original = helper->getAttr("runtime.origin");
        auto restore = llvm::scope_exit(
            [&] { helper->setAttr("runtime.origin", original); });
        Builder builder(&context);
        helper->setAttr(
            "runtime.origin",
            builder.getArrayAttr({builder.getStringAttr("different"),
                                  builder.getArrayAttr({})}));
        require(succeeded(verify(*candidate.module)),
                "origin mutation is malformed");
        refused(checkCandidate(*prepared, candidate), "oracle-common-body");
      });
      if (fixture == "common-recurrence") {
        pir::RepeatOp repeat;
        program.walk([&](pir::RepeatOp op) { repeat = op; });
        cases.run("stale loop store refuses", [&] {
          auto yield = cast<pir::ProtocolYieldOp>(
              repeat.getBody().front().getTerminator());
          unsigned changed = 0;
          for (unsigned i = 1; i < yield.getInputs().size(); ++i)
            if (yield.getInputs()[i] !=
                repeat.getBody().front().getArgument(i + 1)) {
              changed = i;
              break;
            }
          require(changed != 0, "no store was updated");
          auto original = yield.getInputs()[changed];
          auto restore = llvm::scope_exit(
              [&] { yield.getInputsMutable()[changed].set(original); });
          yield.getInputsMutable()[changed].set(
              repeat.getBody().front().getArgument(changed + 1));
          require(succeeded(verify(*candidate.module)),
                  "stale store is malformed");
          refused(checkCandidate(*prepared, candidate), "oracle-common-body");
          yield.getInputsMutable()[changed].set(original);
        });
      }
    }
    if (compile) {
      SmallVector<StringRef> selected{"main"};
      if (fixture == "common-entries")
        append_range(selected, ArrayRef<StringRef>{"companion", "ordinary"});
      if (fixture == "common-return")
        selected.push_back("wrapper");
      if (fixture == "common-empty")
        selected.push_back("at");
      for (StringRef selectedEntry : selected)
        cases.run(fixture + " physical entry " + selectedEntry, [&] {
          auto logicalSource = print(*source);
          CompilationObservation observation;
          RunOptions options;
          options.entry = selectedEntry.str();
          options.observations = &observation;
          auto compiled = compileRun(logicalSource, "oracle-common.mlir",
                                     options, registry);
          std::string name = fixture.str();
          if (selectedEntry != "main")
            name += "-" + selectedEntry.str();
          if (argc > 1) {
            std::filesystem::create_directories(argv[1]);
            auto path =
                std::filesystem::path(argv[1]) / (name + ".compilation.json");
            std::ofstream(path) << formatv("{0:2}", observation.json()).str();
          }
          require(
              bool(compiled),
              "physical compilation: " +
                  (compiled ? std::string() : toString(compiled.takeError())) +
                  diagnostics);
          auto edge = compiled->compilation.oracleRealizationSnapshot();
          require(bool(edge), "production compilation lost realization");
          checked(checkOracleRealization(*edge->original, *edge->candidate,
                                         edge->record));
          OwningOpRef<ModuleOp> selectedSource(
              cast<ModuleOp>(prepared->clone()));
          SmallVector<Operation *> omitted;
          selectedSource->walk([&](pir::MathematicalOp program) {
            if (program.getSymName() != selectedEntry)
              omitted.push_back(program);
          });
          for (Operation *program : omitted)
            program->erase();
          require(print(*edge->original) == print(*selectedSource),
                  "production changed the selected prepared subject");
          checked(checkOracleRealization(*selectedSource, *edge->candidate,
                                         edge->record));
          require(print(*prepared) == frozen,
                  "deployment selection mutated the complete source");
          if (argc > 1) {
            auto base = std::filesystem::path(argv[1]) / name;
            std::ofstream(base.string() + ".mlir") << print(*edge->candidate);
            std::ofstream(base.string() + ".original.mlir")
                << print(*edge->original);
            std::ofstream(base.string() + ".realization.json") << edge->record;
            std::ofstream(base.string() + ".bundle") << compiled->bundle;
          }
        });
    }
  }
  if (mutations && (argc <= 3 || StringRef(argv[3]) == "dynamic-windows")) {
    selectedFixture = true;
    dynamicWindows(cases, context);
  }
  if (!selectedFixture) {
    errs() << "unknown common oracle fixture\n";
    return 1;
  }
  return cases.result();
}

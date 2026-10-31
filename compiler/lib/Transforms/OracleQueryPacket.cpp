#include "OracleQueryPacket.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Support/Refusal.h"
#include <limits>
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  const OracleQueryExchange &model;
  const OracleQueryResponse &response;
  func::FuncOp openOne;
  ArrayRef<OracleMerkleFunctions> merkle;
  uint64_t capacity;
  OracleQueryPacket result;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index, boolean;
  unsigned next = 0;
  Emitter(protocol_ir::ProtocolModuleOp unit, const OracleQueryExchange &model,
          const OracleQueryResponse &response, func::FuncOp openOne,
          ArrayRef<OracleMerkleFunctions> merkle, uint64_t capacity)
      : unit(unit), model(model), response(response), openOne(openOne),
        merkle(merkle), capacity(capacity), builder(unit.getContext()),
        bindings(unit, "_oracle_packet_binding_"),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()) {}
  Error plan(OracleVirtualFunctionWork &work) {
    if (!capacity || capacity >= 1048576 || model.arms.empty() ||
        model.arms.size() > 32 || model.receiverStores.size() > 480 ||
        model.holderStores.size() > 480)
      return error("oracle-packet-capacity");
    auto refuse = [] { return error("oracle-packet-layout"); };
    for (auto types : {ArrayRef<Type>(model.receiverStores),
                       ArrayRef<Type>(model.holderStores)})
      if (!all_of(types, [&](Type type) {
            return type && type.getContext() == unit.getContext();
          }))
        return refuse();
    auto record = [&](Type type, unsigned fields) {
      auto variant = dyn_cast_or_null<data::VariantType>(type);
      return variant && variant.getContext() == unit.getContext() &&
             variant.getAlternatives().size() == 1 &&
             variant.getAlternatives()[0].getLabel().getValue() == "Record" &&
             equal(variant.getAlternatives()[0].getPayload(),
                   Types(fields, index));
    };
    auto request = dyn_cast_or_null<data::VariantType>(model.request);
    auto opened = dyn_cast_or_null<data::VariantType>(model.response);
    auto answer = dyn_cast_or_null<data::VariantType>(response.answer);
    if (!record(model.request, 3) || !opened || !answer ||
        opened.getContext() != unit.getContext() ||
        answer.getContext() != unit.getContext() ||
        opened.getAlternatives().size() != model.arms.size() ||
        answer.getAlternatives().size() != model.arms.size())
      return refuse();
    auto identity = data::importVariantIdentity(
        unit.getContext(),
        json::Array{"zkc.oracle.checked-answer/0",
                    data::exportVariantIdentity(opened.getIdentity())});
    if (!identity || answer.getIdentity() != identity)
      return refuse();
    auto signature = [&](func::FuncOp helper) -> FunctionType {
      if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
          helper->hasAttr("runtime.region"))
        return {};
      return scopedDataSignature(helper);
    };
    Types openInputs{model.request}, authInputs{model.request, model.response};
    append_range(openInputs, model.holderStores);
    append_range(authInputs, model.receiverStores);
    auto openSignature = signature(openOne);
    auto authSignature = signature(response.authenticate);
    if (!openSignature || !authSignature ||
        !equal(openSignature.getInputs(), openInputs) ||
        !equal(openSignature.getResults(), Types{model.response}) ||
        !equal(authSignature.getInputs(), authInputs) ||
        !equal(authSignature.getResults(), Types{response.answer}))
      return refuse();
    uint64_t width =
        std::max(model.receiverStores.size(), model.holderStores.size()) + 16;
    std::set<unsigned> constructors, slots;
    std::set<std::string> names;
    for (auto [ordinal, arm] : enumerate(model.arms)) {
      if (!constructors.insert(arm.constructor).second ||
          !slots.insert(arm.receiverSlot).second ||
          !names.insert(arm.alternative).second || !record(arm.reference, 2) ||
          arm.receiverSlot >= model.receiverStores.size() ||
          arm.constructor >= merkle.size() || arm.opened.size() != 2 ||
          opened.getAlternatives()[ordinal].getLabel().getValue() !=
              arm.alternative ||
          !equal(opened.getAlternatives()[ordinal].getPayload(), arm.opened) ||
          answer.getAlternatives()[ordinal].getLabel().getValue() !=
              arm.alternative ||
          merkle[arm.constructor].open != arm.open ||
          merkle[arm.constructor].authenticate != arm.authenticate)
        return refuse();
      auto lookup = signature(arm.receiverLookup);
      auto position = signature(merkle[arm.constructor].position);
      auto authenticate = signature(arm.authenticate);
      if (!lookup || !position || !authenticate ||
          !equal(lookup.getInputs(),
                 Types{index, index, model.receiverStores[arm.receiverSlot]}) ||
          arm.receiverRows >= lookup.getNumResults() ||
          lookup.getResult(arm.receiverRows) != index ||
          !equal(position.getInputs(), Types(2, index)) ||
          !equal(position.getResults(), Types(3, index)) ||
          authenticate.getNumResults() != 1 ||
          !equal(answer.getAlternatives()[ordinal].getPayload(),
                 authenticate.getResults()))
        return refuse();
      if (lookup.getNumResults() > 480)
        return error("oracle-packet-capacity");
      width = std::max<uint64_t>(width, lookup.getNumResults() + 16);
    }
    auto keyIdentity = data::importVariantIdentity(
        unit.getContext(),
        json::Array{"zkc.oracle.physical-query-key/0",
                    data::exportVariantIdentity(request.getIdentity())});
    if (!keyIdentity)
      return refuse();
    auto alternative = data::AlternativeAttr::get(
        unit.getContext(), builder.getStringAttr("Record"), Types(3, index));
    result.key = data::VariantType::getChecked(
        unit.getLoc(), unit.getContext(), keyIdentity,
        ArrayRef<data::AlternativeAttr>{alternative});
    if (!result.key)
      return refuse();
    auto sequence = [&](Type type) {
      return data::SequenceType::get(unit.getContext(), type);
    };
    result.keySequence = sequence(result.key);
    result.requestSequence = sequence(model.request);
    result.responseSequence = sequence(model.response);
    result.answerSequence = sequence(response.answer);
    result.groupsSequence = sequence(index);
    // Compiler work bounds generated IR, not dynamic loop executions. The
    // first-use search has quadratic runtime cost, metered by the ordinary
    // scoped execution budget; its loop body is emitted only once. Retained
    // physical keys, requests, responses and occurrence groups grow linearly.
    uint64_t operations = 1024 + 512 * model.arms.size();
    uint64_t slotsNeeded = operations * (width + 16) + capacity * (width + 24);
    if (operations > work.operations || slotsNeeded > work.slots)
      return error("oracle-packet-limit");
    work.operations -= operations;
    work.slots -= slotsNeeded;
    return Error::success();
  }
  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_packet_" + label.str() + "_" + std::to_string(next++);
    } while (SymbolTable::lookupSymbolIn(unit, name));
    Types formals{runtime::ScopeType::get(unit.getContext())};
    append_range(formals, inputs);
    auto helper = func::FuncOp::create(
        builder, unit.getLoc(), name,
        builder.getFunctionType(
            formals,
            exec::OutcomeType::get(unit.getContext(), Types(outputs))));
    helper.setPrivate();
    helper.setNoInline(true);
    if (region)
      helper->setAttr("runtime.region", builder.getUnitAttr());
    else
      helper->setAttr("runtime.origin",
                      builder.getArrayAttr({builder.getStringAttr(name),
                                            builder.getArrayAttr({})}));
    builder.setInsertionPointToEnd(helper.addEntryBlock());
    Control control(builder, helper);
    emit(control, helper.getArguments().drop_front());
    return helper;
  }
  Values apply(Control &c, StringRef contract, TypeRange outputs,
               ValueRange inputs, StringRef site,
               ArrayRef<Attribute> statics = {},
               ArrayRef<Attribute> parameters = {}) {
    auto binding =
        bindings.binding(builder, unit.getLoc(),
                         {contract.str(), SmallVector<Attribute>(statics), ""});
    return c.invoke(
        "exec.apply", outputs, c.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  Value number(Control &c, uint64_t n, StringRef site) {
    return apply(c, "index.constant", index, {}, site, {},
                 {builder.getIntegerAttr(index, n)})[0];
  }
  Value compare(Control &c, StringRef contract, Value a, Value b,
                StringRef site) {
    return apply(c, contract, boolean, {a, b}, site)[0];
  }
  void require(Control &c, Value predicate, StringRef site) {
    apply(c, "control.require", {}, predicate, site);
  }
  void requireEqual(Control &c, Value a, Value b, StringRef site) {
    require(c, compare(c, "index.equal", a, b, site.str() + "_equal"), site);
  }
  void bounded(Control &c, Value length, StringRef prefix) {
    auto upper = number(c, capacity + 1, prefix.str() + "_capacity");
    require(c,
            compare(c, "index.less", length, upper,
                    prefix.str() + "_within_capacity"),
            prefix.str() + "_admit_length");
  }
  Values call(Control &c, func::FuncOp helper, ValueRange inputs,
              StringRef site) {
    auto outputs =
        cast<exec::OutcomeType>(helper.getResultTypes()[0]).getPayload();
    return c.invoke(
        "func.call", outputs, c.scoped(inputs),
        {builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
         builder.getNamedAttr("runtime.site", builder.getStringAttr(site))});
  }
  Value pack(Control &c, Type type, ValueRange fields, StringRef site) {
    return c.invoke(
        "exec.variant", type, c.scoped(fields),
        {builder.getNamedAttr("alternative", builder.getStringAttr("Record")),
         builder.getNamedAttr("site", builder.getStringAttr(site))})[0];
  }
  Values unpack(Control &c, Value record, StringRef site) {
    auto fields = cast<data::VariantType>(record.getType())
                      .getAlternatives()[0]
                      .getPayload();
    return c.match(record, {}, fields, {"Record"}, site, [&](unsigned) {
      return function("unpack", fields, fields, true,
                      [&](Control &body, ValueRange a) { body.complete(a); });
    });
  }
  Attribute element(Type sequence) {
    return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
  }
  Value empty(Control &c, Type sequence, StringRef site) {
    return apply(c, "sequence.empty", sequence, {}, site,
                 {element(sequence)})[0];
  }
  Value append(Control &c, Value sequence, Value value, StringRef site) {
    return apply(c, "sequence.append", sequence.getType(), {sequence, value},
                 site, {element(sequence.getType())})[0];
  }
  Value at(Control &c, Value sequence, Value ordinal, StringRef site) {
    return apply(c, "sequence.at",
                 cast<data::SequenceType>(sequence.getType()).getElementType(),
                 {sequence, ordinal}, site, {element(sequence.getType())})[0];
  }
  Value length(Control &c, Value sequence, StringRef site) {
    return apply(c, "sequence.length", index, sequence, site,
                 {element(sequence.getType())})[0];
  }
  Value keyArm(Control &c, ValueRange a, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    auto prefix = "packet_constructor_" + std::to_string(arm.constructor) + "_";
    auto stored =
        call(c, arm.receiverLookup, {a[0], a[1], a[3 + arm.receiverSlot]},
             prefix + "lookup");
    auto position = call(c, merkle[arm.constructor].position,
                         {stored[arm.receiverRows], a[2]}, prefix + "position");
    return pack(c, result.key, {a[0], a[1], position[1]}, prefix + "key");
  }
  Value dispatch(Control &c, ValueRange a, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    auto prefix = "packet_constructor_" + std::to_string(arm.constructor) + "_";
    auto tag = number(c, arm.constructor, prefix + "tag");
    auto selected = compare(c, "index.equal", a[0], tag, prefix + "selected");
    if (ordinal + 1 == model.arms.size()) {
      require(c, selected, prefix + "admit");
      return keyArm(c, a, ordinal);
    }
    return c.conditional(
        selected, a, result.key, prefix + "dispatch", [&](unsigned branch) {
          return function("dispatch", a.getTypes(), result.key, true,
                          [&](Control &body, ValueRange captures) {
                            body.complete(
                                branch == 0
                                    ? keyArm(body, captures, ordinal)
                                    : dispatch(body, captures, ordinal + 1));
                          });
        })[0];
  }
  func::FuncOp keyFunction() {
    Types inputs{model.request};
    append_range(inputs, model.receiverStores);
    return function("key", inputs, result.key, false,
                    [&](Control &c, ValueRange a) {
                      auto fields = unpack(c, a[0], "packet_request");
                      append_range(fields, a.drop_front());
                      c.returned(dispatch(c, fields, 0));
                    });
  }
  Types groupState() {
    return {result.requestSequence, result.keySequence, result.groupsSequence};
  }
  Value scan(Control &c, Value keys, Value key, Value count) {
    auto zero = number(c, 0, "packet_scan_lower");
    return c.loop(
        zero, count, count, {keys, key}, index, true, "packet_scan",
        [&](unsigned) {
          return function(
              "scan", {index, index, result.keySequence, result.key},
              {boolean, index}, true, [&](Control &body, ValueRange a) {
                auto prior = at(body, a[2], a[0], "packet_scan_key");
                auto oldFields = unpack(body, prior, "packet_scan_old");
                auto newFields = unpack(body, a[3], "packet_scan_new");
                auto sameConstructor =
                    compare(body, "index.equal", oldFields[0], newFields[0],
                            "packet_same_constructor");
                auto sameInstance =
                    compare(body, "index.equal", oldFields[1], newFields[1],
                            "packet_same_instance");
                auto sameLeaf = compare(body, "index.equal", oldFields[2],
                                        newFields[2], "packet_same_leaf");
                auto sameAnchor = apply(body, "bool.and", boolean,
                                        {sameConstructor, sameInstance},
                                        "packet_same_anchor")[0];
                auto same = apply(body, "bool.and", boolean,
                                  {sameAnchor, sameLeaf}, "packet_same_key")[0];
                auto group = body.conditional(
                    same, a.take_front(2), index, "packet_found",
                    [&](unsigned branch) {
                      return function(
                          "found", {index, index}, index, true,
                          [&](Control &selected, ValueRange captures) {
                            selected.complete(captures[branch]);
                          });
                    })[0];
                auto proceed = apply(body, "bool.not", boolean, same,
                                     "packet_scan_continue")[0];
                body.complete({proceed, group});
              });
        })[0];
  }
  void emitGroup(func::FuncOp key) {
    Types inputs{result.requestSequence};
    append_range(inputs, model.receiverStores);
    result.group = function(
        "group", inputs, {result.requestSequence, result.groupsSequence}, false,
        [&](Control &c, ValueRange a) {
          auto count = length(c, a[0], "packet_group_length");
          bounded(c, count, "packet_group");
          auto zero = number(c, 0, "packet_group_lower");
          auto physical =
              empty(c, result.requestSequence, "packet_empty_physical");
          auto keys = empty(c, result.keySequence, "packet_empty_keys");
          auto groups = empty(c, result.groupsSequence, "packet_empty_groups");
          auto grouped = c.loop(
              zero, count, {physical, keys, groups}, a, groupState(), false,
              "packet_group", [&](unsigned) {
                Types types{index};
                append_range(types, groupState());
                append_range(types, inputs);
                return function(
                    "group_iteration", types, groupState(), true,
                    [&](Control &body, ValueRange b) {
                      auto request =
                          at(body, b[4], b[0], "packet_logical_request");
                      Values keyInputs{request};
                      append_range(keyInputs, b.drop_front(5));
                      auto currentKey =
                          call(body, key, keyInputs, "packet_resolve_key")[0];
                      auto keyCount = length(body, b[2], "packet_key_count");
                      auto group = scan(body, b[2], currentKey, keyCount);
                      auto fresh = compare(body, "index.equal", group, keyCount,
                                           "packet_new_group");
                      Values captures{b[1],    b[2],       b[3],
                                      request, currentKey, group};
                      Types captureTypes{result.requestSequence,
                                         result.keySequence,
                                         result.groupsSequence,
                                         model.request,
                                         result.key,
                                         index};
                      body.complete(body.conditional(
                          fresh, captures, groupState(), "packet_insert",
                          [&](unsigned branch) {
                            return function(
                                "insert", captureTypes, groupState(), true,
                                [&](Control &selected, ValueRange s) {
                                  Value physical = s[0], keys = s[1];
                                  if (branch == 0) {
                                    physical = append(selected, physical, s[3],
                                                      "packet_add_physical");
                                    keys = append(selected, keys, s[4],
                                                  "packet_add_key");
                                  }
                                  auto groups =
                                      append(selected, s[2], s[5],
                                             branch == 0
                                                 ? "packet_add_new_group"
                                                 : "packet_add_existing_group");
                                  selected.complete({physical, keys, groups});
                                });
                          }));
                    });
              });
          c.returned({grouped[0], grouped[2]});
        });
  }
  void emitOpen() {
    Types inputs{result.requestSequence};
    append_range(inputs, model.holderStores);
    result.open = function(
        "open", inputs, result.responseSequence, false,
        [&](Control &c, ValueRange a) {
          auto count = length(c, a[0], "packet_open_length");
          bounded(c, count, "packet_open");
          auto zero = number(c, 0, "packet_open_lower");
          auto responses =
              empty(c, result.responseSequence, "packet_empty_responses");
          c.returned(c.loop(
              zero, count, responses, a, result.responseSequence, false,
              "packet_open", [&](unsigned) {
                Types types{index, result.responseSequence};
                append_range(types, inputs);
                return function(
                    "open_iteration", types, result.responseSequence, true,
                    [&](Control &body, ValueRange b) {
                      auto request =
                          at(body, b[2], b[0], "packet_physical_request");
                      Values inputs{request};
                      append_range(inputs, b.drop_front(3));
                      auto opened =
                          call(body, openOne, inputs, "packet_open_one")[0];
                      body.complete(
                          append(body, b[1], opened, "packet_add_response"));
                    });
              }));
        });
  }
  void emitAuthenticate() {
    Types inputs{result.requestSequence, result.requestSequence,
                 result.groupsSequence, result.responseSequence};
    append_range(inputs, model.receiverStores);
    result.authenticate = function(
        "authenticate", inputs, result.answerSequence, false,
        [&](Control &c, ValueRange a) {
          auto logical = length(c, a[0], "packet_auth_logical_length");
          auto physical = length(c, a[1], "packet_auth_physical_length");
          auto groups = length(c, a[2], "packet_auth_groups_length");
          auto responses = length(c, a[3], "packet_auth_responses_length");
          requireEqual(c, logical, groups, "packet_logical_group_lengths");
          requireEqual(c, physical, responses,
                       "packet_physical_response_lengths");
          bounded(c, logical, "packet_auth_logical");
          bounded(c, physical, "packet_auth_physical");
          auto zero = number(c, 0, "packet_auth_lower");
          auto answers =
              empty(c, result.answerSequence, "packet_empty_answers");
          c.returned(c.loop(
              zero, logical, answers, a, result.answerSequence, false,
              "packet_authenticate", [&](unsigned) {
                Types types{index, result.answerSequence};
                append_range(types, inputs);
                return function(
                    "authenticate_iteration", types, result.answerSequence,
                    true, [&](Control &body, ValueRange b) {
                      auto request =
                          at(body, b[2], b[0], "packet_auth_request");
                      auto group = at(body, b[4], b[0], "packet_auth_group");
                      auto opened =
                          at(body, b[5], group, "packet_auth_response");
                      Values inputs{request, opened};
                      append_range(inputs, b.drop_front(6));
                      auto answer = call(body, response.authenticate, inputs,
                                         "packet_authenticate_one")[0];
                      body.complete(
                          append(body, b[1], answer, "packet_add_answer"));
                    });
              }));
        });
  }
};
} // namespace
Expected<OracleQueryPacket>
emitOracleQueryPacket(ModuleOp candidate, const OracleQueryExchange &model,
                      const OracleQueryResponse &response, func::FuncOp openOne,
                      ArrayRef<OracleMerkleFunctions> merkle, uint64_t capacity,
                      OracleVirtualFunctionWork &sharedWork) {
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()))
    return error("oracle-packet-source");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      failed(zkc::admitStage(candidate)))
    return error("oracle-packet-source");
  Emitter emitter(unit, model, response, openOne, merkle, capacity);
  if (auto e = emitter.plan(sharedWork))
    return std::move(e);
  auto key = emitter.keyFunction();
  emitter.emitGroup(key);
  emitter.emitOpen();
  emitter.emitAuthenticate();
  return std::move(emitter.result);
}
} // namespace zkc::protocol

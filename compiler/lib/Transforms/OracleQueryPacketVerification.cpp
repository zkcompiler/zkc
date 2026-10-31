#include "NativeBindingApplication.h"
#include "OracleQueryPacket.h"
#include "OracleVerificationContext.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
// Re-derive all ordinary layouts from the immutable supplied model. Helper
// bodies are separate enclosing obligations, not accepted on their names.
bool layout(const OracleVerificationContext &context,
            const OracleQueryExchange &model,
            const OracleQueryResponse &response, func::FuncOp openOne,
            ArrayRef<OracleMerkleFunctions> merkle, uint64_t capacity,
            const OracleQueryPacket &packet) {
  auto unit = context.getUnit();
  auto *ctx = unit.getContext();
  auto index = IntegerType::get(ctx, 64, IntegerType::Unsigned);
  if (!capacity || capacity >= 1048576 || model.arms.empty() ||
      model.arms.size() > 32 || model.receiverStores.size() > 480 ||
      model.holderStores.size() > 480)
    return false;
  for (auto types : {ArrayRef<Type>(model.receiverStores),
                     ArrayRef<Type>(model.holderStores)})
    if (!all_of(types,
                [&](Type type) { return type && type.getContext() == ctx; }))
      return false;
  auto record = [&](Type type, unsigned fields) {
    auto variant = dyn_cast_or_null<data::VariantType>(type);
    return variant && variant.getContext() == ctx &&
           variant.getAlternatives().size() == 1 &&
           variant.getAlternatives()[0].getLabel().getValue() == "Record" &&
           equal(variant.getAlternatives()[0].getPayload(),
                 Types(fields, index));
  };
  auto request = dyn_cast_or_null<data::VariantType>(model.request);
  auto opened = dyn_cast_or_null<data::VariantType>(model.response);
  auto answer = dyn_cast_or_null<data::VariantType>(response.answer);
  if (!record(model.request, 3) || !opened || !answer ||
      opened.getContext() != ctx || answer.getContext() != ctx ||
      opened.getAlternatives().size() != model.arms.size() ||
      answer.getAlternatives().size() != model.arms.size())
    return false;
  auto answerIdentity = data::importVariantIdentity(
      ctx, json::Array{"zkc.oracle.checked-answer/0",
                       data::exportVariantIdentity(opened.getIdentity())});
  if (!answerIdentity || answer.getIdentity() != answerIdentity)
    return false;
  auto signature = [&](func::FuncOp helper) -> FunctionType {
    if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
        helper->hasAttr("runtime.region") ||
        !context.getClosure().bodies.count(helper.getSymName().str()))
      return {};
    return scopedDataSignature(helper);
  };
  Types openInputs{model.request}, authInputs{model.request, model.response};
  append_range(openInputs, model.holderStores);
  append_range(authInputs, model.receiverStores);
  auto opening = signature(openOne),
       authentication = signature(response.authenticate);
  if (!opening || !authentication || !equal(opening.getInputs(), openInputs) ||
      !equal(opening.getResults(), Types{model.response}) ||
      !equal(authentication.getInputs(), authInputs) ||
      !equal(authentication.getResults(), Types{response.answer}))
    return false;
  std::set<unsigned> constructors, slots;
  std::set<std::string> alternatives;
  for (auto [ordinal, arm] : enumerate(model.arms)) {
    if (!constructors.insert(arm.constructor).second ||
        !slots.insert(arm.receiverSlot).second ||
        !alternatives.insert(arm.alternative).second ||
        !record(arm.reference, 2) ||
        arm.receiverSlot >= model.receiverStores.size() ||
        arm.constructor >= merkle.size() || arm.opened.size() != 2 ||
        opened.getAlternatives()[ordinal].getLabel().getValue() !=
            arm.alternative ||
        !equal(opened.getAlternatives()[ordinal].getPayload(), arm.opened) ||
        answer.getAlternatives()[ordinal].getLabel().getValue() !=
            arm.alternative ||
        merkle[arm.constructor].open != arm.open ||
        merkle[arm.constructor].authenticate != arm.authenticate)
      return false;
    auto lookup = signature(arm.receiverLookup);
    auto position = signature(merkle[arm.constructor].position);
    auto authenticate = signature(arm.authenticate);
    if (!lookup || !position || !authenticate || lookup.getNumResults() > 480 ||
        !equal(lookup.getInputs(),
               Types{index, index, model.receiverStores[arm.receiverSlot]}) ||
        arm.receiverRows >= lookup.getNumResults() ||
        lookup.getResult(arm.receiverRows) != index ||
        !equal(position.getInputs(), Types(2, index)) ||
        !equal(position.getResults(), Types(3, index)) ||
        authenticate.getNumResults() != 1 ||
        !equal(answer.getAlternatives()[ordinal].getPayload(),
               authenticate.getResults()))
      return false;
  }
  auto identity = data::importVariantIdentity(
      ctx, json::Array{"zkc.oracle.physical-query-key/0",
                       data::exportVariantIdentity(request.getIdentity())});
  if (!identity)
    return false;
  auto alternative = data::AlternativeAttr::get(
      ctx, StringAttr::get(ctx, "Record"), Types(3, index));
  auto key = data::VariantType::getChecked(
      unit.getLoc(), ctx, identity,
      ArrayRef<data::AlternativeAttr>{alternative});
  auto sequence = [&](Type type) { return data::SequenceType::get(ctx, type); };
  return key && packet.key == key && packet.keySequence == sequence(key) &&
         packet.requestSequence == sequence(model.request) &&
         packet.responseSequence == sequence(model.response) &&
         packet.answerSequence == sequence(response.answer) &&
         packet.groupsSequence == sequence(index) && packet.group &&
         packet.open && packet.authenticate && packet.group != packet.open &&
         packet.group != packet.authenticate &&
         packet.open != packet.authenticate;
}
struct Reader {
  const OracleQueryExchange &model;
  const OracleQueryResponse &response;
  const OracleQueryPacket &packet;
  func::FuncOp openOne;
  ArrayRef<OracleMerkleFunctions> merkle;
  uint64_t capacity;
  protocol_ir::ProtocolModuleOp unit;
  const SourceExecutionClosure &closure;
  Type index, scope, boolean;
  bool valid = true;
  Reader(const OracleVerificationContext &context,
         const OracleQueryExchange &model, const OracleQueryResponse &response,
         func::FuncOp openOne, ArrayRef<OracleMerkleFunctions> merkle,
         uint64_t capacity, const OracleQueryPacket &packet)
      : model(model), response(response), packet(packet), openOne(openOne),
        merkle(merkle), capacity(capacity), unit(context.getUnit()),
        closure(context.getClosure()),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)),
        scope(runtime::ScopeType::get(unit.getContext())),
        boolean(IntegerType::get(unit.getContext(), 1)) {}
  bool expect(bool value) {
    valid &= value;
    return valid;
  }
  struct Cursor {
    Reader &reader;
    ArrayRef<SourceExecutionStep> steps;
    unsigned offset = 0;
    const SourceExecutionStep *take(StringRef operation, StringRef site) {
      if (!reader.valid)
        return nullptr;
      if (!reader.expect(offset < steps.size()))
        return nullptr;
      const auto &step = steps[offset++];
      auto actual = step.operation->getAttrOfType<StringAttr>(
          operation == "func.call" ? "runtime.site" : "site");
      if (!reader.expect(step.operation->getName().getStringRef() ==
                             operation &&
                         actual && actual.getValue() == site))
        return nullptr;
      return &step;
    }
    Values result(const SourceExecutionStep *step, TypeRange types,
                  ValueRange inputs, unsigned regions = 0) {
      if (!reader.valid || !step)
        return Values(types.size());
      if (!reader.expect(equal(step->inputs, inputs) &&
                         step->regions.size() == regions &&
                         equal(ValueRange(step->outputs).getTypes(), types)))
        return Values(types.size());
      return step->outputs;
    }
    Values apply(StringRef contract, TypeRange outputs, ValueRange inputs,
                 StringRef site, ArrayRef<Attribute> statics = {},
                 ArrayRef<std::string> parameters = {}) {
      auto *step = take("exec.apply", site);
      auto values = result(step, outputs, inputs);
      if (!reader.valid)
        return values;
      auto op = cast<exec::ApplyOp>(step->operation);
      auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
          op, op.getBindingAttr());
      if (!reader.expect(binding && binding.getContract() == contract &&
                         binding.getImplementation().empty() &&
                         binding.getArguments().size() == statics.size() &&
                         op.getParameters().size() == parameters.size()))
        return values;
      reader.expect(matchesNativeBinding(
          binding, {contract.str(), SmallVector<Attribute>(statics), {}}));
      reader.expect(
          invocationParametersMatch(contract, binding.getArgumentsAttr(),
                                    op.getParametersAttr(), parameters));
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(value)})
          .front();
    }
    Values local(ValueRange inputs, TypeRange outputs, StringRef site,
                 func::FuncOp &callee) {
      auto *step = take("func.call", site);
      auto values = result(step, outputs, inputs);
      if (reader.valid) {
        auto call = cast<func::CallOp>(step->operation);
        callee = dyn_cast_or_null<func::FuncOp>(
            SymbolTable::lookupSymbolIn(reader.unit, call.getCallee()));
        reader.expect(bool(callee));
      }
      return values;
    }
    Values call(func::FuncOp expected, ValueRange inputs, StringRef site) {
      if (!reader.valid)
        return Values(
            expected ? cast<exec::OutcomeType>(expected.getResultTypes()[0])
                           .getPayload()
                           .size()
                     : 0);
      func::FuncOp actual;
      auto types =
          cast<exec::OutcomeType>(expected.getResultTypes()[0]).getPayload();
      auto values = local(inputs, types, site, actual);
      reader.expect(actual == expected);
      return values;
    }
    Value pack(Type type, StringRef alternative, ValueRange fields,
               StringRef site) {
      auto *step = take("exec.variant", site);
      auto values = result(step, type, fields);
      if (reader.valid)
        reader.expect(cast<exec::VariantOp>(step->operation).getAlternative() ==
                      alternative);
      return values.front();
    }
    Values match(Value input, ValueRange captures, TypeRange outputs,
                 ArrayRef<std::string> alternatives, StringRef site,
                 llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.match", site);
      Values inputs{input};
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, alternatives.size());
      if (!reader.valid)
        return values;
      auto actual = cast<exec::MatchOp>(step->operation).getAlternatives();
      if (!reader.expect(actual.size() == alternatives.size()))
        return values;
      for (auto [i, name] : enumerate(alternatives)) {
        if (!reader.expect(cast<StringAttr>(actual[i]).getValue() == name))
          return values;
        check(i, step->regions[i]);
      }
      return values;
    }
    Values unpack(Value record, StringRef site) {
      Types fields(3, reader.index);
      return match(record, {}, fields, {"Record"}, site,
                   [&](unsigned, func::FuncOp region) {
                     reader.body(
                         region, fields, fields, true,
                         [&](Cursor &c, ValueRange a) { c.finish(a, true); });
                   });
    }
    Value compare(StringRef contract, Value a, Value b, StringRef site) {
      return apply(contract, reader.boolean, {a, b}, site)[0];
    }
    Value empty(Type sequence, StringRef site) {
      return apply("sequence.empty", sequence, {}, site,
                   {reader.element(sequence)})[0];
    }
    Value append(Type sequence, Value previous, Value value, StringRef site) {
      return apply("sequence.append", sequence, {previous, value}, site,
                   {reader.element(sequence)})[0];
    }
    Value at(Type sequence, Value values, Value ordinal, StringRef site) {
      return apply("sequence.at",
                   cast<data::SequenceType>(sequence).getElementType(),
                   {values, ordinal}, site, {reader.element(sequence)})[0];
    }
    Value length(Type sequence, Value values, StringRef site) {
      return apply("sequence.length", reader.index, values, site,
                   {reader.element(sequence)})[0];
    }
    Values conditional(Value condition, ValueRange captures, TypeRange outputs,
                       StringRef site,
                       llvm::function_ref<void(unsigned, func::FuncOp)> check) {
      auto *step = take("exec.test", site);
      Values inputs{condition};
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, 2);
      if (reader.valid)
        for (unsigned branch = 0; branch < 2; ++branch)
          check(branch, step->regions[branch]);
      return values;
    }
    Values loop(Value lower, Value upper, ValueRange seeds, ValueRange captures,
                TypeRange outputs, bool conditional, StringRef site,
                llvm::function_ref<void(func::FuncOp)> check) {
      auto *step = take("exec.range", site);
      Values inputs{lower, upper};
      append_range(inputs, seeds);
      append_range(inputs, captures);
      auto values = result(step, outputs, inputs, 1);
      if (reader.valid && reader.expect(step->conditional == conditional))
        check(step->regions[0]);
      return values;
    }
    void finish(ValueRange values, bool region = false) {
      if (!reader.valid)
        return;
      if (!reader.expect(offset + 1 == steps.size()))
        return;
      const auto &last = steps[offset++];
      reader.expect((region ? isa<exec::CompleteOp>(last.operation)
                            : isa<exec::ReturnOp>(last.operation)) &&
                    last.regions.empty() && last.outputs.empty() &&
                    equal(last.inputs, values));
    }
  };
  void body(func::FuncOp function, TypeRange inputs, TypeRange outputs,
            bool region, llvm::function_ref<void(Cursor &, ValueRange)> check) {
    if (!valid)
      return;
    Types arguments{scope};
    append_range(arguments, inputs);
    if (!expect(function && function->getParentOp() == unit &&
                function.isPrivate() &&
                !function->hasAttr("data.preconditions") &&
                function->getAttrOfType<UnitAttr>("no_inline") &&
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), arguments) &&
                function.getResultTypes().size() == 1))
      return;
    auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
    if (!expect(outcome && equal(outcome.getPayload(), outputs)))
      return;
    if (region) {
      if (!expect(function->getAttrOfType<UnitAttr>("runtime.region") &&
                  !function->hasAttr("runtime.origin")))
        return;
    } else {
      auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
      auto expected = ArrayAttr::get(
          unit.getContext(),
          {StringAttr::get(unit.getContext(), function.getSymName()),
           ArrayAttr::get(unit.getContext(), {})});
      if (!expect(origin == expected))
        return;
    }
    auto found = closure.bodies.find(function.getSymName().str());
    if (!expect(found != closure.bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }
  Attribute element(Type sequence) {
    return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
  }
  void requireEqual(Cursor &c, Value a, Value b, StringRef site) {
    auto predicate = c.compare("index.equal", a, b, site.str() + "_equal");
    c.apply("control.require", {}, predicate, site);
  }
  void bounded(Cursor &c, Value length, StringRef prefix) {
    auto upper = c.number(capacity + 1, prefix.str() + "_capacity");
    auto predicate = c.compare("index.less", length, upper,
                               prefix.str() + "_within_capacity");
    c.apply("control.require", {}, predicate, prefix.str() + "_admit_length");
  }
  Value keyArm(Cursor &c, ValueRange a, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    auto prefix = "packet_constructor_" + std::to_string(arm.constructor) + "_";
    auto stored =
        c.call(arm.receiverLookup, {a[0], a[1], a[3 + arm.receiverSlot]},
               prefix + "lookup");
    auto position =
        c.call(merkle[arm.constructor].position,
               {stored[arm.receiverRows], a[2]}, prefix + "position");
    return c.pack(packet.key, "Record", {a[0], a[1], position[1]},
                  prefix + "key");
  }
  Value dispatch(Cursor &c, ValueRange a, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    auto prefix = "packet_constructor_" + std::to_string(arm.constructor) + "_";
    auto tag = c.number(arm.constructor, prefix + "tag");
    auto selected = c.compare("index.equal", a[0], tag, prefix + "selected");
    if (ordinal + 1 == model.arms.size()) {
      c.apply("control.require", {}, selected, prefix + "admit");
      return keyArm(c, a, ordinal);
    }
    return c.conditional(
        selected, a, packet.key, prefix + "dispatch",
        [&](unsigned branch, func::FuncOp region) {
          body(region, a.getTypes(), packet.key, true,
               [&](Cursor &body, ValueRange captures) {
                 body.finish(branch == 0
                                 ? keyArm(body, captures, ordinal)
                                 : dispatch(body, captures, ordinal + 1),
                             true);
               });
        })[0];
  }
  void keyFunction(func::FuncOp function) {
    Types inputs{model.request};
    append_range(inputs, model.receiverStores);
    body(function, inputs, packet.key, false, [&](Cursor &c, ValueRange a) {
      auto fields = c.unpack(a[0], "packet_request");
      append_range(fields, a.drop_front());
      c.finish(dispatch(c, fields, 0));
    });
  }
  Types groupState() {
    return {packet.requestSequence, packet.keySequence, packet.groupsSequence};
  }
  Value scan(Cursor &c, Value keys, Value key, Value count) {
    auto zero = c.number(0, "packet_scan_lower");
    return c.loop(
        zero, count, count, {keys, key}, index, true, "packet_scan",
        [&](func::FuncOp region) {
          body(region, {index, index, packet.keySequence, packet.key},
               {boolean, index}, true, [&](Cursor &c, ValueRange a) {
                 auto prior =
                     c.at(packet.keySequence, a[2], a[0], "packet_scan_key");
                 auto oldFields = c.unpack(prior, "packet_scan_old");
                 auto newFields = c.unpack(a[3], "packet_scan_new");
                 auto sameConstructor =
                     c.compare("index.equal", oldFields[0], newFields[0],
                               "packet_same_constructor");
                 auto sameInstance =
                     c.compare("index.equal", oldFields[1], newFields[1],
                               "packet_same_instance");
                 auto sameLeaf = c.compare("index.equal", oldFields[2],
                                           newFields[2], "packet_same_leaf");
                 auto sameAnchor = c.apply("bool.and", boolean,
                                           {sameConstructor, sameInstance},
                                           "packet_same_anchor")[0];
                 auto same =
                     c.apply("bool.and", boolean, {sameAnchor, sameLeaf},
                             "packet_same_key")[0];
                 auto group =
                     c.conditional(same, a.take_front(2), index, "packet_found",
                                   [&](unsigned branch, func::FuncOp selected) {
                                     body(selected, {index, index}, index, true,
                                          [&](Cursor &c, ValueRange captures) {
                                            c.finish(captures[branch], true);
                                          });
                                   })[0];
                 auto proceed = c.apply("bool.not", boolean, same,
                                        "packet_scan_continue")[0];
                 c.finish({proceed, group}, true);
               });
        })[0];
  }
  void group() {
    Types inputs{packet.requestSequence};
    append_range(inputs, model.receiverStores);
    body(packet.group, inputs, {packet.requestSequence, packet.groupsSequence},
         false, [&](Cursor &c, ValueRange a) {
           auto count =
               c.length(packet.requestSequence, a[0], "packet_group_length");
           bounded(c, count, "packet_group");
           auto zero = c.number(0, "packet_group_lower");
           auto physical =
               c.empty(packet.requestSequence, "packet_empty_physical");
           auto keys = c.empty(packet.keySequence, "packet_empty_keys");
           auto groups = c.empty(packet.groupsSequence, "packet_empty_groups");
           auto grouped = c.loop(
               zero, count, {physical, keys, groups}, a, groupState(), false,
               "packet_group", [&](func::FuncOp region) {
                 Types types{index};
                 append_range(types, groupState());
                 append_range(types, inputs);
                 body(region, types, groupState(), true,
                      [&](Cursor &c, ValueRange b) {
                        auto request = c.at(packet.requestSequence, b[4], b[0],
                                            "packet_logical_request");
                        Values keyInputs{request};
                        append_range(keyInputs, b.drop_front(5));
                        func::FuncOp key;
                        auto currentKey = c.local(keyInputs, packet.key,
                                                  "packet_resolve_key", key)[0];
                        keyFunction(key);
                        auto keyCount = c.length(packet.keySequence, b[2],
                                                 "packet_key_count");
                        auto group = scan(c, b[2], currentKey, keyCount);
                        auto fresh = c.compare("index.equal", group, keyCount,
                                               "packet_new_group");
                        Values captures{b[1],    b[2],       b[3],
                                        request, currentKey, group};
                        Types captureTypes{packet.requestSequence,
                                           packet.keySequence,
                                           packet.groupsSequence,
                                           model.request,
                                           packet.key,
                                           index};
                        c.finish(
                            c.conditional(
                                fresh, captures, groupState(), "packet_insert",
                                [&](unsigned branch, func::FuncOp selected) {
                                  body(selected, captureTypes, groupState(),
                                       true, [&](Cursor &c, ValueRange s) {
                                         Value physical = s[0], keys = s[1];
                                         if (branch == 0) {
                                           physical = c.append(
                                               packet.requestSequence, physical,
                                               s[3], "packet_add_physical");
                                           keys = c.append(packet.keySequence,
                                                           keys, s[4],
                                                           "packet_add_key");
                                         }
                                         auto groups = c.append(
                                             packet.groupsSequence, s[2], s[5],
                                             branch == 0
                                                 ? "packet_add_new_group"
                                                 : "packet_add_existing_group");
                                         c.finish({physical, keys, groups},
                                                  true);
                                       });
                                }),
                            true);
                      });
               });
           c.finish({grouped[0], grouped[2]});
         });
  }
  void open() {
    Types inputs{packet.requestSequence};
    append_range(inputs, model.holderStores);
    body(packet.open, inputs, packet.responseSequence, false,
         [&](Cursor &c, ValueRange a) {
           auto count =
               c.length(packet.requestSequence, a[0], "packet_open_length");
           bounded(c, count, "packet_open");
           auto zero = c.number(0, "packet_open_lower");
           auto responses =
               c.empty(packet.responseSequence, "packet_empty_responses");
           c.finish(c.loop(
               zero, count, responses, a, packet.responseSequence, false,
               "packet_open", [&](func::FuncOp region) {
                 Types types{index, packet.responseSequence};
                 append_range(types, inputs);
                 body(region, types, packet.responseSequence, true,
                      [&](Cursor &c, ValueRange b) {
                        auto request = c.at(packet.requestSequence, b[2], b[0],
                                            "packet_physical_request");
                        Values inputs{request};
                        append_range(inputs, b.drop_front(3));
                        auto opened =
                            c.call(openOne, inputs, "packet_open_one")[0];
                        c.finish(c.append(packet.responseSequence, b[1], opened,
                                          "packet_add_response"),
                                 true);
                      });
               }));
         });
  }
  void authenticate() {
    Types inputs{packet.requestSequence, packet.requestSequence,
                 packet.groupsSequence, packet.responseSequence};
    append_range(inputs, model.receiverStores);
    body(packet.authenticate, inputs, packet.answerSequence, false,
         [&](Cursor &c, ValueRange a) {
           auto logical = c.length(packet.requestSequence, a[0],
                                   "packet_auth_logical_length");
           auto physical = c.length(packet.requestSequence, a[1],
                                    "packet_auth_physical_length");
           auto groups = c.length(packet.groupsSequence, a[2],
                                  "packet_auth_groups_length");
           auto responses = c.length(packet.responseSequence, a[3],
                                     "packet_auth_responses_length");
           requireEqual(c, logical, groups, "packet_logical_group_lengths");
           requireEqual(c, physical, responses,
                        "packet_physical_response_lengths");
           bounded(c, logical, "packet_auth_logical");
           bounded(c, physical, "packet_auth_physical");
           auto zero = c.number(0, "packet_auth_lower");
           auto answers =
               c.empty(packet.answerSequence, "packet_empty_answers");
           c.finish(c.loop(
               zero, logical, answers, a, packet.answerSequence, false,
               "packet_authenticate", [&](func::FuncOp region) {
                 Types types{index, packet.answerSequence};
                 append_range(types, inputs);
                 body(region, types, packet.answerSequence, true,
                      [&](Cursor &c, ValueRange b) {
                        auto request = c.at(packet.requestSequence, b[2], b[0],
                                            "packet_auth_request");
                        auto group = c.at(packet.groupsSequence, b[4], b[0],
                                          "packet_auth_group");
                        auto opened = c.at(packet.responseSequence, b[5], group,
                                           "packet_auth_response");
                        Values inputs{request, opened};
                        append_range(inputs, b.drop_front(6));
                        auto answer = c.call(response.authenticate, inputs,
                                             "packet_authenticate_one")[0];
                        c.finish(c.append(packet.answerSequence, b[1], answer,
                                          "packet_add_answer"),
                                 true);
                      });
               }));
         });
  }
};
} // namespace
Error checkOracleQueryPacket(const OracleVerificationContext &context,
                             const OracleQueryExchange &model,
                             const OracleQueryResponse &response,
                             func::FuncOp openOne,
                             ArrayRef<OracleMerkleFunctions> merkle,
                             uint64_t capacity,
                             const OracleQueryPacket &actual) {
  if (!layout(context, model, response, openOne, merkle, capacity, actual))
    return error("oracle-packet-body");
  Reader reader(context, model, response, openOne, merkle, capacity, actual);
  reader.group();
  reader.open();
  reader.authenticate();
  return reader.valid ? Error::success() : error("oracle-packet-body");
}
} // namespace zkc::protocol

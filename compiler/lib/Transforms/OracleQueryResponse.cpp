#include "OracleQueryResponse.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Support/Refusal.h"
#include <set>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
using Controller = OracleQueryController;
struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  const OracleQueryExchange &model;
  OracleQueryResponse result;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index;
  unsigned next = 0;
  Emitter(protocol_ir::ProtocolModuleOp unit, const OracleQueryExchange &model)
      : unit(unit), model(model), builder(unit.getContext()),
        bindings(unit, "_oracle_response_binding_"),
        index(IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned)) {}
  Error plan(OracleVirtualFunctionWork &work) {
    auto refuse = [] { return error("oracle-response-layout"); };
    if (model.arms.empty() || model.arms.size() > 32 ||
        model.state.size() > 505 || model.receiverStores.size() > 505)
      return error("oracle-response-capacity");
    if (model.state.size() < Controller::HeaderSize ||
        !all_of(ArrayRef<Type>(model.state).take_front(Controller::HeaderSize),
                [&](Type type) { return type == index; }))
      return refuse();
    for (auto types :
         {ArrayRef<Type>(model.state), ArrayRef<Type>(model.receiverStores)})
      if (!all_of(types, [&](Type type) {
            return type && type.getContext() == unit.getContext();
          }))
        return refuse();
    auto request = dyn_cast_or_null<data::VariantType>(model.request);
    auto response = dyn_cast_or_null<data::VariantType>(model.response);
    if (!request || !response || request.getContext() != unit.getContext() ||
        response.getContext() != unit.getContext() ||
        request.getAlternatives().size() != 1 ||
        request.getAlternatives()[0].getLabel().getValue() != "Record" ||
        !equal(request.getAlternatives()[0].getPayload(), Types(3, index)) ||
        response.getAlternatives().size() != model.arms.size())
      return refuse();
    auto signature = [&](func::FuncOp helper) -> FunctionType {
      if (!helper || helper->getParentOp() != unit || !helper.isPrivate() ||
          helper->hasAttr("runtime.region"))
        return {};
      return scopedDataSignature(helper);
    };
    uint64_t width =
        std::max(model.state.size() + 7, model.receiverStores.size() + 7);
    SmallVector<data::AlternativeAttr> alternatives;
    std::set<unsigned> constructors, slots;
    std::set<std::string> names;
    for (auto [ordinal, arm] : enumerate(model.arms)) {
      auto alternative = response.getAlternatives()[ordinal];
      auto reference = dyn_cast_or_null<data::VariantType>(arm.reference);
      if (!constructors.insert(arm.constructor).second ||
          !slots.insert(arm.receiverSlot).second ||
          !names.insert(arm.alternative).second || arm.opened.size() != 2 ||
          alternative.getLabel().getValue() != arm.alternative ||
          !equal(alternative.getPayload(), arm.opened) || !reference ||
          reference.getAlternatives().size() != 1 ||
          reference.getAlternatives()[0].getLabel().getValue() != "Record" ||
          !equal(reference.getAlternatives()[0].getPayload(),
                 Types(2, index)) ||
          arm.receiverSlot >= model.receiverStores.size())
        return refuse();
      auto lookup = signature(arm.receiverLookup);
      auto authenticate = signature(arm.authenticate);
      auto resume = signature(arm.resume);
      if (!lookup || !authenticate || !resume ||
          !equal(
              lookup.getInputs(),
              Types{arm.reference, model.receiverStores[arm.receiverSlot]}) ||
          arm.root >= lookup.getNumResults() ||
          arm.receiverRows >= lookup.getNumResults() ||
          lookup.getResult(arm.receiverRows) != index ||
          !equal(authenticate.getInputs(),
                 Types{lookup.getResult(arm.root), index, index, arm.opened[0],
                       arm.opened[1]}) ||
          authenticate.getNumResults() != 1)
        return refuse();
      if (lookup.getNumResults() > 512)
        return error("oracle-response-capacity");
      width = std::max<uint64_t>(width, lookup.getNumResults() + 8);
      auto answer = authenticate.getResult(0);
      if (arm.kind >= model.state.size() - Controller::HeaderSize)
        return refuse();
      auto arena = dyn_cast<data::SequenceType>(
          model.state[Controller::HeaderSize + arm.kind]);
      if (!arena || arena.getElementType() != answer)
        return refuse();
      Types inputs(model.state.begin(), model.state.end());
      append_range(inputs, Types(5, index));
      inputs.push_back(answer);
      if (!equal(resume.getInputs(), inputs) ||
          !equal(resume.getResults(), model.state))
        return refuse();
      alternatives.push_back(data::AlternativeAttr::get(
          unit.getContext(), builder.getStringAttr(arm.alternative),
          ArrayRef<Type>{answer}));
    }
    auto identity = data::importVariantIdentity(
        unit.getContext(),
        json::Array{"zkc.oracle.checked-answer/0",
                    data::exportVariantIdentity(response.getIdentity())});
    result.answer = identity
                        ? data::VariantType::getChecked(
                              unit.getLoc(), unit.getContext(), identity,
                              ArrayRef<data::AlternativeAttr>(alternatives))
                        : data::VariantType{};
    if (!result.answer)
      return refuse();
    // Reserve all specialized arms, outlined matches, guards and scoped
    // outcome plumbing before emission. Charge the caller's existing budget.
    uint64_t operations = 256 + 512 * model.arms.size();
    uint64_t slotsNeeded = operations * (width + 16);
    if (operations > work.operations || slotsNeeded > work.slots)
      return error("oracle-response-limit");
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
      name = "_oracle_response_" + label.str() + "_" + std::to_string(next++);
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
               ArrayRef<Attribute> parameters = {}) {
    auto binding =
        bindings.binding(builder, unit.getLoc(), {contract.str(), {}, ""});
    return c.invoke(
        "exec.apply", outputs, c.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  void requireEqual(Control &c, Value left, Value right, StringRef site) {
    auto predicate = apply(c, "index.equal", builder.getI1Type(), {left, right},
                           site.str() + "_equal")[0];
    apply(c, "control.require", {}, predicate, site);
  }
  void requireNumber(Control &c, Value value, unsigned expected,
                     StringRef site) {
    auto constant =
        apply(c, "index.constant", index, {}, site.str() + "_expected",
              {builder.getIntegerAttr(index, expected)})[0];
    requireEqual(c, value, constant, site);
  }
  Value pack(Control &c, Type type, StringRef alternative, ValueRange inputs,
             StringRef site) {
    return c.invoke(
        "exec.variant", type, c.scoped(inputs),
        {builder.getNamedAttr("alternative",
                              builder.getStringAttr(alternative)),
         builder.getNamedAttr("site", builder.getStringAttr(site))})[0];
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
  std::vector<std::string> alternatives() {
    std::vector<std::string> names;
    for (const auto &arm : model.arms)
      names.push_back(arm.alternative);
    return names;
  }
  void emitAuthenticate() {
    Types inputs{model.request, model.response};
    append_range(inputs, model.receiverStores);
    result.authenticate = function(
        "authenticate", inputs, result.answer, false,
        [&](Control &c, ValueRange args) {
          c.returned(c.match(
              args[0], args.drop_front(), result.answer, {"Record"},
              "authenticate_request", [&](unsigned) {
                Types types(3, index);
                types.push_back(model.response);
                append_range(types, model.receiverStores);
                return function(
                    "request", types, result.answer, true,
                    [&](Control &body, ValueRange request) {
                      Values captures(request.take_front(3));
                      append_range(captures, request.drop_front(4));
                      body.complete(body.match(
                          request[3], captures, result.answer, alternatives(),
                          "authenticate_response", [&](unsigned ordinal) {
                            const auto &arm = model.arms[ordinal];
                            Types types(arm.opened.begin(), arm.opened.end());
                            append_range(types, Types(3, index));
                            append_range(types, model.receiverStores);
                            return function(
                                "authenticate_arm", types, result.answer, true,
                                [&](Control &selected, ValueRange a) {
                                  std::string prefix =
                                      "constructor_" +
                                      std::to_string(arm.constructor) + "_";
                                  requireNumber(selected, a[2], arm.constructor,
                                                prefix + "request_constructor");
                                  auto reference =
                                      pack(selected, arm.reference, "Record",
                                           a.slice(2, 2), prefix + "anchor");
                                  auto stored =
                                      call(selected, arm.receiverLookup,
                                           {reference, a[5 + arm.receiverSlot]},
                                           prefix + "load_anchor");
                                  auto answer = call(selected, arm.authenticate,
                                                     {stored[arm.root],
                                                      stored[arm.receiverRows],
                                                      a[4], a[0], a[1]},
                                                     prefix + "authenticate");
                                  selected.complete(pack(
                                      selected, result.answer, arm.alternative,
                                      answer, prefix + "checked_answer"));
                                });
                          }));
                    });
              }));
        });
  }
  void emitResume() {
    Types inputs{model.request, result.answer};
    append_range(inputs, model.state);
    result.resume = function(
        "resume", inputs, model.state, false, [&](Control &c, ValueRange args) {
          c.returned(c.match(
              args[0], args.drop_front(), model.state, {"Record"},
              "resume_request", [&](unsigned) {
                Types types(3, index);
                types.push_back(result.answer);
                append_range(types, model.state);
                return function(
                    "request", types, model.state, true,
                    [&](Control &body, ValueRange request) {
                      Values captures(request.take_front(3));
                      append_range(captures, request.drop_front(4));
                      body.complete(body.match(
                          request[3], captures, model.state, alternatives(),
                          "resume_answer", [&](unsigned ordinal) {
                            const auto &arm = model.arms[ordinal];
                            Type answer = scopedDataSignature(arm.authenticate)
                                              .getResult(0);
                            Types types{answer};
                            append_range(types, Types(3, index));
                            append_range(types, model.state);
                            return function(
                                "resume_arm", types, model.state, true,
                                [&](Control &selected, ValueRange a) {
                                  std::string prefix =
                                      "constructor_" +
                                      std::to_string(arm.constructor) + "_";
                                  auto state = a.drop_front(4);
                                  requireNumber(selected,
                                                state[Controller::Phase],
                                                Controller::Request,
                                                prefix + "request_phase");
                                  requireNumber(selected,
                                                state[Controller::Constructor],
                                                arm.constructor,
                                                prefix + "state_constructor");
                                  requireNumber(
                                      selected, state[Controller::Kind],
                                      arm.kind, prefix + "request_kind");
                                  for (unsigned field = 0; field < 3; ++field)
                                    requireEqual(selected, state[field],
                                                 a[1 + field],
                                                 prefix + "request_field_" +
                                                     std::to_string(field));
                                  Values resumed(state);
                                  append_range(resumed, state.take_front(5));
                                  resumed.push_back(a[0]);
                                  selected.complete(call(selected, arm.resume,
                                                         resumed,
                                                         prefix + "resume"));
                                });
                          }));
                    });
              }));
        });
  }
};
} // namespace
Expected<OracleQueryResponse>
emitOracleQueryResponse(ModuleOp candidate, const OracleQueryExchange &model,
                        OracleVirtualFunctionWork &sharedBudget) {
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()))
    return error("oracle-response-source");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol ||
      failed(zkc::admitStage(candidate)))
    return error("oracle-response-source");
  Emitter emitter(unit, model);
  if (auto e = emitter.plan(sharedBudget))
    return std::move(e);
  emitter.emitAuthenticate();
  emitter.emitResume();
  return std::move(emitter.result);
}
} // namespace zkc::protocol

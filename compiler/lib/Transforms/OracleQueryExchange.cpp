#include "OracleQueryExchange.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
Expected<OracleQueryExchange>
planOracleQueryExchange(const OracleAnchorStorage &storage,
                        const OracleQueryController &receiver,
                        const OracleQueryController &holder,
                        ArrayRef<OracleMerkleFunctions> merkle) {
  auto refuse = [] { return error("oracle-common-communication-profile"); };
  OracleQueryExchange result;
  result.holder = holder.role;
  result.state = receiver.state;
  result.receiverStores = receiver.stores;
  SmallVector<data::AlternativeAttr> alternatives;
  json::Array constructors;
  for (auto [slot, item] : enumerate(receiver.constructors)) {
    const auto &anchor = storage.constructors[item.source];
    if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual)
      continue;
    if (anchor.scheme.empty() || anchor.holder == receiver.role ||
        anchor.holder != holder.role || item.source >= merkle.size())
      return refuse();
    unsigned source = item.source;
    auto held = find_if(holder.constructors, [&](const auto &other) {
      return other.source == source;
    });
    if (held == holder.constructors.end())
      return refuse();
    auto functions = merkle[item.source];
    if (!functions.open || !functions.authenticate ||
        item.kind >= receiver.resume.size())
      return refuse();
    auto reference = oracleReferenceType(anchor.kind);
    if (!reference)
      return reference.takeError();
    OracleQueryExchange::Arm arm;
    arm.constructor = item.source;
    arm.kind = item.kind;
    arm.receiverSlot = slot;
    arm.alternative = "Constructor" + std::to_string(item.source);
    arm.reference = *reference;
    auto payload = cast<exec::OutcomeType>(functions.open.getResultTypes()[0])
                       .getPayload();
    arm.opened.assign(payload.begin(), payload.end());
    if (arm.opened.size() != 2)
      return refuse();
    auto field = [&](unsigned role, StringRef name) {
      const auto &fields = anchor.roles[role].fields;
      return unsigned(
          find_if(fields,
                  [&](const auto &field) { return field.name == name; }) -
          fields.begin());
    };
    arm.openingState = field(held->role, "opening_state");
    arm.holderRows = field(held->role, "shape.rows");
    arm.root = field(item.role, "root");
    arm.receiverRows = field(item.role, "shape.rows");
    if (arm.openingState >= anchor.roles[held->role].fields.size() ||
        arm.holderRows >= anchor.roles[held->role].fields.size() ||
        arm.root >= anchor.roles[item.role].fields.size() ||
        arm.receiverRows >= anchor.roles[item.role].fields.size())
      return refuse();
    arm.holderLookup = held->lookup;
    arm.receiverLookup = item.lookup;
    arm.open = functions.open;
    arm.authenticate = functions.authenticate;
    arm.resume = receiver.resume[item.kind];
    auto *context = arm.opened.front().getContext();
    alternatives.push_back(data::AlternativeAttr::get(
        context, StringAttr::get(context, arm.alternative), arm.opened));
    constructors.push_back(std::to_string(item.source));
    result.holderStores.push_back(anchor.roles[held->role].sequence);
    result.arms.push_back(std::move(arm));
  }
  if (result.arms.empty())
    return refuse();
  auto nominal = [&](StringRef family) {
    return json::Array{family, toHex(storage.entry, true),
                       toHex(receiver.role, true), toHex(holder.role, true),
                       json::Array(constructors)};
  };
  if (alternatives.size() > 32)
    return refuse();
  auto *context = receiver.state.front().getContext();
  auto requestIdentity = data::importVariantIdentity(
      context, nominal("zkc.oracle.opening-request/0"));
  auto responseIdentity = data::importVariantIdentity(
      context, nominal("zkc.oracle.opening-response/0"));
  if (!requestIdentity || !responseIdentity)
    return refuse();
  auto index = IntegerType::get(context, 64, IntegerType::Unsigned);
  auto record =
      data::AlternativeAttr::get(context, StringAttr::get(context, "Record"),
                                 ArrayRef<Type>{index, index, index});
  result.request = data::VariantType::getChecked(
      UnknownLoc::get(context), context, requestIdentity,
      ArrayRef<data::AlternativeAttr>{record});
  result.response = data::VariantType::getChecked(
      UnknownLoc::get(context), context, responseIdentity,
      ArrayRef<data::AlternativeAttr>(alternatives));
  if (!result.request || !result.response)
    return refuse();
  return result;
}
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
struct Emitter {
  protocol_ir::ProtocolModuleOp unit;
  const OracleExchangeRecipe &recipe;
  const OracleQueryExchange &model;
  OpBuilder builder;
  mathematical::RealizationEmitter bindings;
  Type index;
  unsigned next = 0;
  Emitter(ModuleOp module, const OracleExchangeRecipe &recipe)
      : unit(cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front())),
        recipe(recipe), model(*recipe.exchange), builder(module.getContext()),
        bindings(unit, "_oracle_exchange_binding_"),
        index(
            IntegerType::get(module.getContext(), 64, IntegerType::Unsigned)) {}
  func::FuncOp function(TypeRange inputs, TypeRange outputs, bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name = recipe.name;
    if (region)
      do {
        name = recipe.name + "_arm_" + std::to_string(next++);
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
  Value number(Control &c, unsigned value, StringRef site) {
    return apply(c, "index.constant", index, {}, site,
                 {builder.getIntegerAttr(index, value)})[0];
  }
  Value equal(Control &c, Value actual, unsigned expected, StringRef site) {
    auto constant = number(c, expected, site.str() + "_expected");
    return apply(c, "index.equal", builder.getI1Type(), {actual, constant},
                 site)[0];
  }
  void require(Control &c, Value actual, unsigned expected, StringRef site) {
    apply(c, "control.require", {}, equal(c, actual, expected, site),
          site.str() + "_guard");
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
  // The last arm guards its tag too; an unknown tag never selects a default
  // constructor. Only the selected branch looks up a store or opens a row.
  Value dispatch(Control &c, ValueRange inputs, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    std::string prefix = "constructor_" + std::to_string(arm.constructor) + "_";
    auto selected =
        equal(c, inputs[0], arm.constructor, prefix + "select_constructor");
    if (ordinal + 1 == model.arms.size()) {
      apply(c, "control.require", {}, selected, prefix + "admit_constructor");
      return opening(c, inputs, ordinal);
    }
    return c.conditional(
        selected, inputs, model.response, prefix + "dispatch",
        [&](unsigned branch) {
          return function(
              inputs.getTypes(), model.response, true,
              [&](Control &body, ValueRange args) {
                body.complete(branch == 0 ? opening(body, args, ordinal)
                                          : dispatch(body, args, ordinal + 1));
              });
        })[0];
  }
  Value opening(Control &c, ValueRange inputs, unsigned ordinal) {
    const auto &arm = model.arms[ordinal];
    std::string prefix = "constructor_" + std::to_string(arm.constructor) + "_";
    auto reference = pack(c, arm.reference, "Record", inputs.take_front(2),
                          prefix + "anchor");
    auto held = call(c, arm.holderLookup, {reference, inputs[3 + ordinal]},
                     prefix + "load_anchor");
    auto row = call(c, arm.open,
                    {held[arm.openingState], held[arm.holderRows], inputs[2]},
                    prefix + "open");
    return pack(c, model.response, arm.alternative, row, prefix + "response");
  }
  func::FuncOp emit() {
    return function(
        recipe.inputs, recipe.outputs, false,
        [&](Control &c, ValueRange inputs) {
          if (recipe.action == OracleExchangeAction::Open) {
            Types captures(3, index);
            append_range(captures, model.holderStores);
            c.returned(c.match(inputs[0], inputs.drop_front(), model.response,
                               {"Record"}, "request", [&](unsigned) {
                                 return function(
                                     captures, model.response, true,
                                     [&](Control &body, ValueRange args) {
                                       body.complete(dispatch(body, args, 0));
                                     });
                               }));
            return;
          }
          std::vector<std::string> alternatives;
          for (const auto &arm : model.arms)
            alternatives.push_back(arm.alternative);
          c.returned(c.match(
              inputs[0], inputs.drop_front(), model.state, alternatives,
              "response", [&](unsigned ordinal) {
                const auto &arm = model.arms[ordinal];
                Types types(arm.opened.begin(), arm.opened.end());
                append_range(types, model.state);
                append_range(types, model.receiverStores);
                return function(
                    types, model.state, true,
                    [&](Control &body, ValueRange args) {
                      using C = OracleQueryController;
                      std::string prefix = "constructor_" +
                                           std::to_string(arm.constructor) +
                                           "_";
                      auto state =
                          args.drop_front(2).take_front(model.state.size());
                      auto stores = args.drop_front(2 + model.state.size());
                      require(body, state[C::Phase], C::Request,
                              prefix + "request_phase");
                      require(body, state[C::Constructor], arm.constructor,
                              prefix + "request_constructor");
                      require(body, state[C::Kind], arm.kind,
                              prefix + "request_kind");
                      auto reference =
                          pack(body, arm.reference, "Record",
                               {state[C::Constructor], state[C::Instance]},
                               prefix + "anchor");
                      auto stored = call(body, arm.receiverLookup,
                                         {reference, stores[arm.receiverSlot]},
                                         prefix + "load_anchor");
                      auto answer =
                          call(body, arm.authenticate,
                               {stored[arm.root], stored[arm.receiverRows],
                                state[C::Position], args[0], args[1]},
                               prefix + "authenticate");
                      Values resumed(state.begin(), state.end());
                      append_range(resumed, state.take_front(5));
                      resumed.push_back(answer[0]);
                      body.complete(
                          call(body, arm.resume, resumed, prefix + "resume"));
                    });
              }));
        });
  }
};
} // namespace
func::FuncOp emitOracleQueryExchange(ModuleOp module,
                                     const OracleExchangeRecipe &recipe) {
  return Emitter(module, recipe).emit();
}
} // namespace zkc::protocol

#include "OracleQueryDemand.h"
#include "RealizationEmission.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using Demand = OracleQueryDemand;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
struct Emitter {
  ModuleOp candidate;
  const OracleAnchorStorage &storage;
  const OracleQueryController &controller;
  OracleQueryDemand result;
  pir::ProtocolModuleOp unit;
  OpBuilder builder;
  Location loc;
  Type index, scope;
  mathematical::RealizationEmitter bindings;
  unsigned next = 0, rootKind = 0;
  Emitter(ModuleOp candidate, const OracleAnchorStorage &storage,
          const OracleQueryController &controller)
      : candidate(candidate), storage(storage), controller(controller),
        unit(cast<pir::ProtocolModuleOp>(candidate.getBody()->front())),
        builder(candidate.getContext()), loc(candidate.getLoc()),
        index(IntegerType::get(candidate.getContext(), 64,
                               IntegerType::Unsigned)),
        scope(runtime::ScopeType::get(candidate.getContext())),
        bindings(unit, "_oracle_demand_binding_") {}
  Error plan(pir::OracleKindAttr root, OracleVirtualFunctionWork &work) {
    auto capacity = controller.capacity;
    // A node enters once and returns once; final root completion adds at most
    // one transition. Request consumption is outside advance. A frame is
    // appended only for a declared edge. Thus 2*nodes+1 bounds every advance,
    // including an entirely empty tree, without index or native range overflow.
    if (!capacity.nodes || capacity.leaves > capacity.nodes ||
        capacity.nodes > (1048576 - 1) / 2 || capacity.leaves >= 1048576)
      return error("oracle-demand-capacity");
    if (!root || root.getContext() != candidate.getContext() ||
        root.getIdentity() != "table" || controller.kinds.empty() ||
        controller.kinds.size() > 512 || controller.constructors.size() > 512 ||
        controller.stores.size() != controller.constructors.size())
      return error("oracle-demand-layout");
    auto found = find_if(controller.kinds, [&](auto kind) {
      return sameOracleReferenceKind(root, kind);
    });
    if (found == controller.kinds.end())
      return error("oracle-demand-layout");
    rootKind = found - controller.kinds.begin();
    uint64_t queries = 0, width = 0;
    for (auto [ordinal, item] : enumerate(controller.constructors)) {
      if (item.source >= storage.constructors.size())
        return error("oracle-demand-layout");
      const auto &anchor = storage.constructors[item.source];
      if (item.role >= anchor.roles.size() ||
          item.kind >= controller.kinds.size() ||
          !sameOracleReferenceKind(anchor.kind, controller.kinds[item.kind]) ||
          !item.lookup || item.lookup->getParentOp() != unit)
        return error("oracle-demand-layout");
      const auto &owner = anchor.roles[item.role];
      if (owner.role != controller.role ||
          owner.sequence != controller.stores[ordinal] ||
          !any_of(owner.fields, [&](const auto &field) {
            return field.name == "shape.rows" && field.type == index;
          }))
        return error("oracle-demand-layout");
      width = std::max<uint64_t>(width, owner.fields.size());
      queries += item.functions.queries.size();
      for (const auto &q : item.functions.queries) {
        if (!q.position || q.position->getParentOp() != unit ||
            !any_of(controller.kinds,
                    [&](auto kind) {
                      return sameOracleReferenceKind(q.kind, kind);
                    }) ||
            !any_of(owner.fields, [&](const auto &field) {
              return field.name == "source." + std::to_string(q.source);
            }))
          return error("oracle-demand-layout");
      }
    }
    uint64_t ports = Demand::HeaderSize + 1 + controller.stores.size();
    // Conservative reservation for all specialized dispatch, scoped outcome
    // plumbing and record unpacking. No emission resets the caller's budget.
    uint64_t operations =
        512 + 512 * controller.constructors.size() + 1024 * queries;
    if (ports + width > 512 || ports + 1 > 512 || queries > 512 ||
        operations > work.operations ||
        operations * (ports + width + 16) > work.slots)
      return error("oracle-demand-limit");
    work.operations -= operations;
    work.slots -= operations * (ports + width + 16);
    VariantDescriptor descriptor{
        json::Array{"zkc.oracle.demand-frame/0", toHex(storage.entry, true),
                    toHex(controller.role, true)},
        {{"Record", std::vector<std::string>(Demand::FrameSize, "index")}}};
    auto spelling = encodeVariant(descriptor);
    if (!spelling || spelling->size() > 4 * 1024 * 1024)
      return error("oracle-demand-layout");
    auto nominal =
        data::importVariantIdentity(candidate.getContext(), descriptor.nominal);
    auto arm = data::AlternativeAttr::get(candidate.getContext(),
                                          builder.getStringAttr("Record"),
                                          Types(Demand::FrameSize, index));
    result.frame = nominal ? data::VariantType::getChecked(
                                 loc, candidate.getContext(), nominal,
                                 ArrayRef<data::AlternativeAttr>{arm})
                           : data::VariantType{};
    if (!result.frame)
      return error("oracle-demand-layout");
    result.sequence = constructLogicalType(
        [&] { return emitError(loc); }, candidate.getContext(),
        {"sequence", {TypeAttr::get(result.frame)}});
    if (!result.sequence)
      return error("oracle-demand-layout");
    result.state.assign(Demand::HeaderSize, index);
    result.state.push_back(result.sequence);
    return Error::success();
  }
  unsigned kindNumber(pir::OracleKindAttr kind) {
    for (auto [ordinal, current] : enumerate(controller.kinds))
      if (sameOracleReferenceKind(kind, current))
        return ordinal;
    llvm_unreachable("checked controller kind inventory");
  }
  Types allTypes() {
    Types types(result.state.begin(), result.state.end());
    append_range(types, controller.stores);
    return types;
  }
  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_demand_" + label.str() + "_" + std::to_string(next++);
    } while (SymbolTable::lookupSymbolIn(unit, name));
    Types formals{scope};
    append_range(formals, inputs);
    auto outcome =
        exec::OutcomeType::get(candidate.getContext(), Types(outputs));
    auto helper = func::FuncOp::create(
        builder, loc, name, builder.getFunctionType(formals, outcome));
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
  Values apply(Control &control, StringRef contract, TypeRange outputs,
               ValueRange inputs, StringRef site,
               ArrayRef<Attribute> statics = {},
               ArrayRef<Attribute> parameters = {}) {
    auto binding = bindings.binding(
        builder, loc, {contract.str(), SmallVector<Attribute>(statics), ""});
    return control.invoke(
        "exec.apply", outputs, control.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(parameters)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  Value number(Control &c, uint64_t value, StringRef site) {
    return apply(c, "index.constant", index, {}, site, {},
                 {builder.getIntegerAttr(index, value)})
        .front();
  }
  Value compare(Control &c, StringRef contract, Value a, Value b,
                StringRef site) {
    return apply(c, contract, builder.getI1Type(), {a, b}, site).front();
  }
  void require(Control &c, Value condition, StringRef site) {
    apply(c, "control.require", {}, condition, site);
  }
  void equal(Control &c, Value actual, uint64_t expected, StringRef site) {
    auto value = number(c, expected, site.str() + "_expected");
    require(c, compare(c, "index.equal", actual, value, site.str() + "_equal"),
            site);
  }
  Values call(Control &c, func::FuncOp helper, ValueRange inputs,
              StringRef site, bool math = false) {
    auto outputs =
        math ? helper.getResultTypes()
             : cast<exec::OutcomeType>(helper.getResultTypes().front())
                   .getPayload();
    return c.invoke(
        math ? "exec.compute" : "func.call", outputs, c.scoped(inputs),
        {builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
         builder.getNamedAttr(math ? "site" : "runtime.site",
                              builder.getStringAttr(site))});
  }
  Value pack(Control &c, Type type, ValueRange fields, StringRef site) {
    return c
        .invoke("exec.variant", type, c.scoped(fields),
                {builder.getNamedAttr("alternative",
                                      builder.getStringAttr("Record")),
                 builder.getNamedAttr("site", builder.getStringAttr(site))})
        .front();
  }
  Values unpack(Control &c, Value record, TypeRange fields, StringRef site) {
    return c.match(record, {}, fields, {"Record"}, site, [&](unsigned) {
      return function(
          "unpack", fields, fields, true,
          [&](Control &body, ValueRange values) { body.complete(values); });
    });
  }
  Attribute element(Type sequence) {
    return TypeAttr::get(cast<data::SequenceType>(sequence).getElementType());
  }
  Value empty(Control &c, Type sequence, StringRef site) {
    return apply(c, "sequence.empty", sequence, {}, site, {element(sequence)})
        .front();
  }
  Value append(Control &c, Value sequence, Value value, StringRef site) {
    return apply(c, "sequence.append", sequence.getType(), {sequence, value},
                 site, {element(sequence.getType())})
        .front();
  }
  Value at(Control &c, Value sequence, Value offset, Type type,
           StringRef site) {
    return apply(c, "sequence.at", type, {sequence, offset}, site,
                 {element(sequence.getType())})
        .front();
  }
  Value length(Control &c, Value sequence, StringRef site) {
    return apply(c, "sequence.length", index, sequence, site,
                 {element(sequence.getType())})
        .front();
  }
  Values state(ValueRange values) {
    return Values(values.take_front(result.state.size()));
  }
  ValueRange stores(ValueRange values) {
    return values.drop_front(result.state.size());
  }
  Values load(Control &c, unsigned constructor, Value tag, Value instance,
              Value store) {
    auto &item = controller.constructors[constructor];
    return call(c, item.lookup, {tag, instance, store}, "load_anchor");
  }
  unsigned field(unsigned constructor, StringRef name) {
    const auto &item = controller.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (f.name == name)
        return i;
    llvm_unreachable("planned anchor field");
  }
  Values parameters(unsigned constructor, ValueRange record, Value position) {
    Values inputs;
    const auto &item = controller.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (StringRef(f.name).starts_with("parameter."))
        inputs.push_back(record[i]);
    inputs.push_back(position);
    return inputs;
  }
  void child(Control &c, Values &values, unsigned constructor, unsigned query,
             ValueRange record) {
    const auto &q =
        controller.constructors[constructor].functions.queries[query];
    auto offset = length(c, values[Demand::Frames], "frame_index");
    auto nextChild = number(c, query + 1, "next_child");
    Values saved{values[Demand::Constructor], values[Demand::Instance],
                 values[Demand::Position], nextChild,
                 values[Demand::Continuation]};
    auto packed = pack(c, result.frame, saved, "frame_record");
    values[Demand::Frames] =
        append(c, values[Demand::Frames], packed, "save_frame");
    auto one = number(c, 1, "continuation_offset");
    auto continuation =
        apply(c, "index.add", index, {offset, one}, "child_continuation")
            .front();
    auto position =
        call(c, q.position,
             parameters(constructor, record, values[Demand::Position]),
             "child_position", true)
            .front();
    auto reference = unpack(
        c, record[field(constructor, "source." + std::to_string(q.source))],
        TypeRange{index, index}, "child_reference");
    values[Demand::Constructor] = reference[0];
    values[Demand::Instance] = reference[1];
    values[Demand::Position] = position;
    values[Demand::Kind] = number(c, kindNumber(q.kind), "child_kind");
    values[Demand::Continuation] = continuation;
    values[Demand::Phase] = number(c, Demand::Enter, "enter_child");
  }
  func::FuncOp enter(unsigned constructor) {
    return function(
        "enter", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto values = state(inputs);
          const auto &item = controller.constructors[constructor];
          equal(c, values[Demand::Kind], item.kind, "kind");
          auto record =
              load(c, constructor, values[Demand::Constructor],
                   values[Demand::Instance], stores(inputs)[constructor]);
          auto valid =
              compare(c, "index.less", values[Demand::Position],
                      record[field(constructor, "shape.rows")], "domain");
          Types captures = allTypes();
          for (auto value : record)
            captures.push_back(value.getType());
          Values arguments(inputs);
          append_range(arguments, record);
          // Occurrences are unique across this helper and its outlined regions.
          // Keep the branch distinct from the predicate's "domain" occurrence.
          auto nextState = c.conditional(
              valid, arguments, result.state, "domain_branch",
              [&](unsigned branch) {
                return function(
                    "domain_region", captures, result.state, true,
                    [&](Control &body, ValueRange captured) {
                      auto nextState = state(captured);
                      if (branch == 1)
                        nextState[Demand::Phase] =
                            number(body, Demand::DomainCut, "domain_cut");
                      else if (storage.constructors[item.source].constructor !=
                               OracleAnchorConstructor::Kind::Virtual)
                        nextState[Demand::Phase] =
                            number(body, Demand::Request, "request");
                      else if (item.functions.queries.empty())
                        nextState[Demand::Phase] =
                            number(body, Demand::Return, "empty_return");
                      else
                        child(body, nextState, constructor, 0,
                              captured.drop_front(allTypes().size()));
                      body.complete(nextState);
                    });
              });
          c.returned(nextState);
        });
  }
  Types returnTypes() {
    auto types = allTypes();
    types.push_back(index); // Saved next child ordinal, not an answer index.
    return types;
  }
  func::FuncOp parent(unsigned constructor) {
    const auto &item = controller.constructors[constructor];
    SmallVector<std::pair<unsigned, func::FuncOp>> cases;
    for (unsigned nextChild = 1; nextChild <= item.functions.queries.size();
         ++nextChild) {
      auto leaf = function(
          "parent_child", returnTypes(), result.state, false,
          [&](Control &c, ValueRange inputs) {
            auto values = state(inputs);
            equal(c, values[Demand::Kind],
                  kindNumber(item.functions.queries[nextChild - 1].kind),
                  "returned_kind");
            values[Demand::Kind] = number(c, item.kind, "parent_kind");
            if (nextChild == item.functions.queries.size())
              values[Demand::Phase] =
                  number(c, Demand::Return, "return_parent");
            else {
              auto record = load(c, constructor, values[Demand::Constructor],
                                 values[Demand::Instance],
                                 inputs[result.state.size() + constructor]);
              child(c, values, constructor, nextChild, record);
            }
            c.returned(values);
          });
      cases.push_back({nextChild, leaf});
    }
    return dispatch("child_dispatch", returnTypes().size() - 1, cases,
                    returnTypes(), result.state);
  }
  func::FuncOp returned() {
    SmallVector<std::pair<unsigned, func::FuncOp>> cases;
    for (auto [ordinal, item] : enumerate(controller.constructors))
      if (!item.functions.queries.empty())
        cases.push_back({item.source, parent(ordinal)});
    auto selected = dispatch("parent_dispatch", Demand::Constructor, cases,
                             returnTypes(), result.state);
    return function(
        "returned", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto zero = number(c, 0, "root_continuation");
          auto root = compare(c, "index.equal", inputs[Demand::Continuation],
                              zero, "is_root");
          auto nextState = c.conditional(
              root, inputs, result.state, "return", [&](unsigned branch) {
                return function(
                    "return_region", allTypes(), result.state, true,
                    [&](Control &body, ValueRange captured) {
                      auto values = state(captured);
                      if (branch == 0) {
                        equal(body, values[Demand::Kind], rootKind,
                              "root_kind");
                        values[Demand::Phase] =
                            number(body, Demand::Completed, "completed");
                        body.complete(values);
                        return;
                      }
                      auto one = number(body, 1, "continuation_offset");
                      auto offset = apply(body, "index.sub", index,
                                          {values[Demand::Continuation], one},
                                          "frame_index")
                                        .front();
                      auto saved = at(body, values[Demand::Frames], offset,
                                      result.frame, "load_frame");
                      auto frame =
                          unpack(body, saved, Types(Demand::FrameSize, index),
                                 "frame");
                      values[Demand::Constructor] =
                          frame[Demand::ParentConstructor];
                      values[Demand::Instance] = frame[Demand::ParentInstance];
                      values[Demand::Position] = frame[Demand::ParentPosition];
                      values[Demand::Continuation] =
                          frame[Demand::ParentContinuation];
                      append_range(values, stores(captured));
                      values.push_back(frame[Demand::NextChild]);
                      body.complete(
                          call(body, selected, values, "restore_parent"));
                    });
              });
          c.returned(nextState);
        });
  }
  // Branch regions belong to this one callable. Do not route every tree edge
  // through another helper call carrying the complete controller state.
  func::FuncOp dispatch(StringRef label, unsigned selector,
                        ArrayRef<std::pair<unsigned, func::FuncOp>> cases,
                        TypeRange formals, TypeRange outputs,
                        bool region = false, StringRef prefix = {}) {
    return function(
        label, formals, outputs, region, [&](Control &c, ValueRange inputs) {
          auto finish = [&](ValueRange values) {
            if (region)
              c.complete(values);
            else
              c.returned(values);
          };
          if (cases.empty()) {
            c.reject("refused", prefix.str() + "no_constructor");
            return;
          }
          if (cases.size() == 1) {
            equal(c, inputs[selector], cases.front().first,
                  prefix.str() + "selected");
            finish(
                call(c, cases.front().second, inputs, prefix.str() + "case"));
            return;
          }
          auto middle = cases.size() / 2;
          auto pivot = number(c, cases[middle].first, prefix.str() + "pivot");
          auto left = compare(c, "index.less", inputs[selector], pivot,
                              prefix.str() + "partition");
          auto values = c.conditional(
              left, inputs, outputs, prefix.str() + "dispatch",
              [&](unsigned branch) {
                auto subset = branch == 0 ? cases.take_front(middle)
                                          : cases.drop_front(middle);
                return dispatch(label, selector, subset, formals, outputs, true,
                                prefix.str() +
                                    (branch == 0 ? "left_" : "right_"));
              });
          finish(values);
        });
  }
  func::FuncOp dispatch(StringRef label, unsigned selector,
                        ArrayRef<std::pair<unsigned, func::FuncOp>> cases) {
    return dispatch(label, selector, cases, allTypes(), result.state);
  }
  void emitInitialize(pir::OracleKindAttr root) {
    auto reference = cantFail(oracleReferenceType(root));
    result.initialize =
        function("initialize", TypeRange{reference, index}, result.state, false,
                 [&](Control &c, ValueRange inputs) {
                   auto reference =
                       unpack(c, inputs[0], TypeRange{index, index}, "root");
                   auto zero = number(c, 0, "initial");
                   auto kind = number(c, rootKind, "root_kind");
                   Values values{reference[0], reference[1], inputs[1],
                                 kind,         zero,         zero};
                   values.push_back(empty(c, result.sequence, "empty_frames"));
                   c.returned(values);
                 });
    result.consume = function(
        "consume", result.state, result.state, false,
        [&](Control &c, ValueRange inputs) {
          equal(c, inputs[Demand::Phase], Demand::Request, "suspended");
          auto values = state(inputs);
          values[Demand::Phase] = number(c, Demand::Return, "consumed");
          c.returned(values);
        });
  }
  void emitAdvance() {
    SmallVector<std::pair<unsigned, func::FuncOp>> enters;
    for (auto [i, item] : enumerate(controller.constructors))
      enters.push_back({item.source, enter(i)});
    auto entering = dispatch("enter_dispatch", Demand::Constructor, enters);
    auto returning = returned();
    auto step = [&](Control &c, ValueRange inputs) {
      auto zero = number(c, Demand::Enter, "enter_phase");
      auto enteringPhase =
          compare(c, "index.equal", inputs[Demand::Phase], zero, "phase");
      auto next = c.conditional(
          enteringPhase, inputs, result.state, "step", [&](unsigned branch) {
            return function(
                "step_region", allTypes(), result.state, true,
                [&](Control &body, ValueRange captures) {
                  body.complete(call(
                      body, branch == 0 ? entering : returning, captures,
                      branch == 0 ? "enter_transition" : "return_transition"));
                });
          });
      return next;
    };
    result.advance = function(
        "advance", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto zero = number(c, 0, "lower");
          auto two = number(c, Demand::Request, "suspension_phase");
          require(c,
                  compare(c, "index.less", inputs[Demand::Phase], two,
                          "can_advance"),
                  "admit_advance");
          auto upper =
              number(c, controller.capacity.nodes * 2 + 1, "transition_bound");
          auto next = c.loop(
              zero, upper, state(inputs), stores(inputs), result.state, true,
              "advance", [&](unsigned) {
                Types inputs{index};
                append_range(inputs, allTypes());
                Types outputs{builder.getI1Type()};
                append_range(outputs, result.state);
                return function(
                    "advance_iteration", inputs, outputs, true,
                    [&](Control &body, ValueRange captured) {
                      auto values = step(body, captured.drop_front());
                      auto threshold = number(body, Demand::Request,
                                              "iteration_suspension_phase");
                      auto proceed =
                          compare(body, "index.less", values[Demand::Phase],
                                  threshold, "continuing");
                      Values yielded{proceed};
                      append_range(yielded, values);
                      body.complete(yielded);
                    });
              });
          auto one = number(c, Demand::Return, "return_phase");
          require(c,
                  compare(c, "index.less", one, next[Demand::Phase],
                          "stopped_advancing"),
                  "complete_advance");
          c.returned(next);
        });
  }
};
} // namespace
Expected<OracleQueryDemand>
emitOracleQueryDemand(ModuleOp candidate, const OracleAnchorStorage &storage,
                      const OracleQueryController &controller,
                      pir::OracleKindAttr root,
                      OracleVirtualFunctionWork &work) {
  if (!candidate || !hasSingleElement(candidate.getBody()->getOperations()))
    return error("oracle-demand-source");
  auto unit = dyn_cast<pir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!unit || unit.getProfile() != pir::Profile::Protocol ||
      failed(zkc::admitStage(candidate)))
    return error("oracle-demand-source");
  Emitter emitter(candidate, storage, controller);
  if (auto e = emitter.plan(root, work))
    return std::move(e);
  emitter.emitInitialize(root);
  emitter.emitAdvance();
  return std::move(emitter.result);
}
} // namespace zkc::protocol

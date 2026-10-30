#include "OracleQueryController.h"
#include "CollectionRealization.h"
#include "OracleTableRead.h"
#include "RealizationEmission.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
using Controller = OracleQueryController;
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Control = exec::ScopedExecutionBuilder;
struct Emitter {
  ModuleOp candidate, prepared;
  const OracleAnchorStorage &storage;
  OracleQueryController result;
  pir::ProtocolModuleOp unit, original;
  OpBuilder builder;
  Location loc;
  Type index, scope;
  mathematical::RealizationEmitter bindings;
  unsigned next = 0;
  uint64_t metadataRemaining = 4 * 1024 * 1024;
  Emitter(ModuleOp candidate, ModuleOp prepared,
          const OracleAnchorStorage &storage, StringRef role,
          OracleQuerySize capacity, OracleControllerAccess access)
      : candidate(candidate), prepared(prepared), storage(storage),
        unit(cast<pir::ProtocolModuleOp>(candidate.getBody()->front())),
        original(cast<pir::ProtocolModuleOp>(prepared.getBody()->front())),
        builder(candidate.getContext()), loc(candidate.getLoc()),
        index(IntegerType::get(candidate.getContext(), 64,
                               IntegerType::Unsigned)),
        scope(runtime::ScopeType::get(candidate.getContext())),
        bindings(unit, "_oracle_controller_binding_") {
    result.role = role.str();
    result.access = access;
    result.capacity = capacity;
  }
  Expected<Type> sequence(Type type) {
    auto encoded = encodeBoundType(type, false);
    if (!encoded)
      return encoded.takeError();
    auto bound = parseBoundType("sequence<" + encoded->spelling() + ">", false);
    if (!bound)
      return bound.takeError();
    auto decoded = decodeBoundType(candidate.getContext(), *bound);
    if (!decoded)
      return error("oracle-controller-layout");
    return decoded;
  }
  Expected<unsigned> kind(pir::OracleKindAttr kind) {
    if (!kind || kind.getIdentity() != "table")
      return error("oracle-controller-layout");
    auto reference = oracleReferenceType(kind);
    if (!reference)
      return reference.takeError();
    for (auto [i, existing] : enumerate(result.kinds)) {
      auto other = oracleReferenceType(existing);
      if (!other)
        return other.takeError();
      if (*other == *reference)
        return i;
    }
    auto answers = sequence(kind.getAnswerType());
    if (!answers)
      return answers.takeError();
    result.kinds.push_back(kind);
    result.answers.push_back(*answers);
    return result.kinds.size() - 1;
  }
  Error plan(pir::OracleKindAttr root, OracleVirtualFunctionWork &work) {
    auto rootKind = kind(root);
    if (!rootKind)
      return rootKind.takeError();
    for (auto [source, constructor] : enumerate(storage.constructors)) {
      auto role = find_if(constructor.roles, [&](const auto &owner) {
        return owner.role == result.role;
      });
      if (role == constructor.roles.end() ||
          (result.access == OracleControllerAccess::Holder &&
           constructor.holder != result.role))
        continue;
      auto k = kind(constructor.kind);
      if (!k)
        return k.takeError();
      OracleQueryControllerConstructor item{
          unsigned(source),
          unsigned(role - constructor.roles.begin()),
          *k,
          unsigned(result.continuations.size()),
          {},
          {}};
      uint64_t lookupWork = 20 + 2 * role->fields.size();
      if (result.constructors.size() >= 512 || lookupWork > work.operations)
        return error("oracle-controller-limit");
      work.operations -= lookupWork;
      auto lookup =
          emitOracleAnchorLookup(candidate, storage, source, item.role);
      if (!lookup)
        return lookup.takeError();
      item.lookup = *lookup;
      if (constructor.constructor == OracleAnchorConstructor::Kind::Virtual) {
        auto definition = dyn_cast_or_null<pir::OracleDefinitionOp>(
            SymbolTable::lookupSymbolIn(original, constructor.declaration));
        auto functions =
            emitOracleVirtualFunctions(candidate, definition, work);
        if (!functions)
          return functions.takeError();
        item.functions = std::move(*functions);
        if (result.continuations.size() + item.functions.queries.size() +
                result.kinds.size() + result.constructors.size() +
                Controller::HeaderSize >
            512)
          return error("oracle-controller-limit");
        std::vector<unsigned> previous;
        for (auto [ordinal, query] : enumerate(item.functions.queries)) {
          auto childKind = kind(query.kind);
          if (!childKind)
            return childKind.takeError();
          std::vector<std::string> fields(4 + previous.size(), "index");
          VariantDescriptor descriptor{
              json::Array{"zkc.oracle.continuation/0",
                          toHex(storage.entry, true), toHex(result.role, true),
                          std::to_string(source), std::to_string(ordinal)},
              {{"Record", std::move(fields)}}};
          auto spelling = encodeVariant(descriptor);
          if (!spelling)
            return error("oracle-controller-layout");
          if (spelling->size() > metadataRemaining)
            return error("oracle-controller-limit");
          metadataRemaining -= spelling->size();
          Type record =
              data::importVariantType(candidate.getContext(), descriptor);
          auto arena = sequence(record);
          if (!arena)
            return arena.takeError();
          result.continuations.push_back({unsigned(result.constructors.size()),
                                          unsigned(ordinal), record, *arena,
                                          previous});
          previous.push_back(*childKind);
        }
      }
      result.stores.push_back(role->sequence);
      result.constructors.push_back(std::move(item));
    }
    result.state.assign(Controller::HeaderSize, index);
    append_range(result.state, result.answers);
    for (const auto &frame : result.continuations)
      result.state.push_back(frame.sequence);
    // Bound emitted signatures/control before expanding the specialized tree.
    uint64_t ports = result.state.size() + result.stores.size();
    uint64_t bodies = 12 + result.constructors.size() * 32 +
                      result.continuations.size() * 24 +
                      result.kinds.size() * 8;
    if (ports > 512 || bodies > work.operations || ports * bodies > work.slots)
      return error("oracle-controller-limit");
    work.operations -= bodies;
    work.slots -= ports * bodies;
    return Error::success();
  }
  unsigned kindNumber(pir::OracleKindAttr value) {
    auto reference = cantFail(oracleReferenceType(value));
    for (auto [i, kind] : enumerate(result.kinds))
      if (cantFail(oracleReferenceType(kind)) == reference)
        return i;
    llvm_unreachable("planned query kind");
  }
  unsigned answerSlot(unsigned kind) { return Controller::HeaderSize + kind; }
  unsigned frameSlot(unsigned frame) {
    return Controller::HeaderSize + result.kinds.size() + frame;
  }
  Types allTypes() {
    Types types(result.state.begin(), result.state.end());
    append_range(types, result.stores);
    return types;
  }
  func::FuncOp function(StringRef label, TypeRange inputs, TypeRange outputs,
                        bool region,
                        llvm::function_ref<void(Control &, ValueRange)> emit) {
    OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&unit.getBody().front());
    std::string name;
    do {
      name = "_oracle_query_" + label.str() + "_" + std::to_string(next++);
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
               ArrayRef<std::string> statics = {},
               ArrayRef<std::string> parameters = {}) {
    auto binding = bindings.binding(
        builder, loc,
        {contract.str(),
         std::vector<std::string>(statics.begin(), statics.end()), ""});
    SmallVector<Attribute> attrs;
    for (const auto &parameter : parameters)
      attrs.push_back(builder.getStringAttr(parameter));
    return control.invoke(
        "exec.apply", outputs, control.scoped(inputs),
        {builder.getNamedAttr("binding", binding),
         builder.getNamedAttr("parameters", builder.getArrayAttr(attrs)),
         builder.getNamedAttr("site", builder.getStringAttr(site))});
  }
  Value number(Control &c, uint64_t value, StringRef site) {
    return apply(c, "index.constant", index, {}, site, {},
                 {std::to_string(value)})
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
  std::string element(Type sequence) {
    auto bound = cantFail(encodeBoundType(sequence, false));
    return bound.arguments.front().type->spelling();
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
    auto &item = result.constructors[constructor];
    auto type =
        cantFail(oracleReferenceType(storage.constructors[item.source].kind));
    auto reference = pack(c, type, {tag, instance}, "anchor");
    return call(c, item.lookup, {reference, store}, "load_anchor");
  }
  unsigned field(unsigned constructor, StringRef name) {
    const auto &item = result.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (f.name == name)
        return i;
    llvm_unreachable("planned anchor field");
  }
  Values parameters(unsigned constructor, ValueRange record, Value position) {
    Values inputs;
    const auto &item = result.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (StringRef(f.name).starts_with("parameter."))
        inputs.push_back(record[i]);
    inputs.push_back(position);
    return inputs;
  }
  void answer(Control &c, Values &values, unsigned kind, Value value) {
    auto arena = values[answerSlot(kind)];
    values[Controller::AnswerIndex] = length(c, arena, "answer_index");
    values[answerSlot(kind)] = append(c, arena, value, "answer_value");
    values[Controller::Kind] = number(c, kind, "answer_kind");
    values[Controller::Phase] = number(c, Controller::Return, "return");
  }
  Value answer(Control &c, ValueRange values, unsigned kind) {
    return at(c, values[answerSlot(kind)], values[Controller::AnswerIndex],
              result.kinds[kind].getAnswerType(), "read_answer");
  }
  void child(Control &c, Values &values, unsigned constructor, unsigned query,
             ValueRange record, ValueRange previous) {
    const auto &item = result.constructors[constructor];
    const auto &q = item.functions.queries[query];
    auto frame = item.firstContinuation + query;
    const auto &layout = result.continuations[frame];
    Values saved{values[Controller::Continuation],
                 values[Controller::ContinuationInstance],
                 values[Controller::Instance], values[Controller::Position]};
    append_range(saved, previous);
    auto instance = length(c, values[frameSlot(frame)], "frame_instance");
    auto packed = pack(c, layout.record, saved, "frame_record");
    values[frameSlot(frame)] =
        append(c, values[frameSlot(frame)], packed, "save_frame");
    auto position =
        call(c, q.position,
             parameters(constructor, record, values[Controller::Position]),
             "child_position", true)
            .front();
    auto source =
        record[field(constructor, "source." + std::to_string(q.source))];
    auto reference =
        unpack(c, source, TypeRange{index, index}, "child_reference");
    values[Controller::Constructor] = reference[0];
    values[Controller::Instance] = reference[1];
    values[Controller::Position] = position;
    values[Controller::Continuation] =
        number(c, frame + 1, "child_continuation");
    values[Controller::ContinuationInstance] = instance;
    values[Controller::Kind] = number(c, kindNumber(q.kind), "child_kind");
    values[Controller::Phase] = number(c, Controller::Enter, "enter_child");
  }
  func::FuncOp enter(unsigned constructor) {
    return function(
        "enter", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto values = state(inputs);
          const auto &item = result.constructors[constructor];
          equal(c, values[Controller::Kind], item.kind, "kind");
          auto record =
              load(c, constructor, values[Controller::Constructor],
                   values[Controller::Instance], stores(inputs)[constructor]);
          auto rows = record[field(constructor, "shape.rows")];
          auto valid = compare(c, "index.less", values[Controller::Position],
                               rows, "domain");
          require(c, valid, "admit_domain");
          if (storage.constructors[item.source].constructor !=
              OracleAnchorConstructor::Kind::Virtual)
            values[Controller::Phase] =
                number(c, Controller::Request, "request");
          else if (item.functions.queries.empty()) {
            auto value = call(c, item.functions.answer,
                              parameters(constructor, record,
                                         values[Controller::Position]),
                              "virtual_answer", true)
                             .front();
            answer(c, values, item.kind, value);
          } else
            child(c, values, constructor, 0, record, {});
          c.returned(values);
        });
  }
  func::FuncOp returned(unsigned frame) {
    return function(
        "resume_frame", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto values = state(inputs);
          const auto &layout = result.continuations[frame];
          const auto &item = result.constructors[layout.constructor];
          const auto &query = item.functions.queries[layout.query];
          auto k = kindNumber(query.kind);
          equal(c, values[Controller::Kind], k, "returned_kind");
          auto saved = at(c, values[frameSlot(frame)],
                          values[Controller::ContinuationInstance],
                          layout.record, "load_frame");
          Types fields(4 + layout.previousKinds.size(), index);
          auto record = unpack(c, saved, fields, "frame");
          Values references(record.begin() + 4, record.end());
          references.push_back(values[Controller::AnswerIndex]);
          values[Controller::Continuation] = record[0];
          values[Controller::ContinuationInstance] = record[1];
          values[Controller::Constructor] =
              number(c, item.source, "parent_constructor");
          values[Controller::Instance] = record[2];
          values[Controller::Position] = record[3];
          auto parent = load(
              c, layout.constructor, values[Controller::Constructor],
              values[Controller::Instance], stores(inputs)[layout.constructor]);
          if (layout.query + 1 == item.functions.queries.size()) {
            auto arguments = parameters(layout.constructor, parent, record[3]);
            for (auto [ordinal, reference] : enumerate(references)) {
              auto childKind = kindNumber(item.functions.queries[ordinal].kind);
              arguments.push_back(
                  at(c, values[answerSlot(childKind)], reference,
                     result.kinds[childKind].getAnswerType(),
                     "child_answer_" + std::to_string(ordinal)));
            }
            auto output = call(c, item.functions.answer, arguments,
                               "virtual_answer", true)
                              .front();
            answer(c, values, item.kind, output);
          } else
            child(c, values, layout.constructor, layout.query + 1, parent,
                  references);
          c.returned(values);
        });
  }
  func::FuncOp dispatch(StringRef label, unsigned selector,
                        ArrayRef<std::pair<unsigned, func::FuncOp>> cases,
                        TypeRange formals, TypeRange outputs) {
    return function(
        label, formals, outputs, false, [&](Control &c, ValueRange inputs) {
          if (cases.empty()) {
            c.reject("refused", "no_constructor");
            return;
          }
          if (cases.size() == 1) {
            equal(c, inputs[selector], cases.front().first, "selected");
            c.returned(call(c, cases.front().second, inputs, "case"));
            return;
          }
          auto middle = cases.size() / 2;
          auto pivot = number(c, cases[middle].first, "pivot");
          auto left =
              compare(c, "index.less", inputs[selector], pivot, "partition");
          auto values = c.conditional(
              left, inputs, outputs, "dispatch", [&](unsigned branch) {
                auto subset = branch == 0 ? cases.take_front(middle)
                                          : cases.drop_front(middle);
                auto selected =
                    dispatch(label, selector, subset, formals, outputs);
                return function(
                    "dispatch_region", formals, outputs, true,
                    [&](Control &body, ValueRange captures) {
                      body.complete(
                          call(body, selected, captures,
                               "selected_branch_" + std::to_string(branch)));
                    });
              });
          c.returned(values);
        });
  }
  func::FuncOp dispatch(StringRef label, unsigned selector,
                        ArrayRef<std::pair<unsigned, func::FuncOp>> cases) {
    return dispatch(label, selector, cases, allTypes(), result.state);
  }
  void emitMetadata(StringRef fieldName, StringRef label,
                    std::vector<func::FuncOp> &outputs) {
    Types dispatchTypes{index, index};
    append_range(dispatchTypes, result.stores);
    for (unsigned kind = 0; kind < result.kinds.size(); ++kind) {
      SmallVector<std::pair<unsigned, func::FuncOp>> cases;
      for (auto [ordinal, item] : enumerate(result.constructors)) {
        if (item.kind != kind)
          continue;
        auto constructor = unsigned(ordinal);
        auto leaf =
            function("stored_count", dispatchTypes, index, false,
                     [&](Control &c, ValueRange inputs) {
                       auto record = load(c, constructor, inputs[0], inputs[1],
                                          inputs[2 + constructor]);
                       c.returned(record[field(constructor, fieldName)]);
                     });
        cases.push_back({item.source, leaf});
      }
      func::FuncOp select;
      if (!cases.empty())
        select = dispatch("count_dispatch", 0, cases, dispatchTypes, index);
      auto reference = cantFail(oracleReferenceType(result.kinds[kind]));
      Types inputs{reference};
      append_range(inputs, result.stores);
      auto count = function(
          label, inputs, index, false, [&](Control &c, ValueRange inputs) {
            auto identity =
                unpack(c, inputs[0], TypeRange{index, index}, "reference");
            if (!select) {
              auto zero = number(c, 0, "none");
              require(c, compare(c, "index.less", zero, zero, "no_constructor"),
                      "unavailable_kind");
              c.returned(zero);
              return;
            }
            append_range(identity, inputs.drop_front());
            c.returned(call(c, select, identity, "select_count"));
          });
      outputs.push_back(count);
    }
  }
  Error emitCounts() {
    emitMetadata("query.leaves", "leaf_count", result.leafCounts);
    emitMetadata("shape.rows", "row_count", result.rowCounts);
    for (const auto &item : result.constructors) {
      const auto &anchor = storage.constructors[item.source];
      Types sources;
      for (const auto &field : anchor.roles[item.role].fields)
        if (StringRef(field.name).starts_with("source."))
          sources.push_back(field.type);
      Types inputs(sources);
      append_range(inputs, result.stores);
      if (inputs.size() > 512)
        return error("oracle-controller-limit");
      auto count = function(
          "construction_count", inputs, index, false,
          [&](Control &c, ValueRange inputs) {
            auto base =
                anchor.constructor != OracleAnchorConstructor::Kind::Virtual;
            Value total = number(c, base ? 1 : 0, "initial_count");
            for (auto [ordinal, query] : enumerate(item.functions.queries)) {
              Values arguments{inputs[query.source]};
              append_range(arguments, inputs.drop_front(sources.size()));
              auto child =
                  call(c, result.leafCounts[kindNumber(query.kind)], arguments,
                       "child_count_" + std::to_string(ordinal))
                      .front();
              total = apply(c, "index.add", index, {total, child},
                            "sum_count_" + std::to_string(ordinal))
                          .front();
            }
            c.returned(total);
          });
      result.constructionCounts.push_back(count);
    }
    return Error::success();
  }
  void emitInitialize(pir::OracleKindAttr root) {
    auto reference = cantFail(oracleReferenceType(root));
    result.initialize =
        function("initialize", TypeRange{reference, index}, result.state, false,
                 [&](Control &c, ValueRange inputs) {
                   auto reference =
                       unpack(c, inputs[0], TypeRange{index, index}, "root");
                   auto zero = number(c, 0, "initial");
                   Values values{reference[0], reference[1], inputs[1], zero,
                                 zero,         zero,         zero,      zero};
                   for (auto [slot, type] :
                        enumerate(ArrayRef<Type>(result.state)
                                      .drop_front(Controller::HeaderSize)))
                     values.push_back(
                         empty(c, type, "empty_state_" + std::to_string(slot)));
                   c.returned(values);
                 });
  }
  void emitResume() {
    for (unsigned kind = 0; kind < result.kinds.size(); ++kind) {
      auto type = result.kinds[kind];
      Types inputs(result.state.begin(), result.state.end());
      inputs.append(5, index);
      inputs.push_back(type.getAnswerType());
      auto helper = function(
          "resume", inputs, result.state, false,
          [&](Control &c, ValueRange inputs) {
            auto values = state(inputs);
            equal(c, values[Controller::Phase], Controller::Request,
                  "suspended");
            equal(c, values[Controller::Kind], kind, "kind");
            for (unsigned i = 0; i < 5; ++i)
              require(c,
                      compare(c, "index.equal", values[i],
                              inputs[result.state.size() + i],
                              "request_coordinate_" + std::to_string(i)),
                      "same_request_" + std::to_string(i));
            answer(c, values, kind, inputs.back());
            c.returned(values);
          });
      result.resume.push_back(helper);
    }
  }
  void emitAdvance() {
    SmallVector<std::pair<unsigned, func::FuncOp>> enters, returns;
    for (auto [i, item] : enumerate(result.constructors))
      enters.push_back({item.source, enter(i)});
    returns.push_back({0, function("completed", allTypes(), result.state, false,
                                   [&](Control &c, ValueRange inputs) {
                                     auto values = state(inputs);
                                     values[Controller::Phase] = number(
                                         c, Controller::Completed, "completed");
                                     c.returned(values);
                                   })});
    for (unsigned i = 0; i < result.continuations.size(); ++i)
      returns.push_back({i + 1, returned(i)});
    auto entering = dispatch("enter_dispatch", Controller::Constructor, enters);
    auto returning =
        dispatch("return_dispatch", Controller::Continuation, returns);
    auto step = function(
        "step", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto zero = number(c, Controller::Enter, "enter_phase");
          auto enteringPhase = compare(
              c, "index.equal", inputs[Controller::Phase], zero, "phase");
          auto next = c.conditional(
              enteringPhase, inputs, result.state, "step",
              [&](unsigned branch) {
                return function("step_region", allTypes(), result.state, true,
                                [&](Control &body, ValueRange captures) {
                                  body.complete(call(
                                      body, branch == 0 ? entering : returning,
                                      captures,
                                      branch == 0 ? "enter_transition"
                                                  : "return_transition"));
                                });
              });
          c.returned(next);
        });
    result.advance = function(
        "advance", allTypes(), result.state, false,
        [&](Control &c, ValueRange inputs) {
          auto zero = number(c, 0, "lower");
          auto two = number(c, Controller::Request, "suspension_phase");
          require(c,
                  compare(c, "index.less", inputs[Controller::Phase], two,
                          "can_advance"),
                  "admit_advance");
          auto upper =
              number(c, result.capacity.nodes * 2 + 1, "transition_bound");
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
                      auto values =
                          call(body, step, captured.drop_front(), "step");
                      auto threshold = number(body, Controller::Request,
                                              "iteration_suspension_phase");
                      auto proceed =
                          compare(body, "index.less", values[Controller::Phase],
                                  threshold, "continuing");
                      Values yielded{proceed};
                      append_range(yielded, values);
                      body.complete(yielded);
                    });
              });
          auto one = number(c, Controller::Return, "return_phase");
          require(c,
                  compare(c, "index.less", one, next[Controller::Phase],
                          "stopped_advancing"),
                  "complete_advance");
          c.returned(next);
        });
    result.finish =
        function("finish", result.state, rootAnswer(), false,
                 [&](Control &c, ValueRange inputs) {
                   equal(c, inputs[Controller::Phase], Controller::Completed,
                         "completed");
                   equal(c, inputs[Controller::Kind], 0, "root_kind");
                   c.returned(answer(c, inputs, 0));
                 });
  }
  Error emitContents(pir::OracleKindAttr root) {
    if (result.access != OracleControllerAccess::Holder)
      return Error::success();
    if (!result.evaluate)
      return error("oracle-controller-custody");
    auto collection = mathematical::collectionRealization(root.getDataType());
    if (!collection || collection->rank != 1 || !collection->empty ||
        !collection->append || collection->element != root.getAnswerType())
      return error("oracle-controller-layout");
    Type data = root.getDataType();
    Types dispatchTypes{index, index};
    append_range(dispatchTypes, result.stores);
    SmallVector<std::pair<unsigned, func::FuncOp>> cases;
    for (auto [ordinal, item] : enumerate(result.constructors)) {
      if (item.kind != 0)
        continue;
      auto constructor = unsigned(ordinal);
      const auto &anchor = storage.constructors[item.source];
      auto read = function(
          "contents_case", dispatchTypes, data, false,
          [&](Control &c, ValueRange inputs) {
            auto record = load(c, constructor, inputs[0], inputs[1],
                               inputs[2 + constructor]);
            if (anchor.constructor != OracleAnchorConstructor::Kind::Virtual) {
              c.returned(record[field(constructor, "data")]);
              return;
            }
            auto reference = pack(c, cantFail(oracleReferenceType(root)),
                                  inputs.take_front(2), "root");
            auto zero = number(c, 0, "lower");
            auto empty = apply(c, collection->empty->contract, data, {},
                               "empty", collection->empty->arguments)
                             .front();
            Values captures{reference};
            append_range(captures, inputs.drop_front(2));
            auto materialized = c.loop(
                zero, record[field(constructor, "shape.rows")], empty, captures,
                data, false, "rows", [&](unsigned) {
                  Types arguments{index, data, reference.getType()};
                  append_range(arguments, result.stores);
                  return function(
                      "contents_row", arguments, data, true,
                      [&](Control &row, ValueRange inputs) {
                        Values query{inputs[2], inputs[0]};
                        append_range(query, inputs.drop_front(3));
                        auto answer =
                            call(row, result.evaluate, query, "evaluate")
                                .front();
                        row.complete(apply(row, collection->append->contract,
                                           data, {inputs[1], answer}, "append",
                                           collection->append->arguments));
                      });
                });
            c.returned(materialized);
          });
      cases.push_back({item.source, read});
    }
    auto select = dispatch("contents_dispatch", 0, cases, dispatchTypes, data);
    Types inputs{cantFail(oracleReferenceType(root))};
    append_range(inputs, result.stores);
    result.contents = function(
        "contents", inputs, data, false, [&](Control &c, ValueRange inputs) {
          auto identity =
              unpack(c, inputs[0], TypeRange{index, index}, "reference");
          append_range(identity, inputs.drop_front());
          c.returned(call(c, select, identity, "select_contents"));
        });
    return Error::success();
  }
  Type rootAnswer() { return result.kinds.front().getAnswerType(); }
  Error emitEvaluator(pir::OracleKindAttr root) {
    // Decide availability before emitting any evaluator helper. A receiver
    // without a base table uses the common opening exchange at suspension.
    for (const auto &item : result.constructors) {
      const auto &anchor = storage.constructors[item.source];
      if (anchor.constructor != OracleAnchorConstructor::Kind::Virtual &&
          none_of(anchor.roles[item.role].fields,
                  [](const auto &field) { return field.name == "data"; }))
        return Error::success();
    }
    SmallVector<std::pair<unsigned, func::FuncOp>> leaves;
    for (unsigned constructor = 0; constructor < result.constructors.size();
         ++constructor) {
      const auto &item = result.constructors[constructor];
      const auto &anchor = storage.constructors[item.source];
      if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual)
        continue;
      auto read = emitOracleTableRead(candidate, anchor.kind);
      if (!read)
        return read.takeError();
      auto helper = function(
          "read_leaf", allTypes(), result.state, false,
          [&](Control &c, ValueRange inputs) {
            auto values = state(inputs);
            auto record =
                load(c, constructor, values[Controller::Constructor],
                     values[Controller::Instance], stores(inputs)[constructor]);
            auto value = call(c, *read,
                              {record[field(constructor, "data")],
                               record[field(constructor, "shape.rows")],
                               values[Controller::Position]},
                              "leaf_answer")
                             .front();
            Values arguments(values);
            append_range(arguments, ValueRange(values).take_front(5));
            arguments.push_back(value);
            c.returned(call(c, result.resume[item.kind], arguments, "resume"));
          });
      leaves.push_back({item.source, helper});
    }
    // A program containing only zero-query virtual anchors needs no leaf
    // evaluator. The guarded branch must nevertheless reject a fabricated
    // request without constructing an answer of an arbitrary type.
    func::FuncOp leaf;
    if (leaves.empty())
      leaf = function(
          "no_leaf", allTypes(), result.state, false,
          [&](Control &c, ValueRange inputs) {
            auto zero = number(c, 0, "none");
            require(c, compare(c, "index.less", zero, zero, "no_request"),
                    "unexpected_request");
            c.returned(state(inputs));
          });
    else
      leaf = dispatch("leaf_dispatch", Controller::Constructor, leaves);
    Types inputs{cantFail(oracleReferenceType(root)), index};
    append_range(inputs, result.stores);
    result.evaluate = function(
        "evaluate", inputs, rootAnswer(), false,
        [&](Control &c, ValueRange inputs) {
          auto initial =
              call(c, result.initialize, inputs.take_front(2), "initialize");
          auto zero = number(c, 0, "lower");
          auto upper = number(c, result.capacity.leaves + 1, "request_bound");
          auto final = c.loop(
              zero, upper, initial, inputs.drop_front(2), result.state, true,
              "requests", [&](unsigned) {
                Types arguments{index};
                append_range(arguments, allTypes());
                Types outputs{builder.getI1Type()};
                append_range(outputs, result.state);
                return function(
                    "request_iteration", arguments, outputs, true,
                    [&](Control &body, ValueRange inputs) {
                      auto captured = inputs.drop_front();
                      auto current =
                          call(body, result.advance, captured, "advance");
                      auto requestPhase =
                          number(body, Controller::Request, "request_phase");
                      auto requested = compare(body, "index.equal",
                                               current[Controller::Phase],
                                               requestPhase, "has_request");
                      append_range(current, stores(captured));
                      auto next = body.conditional(
                          requested, current, result.state, "request",
                          [&](unsigned branch) {
                            return function(
                                "request_region", allTypes(), result.state,
                                true,
                                [&](Control &region, ValueRange captured) {
                                  region.complete(
                                      branch == 0 ? call(region, leaf, captured,
                                                         "answer_request")
                                                  : state(captured));
                                });
                          });
                      auto completed = number(body, Controller::Completed,
                                              "completed_phase");
                      auto proceed =
                          compare(body, "index.less", next[Controller::Phase],
                                  completed, "continuing");
                      Values yielded{proceed};
                      append_range(yielded, next);
                      body.complete(yielded);
                    });
              });
          c.returned(call(c, result.finish, final, "finish"));
        });
    return Error::success();
  }
};
} // namespace
Expected<OracleQueryController> emitOracleQueryController(
    ModuleOp candidate, ModuleOp prepared, const OracleAnchorStorage &storage,
    StringRef role, pir::OracleKindAttr root, OracleQuerySize capacity,
    OracleVirtualFunctionWork &work, OracleControllerAccess access) {
  auto unit = [](ModuleOp module) -> pir::ProtocolModuleOp {
    if (!module || !hasSingleElement(module.getBody()->getOperations()))
      return {};
    return dyn_cast<pir::ProtocolModuleOp>(module.getBody()->front());
  };
  auto target = unit(candidate), source = unit(prepared);
  if (!target || !source || target == source ||
      candidate.getContext() != prepared.getContext() || !root ||
      root.getContext() != candidate.getContext() ||
      root.getIdentity() != "table" ||
      target.getProfile() != pir::Profile::Protocol ||
      source.getProfile() != pir::Profile::Protocol ||
      failed(verify(candidate)) || failed(verify(prepared)))
    return error("oracle-controller-source");
  // Native range admission is bounded. Refuse generation instead of silently
  // truncating the source's recursive expansion or adding a validity premise.
  if ((access != OracleControllerAccess::Available &&
       access != OracleControllerAccess::Holder) ||
      !capacity.nodes || capacity.leaves > capacity.nodes ||
      capacity.nodes > (1048576 - 1) / 2 || capacity.leaves >= 1048576)
    return error("oracle-controller-capacity");
  auto program = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(source, storage.entry));
  if (!program || !is_contained(program.getRoles(),
                                StringAttr::get(prepared.getContext(), role)))
    return error("oracle-controller-layout");
  Emitter emit(candidate, prepared, storage, role, capacity, access);
  if (auto e = emit.plan(root, work))
    return std::move(e);
  if (auto e = emit.emitCounts())
    return std::move(e);
  emit.emitInitialize(root);
  emit.emitResume();
  emit.emitAdvance();
  if (auto e = emit.emitEvaluator(root))
    return std::move(e);
  if (auto e = emit.emitContents(root))
    return std::move(e);
  return std::move(emit.result);
}
} // namespace zkc::protocol

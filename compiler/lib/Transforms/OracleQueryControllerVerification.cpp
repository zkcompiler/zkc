#include "OracleQueryController.h"
#include "OracleTableRead.h"
#include "OracleVerificationContext.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
Error layout(const OracleVerificationContext &targetContext,
             const OracleVerificationContext &sourceContext,
             const OracleAnchorStorage &storage, StringRef role,
             pir::OracleKindAttr root, OracleQuerySize capacity,
             const Controller &actual, OracleControllerAccess access) {
  auto refuse = [] { return error("oracle-controller-body"); };
  if (actual.state.size() > 512 || actual.stores.size() > 512 ||
      actual.state.size() + actual.stores.size() > 512 ||
      actual.constructors.size() > 512 || actual.continuations.size() > 512 ||
      actual.kinds.size() > 512)
    return refuse();
  uint64_t metadataRemaining = 4 * 1024 * 1024;
  if ((access != OracleControllerAccess::Available &&
       access != OracleControllerAccess::Holder) ||
      actual.access != access || actual.role != role ||
      !(actual.capacity == capacity) || !root ||
      root.getIdentity() != "table" || !capacity.nodes ||
      capacity.leaves > capacity.nodes || capacity.nodes > (1048576 - 1) / 2 ||
      capacity.leaves >= 1048576)
    return refuse();
  auto *context = targetContext.getModule().getContext();
  auto source = sourceContext.getUnit();
  auto program = dyn_cast_or_null<pir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(source, storage.entry));
  if (!program ||
      !is_contained(program.getRoles(), StringAttr::get(context, role)))
    return refuse();
  auto index = IntegerType::get(context, 64, IntegerType::Unsigned);
  std::vector<pir::OracleKindAttr> kinds;
  std::vector<Type> references, answers, stores;
  auto sequence = [&](Type type) -> Expected<Type> {
    auto bound = encodeBoundType(type, false);
    if (!bound)
      return bound.takeError();
    auto sequence =
        parseBoundType("sequence<" + bound->spelling() + ">", false);
    if (!sequence)
      return sequence.takeError();
    auto decoded = decodeBoundType(context, *sequence);
    if (!decoded)
      return refuse();
    return decoded;
  };
  auto intern = [&](pir::OracleKindAttr kind) -> Expected<unsigned> {
    if (!kind || kind.getIdentity() != "table")
      return refuse();
    auto reference = oracleReferenceType(kind);
    if (!reference)
      return reference.takeError();
    auto found = llvm::find(references, *reference);
    if (found != references.end())
      return unsigned(found - references.begin());
    auto answer = sequence(kind.getAnswerType());
    if (!answer)
      return answer.takeError();
    kinds.push_back(kind);
    references.push_back(*reference);
    answers.push_back(*answer);
    return unsigned(kinds.size() - 1);
  };
  auto first = intern(root);
  if (!first)
    return first.takeError();
  unsigned constructorCount = 0, frameCount = 0;
  for (auto [ordinal, constructor] : enumerate(storage.constructors)) {
    auto owner = find_if(constructor.roles,
                         [&](const auto &owner) { return owner.role == role; });
    if (owner == constructor.roles.end() ||
        (access == OracleControllerAccess::Holder &&
         constructor.holder != role))
      continue;
    if (constructorCount >= actual.constructors.size())
      return refuse();
    const auto &item = actual.constructors[constructorCount];
    auto kind = intern(constructor.kind);
    if (!kind)
      return kind.takeError();
    if (item.source != ordinal ||
        item.role != unsigned(owner - constructor.roles.begin()) ||
        item.kind != *kind || item.firstContinuation != frameCount)
      return refuse();
    if (auto e = checkOracleAnchorLookup(targetContext, item.lookup, storage,
                                         ordinal, item.role))
      return e;
    stores.push_back(owner->sequence);
    if (constructor.constructor == OracleAnchorConstructor::Kind::Virtual) {
      auto original = dyn_cast_or_null<pir::OracleDefinitionOp>(
          SymbolTable::lookupSymbolIn(source, constructor.declaration));
      if (!original)
        return refuse();
      if (auto e = checkOracleVirtualFunctions(targetContext, sourceContext,
                                               original, item.functions))
        return e;
      std::vector<unsigned> previous;
      unsigned queryIndex = 0;
      for (auto query :
           original.getBody().front().getOps<pir::OracleQueryOp>()) {
        auto queryKind = intern(query.getHandle().getType().getKind());
        if (!queryKind)
          return queryKind.takeError();
        if (frameCount >= actual.continuations.size())
          return refuse();
        const auto &frame = actual.continuations[frameCount];
        if (frame.constructor != constructorCount ||
            frame.query != queryIndex || frame.previousKinds != previous)
          return refuse();
        std::vector<std::string> fields(4 + previous.size(), "index");
        auto descriptor = encodeVariant(
            {json::Array{"zkc.oracle.continuation/0",
                         toHex(storage.entry, true), toHex(role, true),
                         std::to_string(ordinal), std::to_string(queryIndex)},
             {{"Record", std::move(fields)}}});
        if (!descriptor || descriptor->size() > metadataRemaining)
          return refuse();
        metadataRemaining -= descriptor->size();
        Type record = data::VariantType::get(context, *descriptor);
        auto arena = sequence(record);
        if (!arena)
          return arena.takeError();
        if (frame.record != record || frame.sequence != *arena)
          return refuse();
        previous.push_back(*queryKind);
        ++frameCount;
        ++queryIndex;
      }
    } else if (item.functions.answer || !item.functions.queries.empty())
      return refuse();
    ++constructorCount;
  }
  if (constructorCount != actual.constructors.size() ||
      frameCount != actual.continuations.size() || actual.kinds != kinds ||
      actual.answers != answers || actual.stores != stores ||
      actual.resume.size() != kinds.size() ||
      actual.leafCounts.size() != kinds.size() ||
      actual.rowCounts.size() != kinds.size() ||
      actual.constructionCounts.size() != constructorCount)
    return refuse();
  std::vector<Type> state(Controller::HeaderSize, index);
  append_range(state, answers);
  for (const auto &frame : actual.continuations)
    state.push_back(frame.sequence);
  if (actual.state != state)
    return refuse();
  return Error::success();
}
struct Reader {
  const OracleVerificationContext &context;
  const OracleAnchorStorage &storage;
  const Controller &model;
  pir::ProtocolModuleOp unit;
  const SourceExecutionClosure &closure;
  Type index, scope, boolean;
  bool valid = true;
  Reader(const OracleAnchorStorage &storage, const Controller &model,
         const OracleVerificationContext &context)
      : context(context), storage(storage), model(model),
        unit(context.getUnit()), closure(context.getClosure()),
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
                 StringRef site, ArrayRef<std::string> statics = {},
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
      for (auto [actual, expected] : zip(binding.getArguments(), statics))
        reader.expect(cast<StringAttr>(actual).getValue() == expected);
      for (auto [actual, expected] : zip(op.getParameters(), parameters))
        reader.expect(cast<StringAttr>(actual).getValue() == expected);
      return values;
    }
    Value number(uint64_t value, StringRef site) {
      return apply("index.constant", reader.index, {}, site, {},
                   {std::to_string(value)})
          .front();
    }
    Value compare(StringRef contract, Value left, Value right, StringRef site) {
      return apply(contract, reader.boolean, {left, right}, site).front();
    }
    void require(Value predicate, StringRef site) {
      apply("control.require", {}, predicate, site);
    }
    void equalTo(Value value, uint64_t expected, StringRef site) {
      auto constant = number(expected, site.str() + "_expected");
      auto equality =
          compare("index.equal", value, constant, site.str() + "_equal");
      require(equality, site);
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
    Value compute(func::FuncOp expected, ValueRange inputs, StringRef site) {
      auto *step = take("exec.compute", site);
      auto values = result(step, expected.getResultTypes(), inputs);
      if (reader.valid) {
        auto op = cast<exec::ComputeOp>(step->operation);
        auto actual = SymbolTable::lookupSymbolIn(reader.unit, op.getCallee());
        reader.expect(actual == expected.getOperation());
      }
      return values.front();
    }
    Value pack(Type type, ValueRange fields, StringRef site) {
      auto *step = take("exec.variant", site);
      auto values = result(step, type, fields);
      if (reader.valid)
        reader.expect(cast<exec::VariantOp>(step->operation).getAlternative() ==
                      "Record");
      return values.front();
    }
    Values unpack(Value value, TypeRange fields, StringRef site) {
      auto *step = take("exec.match", site);
      auto values = result(step, fields, value, 1);
      if (!reader.valid)
        return values;
      auto op = cast<exec::MatchOp>(step->operation);
      if (!reader.expect(op.getAlternatives().size() == 1 &&
                         cast<StringAttr>(op.getAlternatives()[0]).getValue() ==
                             "Record"))
        return values;
      reader.body(step->regions[0], fields, fields, true,
                  [&](Cursor &body, ValueRange arguments) {
                    body.finish(arguments, true);
                  });
      return values;
    }
    Value empty(Type sequence, StringRef site) {
      return apply("sequence.empty", sequence, {}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value append(Type sequence, Value previous, Value value, StringRef site) {
      return apply("sequence.append", sequence, {previous, value}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value at(Type sequence, Type element, Value values, Value offset,
             StringRef site) {
      return apply("sequence.at", element, {values, offset}, site,
                   {reader.element(sequence)})
          .front();
    }
    Value length(Type sequence, Value values, StringRef site) {
      return apply("sequence.length", reader.index, values, site,
                   {reader.element(sequence)})
          .front();
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
    Values loop(Value lower, Value upper, ValueRange state, ValueRange stores,
                TypeRange outputs, bool conditional, StringRef site,
                llvm::function_ref<void(func::FuncOp)> check) {
      auto *step = take("exec.range", site);
      Values inputs{lower, upper};
      append_range(inputs, state);
      append_range(inputs, stores);
      auto values = result(step, outputs, inputs, 1);
      if (reader.valid && reader.expect(step->conditional == conditional))
        check(step->regions[0]);
      return values;
    }
    Values loop(Value lower, Value upper, ValueRange state, ValueRange stores,
                StringRef site, llvm::function_ref<void(func::FuncOp)> check) {
      return loop(lower, upper, state, stores, reader.model.state, true, site,
                  check);
    }
    void reject(StringRef reason, StringRef site) {
      auto *step = take("exec.reject", site);
      if (!reader.valid)
        return;
      reader.expect(cast<exec::RejectOp>(step->operation).getReason() ==
                        reason &&
                    step->inputs.empty() && step->outputs.empty() &&
                    step->regions.empty() && offset == steps.size());
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
                function->hasAttr("runtime.region") == region &&
                equal(function.getArgumentTypes(), arguments) &&
                function.getResultTypes().size() == 1))
      return;
    auto outcome = dyn_cast<exec::OutcomeType>(function.getResultTypes()[0]);
    if (!expect(outcome && equal(outcome.getPayload(), outputs)))
      return;
    auto found = closure.bodies.find(function.getSymName().str());
    if (!expect(found != closure.bodies.end()))
      return;
    Cursor cursor{*this, found->second};
    check(cursor, function.getArguments().drop_front());
    expect(cursor.offset == cursor.steps.size());
  }
  std::string element(Type sequence) {
    return cantFail(encodeBoundType(sequence, false))
        .arguments.front()
        .type->spelling();
  }
  Types allTypes() {
    Types types(model.state.begin(), model.state.end());
    append_range(types, model.stores);
    return types;
  }
  Values state(ValueRange values) {
    return Values(values.take_front(model.state.size()));
  }
  ValueRange stores(ValueRange values) {
    return values.drop_front(model.state.size());
  }
  unsigned answerSlot(unsigned kind) { return Controller::HeaderSize + kind; }
  unsigned frameSlot(unsigned frame) {
    return Controller::HeaderSize + model.kinds.size() + frame;
  }
  unsigned kindNumber(pir::OracleKindAttr kind) {
    auto reference = cantFail(oracleReferenceType(kind));
    for (auto [i, current] : enumerate(model.kinds))
      if (cantFail(oracleReferenceType(current)) == reference)
        return i;
    llvm_unreachable("validated controller kind inventory");
  }
  unsigned field(unsigned constructor, StringRef name) {
    const auto &item = model.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (f.name == name)
        return i;
    llvm_unreachable("derived anchor field inventory");
  }
  Values load(Cursor &c, unsigned constructor, Value tag, Value instance,
              Value store) {
    auto &item = model.constructors[constructor];
    auto reference =
        cantFail(oracleReferenceType(storage.constructors[item.source].kind));
    auto handle = c.pack(reference, {tag, instance}, "anchor");
    return c.call(item.lookup, {handle, store}, "load_anchor");
  }
  Values parameters(unsigned constructor, ValueRange record, Value position) {
    Values inputs;
    const auto &item = model.constructors[constructor];
    const auto &fields =
        storage.constructors[item.source].roles[item.role].fields;
    for (auto [i, f] : enumerate(fields))
      if (StringRef(f.name).starts_with("parameter."))
        inputs.push_back(record[i]);
    inputs.push_back(position);
    return inputs;
  }
  void putAnswer(Cursor &c, Values &state, unsigned kind, Value answer) {
    auto arena = state[answerSlot(kind)];
    state[Controller::AnswerIndex] =
        c.length(model.answers[kind], arena, "answer_index");
    state[answerSlot(kind)] =
        c.append(model.answers[kind], arena, answer, "answer_value");
    state[Controller::Kind] = c.number(kind, "answer_kind");
    state[Controller::Phase] = c.number(1, "return");
  }
  Value getAnswer(Cursor &c, ValueRange state, unsigned kind) {
    return c.at(model.answers[kind], model.kinds[kind].getAnswerType(),
                state[answerSlot(kind)], state[Controller::AnswerIndex],
                "read_answer");
  }
  // Remaining body checks are deliberately separate from production emission.
  void child(Cursor &c, Values &values, unsigned constructor, unsigned query,
             ValueRange record, ValueRange previous) {
    const auto &item = model.constructors[constructor];
    const auto &q = item.functions.queries[query];
    unsigned ordinal = item.firstContinuation + query;
    const auto &frame = model.continuations[ordinal];
    Values saved{values[Controller::Continuation],
                 values[Controller::ContinuationInstance],
                 values[Controller::Instance], values[Controller::Position]};
    append_range(saved, previous);
    auto instance =
        c.length(frame.sequence, values[frameSlot(ordinal)], "frame_instance");
    auto recordValue = c.pack(frame.record, saved, "frame_record");
    values[frameSlot(ordinal)] = c.append(
        frame.sequence, values[frameSlot(ordinal)], recordValue, "save_frame");
    auto position =
        c.compute(q.position,
                  parameters(constructor, record, values[Controller::Position]),
                  "child_position");
    auto source =
        record[field(constructor, "source." + std::to_string(q.source))];
    auto reference =
        c.unpack(source, TypeRange{index, index}, "child_reference");
    values[Controller::Constructor] = reference[0];
    values[Controller::Instance] = reference[1];
    values[Controller::Position] = position;
    values[Controller::Continuation] =
        c.number(ordinal + 1, "child_continuation");
    values[Controller::ContinuationInstance] = instance;
    values[Controller::Kind] = c.number(kindNumber(q.kind), "child_kind");
    values[Controller::Phase] = c.number(0, "enter_child");
  }
  void enter(func::FuncOp function, unsigned constructor) {
    body(function, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto values = state(inputs);
           const auto &item = model.constructors[constructor];
           c.equalTo(values[Controller::Kind], item.kind, "kind");
           auto record =
               load(c, constructor, values[Controller::Constructor],
                    values[Controller::Instance], stores(inputs)[constructor]);
           auto rows = record[field(constructor, "shape.rows")];
           auto valid = c.compare("index.less", values[Controller::Position],
                                  rows, "domain");
           c.require(valid, "admit_domain");
           if (storage.constructors[item.source].constructor !=
               OracleAnchorConstructor::Kind::Virtual)
             values[Controller::Phase] = c.number(2, "request");
           else if (item.functions.queries.empty()) {
             auto answer = c.compute(
                 item.functions.answer,
                 parameters(constructor, record, values[Controller::Position]),
                 "virtual_answer");
             putAnswer(c, values, item.kind, answer);
           } else
             child(c, values, constructor, 0, record, {});
           c.finish(values);
         });
  }
  void returned(func::FuncOp function, unsigned frame) {
    body(
        function, allTypes(), model.state, false,
        [&](Cursor &c, ValueRange inputs) {
          auto values = state(inputs);
          const auto &layout = model.continuations[frame];
          const auto &item = model.constructors[layout.constructor];
          const auto &query = item.functions.queries[layout.query];
          auto kind = kindNumber(query.kind);
          c.equalTo(values[Controller::Kind], kind, "returned_kind");
          auto saved =
              c.at(layout.sequence, layout.record, values[frameSlot(frame)],
                   values[Controller::ContinuationInstance], "load_frame");
          Types fields(4 + layout.previousKinds.size(), index);
          auto record = c.unpack(saved, fields, "frame");
          Values references(record.begin() + 4, record.end());
          references.push_back(values[Controller::AnswerIndex]);
          values[Controller::Continuation] = record[0];
          values[Controller::ContinuationInstance] = record[1];
          values[Controller::Constructor] =
              c.number(item.source, "parent_constructor");
          values[Controller::Instance] = record[2];
          values[Controller::Position] = record[3];
          auto parent = load(
              c, layout.constructor, values[Controller::Constructor],
              values[Controller::Instance], stores(inputs)[layout.constructor]);
          if (layout.query + 1 == item.functions.queries.size()) {
            auto inputs = parameters(layout.constructor, parent, record[3]);
            for (auto [ordinal, reference] : enumerate(references)) {
              auto childKind = kindNumber(item.functions.queries[ordinal].kind);
              inputs.push_back(c.at(model.answers[childKind],
                                    model.kinds[childKind].getAnswerType(),
                                    values[answerSlot(childKind)], reference,
                                    "child_answer_" + std::to_string(ordinal)));
            }
            auto result =
                c.compute(item.functions.answer, inputs, "virtual_answer");
            putAnswer(c, values, item.kind, result);
          } else
            child(c, values, layout.constructor, layout.query + 1, parent,
                  references);
          c.finish(values);
        });
  }
  void dispatch(func::FuncOp function, unsigned selector,
                ArrayRef<unsigned> cases, TypeRange formals, TypeRange outputs,
                llvm::function_ref<void(unsigned, func::FuncOp)> leaf) {
    body(function, formals, outputs, false, [&](Cursor &c, ValueRange inputs) {
      if (cases.empty()) {
        c.reject("refused", "no_constructor");
        return;
      }
      if (cases.size() == 1) {
        c.equalTo(inputs[selector], cases.front(), "selected");
        func::FuncOp selected;
        auto values = c.local(inputs, outputs, "case", selected);
        if (valid)
          leaf(cases.front(), selected);
        c.finish(values);
        return;
      }
      auto middle = cases.size() / 2;
      auto pivot = c.number(cases[middle], "pivot");
      auto left = c.compare("index.less", inputs[selector], pivot, "partition");
      auto values = c.conditional(
          left, inputs, outputs, "dispatch",
          [&](unsigned branch, func::FuncOp region) {
            body(region, formals, outputs, true,
                 [&](Cursor &c, ValueRange captured) {
                   func::FuncOp selected;
                   auto result = c.local(
                       captured, outputs,
                       "selected_branch_" + std::to_string(branch), selected);
                   auto subset = branch == 0 ? cases.take_front(middle)
                                             : cases.drop_front(middle);
                   dispatch(selected, selector, subset, formals, outputs, leaf);
                   c.finish(result, true);
                 });
          });
      c.finish(values);
    });
  }
  void dispatch(func::FuncOp function, unsigned selector,
                ArrayRef<unsigned> cases,
                llvm::function_ref<void(unsigned, func::FuncOp)> leaf) {
    dispatch(function, selector, cases, allTypes(), model.state, leaf);
  }
  void metadata(StringRef fieldName, ArrayRef<func::FuncOp> functions) {
    Types dispatchTypes{index, index};
    append_range(dispatchTypes, model.stores);
    for (unsigned kind = 0; kind < model.kinds.size(); ++kind) {
      SmallVector<unsigned> cases;
      for (const auto &item : model.constructors)
        if (item.kind == kind)
          cases.push_back(item.source);
      auto reference = cantFail(oracleReferenceType(model.kinds[kind]));
      Types inputs{reference};
      append_range(inputs, model.stores);
      body(functions[kind], inputs, index, false,
           [&](Cursor &c, ValueRange inputs) {
             auto identity =
                 c.unpack(inputs[0], TypeRange{index, index}, "reference");
             if (cases.empty()) {
               auto zero = c.number(0, "none");
               c.require(c.compare("index.less", zero, zero, "no_constructor"),
                         "unavailable_kind");
               c.finish(zero);
               return;
             }
             append_range(identity, inputs.drop_front());
             func::FuncOp select;
             auto value = c.local(identity, index, "select_count", select);
             dispatch(select, 0, cases, dispatchTypes, index,
                      [&](unsigned source, func::FuncOp leaf) {
                        auto found =
                            find_if(model.constructors, [&](const auto &item) {
                              return item.source == source;
                            });
                        unsigned constructor =
                            found - model.constructors.begin();
                        body(leaf, dispatchTypes, index, false,
                             [&](Cursor &c, ValueRange arguments) {
                               auto record = load(c, constructor, arguments[0],
                                                  arguments[1],
                                                  arguments[2 + constructor]);
                               c.finish(record[field(constructor, fieldName)]);
                             });
                      });
             c.finish(value);
           });
    }
  }
  void counts() {
    metadata("query.leaves", model.leafCounts);
    metadata("shape.rows", model.rowCounts);
    for (auto [ordinal, item] : enumerate(model.constructors)) {
      const auto &anchor = storage.constructors[item.source];
      Types sourceTypes;
      for (const auto &field : anchor.roles[item.role].fields)
        if (StringRef(field.name).starts_with("source."))
          sourceTypes.push_back(field.type);
      Types inputs(sourceTypes);
      append_range(inputs, model.stores);
      if (!expect(inputs.size() <= 512))
        return;
      const auto &queries = item.functions.queries;
      body(model.constructionCounts[ordinal], inputs, index, false,
           [&](Cursor &c, ValueRange inputs) {
             Value total = c.number(
                 anchor.constructor == OracleAnchorConstructor::Kind::Virtual
                     ? 0
                     : 1,
                 "initial_count");
             for (auto [i, query] : enumerate(queries)) {
               Values arguments{inputs[query.source]};
               append_range(arguments, inputs.drop_front(sourceTypes.size()));
               auto count =
                   c.call(model.leafCounts[kindNumber(query.kind)], arguments,
                          "child_count_" + std::to_string(i))
                       .front();
               total = c.apply("index.add", index, {total, count},
                               "sum_count_" + std::to_string(i))
                           .front();
             }
             c.finish(total);
           });
    }
  }
  void step(func::FuncOp function) {
    body(function, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto zero = c.number(0, "enter_phase");
           auto entering = c.compare("index.equal", inputs[Controller::Phase],
                                     zero, "phase");
           auto values = c.conditional(
               entering, inputs, model.state, "step",
               [&](unsigned branch, func::FuncOp region) {
                 body(region, allTypes(), model.state, true,
                      [&](Cursor &body, ValueRange captured) {
                        func::FuncOp selected;
                        auto values =
                            body.local(captured, model.state,
                                       branch == 0 ? "enter_transition"
                                                   : "return_transition",
                                       selected);
                        SmallVector<unsigned> cases;
                        if (branch == 0) {
                          for (auto item : model.constructors)
                            cases.push_back(item.source);
                          dispatch(
                              selected, Controller::Constructor, cases,
                              [&](unsigned source, func::FuncOp leaf) {
                                auto found = find_if(
                                    model.constructors, [&](const auto &item) {
                                      return item.source == source;
                                    });
                                enter(leaf, found - model.constructors.begin());
                              });
                        } else {
                          for (unsigned i = 0; i <= model.continuations.size();
                               ++i)
                            cases.push_back(i);
                          dispatch(
                              selected, Controller::Continuation, cases,
                              [&](unsigned continuation, func::FuncOp leaf) {
                                if (continuation)
                                  returned(leaf, continuation - 1);
                                else
                                  this->body(
                                      leaf, allTypes(), model.state, false,
                                      [&](Cursor &body, ValueRange arguments) {
                                        auto result = state(arguments);
                                        result[Controller::Phase] =
                                            body.number(3, "completed");
                                        body.finish(result);
                                      });
                              });
                        }
                        body.finish(values, true);
                      });
               });
           c.finish(values);
         });
  }
  void initialize() {
    auto reference = cantFail(oracleReferenceType(model.kinds.front()));
    body(model.initialize, TypeRange{reference, index}, model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto reference =
               c.unpack(inputs[0], TypeRange{index, index}, "root");
           auto zero = c.number(0, "initial");
           Values values{reference[0], reference[1], inputs[1], zero,
                         zero,         zero,         zero,      zero};
           for (auto [slot, type] :
                enumerate(ArrayRef<Type>(model.state)
                              .drop_front(Controller::HeaderSize)))
             values.push_back(
                 c.empty(type, "empty_state_" + std::to_string(slot)));
           c.finish(values);
         });
  }
  void resume() {
    for (unsigned kind = 0; kind < model.kinds.size(); ++kind) {
      Types inputs(model.state.begin(), model.state.end());
      inputs.append(5, index);
      inputs.push_back(model.kinds[kind].getAnswerType());
      body(model.resume[kind], inputs, model.state, false,
           [&](Cursor &c, ValueRange inputs) {
             auto values = state(inputs);
             c.equalTo(values[Controller::Phase], 2, "suspended");
             c.equalTo(values[Controller::Kind], kind, "kind");
             for (unsigned i = 0; i < 5; ++i) {
               auto equal = c.compare(
                   "index.equal", values[i], inputs[model.state.size() + i],
                   "request_coordinate_" + std::to_string(i));
               c.require(equal, "same_request_" + std::to_string(i));
             }
             putAnswer(c, values, kind, inputs.back());
             c.finish(values);
           });
    }
  }
  void advance() {
    body(model.advance, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto zero = c.number(0, "lower");
           auto two = c.number(2, "suspension_phase");
           auto allowed = c.compare("index.less", inputs[Controller::Phase],
                                    two, "can_advance");
           c.require(allowed, "admit_advance");
           auto upper =
               c.number(model.capacity.nodes * 2 + 1, "transition_bound");
           auto values =
               c.loop(zero, upper, state(inputs), stores(inputs), "advance",
                      [&](func::FuncOp region) {
                        Types inputs{index};
                        append_range(inputs, allTypes());
                        Types outputs{boolean};
                        append_range(outputs, model.state);
                        body(region, inputs, outputs, true,
                             [&](Cursor &body, ValueRange captures) {
                               func::FuncOp transition;
                               auto values =
                                   body.local(captures.drop_front(),
                                              model.state, "step", transition);
                               step(transition);
                               auto threshold =
                                   body.number(2, "iteration_suspension_phase");
                               auto proceed = body.compare(
                                   "index.less", values[Controller::Phase],
                                   threshold, "continuing");
                               Values yielded{proceed};
                               append_range(yielded, values);
                               body.finish(yielded, true);
                             });
                      });
           auto one = c.number(1, "return_phase");
           auto stopped =
               c.compare("index.less", one, values[Controller::Phase],
                         "stopped_advancing");
           c.require(stopped, "complete_advance");
           c.finish(values);
         });
  }
  void finish() {
    body(model.finish, model.state, model.kinds.front().getAnswerType(), false,
         [&](Cursor &c, ValueRange inputs) {
           c.equalTo(inputs[Controller::Phase], 3, "completed");
           c.equalTo(inputs[Controller::Kind], 0, "root_kind");
           c.finish(getAnswer(c, inputs, 0));
         });
  }
  void leaf(func::FuncOp function, unsigned constructor) {
    body(function, allTypes(), model.state, false,
         [&](Cursor &c, ValueRange inputs) {
           auto values = state(inputs);
           const auto &item = model.constructors[constructor];
           auto record =
               load(c, constructor, values[Controller::Constructor],
                    values[Controller::Instance], stores(inputs)[constructor]);
           func::FuncOp read;
           auto answer = c.local({record[field(constructor, "data")],
                                  record[field(constructor, "shape.rows")],
                                  values[Controller::Position]},
                                 model.kinds[item.kind].getAnswerType(),
                                 "leaf_answer", read)
                             .front();
           if (valid)
             if (auto e = checkOracleTableRead(
                     context, read, storage.constructors[item.source].kind)) {
               consumeError(std::move(e));
               valid = false;
             }
           Values arguments(values);
           append_range(arguments, ValueRange(values).take_front(5));
           arguments.push_back(answer);
           c.finish(c.call(model.resume[item.kind], arguments, "resume"));
         });
  }
  void contents() {
    if (model.access != OracleControllerAccess::Holder) {
      expect(!model.contents);
      return;
    }
    if (!expect(bool(model.evaluate)))
      return;
    auto root = model.kinds.front();
    auto answer = encodeBoundType(root.getAnswerType(), false);
    if (!answer) {
      consumeError(answer.takeError());
      valid = false;
      return;
    }
    std::string family = "sequence";
    std::vector<std::string> statics{answer->spelling()};
    if (answer->kind == "index") {
      family = "indices";
      statics.clear();
    } else if (answer->kind == "field" || answer->kind == "group") {
      family = answer->kind == "field" ? "vector" : "curve";
      statics = {answer->identity};
    }
    Type data = root.getDataType();
    auto reference = cantFail(oracleReferenceType(root));
    Types arguments{reference};
    append_range(arguments, model.stores);
    Types dispatchTypes{index, index};
    append_range(dispatchTypes, model.stores);
    SmallVector<unsigned> cases;
    for (const auto &item : model.constructors)
      if (item.kind == 0)
        cases.push_back(item.source);
    body(model.contents, arguments, data, false,
         [&](Cursor &c, ValueRange inputs) {
           auto identity =
               c.unpack(inputs[0], TypeRange{index, index}, "reference");
           append_range(identity, inputs.drop_front());
           func::FuncOp select;
           auto result = c.local(identity, data, "select_contents", select);
           dispatch(
               select, 0, cases, dispatchTypes, data,
               [&](unsigned source, func::FuncOp leaf) {
                 auto item = find_if(model.constructors, [&](const auto &item) {
                   return item.source == source;
                 });
                 unsigned constructor = item - model.constructors.begin();
                 body(leaf, dispatchTypes, data, false,
                      [&](Cursor &c, ValueRange inputs) {
                        auto record = load(c, constructor, inputs[0], inputs[1],
                                           inputs[2 + constructor]);
                        if (storage.constructors[source].constructor !=
                            OracleAnchorConstructor::Kind::Virtual) {
                          c.finish(record[field(constructor, "data")]);
                          return;
                        }
                        auto root =
                            c.pack(reference, inputs.take_front(2), "root");
                        auto zero = c.number(0, "lower");
                        auto empty = c.apply(family + ".empty", data, {},
                                             "empty", statics)
                                         .front();
                        Values captures{root};
                        append_range(captures, inputs.drop_front(2));
                        auto result = c.loop(
                            zero, record[field(constructor, "shape.rows")],
                            empty, captures, data, false, "rows",
                            [&](func::FuncOp row) {
                              Types arguments{index, data, reference};
                              append_range(arguments, model.stores);
                              body(row, arguments, data, true,
                                   [&](Cursor &c, ValueRange inputs) {
                                     Values query{inputs[2], inputs[0]};
                                     append_range(query, inputs.drop_front(3));
                                     auto answer = c.call(model.evaluate, query,
                                                          "evaluate")
                                                       .front();
                                     c.finish(c.apply(family + ".append", data,
                                                      {inputs[1], answer},
                                                      "append", statics),
                                              true);
                                   });
                            });
                        c.finish(result);
                      });
               });
           c.finish(result);
         });
  }
  void evaluate() {
    SmallVector<unsigned> leaves;
    for (const auto &item : model.constructors) {
      const auto &anchor = storage.constructors[item.source];
      if (anchor.constructor == OracleAnchorConstructor::Kind::Virtual)
        continue;
      if (none_of(anchor.roles[item.role].fields,
                  [](const auto &field) { return field.name == "data"; })) {
        expect(!model.evaluate);
        return;
      }
      leaves.push_back(item.source);
    }
    auto reference = cantFail(oracleReferenceType(model.kinds.front()));
    Types inputs{reference, index};
    append_range(inputs, model.stores);
    body(
        model.evaluate, inputs, model.kinds.front().getAnswerType(), false,
        [&](Cursor &c, ValueRange inputs) {
          auto initial =
              c.call(model.initialize, inputs.take_front(2), "initialize");
          auto zero = c.number(0, "lower");
          auto upper = c.number(model.capacity.leaves + 1, "request_bound");
          auto final = c.loop(
              zero, upper, initial, inputs.drop_front(2), "requests",
              [&](func::FuncOp region) {
                Types inputs{index};
                append_range(inputs, allTypes());
                Types outputs{boolean};
                append_range(outputs, model.state);
                body(
                    region, inputs, outputs, true,
                    [&](Cursor &iteration, ValueRange arguments) {
                      auto captured = arguments.drop_front();
                      auto state =
                          iteration.call(model.advance, captured, "advance");
                      auto requestPhase = iteration.number(2, "request_phase");
                      auto requested = iteration.compare(
                          "index.equal", state[Controller::Phase], requestPhase,
                          "has_request");
                      append_range(state, stores(captured));
                      auto next = iteration.conditional(
                          requested, state, model.state, "request",
                          [&](unsigned branch, func::FuncOp region) {
                            body(
                                region, allTypes(), model.state, true,
                                [&](Cursor &body, ValueRange captures) {
                                  if (branch) {
                                    body.finish(this->state(captures), true);
                                    return;
                                  }
                                  func::FuncOp request;
                                  auto values =
                                      body.local(captures, model.state,
                                                 "answer_request", request);
                                  if (leaves.empty())
                                    this->body(
                                        request, allTypes(), model.state, false,
                                        [&](Cursor &empty,
                                            ValueRange arguments) {
                                          auto zero = empty.number(0, "none");
                                          auto impossible =
                                              empty.compare("index.less", zero,
                                                            zero, "no_request");
                                          empty.require(impossible,
                                                        "unexpected_request");
                                          empty.finish(this->state(arguments));
                                        });
                                  else
                                    dispatch(
                                        request, Controller::Constructor,
                                        leaves,
                                        [&](unsigned source,
                                            func::FuncOp leaf) {
                                          auto found = find_if(
                                              model.constructors,
                                              [&](const auto &item) {
                                                return item.source == source;
                                              });
                                          this->leaf(
                                              leaf,
                                              found -
                                                  model.constructors.begin());
                                        });
                                  body.finish(values, true);
                                });
                          });
                      auto completed = iteration.number(3, "completed_phase");
                      auto proceed = iteration.compare("index.less",
                                                       next[Controller::Phase],
                                                       completed, "continuing");
                      Values yielded{proceed};
                      append_range(yielded, next);
                      iteration.finish(yielded, true);
                    });
              });
          c.finish(c.call(model.finish, final, "finish"));
        });
  }
};
} // namespace
Error checkOracleQueryController(ModuleOp candidate, ModuleOp prepared,
                                 const OracleAnchorStorage &storage,
                                 StringRef role, pir::OracleKindAttr root,
                                 OracleQuerySize capacity,
                                 const Controller &actual,
                                 OracleControllerAccess access) {
  auto targetContext = OracleVerificationContext::read(candidate);
  if (!targetContext) {
    consumeError(targetContext.takeError());
    return error("oracle-controller-body");
  }
  auto sourceContext = OracleVerificationContext::read(prepared);
  if (!sourceContext) {
    consumeError(sourceContext.takeError());
    return error("oracle-controller-body");
  }
  return checkOracleQueryController(*targetContext, *sourceContext, storage,
                                    role, root, capacity, actual, access);
}
Error checkOracleQueryController(const OracleVerificationContext &targetContext,
                                 const OracleVerificationContext &sourceContext,
                                 const OracleAnchorStorage &storage,
                                 StringRef role, pir::OracleKindAttr root,
                                 OracleQuerySize capacity,
                                 const Controller &actual,
                                 OracleControllerAccess access) {
  auto refuse = [] { return error("oracle-controller-body"); };
  if (targetContext.getUnit() == sourceContext.getUnit() ||
      targetContext.getModule().getContext() !=
          sourceContext.getModule().getContext())
    return refuse();
  if (auto e = layout(targetContext, sourceContext, storage, role, root,
                      capacity, actual, access)) {
    consumeError(std::move(e));
    return refuse();
  }
  Reader reader(storage, actual, targetContext);
  reader.counts();
  reader.initialize();
  reader.resume();
  reader.advance();
  reader.finish();
  reader.evaluate();
  reader.contents();
  return reader.valid ? Error::success() : refuse();
}
} // namespace zkc::protocol

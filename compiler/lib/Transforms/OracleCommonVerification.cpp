#include "OracleAccounting.h"
#include "OracleCommonPlan.h"
#include "OracleNativeCommon.h"
#include "OracleQuerySchedule.h"
#include "OracleVerificationContext.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SaveAndRestore.h"
#include <map>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
Error refuse() { return error("oracle-common-body"); }
using Values = std::vector<Value>;
using Types = std::vector<Type>;

Expected<Type> converted(Type type, OracleNativeWork &work) {
  if (auto handle = dyn_cast<pir::OracleHandleType>(type))
    return oracleReferenceTypeWithWork(handle.getKind(), work);
  if (auto sequence = dyn_cast<pir::OracleSequenceType>(type)) {
    auto element = oracleReferenceTypeWithWork(sequence.getKind(), work);
    if (!element)
      return element.takeError();
    auto result = constructLogicalType(
        [&] { return emitError(UnknownLoc::get(type.getContext())); },
        type.getContext(), {"sequence", {TypeAttr::get(*element)}});
    if (!result)
      return error("oracle-common-profile");
    return result;
  }
  return type;
}
bool logical(Type type) {
  return isa<pir::OracleHandleType, pir::OracleSequenceType>(type);
}
Expected<NativeBindingApplication> length(pir::OracleKindAttr kind) {
  Type answer = kind.getAnswerType();
  auto *context = kind.getContext();
  if (answer == IntegerType::get(context, 64, IntegerType::Unsigned))
    return NativeBindingApplication{"indices.length", {}, ""};
  if (auto field = dyn_cast<algebra::FieldType>(answer))
    return NativeBindingApplication{
        "vector.length", {StringAttr::get(context, field.getDomain())}, ""};
  if (auto group = dyn_cast<algebra::GroupType>(answer))
    return NativeBindingApplication{
        "curve.length", {StringAttr::get(context, group.getDomain())}, ""};
  return NativeBindingApplication{
      "sequence.length", {TypeAttr::get(answer)}, ""};
}
// A reader result contains only derived facts and typed local obligations.
// There is no candidate-shaped expected body and no call to materialization.
struct SourceReader {
  ModuleOp source;
  pir::MathematicalOp program;
  SymbolTable &sourceSymbols;
  Operation *activeSource = nullptr;
  const OracleCommonRequirements &requirements;
  ArrayRef<OracleCommonController> controllers;
  ArrayRef<std::vector<func::FuncOp>> allocators;
  ArrayRef<OracleMerkleFunctions> merkle;
  OracleAuthentication authentication;
  const OracleQuerySchedule &schedule;
  ArrayRef<OracleCommonRemote> remotes;
  ArrayRef<OracleCommonBatch> batches;
  std::map<unsigned, Value> inputRows;
  Builder builder;
  Type index;
  OracleCommonAnalysis result;
  std::vector<std::pair<Operation *, Operation *>> associations;
  OracleNativeWork &work;
  pir::MathematicalOp candidate;
  llvm::DenseMap<Block *, Block::iterator> cursors;
  unsigned nextArgument = 0;
  std::string occurrencePrefix;
  std::map<std::pair<unsigned, unsigned>, Value> store;
  llvm::DenseMap<Value, Value> values;
  struct DataView {
    Value reference;
    std::string holder;
    Type type;
  };
  llvm::DenseMap<Value, DataView> dataViews;
  Values coordinates;
  explicit SourceReader(ModuleOp source, pir::MathematicalOp program,
                        const OracleCommonRequirements &requirements,
                        ArrayRef<OracleCommonController> controllers,
                        ArrayRef<std::vector<func::FuncOp>> allocators,
                        ArrayRef<OracleMerkleFunctions> merkle,
                        OracleAuthentication authentication,
                        const OracleQuerySchedule &schedule,
                        ArrayRef<OracleCommonRemote> remotes,
                        ArrayRef<OracleCommonBatch> batches,
                        pir::MathematicalOp candidate,
                        OracleNativeWork &sharedWork,
                        SymbolTable &sourceSymbols)
      : source(source), program(program), sourceSymbols(sourceSymbols),
        requirements(requirements), controllers(controllers),
        allocators(allocators), merkle(merkle), authentication(authentication),
        schedule(schedule), remotes(remotes), batches(batches),
        builder(source.getContext()),
        index(IntegerType::get(source.getContext(), 64, IntegerType::Unsigned)),
        work(sharedWork), candidate(candidate) {
    llvm::StringSet<> used;
    program.walk([&](Operation *op) {
      if (!work.charge(1 + op->getNumOperands() + op->getNumResults()))
        return WalkResult::interrupt();
      if (auto site = op->getAttrOfType<StringAttr>("site")) {
        auto name = site.getValue();
        if (name.consume_front("oracle_")) {
          auto separator = name.find('_');
          if (separator != StringRef::npos)
            used.insert(name.take_front(separator));
        }
      }
      return WalkResult::advance();
    });
    for (unsigned suffix = 0;; ++suffix) {
      if (!work.charge())
        break;
      if (!used.contains(std::to_string(suffix))) {
        occurrencePrefix = "oracle_" + std::to_string(suffix) + "_";
        break;
      }
    }
  }
  Operation *peek(Block &block) {
    auto [cursor, inserted] = cursors.try_emplace(&block, block.begin());
    return cursor->second == block.end() ? nullptr : &*cursor->second;
  }
  bool complete(Block &block) { return !peek(block); }
  Expected<Block *> region(Block &parent, TypeRange types, unsigned arm = 0) {
    if (!work.charge(1 + types.size()))
      return error("oracle-common-limit");
    auto *control = peek(parent);
    if (!control || arm >= control->getNumRegions() ||
        !hasSingleElement(control->getRegion(arm)))
      return refuse();
    auto &body = control->getRegion(arm).front();
    if (!equal(body.getArgumentTypes(), types) || cursors.count(&body))
      return refuse();
    cursors.try_emplace(&body, body.begin());
    return &body;
  }
  template <typename Op>
  Expected<Values> read(Block &block, TypeRange types, ValueRange inputs,
                        DictionaryAttr attributes = {},
                        ArrayRef<Block *> regions = {}) {
    if (!work.operation(inputs.size() + types.size() + regions.size()))
      return error("oracle-common-limit");
    auto *op = peek(block);
    auto expected = attributes ? attributes : builder.getDictionaryAttr({});
    if (!op || !isa<Op>(op) || op->getAttrDictionary() != expected ||
        !equal(op->getResultTypes(), types) ||
        !equal(op->getOperands(), inputs) ||
        op->getNumRegions() != regions.size())
      return refuse();
    for (auto [i, body] : enumerate(regions))
      if (!hasSingleElement(op->getRegion(i)) ||
          &op->getRegion(i).front() != body || !complete(*body))
        return refuse();
    ++cursors.find(&block)->second;
    if (activeSource)
      associations.emplace_back(activeSource, op);
    return Values(op->getResults().begin(), op->getResults().end());
  }
  Expected<Values> preserved(Block &block, Operation &original, TypeRange types,
                             ValueRange inputs) {
    if (!work.operation(inputs.size() + types.size()))
      return error("oracle-common-limit");
    Operation *actual = peek(block);
    // Compare actual source operands through the closed environment, not their
    // type or position in a producer's occurrence record. Extra store operands
    // on structural returns/yields were derived from source control above.
    if (!actual || actual->getName() != original.getName() ||
        actual->getAttrDictionary() != original.getAttrDictionary() ||
        actual->getNumRegions() != original.getNumRegions() ||
        !equal(actual->getResultTypes(), types) ||
        !equal(actual->getOperands(), inputs))
      return refuse();
    if (original.getNumRegions()) {
      if (auto failure = checkOracleNativeMathRegion(&original, work))
        return std::move(failure);
      if (auto failure = boundOracleNativeIR(actual, &work))
        return std::move(failure);
      llvm::DenseMap<Value, Value> mapped;
      for (auto [source, target] : zip(original.getOperands(), inputs))
        mapped[source] = target;
      if (!OperationEquivalence::isEquivalentTo(
              &original, actual,
              [&](Value source, Value target) {
                return success(mapped.lookup(source) == target);
              },
              [&](Value source, Value target) { mapped[source] = target; },
              OperationEquivalence::IgnoreLocations))
        return refuse();
    }
    ++cursors.find(&block)->second;
    associations.emplace_back(&original, actual);
    return Values(actual->getResults().begin(), actual->getResults().end());
  }
  Expected<Value> argument(Type type) {
    auto &body = candidate.getBody().front();
    if (!work.charge())
      return error("oracle-common-limit");
    if (nextArgument >= body.getNumArguments())
      return refuse();
    Value value = body.getArgument(nextArgument++);
    if (value.getType() != type)
      return refuse();
    return value;
  }
  DictionaryAttr attrs(std::initializer_list<NamedAttribute> values) {
    return builder.getDictionaryAttr(values);
  }
  NamedAttribute text(StringRef key, StringRef value) {
    return builder.getNamedAttr(key, builder.getStringAttr(value));
  }
  Expected<Value> constant(Block &block, uint64_t value) {
    auto output = read<data::IndexOp>(
        block, index, {},
        attrs({builder.getNamedAttr("value",
                                    builder.getIntegerAttr(index, value))}));
    if (!output)
      return output.takeError();
    return output->front();
  }
  std::string site(ArrayRef<unsigned> path, StringRef label,
                   StringRef role = {}) {
    if (!work.charge(1 + path.size()))
      return {};
    std::string name = occurrencePrefix +
                       std::to_string(result.occurrences.size()) + "_" +
                       label.str();
    result.occurrences.push_back(
        {name, label.str(), role.str(), {path.begin(), path.end()}});
    return name;
  }

  Expected<Values> call(Block &block, func::FuncOp helper, StringRef role,
                        ValueRange inputs, StringRef site) {
    if (!helper || helper.getNumResults() != 1)
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    auto outcome = dyn_cast<exec::OutcomeType>(helper.getResultTypes()[0]);
    if (!outcome || helper.getNumArguments() != inputs.size() + 1)
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    return read<pir::LocalCallOp>(
        block, outcome.getPayload(), inputs,
        attrs({builder.getNamedAttr("callee", FlatSymbolRefAttr::get(helper)),
               text("role", role), text("site", site)}));
  }
  Expected<Values> call(Block &block, const OracleHelperSignature &local,
                        StringRef role, ValueRange inputs, StringRef site) {
    return read<pir::LocalCallOp>(
        block, local.outputs, inputs,
        attrs({builder.getNamedAttr(
                   "callee",
                   FlatSymbolRefAttr::get(builder.getContext(), local.name)),
               text("role", role), text("site", site)}));
  }
  Expected<Value> assemble(Block &block, Type type, ValueRange components,
                           ArrayRef<std::string> roles) {
    SmallVector<StringRef> names;
    for (const auto &role : roles)
      names.push_back(role);
    auto output = read<pir::AssembleRolesOp>(
        block, type, components,
        attrs({builder.getNamedAttr("roles", builder.getStrArrayAttr(names))}));
    if (!output)
      return output.takeError();
    return output->front();
  }
  Expected<Value> value(Value original) {
    if (!work.charge())
      return error("oracle-common-limit");
    auto found = values.find(original);
    if (found == values.end())
      return error("oracle-common-value");
    return found->second;
  }
  Error demand(Block &block, Value original, ArrayRef<unsigned> path) {
    if (values.contains(original))
      return Error::success();
    auto found = dataViews.find(original);
    if (found == dataViews.end())
      return error("oracle-common-value");
    const auto &view = found->second;
    auto kind = pir::getOracleFamilyKind(view.type);
    auto *body = controller(view.holder, kind, OracleControllerAccess::Holder);
    if (!body || !body->contents)
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    auto captures = stores(*body);
    if (!captures)
      return captures.takeError();
    if (auto sequence = dyn_cast<pir::OracleSequenceType>(view.type)) {
      // A component view stays lazy through internal ports. Enumerate data
      // only when an ordinary consumer actually demands this projection.
      Type data = pir::getOracleFamilyDataType(view.type);
      if (!data)
        return error("oracle-common-limit");
      auto empty = read<data::SequenceEmptyOp>(block, data, {});
      if (!empty)
        return empty.takeError();
      auto count = read<data::SequenceLengthOp>(block, index, {view.reference});
      if (!count)
        return count.takeError();
      auto output = traverseSequence(
          block, sequence, view.reference, count->front(), view.holder,
          *captures, body->stores, data, *empty, path, "component_data",
          [&](Block &region, Value reference, ValueRange carried,
              ValueRange stores) -> Expected<Values> {
            Values arguments{reference};
            append_range(arguments, stores);
            auto element = call(region, body->contents, view.holder, arguments,
                                site(path, "component_element", view.holder));
            if (!element)
              return element.takeError();
            return read<data::SequenceAppendOp>(
                region, data, {carried.front(), element->front()});
          });
      if (!output)
        return output.takeError();
      values[original] = output->front();
      return Error::success();
    }
    Values arguments{view.reference};
    append_range(arguments, *captures);
    auto output = call(block, body->contents, view.holder, arguments,
                       site(path, "component_data", view.holder));
    if (!output)
      return output.takeError();
    values[original] = output->front();
    return Error::success();
  }
  Expected<Values> inputs(ValueRange originals) {
    if (!work.charge(originals.size()))
      return error("oracle-common-limit");
    Values result;
    for (Value original : originals) {
      auto mapped = value(original);
      if (!mapped)
        return mapped.takeError();
      result.push_back(*mapped);
    }
    return result;
  }
  const OracleQueryController *controller(
      StringRef role, pir::OracleKindAttr kind,
      OracleControllerAccess access = OracleControllerAccess::Available) {
    for (const auto &item : controllers) {
      if (!work.charge())
        return nullptr;
      if (item.role == role && item.access == access &&
          sameOracleReferenceKind(item.kind, kind))
        return &item.body;
    }
    return nullptr;
  }
  Expected<Value> stored(std::pair<unsigned, unsigned> key) {
    if (!work.charge())
      return error("oracle-common-limit");
    auto found = store.find(key);
    if (found == store.end() || !found->second)
      return error("oracle-common-store");
    return found->second;
  }
  Expected<Values> stores(const OracleQueryController &body) {
    Values inputs;
    if (!work.charge(body.constructors.size()))
      return error("oracle-common-limit");
    for (const auto &constructor : body.constructors) {
      auto found = store.find({constructor.source, constructor.role});
      if (found == store.end())
        return error("oracle-common-store");
      inputs.push_back(found->second);
    }
    return inputs;
  }
  Expected<OracleLocalRecipe> local(TypeRange inputs, TypeRange outputs) {
    auto recipe = oracleLocalRecipe(inputs, outputs, work);
    if (!recipe)
      return recipe.takeError();
    auto unit = cast<pir::ProtocolModuleOp>(source.getBody()->front());
    unsigned ordinal = 0;
    for (auto other : unit.getBody().front().getOps<pir::MathematicalOp>()) {
      if (!work.charge())
        return error("oracle-common-limit");
      if (other == program)
        break;
      ++ordinal;
    }
    std::string prefix =
        "_oracle_common_local_" + std::to_string(ordinal) + "_";
    unsigned suffix = result.locals.size();
    do {
      if (!work.charge(1 + result.locals.size()))
        return error("oracle-common-limit");
      recipe->name = prefix + std::to_string(suffix++);
    } while (sourceSymbols.lookup(recipe->name) ||
             any_of(result.locals, [&](const auto &other) {
               return localSignature(other).name == recipe->name;
             }));
    return std::move(*recipe);
  }
  Expected<std::vector<unsigned>> apply(OracleLocalRecipe &recipe,
                                        NativeBindingApplication binding,
                                        TypeRange types,
                                        ArrayRef<unsigned> inputs,
                                        ArrayRef<Attribute> parameters = {}) {
    return appendOracleLocalInstruction(recipe, std::move(binding), types,
                                        inputs, parameters, work);
  }
  Expected<unsigned> scalar(OracleLocalRecipe &recipe,
                            NativeBindingApplication binding, Type type,
                            ArrayRef<unsigned> inputs,
                            ArrayRef<Attribute> parameters = {}) {
    auto outputs = apply(recipe, std::move(binding), type, inputs, parameters);
    if (!outputs)
      return outputs.takeError();
    return outputs->front();
  }
  Expected<unsigned> number(OracleLocalRecipe &recipe, uint64_t n) {
    return scalar(recipe, {"index.constant", {}, ""}, index, {},
                  {IntegerAttr::get(index, n)});
  }
  Error require(OracleLocalRecipe &recipe, unsigned condition) {
    auto outputs = apply(recipe, {"control.require", {}, ""}, {}, {condition});
    if (!outputs)
      return outputs.takeError();
    return Error::success();
  }
  Error same(OracleLocalRecipe &recipe, unsigned left, unsigned right) {
    auto equal = scalar(recipe, {"index.equal", {}, ""}, builder.getI1Type(),
                        {left, right});
    if (!equal)
      return equal.takeError();
    return require(recipe, *equal);
  }
  Expected<Values>
  traverseSequence(Block &block, pir::OracleSequenceType sequence,
                   Value reference, Value count, StringRef role,
                   ValueRange captures, TypeRange captureTypes,
                   TypeRange carriedTypes, ValueRange seeds,
                   ArrayRef<unsigned> path, StringRef purpose,
                   llvm::function_ref<Expected<Values>(Block &, Value,
                                                       ValueRange, ValueRange)>
                       visit) {
    // Common repeat has its own finite native bound. Do not narrow a logical
    // uint64 capacity into its signed attribute or silently truncate traversal.
    if (sequence.getMaximum() > 1048576)
      return error("oracle-common-limit");
    auto sequenceType = converted(sequence, work);
    if (!sequenceType)
      return sequenceType.takeError();
    auto element = oracleReferenceTypeWithWork(sequence.getKind(), work);
    if (!element)
      return element.takeError();
    auto select = local({*sequenceType, index}, *element);
    if (!select)
      return select.takeError();
    auto selectedResults =
        apply(*select, {"sequence.at", {TypeAttr::get(*element)}, ""}, *element,
              {0, 1});
    if (!selectedResults)
      return selectedResults.takeError();
    select->results = std::move(*selectedResults);
    Types regionTypes{index};
    append_range(regionTypes, carriedTypes);
    regionTypes.push_back(*sequenceType);
    append_range(regionTypes, captureTypes);
    auto created = region(block, regionTypes);
    if (!created)
      return created.takeError();
    Block *nested = *created;
    unsigned referenceIndex = 1 + seeds.size();
    auto selected = call(*nested, *select, role,
                         {nested->getArguments()[referenceIndex],
                          nested->getArguments().front()},
                         site(path, "sequence_reference", role));
    if (!selected)
      return selected.takeError();
    result.locals.push_back(std::move(*select));
    ValueRange arguments(nested->getArguments());
    auto yielded =
        visit(*nested, selected->front(), arguments.slice(1, seeds.size()),
              arguments.drop_front(referenceIndex + 1));
    if (!yielded)
      return yielded.takeError();
    auto terminator = read<pir::ProtocolYieldOp>(*nested, {}, *yielded);
    if (!terminator)
      return terminator.takeError();
    Values inputs{count};
    append_range(inputs, seeds);
    inputs.push_back(reference);
    append_range(inputs, captures);
    SmallVector<Attribute> carriedRoles(seeds.size(),
                                        builder.getStrArrayAttr({role}));
    return read<pir::RepeatOp>(
        block, carriedTypes, inputs,
        attrs({text("site", site(path, purpose, role)),
               builder.getNamedAttr("carried",
                                    builder.getI64IntegerAttr(seeds.size())),
               builder.getNamedAttr(
                   "maximum", builder.getI64IntegerAttr(sequence.getMaximum())),
               builder.getNamedAttr("roles", builder.getStrArrayAttr({role})),
               builder.getNamedAttr("carried_roles",
                                    builder.getArrayAttr(carriedRoles))}),
        {nested});
  }
  Expected<OracleLocalRecipe> checkShape(pir::OracleKindAttr kind,
                                         DictionaryAttr bounds, bool data,
                                         bool inferred) {
    Types inputs;
    if (data)
      inputs.push_back(kind.getDataType());
    if (!inferred)
      inputs.push_back(index);
    auto recipe = local(inputs, index);
    if (!recipe)
      return recipe.takeError();
    unsigned rows = data && !inferred ? 1 : 0;
    if (data) {
      auto binding = length(kind);
      if (!binding)
        return binding.takeError();
      auto actual = scalar(*recipe, *binding, index, {0});
      if (!actual)
        return actual.takeError();
      if (inferred)
        rows = *actual;
      else if (auto e = same(*recipe, rows, *actual))
        return std::move(e);
    }
    auto dimensions = kind.getShapeDimensions();
    if (dimensions.size() != 1 || dimensions[0].name != "rows")
      return refuse();
    if (dimensions[0].extent) {
      auto expected = number(*recipe, *dimensions[0].extent);
      if (!expected)
        return expected.takeError();
      if (auto e = same(*recipe, rows, *expected))
        return std::move(e);
    } else {
      auto bound = bounds.getAs<IntegerAttr>("rows");
      if (!bound)
        return refuse();
      auto maximum = number(*recipe, bound.getValue().getZExtValue());
      if (!maximum)
        return maximum.takeError();
      auto tooLarge = scalar(*recipe, {"index.less", {}, ""},
                             builder.getI1Type(), {*maximum, rows});
      if (!tooLarge)
        return tooLarge.takeError();
      auto no = scalar(*recipe, {"bool.not", {}, ""}, builder.getI1Type(),
                       {*tooLarge});
      if (!no)
        return no.takeError();
      if (auto e = require(*recipe, *no))
        return std::move(e);
    }
    recipe->results = {rows};
    return std::move(*recipe);
  }

  Error checkSequenceRebinding(Block &block, pir::OracleInputOp input,
                               Value reference, ArrayRef<unsigned> path) {
    auto sequence =
        dyn_cast<pir::OracleSequenceType>(input.getHandle().getType());
    if (!sequence)
      return Error::success();
    auto type = converted(sequence, work);
    if (!type)
      return type.takeError();
    auto element = oracleReferenceTypeWithWork(sequence.getKind(), work);
    if (!element)
      return element.takeError();
    auto capacity = local(*type, index);
    if (!capacity)
      return capacity.takeError();
    auto count =
        scalar(*capacity, {"sequence.length", {TypeAttr::get(*element)}, ""},
               index, {0});
    if (!count)
      return count.takeError();
    auto maximum = number(*capacity, sequence.getMaximum());
    if (!maximum)
      return maximum.takeError();
    auto tooLarge = scalar(*capacity, {"index.less", {}, ""},
                           builder.getI1Type(), {*maximum, *count});
    if (!tooLarge)
      return tooLarge.takeError();
    auto allowed = scalar(*capacity, {"bool.not", {}, ""}, builder.getI1Type(),
                          {*tooLarge});
    if (!allowed)
      return allowed.takeError();
    if (auto e = require(*capacity, *allowed))
      return e;
    capacity->results = {*count};
    // Reserve helper identities before generating nested recipes.
    result.locals.push_back(*capacity);
    SmallVector<Attribute> roles{input.getHolderAttr()};
    append_range(roles, input.getReceivers());
    auto kind = sequence.getKind();
    for (auto attribute : roles) {
      auto role = cast<StringAttr>(attribute).getValue();
      auto checked = call(block, *capacity, role, {reference},
                          site(path, "sequence_capacity", role));
      if (!checked)
        return checked.takeError();
      // Row bounds constrain each actual element, independently of the
      // sequence capacity. Metadata reads never evaluate virtual contents.
      if (kind.getStaticShape("rows") || !sequence.getMaximum())
        continue;
      auto *body = controller(role, kind);
      if (!body || body->rowCounts.empty())
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-helper");
      auto captures = stores(*body);
      if (!captures)
        return captures.takeError();
      auto shape = checkShape(kind, input.getShapeBounds(), false, false);
      if (!shape)
        return shape.takeError();
      result.locals.push_back(*shape);
      auto output = traverseSequence(
          block, sequence, reference, checked->front(), role, *captures,
          body->stores, {}, {}, path, "sequence_shape",
          [&](Block &region, Value element, ValueRange,
              ValueRange stores) -> Expected<Values> {
            Values arguments{element};
            append_range(arguments, stores);
            auto rows = call(region, body->rowCounts[0], role, arguments,
                             site(path, "element_rows", role));
            if (!rows)
              return rows.takeError();
            auto checked = call(region, *shape, role, *rows,
                                site(path, "element_shape", role));
            if (!checked)
              return checked.takeError();
            return Values{};
          });
      if (!output)
        return output.takeError();
    }
    return Error::success();
  }
  Operation *sourceOperation(ArrayRef<unsigned> path) {
    Block *body = &program.getBody().front();
    Operation *op = nullptr;
    for (unsigned i = 0; i < path.size(); ++i) {
      if (!work.charge(1 + uint64_t(path[i])))
        return nullptr;
      auto operation = body->begin();
      for (unsigned offset = 0; offset < path[i] && operation != body->end();
           ++offset)
        ++operation;
      if (operation == body->end())
        return nullptr;
      op = &*operation;
      if (i + 1 == path.size())
        return op;
      if (auto repeat = dyn_cast<pir::RepeatOp>(op))
        body = &repeat.getBody().front();
      else if (auto branch = dyn_cast<pir::BranchOp>(op)) {
        if (i + 2 >= path.size())
          return nullptr;
        unsigned arm = path[++i];
        if (arm >= branch->getNumRegions())
          return nullptr;
        body = &branch->getRegion(arm).front();
      } else
        return nullptr;
    }
    return op;
  }
  std::optional<unsigned> inputAnchor(Value anchor) {
    while (auto restricted = anchor.getDefiningOp<pir::RestrictRolesOp>())
      anchor = restricted.getInput();
    auto argument = dyn_cast<BlockArgument>(anchor);
    if (!argument || argument.getOwner() != &program.getBody().front())
      return {};
    return argument.getArgNumber();
  }
  Error construct(Block &block, Operation &op, ArrayRef<unsigned> path,
                  unsigned ordinal) {
    const auto &construction = requirements.storage.constructors[ordinal];
    if (coordinates.size() != construction.repeatDepth)
      return error("oracle-common-store");
    auto kind = construction.kind;
    auto reference = oracleReferenceTypeWithWork(kind, work);
    if (!reference)
      return reference.takeError();
    Values references;
    std::vector<std::string> roles;
    std::map<std::string, Value> delivered;
    if (auto send = dyn_cast<pir::OracleSendOp>(op)) {
      auto data = value(send.getData());
      if (!data)
        return data.takeError();
      delivered[construction.holder] = *data;
    }
    Value incoming;
    Values committed;
    if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
      auto data = value(input.getData()), anchor = value(input.getAnchor());
      if (!data)
        return data.takeError();
      if (!anchor)
        return anchor.takeError();
      delivered[construction.holder] = *data;
      incoming = *anchor;
    }
    for (auto [roleIndex, role] : enumerate(construction.roles)) {
      auto *body = controller(role.role, kind);
      if (!body)
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-helper");
      auto captures = stores(*body);
      if (!captures)
        return captures.takeError();
      auto found = find_if(body->constructors, [&](const auto &item) {
        return item.source == ordinal;
      });
      if (found == body->constructors.end())
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-helper");
      Value row;
      Values payload, children;
      if (auto virtualOracle = dyn_cast<pir::OracleVirtualOp>(op)) {
        auto declaration = cast<pir::OracleDefinitionOp>(
            sourceSymbols.lookup(virtualOracle.getCallee()));
        auto actual = inputs(virtualOracle.getInputs());
        if (!actual)
          return actual.takeError();
        payload = *actual;
        children.assign(actual->begin(),
                        actual->begin() + declaration.getNumSources());
        Value raw;
        auto dimension = kind.getShapeDimensions()[0];
        if (dimension.extent) {
          auto n = constant(block, *dimension.extent);
          if (!n)
            return n.takeError();
          raw = *n;
        } else {
          auto argument =
              declaration.getShapeArguments().getAs<IntegerAttr>("rows");
          if (!argument)
            return refuse();
          raw = (*actual)[argument.getValue().getZExtValue()];
        }
        auto recipe =
            checkShape(kind, declaration.getShapeBounds(), false, false);
        if (!recipe)
          return recipe.takeError();
        auto checked = call(block, *recipe, role.role, {raw},
                            site(path, "shape", role.role));
        if (!checked)
          return checked.takeError();
        row = checked->front();
        result.locals.push_back(std::move(*recipe));
      } else {
        bool authenticated = !construction.scheme.empty();
        bool holder = role.role == construction.holder;
        DictionaryAttr bounds;
        bool inferred =
            isa<pir::OracleInputOp>(op) && (!authenticated || holder);
        Values arguments;
        if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
          bounds = input.getShapeBounds();
          if (!holder) {
            delivered[role.role] = incoming;
            if (authenticated) {
              auto dimension = kind.getShapeDimensions()[0];
              if (dimension.extent) {
                auto count = constant(block, *dimension.extent);
                if (!count)
                  return count.takeError();
                arguments.push_back(*count);
              } else {
                auto anchor = inputAnchor(input.getAnchor());
                if (!anchor || !inputRows.count(*anchor))
                  return error("oracle-common-interface");
                arguments.push_back(inputRows.at(*anchor));
              }
            }
          }
        } else {
          auto send = cast<pir::OracleSendOp>(op);
          bounds = send.getShapeBounds();
          if (!holder) {
            if (authenticated && committed.size() != 2)
              return error(work.exhausted ? "oracle-common-limit"
                                          : "oracle-common-helper");
            auto commit = merkle[ordinal].commit;
            Type deliveryType =
                authenticated
                    ? cast<exec::OutcomeType>(commit.getResultTypes()[0])
                          .getPayload()[0]
                    : kind.getDataType();
            auto exchange = read<pir::ExchangeOp>(
                block, deliveryType,
                {authenticated ? committed[0] : delivered[construction.holder]},
                attrs({text("sender", construction.holder),
                       text("receiver", role.role),
                       text("site", site(path, "deliver", role.role))}));
            if (!exchange)
              return exchange.takeError();
            delivered[role.role] = exchange->front();
          }
          auto dimension = value(send.getShapeOperand("rows"));
          if (!dimension)
            return dimension.takeError();
          arguments.push_back(*dimension);
        }
        bool data = !authenticated || holder;
        if (data)
          arguments.insert(arguments.begin(), delivered[role.role]);
        auto recipe = checkShape(kind, bounds, data, inferred);
        if (!recipe)
          return recipe.takeError();
        auto checked = call(block, *recipe, role.role, arguments,
                            site(path, "shape", role.role));
        if (!checked)
          return checked.takeError();
        row = checked->front();
        result.locals.push_back(std::move(*recipe));
        payload = {delivered[role.role]};
        if (authenticated) {
          if (holder) {
            auto output = call(block, merkle[ordinal].commit, role.role,
                               {delivered[role.role], row},
                               site(path, "commit", role.role));
            if (!output)
              return output.takeError();
            committed = *output;
            payload.push_back(committed[1]);
          } else {
            auto zero = constant(block, 0);
            if (!zero)
              return zero.takeError();
            auto admitted = call(block, merkle[ordinal].position, role.role,
                                 {row, *zero}, site(path, "layout", role.role));
            if (!admitted)
              return admitted.takeError();
          }
        }
      }
      append_range(children, *captures);
      auto count = call(
          block, body->constructionCounts[found - body->constructors.begin()],
          role.role, children, site(path, "count", role.role));
      if (!count)
        return count.takeError();
      auto previous = stored({ordinal, unsigned(roleIndex)});
      if (!previous)
        return previous.takeError();
      Values allocation{*previous};
      append_range(allocation, coordinates);
      allocation.push_back(row);
      allocation.push_back(count->front());
      append_range(allocation, payload);
      auto allocated = call(block, allocators[ordinal][roleIndex], role.role,
                            allocation, site(path, "allocate", role.role));
      if (!allocated)
        return allocated.takeError();
      references.push_back((*allocated)[0]);
      store[{ordinal, unsigned(roleIndex)}] = (*allocated)[1];
      roles.push_back(role.role);
    }
    auto joined = assemble(block, *reference, references, roles);
    if (!joined)
      return joined.takeError();
    values[op.getResult(0)] = *joined;
    return Error::success();
  }
  Error sequence(Block &block, Operation &op, ArrayRef<unsigned> path) {
    auto actual = inputs(op.getOperands());
    if (!actual)
      return actual.takeError();
    auto output = converted(op.getResult(0).getType(), work);
    if (!output)
      return output.takeError();
    if (isa<pir::OracleSequenceEmptyOp, pir::OracleSequenceLengthOp>(op)) {
      auto made = (isa<pir::OracleSequenceEmptyOp>(op)
                       ? read<data::SequenceEmptyOp>(block, *output, *actual)
                       : read<data::SequenceLengthOp>(block, *output, *actual));
      if (!made)
        return made.takeError();
      values[op.getResult(0)] = made->front();
      return Error::success();
    }
    auto sequence = cast<pir::OracleSequenceType>(op.getOperand(0).getType());
    auto element = oracleReferenceTypeWithWork(sequence.getKind(), work);
    if (!element)
      return element.takeError();
    Types arguments;
    for (auto type : op.getOperandTypes()) {
      auto convertedType = converted(type, work);
      if (!convertedType)
        return convertedType.takeError();
      arguments.push_back(*convertedType);
    }
    auto recipe = local(arguments, *output);
    if (!recipe)
      return recipe.takeError();
    auto size =
        scalar(*recipe, {"sequence.length", {TypeAttr::get(*element)}, ""},
               index, {0});
    if (!size)
      return size.takeError();
    bool append = isa<pir::OracleSequenceAppendOp>(op);
    unsigned left = append ? *size : 1;
    unsigned right = *size;
    if (append) {
      auto maximum = number(*recipe, sequence.getMaximum());
      if (!maximum)
        return maximum.takeError();
      right = *maximum;
    }
    auto allowed = scalar(*recipe, {"index.less", {}, ""}, builder.getI1Type(),
                          {left, right});
    if (!allowed)
      return allowed.takeError();
    if (auto e = require(*recipe, *allowed))
      return e;
    auto results = apply(*recipe,
                         {append ? "sequence.append" : "sequence.at",
                          {TypeAttr::get(*element)},
                          ""},
                         *output, {0, 1});
    if (!results)
      return results.takeError();
    recipe->results = std::move(*results);
    auto selected = op.getAttrOfType<ArrayAttr>("roles");
    Values components;
    std::vector<std::string> roles;
    for (auto role : selected) {
      auto name = cast<StringAttr>(role).getValue();
      auto component =
          call(block, *recipe, name, *actual, site(path, "sequence", name));
      if (!component)
        return component.takeError();
      components.push_back(component->front());
      roles.push_back(name.str());
    }
    result.locals.push_back(std::move(*recipe));
    auto joined = assemble(block, *output, components, roles);
    if (!joined)
      return joined.takeError();
    values[op.getResult(0)] = *joined;
    return Error::success();
  }
  // The admitted common language gives each handle an exact role family.
  // Loop carriers declare their family; captures retain the actual operand's.
  // This is availability, never an inference from possible anchor origins.
  Expected<std::vector<std::string>> handleRoles(Value value,
                                                 unsigned depth = 64) {
    if (!depth || !work.charge())
      return error("oracle-common-limit");
    ArrayAttr selected;
    std::string holder;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto *parent = argument.getOwner()->getParentOp();
      if (auto function = dyn_cast<pir::MathematicalOp>(parent))
        selected =
            cast<ArrayAttr>(function.getInputRoles()[argument.getArgNumber()]);
      else if (isa<pir::BranchOp>(parent)) {
        Value capture = selectedCapture(argument);
        if (!capture)
          return error("oracle-common-interface");
        return handleRoles(capture, depth - 1);
      } else if (auto repeat = dyn_cast<pir::RepeatOp>(parent)) {
        unsigned index = argument.getArgNumber();
        if (index > 0 && index <= unsigned(repeat.getCarried()))
          selected = cast<ArrayAttr>(repeat.getCarriedRoles()[index - 1]);
        else if (index > unsigned(repeat.getCarried()))
          return handleRoles(repeat.getInputs()[index], depth - 1);
      }
    } else if (auto repeat = value.getDefiningOp<pir::RepeatOp>())
      selected = cast<ArrayAttr>(
          repeat.getCarriedRoles()[cast<OpResult>(value).getResultNumber()]);
    else if (auto branch = value.getDefiningOp<pir::BranchOp>())
      selected = cast<ArrayAttr>(
          branch.getOutputRoles()[cast<OpResult>(value).getResultNumber()]);
    else if (auto restrict = value.getDefiningOp<pir::RestrictRolesOp>())
      selected = restrict.getRoles();
    else if (auto forget = value.getDefiningOp<pir::OracleForgetShapeOp>())
      return handleRoles(forget.getInput(), depth - 1);
    else if (auto components = value.getDefiningOp<pir::OracleComponentsOp>())
      selected = components.getReceivers();
    else if (auto at = value.getDefiningOp<pir::OracleSequenceAtOp>())
      selected = at.getRoles();
    else if (auto send = value.getDefiningOp<pir::OracleSendOp>()) {
      selected = send.getReceivers();
      holder = send.getSender().str();
    } else if (auto input = value.getDefiningOp<pir::OracleInputOp>()) {
      selected = input.getReceivers();
      holder = input.getHolder().str();
    } else if (auto constructed = value.getDefiningOp<pir::OracleVirtualOp>()) {
      selected = constructed.getReceivers();
      holder = constructed.getHolder().str();
    }
    if (!selected)
      return error("oracle-common-interface");
    // Roster order is observable in the component assembly. Charge the
    // complete membership product before scanning, including repeated shape
    // views of one handle; a single charge per handle use is insufficient.
    if (!work.charge(program.getRoles().size()) ||
        !work.chargeProduct(program.getRoles().size(), selected.size()))
      return error("oracle-common-limit");
    std::vector<std::string> roles;
    for (auto attribute : program.getRoles()) {
      auto role = cast<StringAttr>(attribute);
      if (role.getValue() == holder || is_contained(selected, attribute)) {
        if (!work.charge(role.getValue().size()))
          return error("oracle-common-limit");
        roles.push_back(role.getValue().str());
      }
    }
    return roles;
  }
  Error branch(Block &block, pir::BranchOp selected, std::vector<unsigned> path,
               unsigned depth) {
    if (!depth || selected->getNumRegions() > selectedRegionArmLimit)
      return error("oracle-common-limit");
    Values actualOperands;
    std::vector<std::optional<DataView>> capturedViews;
    if (!work.charge(selected->getNumOperands()))
      return error("oracle-common-limit");
    for (auto [i, operand] : enumerate(selected->getOperands())) {
      auto view = dataViews.find(operand);
      // A lazy component capture forwards its actual reference. Materializing
      // its Data here could execute a scoped lookup for an untaken arm.
      if (i && !values.count(operand) && view != dataViews.end()) {
        actualOperands.push_back(view->second.reference);
        capturedViews.push_back(view->second);
        continue;
      }
      if (auto e = demand(block, operand, path))
        return e;
      auto mapped = value(operand);
      if (!mapped)
        return mapped.takeError();
      actualOperands.push_back(*mapped);
      if (i)
        capturedViews.push_back(std::nullopt);
    }
    auto *operands = &actualOperands;
    if (!work.charge(values.size() + dataViews.size() + store.size() +
                     coordinates.size()))
      return error("oracle-common-limit");
    auto outerValues = values;
    auto outerViews = dataViews;
    auto outerStores = store;
    auto outerCoordinates = coordinates;
    Types outputs;
    for (Type type : selected.getResultTypes()) {
      auto native = converted(type, work);
      if (!native)
        return native.takeError();
      outputs.push_back(*native);
    }
    SmallVector<Attribute> outputRoles(selected.getOutputRoles().getValue());
    std::vector<std::pair<unsigned, unsigned>> joinedStores;
    for (auto &[key, value] : outerStores) {
      auto &owner =
          requirements.storage.constructors[key.first].roles[key.second];
      if (!is_contained(selected.getRoles(), builder.getStringAttr(owner.role)))
        continue;
      if (!work.charge())
        return error("oracle-common-limit");
      joinedStores.push_back(key);
      operands->push_back(value);
      outputs.push_back(owner.sequence);
      outputRoles.push_back(builder.getStrArrayAttr({owner.role}));
    }
    append_range(*operands, outerCoordinates);
    SmallVector<Block *> arms;
    for (unsigned arm = 0; arm < selected->getNumRegions(); ++arm) {
      auto &sourceRegion = selected->getRegion(arm);
      if (!hasSingleElement(sourceRegion) || sourceRegion.front().empty() ||
          !isa<pir::ProtocolYieldOp>(sourceRegion.front().back()))
        return error("oracle-common-body");
      auto &original = sourceRegion.front();
      if (!work.charge(1 + original.getNumArguments() + joinedStores.size() +
                       outerCoordinates.size() + path.size()))
        return error("oracle-common-limit");
      auto payload = selectedPayloadTypes(selected, arm);
      if (!payload)
        return payload.takeError();
      if (original.getNumArguments() !=
          payload->size() + selected->getNumOperands() - 1)
        return error("oracle-common-body");
      Types arguments;
      for (auto [i, type] : enumerate(original.getArgumentTypes())) {
        if (i >= payload->size() && capturedViews[i - payload->size()]) {
          arguments.push_back(
              capturedViews[i - payload->size()]->reference.getType());
          continue;
        }
        auto native = converted(type, work);
        if (!native)
          return native.takeError();
        arguments.push_back(*native);
      }
      for (auto key : joinedStores)
        arguments.push_back(requirements.storage.constructors[key.first]
                                .roles[key.second]
                                .sequence);
      arguments.insert(arguments.end(), outerCoordinates.size(), index);
      auto created = region(block, arguments, arm);
      if (!created)
        return created.takeError();
      Block *nested = *created;
      arms.push_back(nested);
      // Payloads are supplied by selected entry; only actual captures are
      // forwarded. No outer value or prior arm environment survives this reset.
      values.clear();
      dataViews.clear();
      store.clear();
      coordinates.clear();
      IRMapping armMapping;
      for (auto [from, to] :
           zip(original.getArguments(), nested->getArguments())) {
        armMapping.map(from, to);
        unsigned i = from.getArgNumber();
        if (i >= payload->size() && capturedViews[i - payload->size()]) {
          const auto &view = *capturedViews[i - payload->size()];
          dataViews[from] = {armMapping.lookup(from), view.holder, view.type};
        } else
          values[from] = armMapping.lookup(from);
      }
      unsigned offset = original.getNumArguments();
      for (auto key : joinedStores)
        store[key] = nested->getArgument(offset++);
      for (unsigned i = 0; i < outerCoordinates.size(); ++i)
        coordinates.push_back(nested->getArgument(offset++));
      auto armPath = path;
      armPath.push_back(arm);
      if (auto e = visit(*nested, original, armPath, depth - 1, joinedStores))
        return e;
    }
    NamedAttrList attributes(selected->getAttrs());
    attributes.set("output_roles", builder.getArrayAttr(outputRoles));
    auto joined = read<pir::BranchOp>(
        block, outputs, *operands,
        attributes.getDictionary(builder.getContext()), arms);
    if (!joined)
      return joined.takeError();
    if (!work.charge(outerValues.size() + outerViews.size() +
                     outerStores.size() + joined->size()))
      return error("oracle-common-limit");
    values = std::move(outerValues);
    dataViews = std::move(outerViews);
    store = std::move(outerStores);
    coordinates = std::move(outerCoordinates);
    for (auto [from, to] : zip(selected.getResults(), *joined))
      values[from] = to;
    for (auto [i, key] : enumerate(joinedStores))
      store[key] = (*joined)[selected.getNumResults() + i];
    return Error::success();
  }
  Error repeat(Block &block, pir::RepeatOp repeat, std::vector<unsigned> path,
               unsigned depth) {
    Values actualArguments;
    std::vector<std::optional<DataView>> capturedViews;
    if (!work.charge(repeat.getNumOperands()))
      return error("oracle-common-limit");
    for (auto [i, input] : enumerate(repeat.getInputs())) {
      bool capture = i > unsigned(repeat.getCarried());
      auto view = dataViews.find(input);
      if (capture && !values.count(input) && view != dataViews.end()) {
        actualArguments.push_back(view->second.reference);
        capturedViews.push_back(view->second);
        continue;
      }
      if (auto e = demand(block, input, path))
        return e;
      auto mapped = value(input);
      if (!mapped)
        return mapped.takeError();
      actualArguments.push_back(*mapped);
      if (capture)
        capturedViews.push_back(std::nullopt);
    }
    auto *arguments = &actualArguments;
    if (!work.charge(values.size() + dataViews.size() + store.size() +
                     coordinates.size()))
      return error("oracle-common-limit");
    auto previousValues = values;
    auto previousViews = dataViews;
    auto previousStore = store;
    auto previousCoordinates = coordinates;
    std::vector<std::pair<unsigned, unsigned>> carriedStores;
    auto active = [&](StringRef role) {
      return is_contained(repeat.getRoles(), builder.getStringAttr(role));
    };
    Values oldSeeds(arguments->begin() + 1,
                    arguments->begin() + 1 + repeat.getCarried());
    Values captures(arguments->begin() + 1 + repeat.getCarried(),
                    arguments->end());
    Types seedTypes, captureTypes;
    for (Type type : repeat.getInputs()
                         .drop_front(1)
                         .take_front(repeat.getCarried())
                         .getTypes()) {
      auto result = converted(type, work);
      if (!result)
        return result.takeError();
      seedTypes.push_back(*result);
    }
    for (Value capture : captures)
      captureTypes.push_back(capture.getType());
    SmallVector<Attribute> carriedRoles(repeat.getCarriedRoles().begin(),
                                        repeat.getCarriedRoles().end());
    for (const auto &[key, value] : previousStore) {
      const auto &owner =
          requirements.storage.constructors[key.first].roles[key.second];
      if (!active(owner.role))
        continue;
      carriedStores.push_back(key);
      oldSeeds.push_back(value);
      seedTypes.push_back(owner.sequence);
      carriedRoles.push_back(builder.getStrArrayAttr({owner.role}));
    }
    append_range(captures, coordinates);
    captureTypes.insert(captureTypes.end(), coordinates.size(), index);
    Types regionTypes{index};
    append_range(regionTypes, seedTypes);
    append_range(regionTypes, captureTypes);
    auto created = region(block, regionTypes);
    if (!created)
      return created.takeError();
    Block *nested = *created;
    auto &original = repeat.getBody().front();
    values.clear();
    dataViews.clear();
    values[original.getArgument(0)] = nested->getArguments()[0];
    for (unsigned i = 0; i < unsigned(repeat.getCarried()); ++i)
      values[original.getArgument(1 + i)] = nested->getArguments()[1 + i];
    for (unsigned i = 0;
         i < original.getNumArguments() - 1 - repeat.getCarried(); ++i) {
      auto from = original.getArgument(1 + repeat.getCarried() + i);
      auto to = nested->getArgument(1 + seedTypes.size() + i);
      if (capturedViews[i]) {
        const auto &view = *capturedViews[i];
        dataViews[from] = {to, view.holder, view.type};
      } else
        values[from] = to;
    }
    store.clear();
    for (auto [i, key] : enumerate(carriedStores))
      store[key] = nested->getArguments()[1 + repeat.getCarried() + i];
    coordinates.clear();
    auto coordinateStart =
        nested->getArguments().size() - previousCoordinates.size();
    for (unsigned i = 0; i < previousCoordinates.size(); ++i)
      coordinates.push_back(nested->getArguments()[coordinateStart + i]);
    coordinates.push_back(nested->getArguments()[0]);
    if (auto e = visit(*nested, original, path, depth - 1, carriedStores))
      return e;
    Values operands{arguments->front()};
    append_range(operands, oldSeeds);
    append_range(operands, captures);
    NamedAttrList attributes(repeat->getAttrs());
    attributes.set("carried", builder.getI64IntegerAttr(seedTypes.size()));
    attributes.set("carried_roles", builder.getArrayAttr(carriedRoles));
    auto outputs = read<pir::RepeatOp>(
        block, seedTypes, operands,
        attributes.getDictionary(builder.getContext()), {nested});
    if (!outputs)
      return outputs.takeError();
    if (!work.charge(previousValues.size() + previousViews.size() +
                     previousStore.size() + outputs->size()))
      return error("oracle-common-limit");
    values = std::move(previousValues);
    dataViews = std::move(previousViews);
    store = std::move(previousStore);
    coordinates = std::move(previousCoordinates);
    for (auto [i, output] : enumerate(repeat.getOutputs()))
      values[output] = (*outputs)[i];
    for (auto [i, key] : enumerate(carriedStores))
      store[key] = (*outputs)[repeat.getCarried() + i];
    return Error::success();
  }
  Expected<Values> remoteBlock(Block &block, unsigned ordinal) {
    const auto &selection = schedule.batches[ordinal];
    const auto &batch = batches[ordinal];
    if (batch.remotes != selection.remotes || selection.remotes.empty())
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    const auto &first = remotes[selection.remotes.front()];
    const auto &receiver = controllers[first.receiver].body;
    const auto &holder = controllers[first.holder].body;
    const auto &exchange = schedule.remotes[selection.remotes.front()].exchange;
    const auto &path = selection.queries.front();
    auto captures = stores(receiver);
    if (!captures)
      return captures.takeError();
    Values heldStores;
    for (const auto &arm : exchange.arms) {
      auto held = find_if(holder.constructors, [&](const auto &item) {
        return item.source == arm.constructor;
      });
      if (held == holder.constructors.end())
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-helper");
      auto found = store.find({arm.constructor, held->role});
      if (found == store.end())
        return error("oracle-common-store");
      heldStores.push_back(found->second);
    }
    Values discovery, evaluation;
    for (auto [remoteIndex, coordinate] :
         zip(selection.remotes, selection.queries)) {
      const auto &remote = remotes[remoteIndex];
      const auto &body = controllers[remote.receiver].body;
      auto query =
          dyn_cast_or_null<pir::OracleQueryOp>(sourceOperation(coordinate));
      if (!query || body.role != receiver.role)
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-query-block-source");
      auto rootStores = stores(body);
      if (!rootStores)
        return rootStores.takeError();
      if (*rootStores != *captures)
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-query-block-source");
      auto arguments = inputs(query->getOperands());
      if (!arguments)
        return arguments.takeError();
      auto demand =
          call(block, remote.demand.initialize, receiver.role, *arguments,
               site(coordinate, "query_discovery_initialize", receiver.role));
      if (!demand)
        return demand.takeError();
      auto state = call(block, body.initialize, receiver.role, *arguments,
                        site(coordinate, "query_initialize", receiver.role));
      if (!state)
        return state.takeError();
      append_range(discovery, *demand);
      append_range(evaluation, *state);
    }
    // Both participants derive the same structural round count from their own
    // immutable graph. A count bounds communication; it is not domain evidence.
    Values counts;
    detail::OracleRepeatCount observation;
    observation.source = source;
    observation.candidate = candidate->getParentOfType<ModuleOp>();
    observation.originalEntry = program;
    observation.actualEntry = candidate;
    observation.capacity = schedule.capacity;
    observation.authentication = unsigned(authentication);
    if (!schedule.capacity || !work.charge(path.size() + coordinates.size()))
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-body");
    append_range(observation.sourcePath, path);
    append_range(observation.iterations, coordinates);
    std::vector<std::string> owners{receiver.role, holder.role};
    for (unsigned role = 0; role < owners.size(); ++role) {
      Values leaves;
      for (auto [remoteIndex, coordinate] :
           zip(selection.remotes, selection.queries)) {
        const auto &remote = remotes[remoteIndex];
        const auto &body =
            controllers[role ? remote.holder : remote.receiver].body;
        auto query =
            dyn_cast_or_null<pir::OracleQueryOp>(sourceOperation(coordinate));
        if (!query)
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-query-block-source");
        auto roles = handleRoles(query.getHandle());
        if (!roles)
          return roles.takeError();
        if (!is_contained(*roles, body.role) || body.leafCounts.empty())
          return error("oracle-common-communication-profile");
        auto handle = value(query.getHandle());
        auto rootStores = stores(body);
        if (!handle)
          return handle.takeError();
        if (!rootStores)
          return rootStores.takeError();
        Values arguments{*handle};
        append_range(arguments, *rootStores);
        auto count = call(block, body.leafCounts[0], body.role, arguments,
                          site(coordinate, "query_count", body.role));
        if (!count)
          return count.takeError();
        leaves.push_back(count->front());
        if (!work.charge(2))
          return error("oracle-common-limit");
        if (!role)
          observation.queries.push_back(query);
        observation.leafCalls.push_back(count->front().getDefiningOp());
      }
      // Reserve the signature width before constructing its type vector.
      if (!work.charge(leaves.size()))
        return error("oracle-common-limit");
      auto rounds = local(Types(leaves.size(), index), index);
      if (!rounds)
        return rounds.takeError();
      auto zero = number(*rounds, 0);
      if (!zero)
        return zero.takeError();
      unsigned total = *zero;
      for (unsigned i = 0; i < leaves.size(); ++i) {
        auto sum = scalar(*rounds, {"index.add", {}, ""}, index, {total, i});
        if (!sum)
          return sum.takeError();
        total = *sum;
      }
      auto bound = number(*rounds, selection.leaves + 1);
      if (!bound)
        return bound.takeError();
      auto allowed = scalar(*rounds, {"index.less", {}, ""},
                            builder.getI1Type(), {total, *bound});
      if (!allowed)
        return allowed.takeError();
      if (auto e = require(*rounds, *allowed))
        return std::move(e);
      // ceil(total / capacity), guarded below the representable native bound.
      auto offset = number(*rounds, schedule.capacity - 1);
      if (!offset)
        return offset.takeError();
      auto numerator =
          scalar(*rounds, {"index.add", {}, ""}, index, {total, *offset});
      if (!numerator)
        return numerator.takeError();
      auto width = number(*rounds, schedule.capacity);
      if (!width)
        return width.takeError();
      auto results =
          apply(*rounds, {"index.div", {}, ""}, index, {*numerator, *width});
      if (!results)
        return results.takeError();
      rounds->results = std::move(*results);
      auto count = call(block, *rounds, owners[role], leaves,
                        site(path, "query_round_count", owners[role]));
      if (!count)
        return count.takeError();
      result.locals.push_back(std::move(*rounds));
      counts.push_back(count->front());
    }
    auto count = assemble(block, index, counts, owners);
    if (!count)
      return count.takeError();
    observation.assembly = count->getDefiningOp<pir::AssembleRolesOp>();
    if (!work.charge(counts.size()))
      return error("oracle-common-limit");
    append_range(observation.counts, counts);
    Types stateTypes(batch.body.demandState);
    append_range(stateTypes, batch.body.evaluatorState);
    Types regionTypes{index};
    append_range(regionTypes, stateTypes);
    append_range(regionTypes, receiver.stores);
    append_range(regionTypes, exchange.holderStores);
    auto created = region(block, regionTypes);
    if (!created)
      return created.takeError();
    Block *nested = *created;
    auto slice = [&](unsigned offset, unsigned size) {
      return Values(nested->getArguments().begin() + offset,
                    nested->getArguments().begin() + offset + size);
    };
    auto loopDemand = slice(1, discovery.size());
    auto loopEvaluation = slice(1 + discovery.size(), evaluation.size());
    auto loopStores = slice(1 + stateTypes.size(), captures->size());
    auto loopHeld =
        slice(1 + stateTypes.size() + captures->size(), heldStores.size());
    Values collecting(loopDemand);
    append_range(collecting, loopStores);
    auto collected =
        call(*nested, batch.body.collect, receiver.role, collecting,
             site(path, "query_collect", receiver.role));
    if (!collected)
      return collected.takeError();
    if (collected->size() != discovery.size() + 1 + selection.remotes.size())
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    Value requests = (*collected)[discovery.size()];
    Values checking{requests};
    append_range(checking, loopEvaluation);
    append_range(checking, loopStores);
    auto available =
        call(*nested, batch.body.checkAvailable, receiver.role, checking,
             site(path, "query_check_available", receiver.role));
    if (!available)
      return available.takeError();
    if (!available->empty())
      return error(work.exhausted ? "oracle-common-limit"
                                  : "oracle-common-helper");
    Values grouping{requests};
    append_range(grouping, loopStores);
    auto grouped = call(*nested, first.packet.group, receiver.role, grouping,
                        site(path, "opening_group", receiver.role));
    if (!grouped)
      return grouped.takeError();
    auto sent = read<pir::ExchangeOp>(
        *nested, first.packet.requestSequence, {(*grouped)[0]},
        attrs({text("sender", receiver.role), text("receiver", holder.role),
               text("site", site(path, "opening_request", holder.role))}));
    if (!sent)
      return sent.takeError();
    Values opening{sent->front()};
    append_range(opening, loopHeld);
    auto opened = call(*nested, first.packet.open, holder.role, opening,
                       site(path, "opening_dispatch", holder.role));
    if (!opened)
      return opened.takeError();
    auto returned = read<pir::ExchangeOp>(
        *nested, first.packet.responseSequence, *opened,
        attrs({text("sender", holder.role), text("receiver", receiver.role),
               text("site", site(path, "opening_response", receiver.role))}));
    if (!returned)
      return returned.takeError();
    Values authenticationInputs{requests, (*grouped)[0], (*grouped)[1],
                                returned->front()};
    append_range(authenticationInputs, loopStores);
    auto authenticated = call(
        *nested, first.packet.authenticate, receiver.role, authenticationInputs,
        site(path, "opening_authenticate", receiver.role));
    if (!authenticated)
      return authenticated.takeError();
    Values replaying(loopEvaluation);
    replaying.push_back(requests);
    replaying.push_back(authenticated->front());
    append_range(replaying,
                 ArrayRef(*collected).drop_front(discovery.size() + 1));
    append_range(replaying, loopStores);
    auto replayed = call(*nested, batch.body.replay, receiver.role, replaying,
                         site(path, "query_replay", receiver.role));
    if (!replayed)
      return replayed.takeError();
    Values advanced(collected->begin(), collected->begin() + discovery.size());
    append_range(advanced, *replayed);
    auto yielded = read<pir::ProtocolYieldOp>(*nested, {}, advanced);
    if (!yielded)
      return yielded.takeError();
    Values loopInputs{*count};
    append_range(loopInputs, discovery);
    append_range(loopInputs, evaluation);
    append_range(loopInputs, *captures);
    append_range(loopInputs, heldStores);
    SmallVector<Attribute> carried(stateTypes.size(),
                                   builder.getStrArrayAttr({receiver.role}));
    uint64_t maximum = authentication == OracleAuthentication::AtomicBlocks
                           ? 1
                           : std::max(uint64_t(1), selection.leaves);
    auto final = read<pir::RepeatOp>(
        block, stateTypes, loopInputs,
        attrs({text("site", site(path, "query_requests", receiver.role)),
               builder.getNamedAttr(
                   "carried", builder.getI64IntegerAttr(stateTypes.size())),
               builder.getNamedAttr("maximum",
                                    builder.getI64IntegerAttr(maximum)),
               builder.getNamedAttr("roles", builder.getStrArrayAttr(
                                                 {holder.role, receiver.role})),
               builder.getNamedAttr("carried_roles",
                                    builder.getArrayAttr(carried))}),
        {nested});
    if (!final)
      return final.takeError();
    observation.repeat = cast<pir::RepeatOp>(nested->getParentOp());
    observation.maximum = maximum;
    for (Operation *child = observation.repeat;
         child->getParentOp() != candidate.getOperation();) {
      if (!work.charge() || observation.ancestry.size() >= 64)
        return error("oracle-common-limit");
      auto *parent = child->getParentOp();
      if (!parent)
        return refuse();
      observation.ancestry.emplace_back(
          parent, child->getParentRegion()->getRegionNumber());
      child = parent;
    }
    if (!work.charge())
      return error("oracle-common-limit");
    result.repeatCounts.push_back(std::move(observation));
    Values finishing(final->begin() + discovery.size(), final->end());
    append_range(finishing, *captures);
    auto answers = call(block, batch.body.finish, receiver.role, finishing,
                        site(path, "query_finish", receiver.role));
    if (!answers)
      return answers.takeError();
    result.queryBlocks.push_back({selection.queries, schedule.capacity});
    return answers;
  }
  Error visit(Block &block, Block &original, std::vector<unsigned> prefix,
              unsigned depth,
              ArrayRef<std::pair<unsigned, unsigned>> yieldedStores = {}) {
    if (!depth)
      return error("oracle-common-limit");
    unsigned skipped = 0;
    for (auto [ordinal, op] : enumerate(original)) {
      if (!work.charge(1 + op.getNumOperands() + op.getNumResults() +
                       prefix.size()))
        return error("oracle-common-limit");
      if (skipped) {
        --skipped;
        continue;
      }
      SaveAndRestore<Operation *> sourceAssociation(activeSource, &op);
      auto path = prefix;
      path.push_back(ordinal);
      // Statements select logical claims, not executable effects. The frozen
      // original and checked record retain their full binding. A candidate
      // alone cannot publish the original claim after representation changes.
      if (isa<pir::StatementOp>(op))
        continue;
      if (auto selected = dyn_cast<pir::BranchOp>(op)) {
        if (auto e = branch(block, selected, path, depth))
          return e;
        continue;
      }
      if (auto repetition = dyn_cast<pir::RepeatOp>(op)) {
        if (auto e = repeat(block, repetition, path, depth))
          return e;
        continue;
      }
      if (auto components = dyn_cast<pir::OracleComponentsOp>(op)) {
        auto anchor = value(components.getHandle());
        if (!anchor)
          return anchor.takeError();
        auto type = converted(components.getAnchor().getType(), work);
        if (!type)
          return type.takeError();
        auto receiver = read<pir::RestrictRolesOp>(
            block, *type, {*anchor},
            attrs({builder.getNamedAttr("roles", components.getReceivers())}));
        if (!receiver)
          return receiver.takeError();
        values[components.getAnchor()] = receiver->front();
        dataViews[components.getData()] = {*anchor,
                                           components.getHolder().str(),
                                           components.getHandle().getType()};
        continue;
      }
      if (auto restrict = dyn_cast<pir::RestrictRolesOp>(op)) {
        if (auto found = dataViews.find(restrict.getInput());
            found != dataViews.end()) {
          // Insertion can grow the map and invalidate the input iterator.
          auto view = found->second;
          dataViews[restrict.getOutput()] = std::move(view);
          if (auto data = values.find(restrict.getInput());
              data != values.end())
            values[restrict.getOutput()] = data->second;
          continue;
        }
      }
      if (auto input = dyn_cast<pir::OracleInputOp>(op)) {
        if (none_of(requirements.storage.constructors,
                    [&](const auto &item) { return item.path == path; })) {
          Value receiver = input.getAnchor();
          while (auto view = receiver.getDefiningOp<pir::RestrictRolesOp>()) {
            if (!work.charge())
              return error("oracle-common-limit");
            receiver = view.getInput();
          }
          auto components = receiver.getDefiningOp<pir::OracleComponentsOp>();
          if (!components)
            return error("oracle-common-interface");
          // Admission already checked the exact data/receiver pair. Retain the
          // actual view's dynamic reference; possible origins are insufficient.
          auto anchor = value(components.getHandle());
          auto type = converted(input.getHandle().getType(), work);
          if (!anchor)
            return anchor.takeError();
          if (!type)
            return type.takeError();
          if (auto e = checkSequenceRebinding(block, input, *anchor, path))
            return e;
          SmallVector<Attribute> roles{input.getHolderAttr()};
          append_range(roles, input.getReceivers());
          auto rebound = read<pir::RestrictRolesOp>(
              block, *type, {*anchor},
              attrs({builder.getNamedAttr("roles",
                                          builder.getArrayAttr(roles))}));
          if (!rebound)
            return rebound.takeError();
          values[input.getHandle()] = rebound->front();
          continue;
        }
      }
      for (Value input : op.getOperands())
        if (auto e = demand(block, input, path))
          return e;
      if (isa<pir::OracleInputOp, pir::OracleSendOp, pir::OracleVirtualOp>(
              op)) {
        auto found =
            find_if(requirements.storage.constructors,
                    [&](const auto &item) { return item.path == path; });
        if (found == requirements.storage.constructors.end())
          return error("oracle-common-interface");
        if (auto e =
                construct(block, op, path,
                          found - requirements.storage.constructors.begin()))
          return e;
        continue;
      }
      if (auto query = dyn_cast<pir::OracleQueryOp>(op)) {
        auto *body = controller(*query.getOwner(),
                                query.getHandle().getType().getKind());
        if (!body)
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-common-helper");
        if (body->evaluate) {
          auto arguments = inputs(query->getOperands());
          auto captures = stores(*body);
          if (!arguments)
            return arguments.takeError();
          if (!captures)
            return captures.takeError();
          append_range(*arguments, *captures);
          auto output =
              call(block, body->evaluate, *query.getOwner(), *arguments,
                   site(path, "query", *query.getOwner()));
          if (!output)
            return output.takeError();
          values[query.getAnswer()] = output->front();
          result.queryBlocks.push_back({{path}, std::nullopt});
          continue;
        }
        auto batch = find_if(schedule.batches, [&](const auto &item) {
          return !item.queries.empty() && item.queries.front() == path;
        });
        if (batch == schedule.batches.end())
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-query-block-source");
        auto answers = remoteBlock(block, batch - schedule.batches.begin());
        if (!answers)
          return answers.takeError();
        if (answers->size() != batch->queries.size())
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-common-helper");
        for (auto [coordinate, answer] : zip(batch->queries, *answers)) {
          auto originalQuery =
              dyn_cast_or_null<pir::OracleQueryOp>(sourceOperation(coordinate));
          if (!originalQuery)
            return error(work.exhausted ? "oracle-common-limit"
                                        : "oracle-query-block-source");
          values[originalQuery.getAnswer()] = answer;
        }
        skipped = batch->queries.size() - 1;
        continue;
      }
      if (auto contents = dyn_cast<pir::OracleContentsOp>(op)) {
        auto *body = controller(contents.getOwner(),
                                contents.getHandle().getType().getKind(),
                                OracleControllerAccess::Holder);
        if (!body || !body->contents)
          return error(work.exhausted ? "oracle-common-limit"
                                      : "oracle-common-helper");
        auto arguments = inputs(contents->getOperands());
        auto captures = stores(*body);
        if (!arguments)
          return arguments.takeError();
        if (!captures)
          return captures.takeError();
        append_range(*arguments, *captures);
        auto output =
            call(block, body->contents, contents.getOwner(), *arguments,
                 site(path, "contents", contents.getOwner()));
        if (!output)
          return output.takeError();
        values[contents.getData()] = output->front();
        continue;
      }
      if (auto shape = dyn_cast<pir::OracleShapeOp>(op)) {
        if (shape.getDimension() != "rows")
          return error("oracle-common-interface");
        auto roles = handleRoles(shape.getHandle());
        if (!roles)
          return roles.takeError();
        Values components;
        for (const auto &role : *roles) {
          auto *body = controller(role, shape.getHandle().getType().getKind());
          if (!body || body->rowCounts.empty())
            return error(work.exhausted ? "oracle-common-limit"
                                        : "oracle-common-helper");
          auto arguments = inputs(shape->getOperands());
          auto captures = stores(*body);
          if (!arguments)
            return arguments.takeError();
          if (!captures)
            return captures.takeError();
          append_range(*arguments, *captures);
          auto output = call(block, body->rowCounts[0], role, *arguments,
                             site(path, "shape_view", role));
          if (!output)
            return output.takeError();
          components.push_back(output->front());
        }
        auto output = assemble(block, index, components, *roles);
        if (!output)
          return output.takeError();
        values[shape.getExtent()] = *output;
        continue;
      }
      if (auto forget = dyn_cast<pir::OracleForgetShapeOp>(op)) {
        auto original = value(forget.getInput());
        if (!original)
          return original.takeError();
        values[forget.getOutput()] = *original;
        continue;
      }
      if (isa<pir::OracleSequenceEmptyOp, pir::OracleSequenceLengthOp,
              pir::OracleSequenceAppendOp, pir::OracleSequenceAtOp>(op)) {
        if (auto e = sequence(block, op, path))
          return e;
        continue;
      }
      if (isa<data::BranchOp>(op)) {
        // Read actual native SSA, independently of materializer associations.
        // Equivalence checks both arms, captures, yields and nested regions.
        auto arguments = inputs(op.getOperands());
        if (!arguments)
          return arguments.takeError();
        auto output = preserved(block, op, op.getResultTypes(), *arguments);
        if (!output)
          return output.takeError();
        for (auto [original, mapped] : zip(op.getResults(), *output))
          values[original] = mapped;
        continue;
      }
      if (op.getName().getStringRef().starts_with("protocol.oracle_"))
        return error("oracle-common-interface");
      if (op.getNumRegions() || isa<pir::ApplyOp>(op))
        return refuse();
      if (any_of(op.getOperandTypes(), logical) &&
          !isa<pir::RestrictRolesOp, pir::ProtocolYieldOp,
               pir::MathematicalReturnOp, pir::FinishIfOp>(op))
        return error("oracle-common-interface");
      auto arguments = inputs(op.getOperands());
      if (!arguments)
        return arguments.takeError();
      if (isa<pir::ProtocolYieldOp>(op))
        for (const auto &key : yieldedStores) {
          auto successor = stored(key);
          if (!successor)
            return successor.takeError();
          arguments->push_back(*successor);
        }
      if (isa<pir::MathematicalReturnOp, pir::FinishIfOp>(op) &&
          !work.charge(result.resultStores.size()))
        return error("oracle-common-limit");
      if (isa<pir::MathematicalReturnOp>(op))
        for (const auto &support : result.resultStores) {
          auto successor = stored({support.constructor, support.role});
          if (!successor)
            return successor.takeError();
          arguments->push_back(*successor);
        }
      if (auto completion = dyn_cast<pir::FinishIfOp>(op))
        for (const auto &support : result.resultStores) {
          const auto &owner =
              requirements.storage.constructors[support.constructor]
                  .roles[support.role];
          if (owner.role != completion.getOwner())
            continue;
          auto found = store.find({support.constructor, support.role});
          if (found == store.end())
            return error("oracle-common-store");
          arguments->push_back(found->second);
        }
      Types outputs;
      for (auto type : op.getResultTypes()) {
        auto actual = converted(type, work);
        if (!actual)
          return actual.takeError();
        outputs.push_back(*actual);
      }
      auto output = preserved(block, op, outputs, *arguments);
      if (!output)
        return output.takeError();
      for (auto [original, mapped] : zip(op.getResults(), *output))
        values[original] = mapped;
    }
    return Error::success();
  }
  Expected<OracleCommonAnalysis> run() {
    if (!candidate || !hasSingleElement(candidate.getBody()))
      return refuse();
    Block &actualBody = candidate.getBody().front();
    if (!work.charge(program.getFunctionType().getNumInputs() +
                     program.getFunctionType().getNumResults() +
                     requirements.storage.constructors.size() +
                     controllers.size()))
      return error("oracle-common-limit");
    Types inputs;
    auto &original = program.getBody().front();
    std::map<unsigned, unsigned> selectedInputs;
    for (auto [ordinal, constructor] :
         enumerate(requirements.storage.constructors)) {
      if (constructor.constructor != OracleAnchorConstructor::Kind::Input)
        continue;
      auto input = dyn_cast_or_null<pir::OracleInputOp>(
          sourceOperation(constructor.path));
      if (!input)
        return error(work.exhausted ? "oracle-common-limit"
                                    : "oracle-common-interface");
      auto anchor = inputAnchor(input.getAnchor());
      if (!anchor)
        return error("oracle-common-interface");
      // Protocol admission owns the unique binding of each raw entry anchor.
      selectedInputs.emplace(*anchor, ordinal);
    }
    for (auto [ordinal, argument] : enumerate(original.getArguments())) {
      Type type = argument.getType();
      if (auto handle = dyn_cast<pir::OracleHandleType>(type)) {
        auto selected = selectedInputs.find(ordinal);
        if (selected == selectedInputs.end())
          return error("oracle-common-interface");
        auto &constructor = requirements.storage.constructors[selected->second];
        if (constructor.scheme.empty())
          type = handle.getKind().getDataType();
        else {
          auto receiver = find_if(constructor.roles, [&](const auto &role) {
            return role.role != constructor.holder;
          });
          if (receiver == constructor.roles.end())
            return error("oracle-common-interface");
          const auto &fields = receiver->fields;
          auto field = find_if(
              fields, [](const auto &field) { return field.name == "root"; });
          if (field == fields.end())
            return error("oracle-common-interface");
          type = field->type;
        }
      } else if (logical(type))
        return error("oracle-common-interface");
      auto mapped = this->argument(type);
      if (!mapped)
        return mapped.takeError();
      values[argument] = *mapped;
      inputs.push_back(type);
    }
    SmallVector<Attribute> inputRoles(program.getInputRoles().begin(),
                                      program.getInputRoles().end());
    for (const auto &[anchor, ordinal] : selectedInputs) {
      const auto &constructor = requirements.storage.constructors[ordinal];
      if (constructor.scheme.empty() ||
          constructor.kind.getShapeDimensions()[0].extent)
        continue;
      result.inputShapes.push_back({anchor, unsigned(inputs.size())});
      auto mapped = argument(index);
      if (!mapped)
        return mapped.takeError();
      inputRows[anchor] = *mapped;
      inputs.push_back(index);
      inputRoles.push_back(program.getInputRoles()[anchor]);
    }
    Types outputs;
    for (Type type : program.getFunctionType().getResults()) {
      auto output = converted(type, work);
      if (!output)
        return output.takeError();
      outputs.push_back(*output);
    }
    SmallVector<Attribute> outputRoles(program.getOutputRoles().begin(),
                                       program.getOutputRoles().end());
    // Reserve the role/result cross product before scanning, including the
    // membership scans of logical output-owner lists. Neither repeated types
    // nor repeated owner attributes make these iterations free.
    if (!work.chargeProduct(program.getRoles().size(),
                            program.getFunctionType().getNumResults()))
      return error("oracle-common-limit");
    for (auto [type, roles] :
         zip(program.getFunctionType().getResults(), program.getOutputRoles()))
      if (logical(type) && !work.chargeProduct(program.getRoles().size(),
                                               cast<ArrayAttr>(roles).size()))
        return error("oracle-common-limit");
    // Retain one complete immutable constructor environment per receiver role
    // with an escaping reference. This is a closed-unit result representation,
    // not permission to import arbitrary graphs at separately compiled roots.
    for (Attribute role : program.getRoles()) {
      bool needed = false;
      for (auto [type, roles] : zip(program.getFunctionType().getResults(),
                                    program.getOutputRoles()))
        needed |= logical(type) && is_contained(cast<ArrayAttr>(roles), role);
      if (!needed)
        continue;
      if (!work.charge(requirements.storage.constructors.size()))
        return error("oracle-common-limit");
      for (auto [constructor, item] :
           enumerate(requirements.storage.constructors)) {
        if (!work.charge(item.roles.size()))
          return error("oracle-common-limit");
        for (auto [index, storage] : enumerate(item.roles))
          if (storage.role == cast<StringAttr>(role).getValue()) {
            result.resultStores.push_back({unsigned(constructor),
                                           unsigned(index),
                                           unsigned(outputs.size())});
            outputs.push_back(storage.sequence);
            outputRoles.push_back(builder.getArrayAttr({role}));
          }
      }
    }
    for (auto [index, type] : enumerate(program.getFunctionType().getResults()))
      if (logical(type)) {
        auto roles = cast<ArrayAttr>(program.getOutputRoles()[index]);
        if (!work.charge(roles.size()) ||
            !work.chargeProduct(roles.size(), result.resultStores.size()))
          return error("oracle-common-limit");
        for (Attribute role : roles) {
          OracleResultReference reference{
              unsigned(index), cast<StringAttr>(role).getValue().str(), {}};
          for (const auto &support : result.resultStores)
            if (requirements.storage.constructors[support.constructor]
                    .roles[support.role]
                    .role == reference.role)
              reference.storePorts.push_back(support.port);
          if (reference.storePorts.empty() &&
              !isa<pir::OracleSequenceType>(type))
            return error("oracle-common-interface");
          result.resultReferences.push_back(std::move(reference));
        }
      }
    NamedAttrList attributes(program->getAttrs());
    // Logical port selectors belong to the original signature. Keeping them
    // here could silently reinterpret an anchor as a native reference or store.
    // Their complete inventory remains in the checked realization edge.
    attributes.erase("contracts");
    attributes.set("function_type",
                   TypeAttr::get(builder.getFunctionType(inputs, outputs)));
    attributes.set("input_roles", builder.getArrayAttr(inputRoles));
    attributes.set("output_roles", builder.getArrayAttr(outputRoles));
    result.attributes = attributes.getDictionary(builder.getContext());
    for (auto [constructor, item] :
         enumerate(requirements.storage.constructors))
      for (auto [role, storage] : enumerate(item.roles)) {
        // These empty immutable seeds also represent a zero-trip result. They
        // carry no anchor authority. Constructor appends, controller execution
        // and changed successors stay inside their actual selected arms.
        // Stores may contain private opening state. Their empty value is an
        // owner-local allocation, not a total mathematical sequence shared by
        // all participants. Use the same scoped route for every store layout.
        auto recipe = local({}, storage.sequence);
        if (!recipe)
          return recipe.takeError();
        auto results = apply(
            *recipe, {"sequence.empty", {TypeAttr::get(storage.record)}, ""},
            storage.sequence, {});
        if (!results)
          return results.takeError();
        recipe->results = std::move(*results);
        auto empty = call(actualBody, *recipe, storage.role, {},
                          site(item.path, "empty_store", storage.role));
        if (!empty)
          return empty.takeError();
        store[{constructor, role}] = empty->front();
        result.locals.push_back(std::move(*recipe));
      }
    if (auto e = visit(actualBody, original, {}, 64))
      return std::move(e);
    if (nextArgument != actualBody.getNumArguments() ||
        candidate->getAttrDictionary() != result.attributes ||
        !complete(actualBody))
      return refuse();
    if (work.exhausted)
      return error("oracle-common-limit");
    return std::move(result);
  }
};
bool local(const OracleLocalRecipe &recipe, func::FuncOp actual,
           const OracleVerificationContext &context, OracleNativeWork &work,
           SymbolTableCollection &symbols) {
  const auto &closure = context.getClosure();
  if (!work.charge(1 + recipe.inputs.size() + recipe.outputs.size() +
                   recipe.instructions.size() + recipe.results.size()))
    return false;
  if (!actual || !actual.isPrivate() || actual->hasAttr("runtime.region") ||
      actual.getSymName() != recipe.name || actual.getNumResults() != 1 ||
      actual.getNumArguments() != recipe.inputs.size() + 1 ||
      !isa<runtime::ScopeType>(actual.getArgument(0).getType()) ||
      !equal(actual.getArgumentTypes().drop_front(), recipe.inputs))
    return false;
  auto outcome = dyn_cast<exec::OutcomeType>(actual.getResultTypes()[0]);
  if (!outcome || !equal(outcome.getPayload(), recipe.outputs))
    return false;
  auto found = closure.bodies.find(actual.getSymName().str());
  if (found == closure.bodies.end() ||
      found->second.size() != recipe.instructions.size() + 1)
    return false;
  SmallVector<Value> values(actual.getArguments().drop_front());
  for (auto [i, expected] : enumerate(recipe.instructions)) {
    if (!work.charge(1 + expected.inputs.size() + expected.outputs.size() +
                     expected.types.size() + expected.parameters.size() +
                     expected.binding.arguments.size()))
      return false;
    const auto &step = found->second[i];
    auto op = dyn_cast<exec::ApplyOp>(step.operation);
    if (!op || !step.regions.empty() ||
        step.inputs.size() != expected.inputs.size() ||
        !equal(ValueRange(step.outputs).getTypes(), expected.types) ||
        op.getSite() != "step_" + std::to_string(i) ||
        op.getParameters().size() != expected.parameters.size())
      return false;
    for (auto [id, input] : zip(expected.inputs, step.inputs))
      if (id >= values.size() || values[id] != input)
        return false;
    if (!equal(op.getParameters(), expected.parameters))
      return false;
    auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!binding || binding.getContract() != expected.binding.contract ||
        binding.getImplementation() != expected.binding.implementation ||
        binding.getArguments().size() != expected.binding.arguments.size())
      return false;
    if (!context.matchesBinding(binding, expected.binding))
      return false;
    append_range(values, step.outputs);
  }
  const auto &last = found->second.back();
  if (!isa<exec::ReturnOp>(last.operation) || !last.regions.empty() ||
      last.inputs.size() != recipe.results.size())
    return false;
  for (auto [id, input] : zip(recipe.results, last.inputs))
    if (id >= values.size() || values[id] != input)
      return false;
  return true;
}
// Every extra declaration is reachable from a checked generated primitive or
// the realized entry. Original declarations retain their exact body. A spare
// implementation cannot hide behind an unused symbol in a checked candidate.
bool inventory(pir::ProtocolModuleOp source, pir::ProtocolModuleOp candidate,
               ArrayRef<std::string> entries, ArrayRef<Operation *> roots,
               OracleNativeWork &work,
               const OracleNativeSourcePreflight &sourcePreflight,
               const OracleNativeSourcePreflight &candidatePreflight) {
  if (!work.charge(1 + roots.size() + entries.size()))
    return false;
  // Both lazy symbol tables were reserved by their immutable preflights.
  auto &candidateSymbols =
      candidatePreflight.getSymbols().getSymbolTable(candidate);
  // All names below belong to the admitted subjects' single MLIR context.
  // Keep their immutable interned keys through membership and lookup instead
  // of copying and hashing their byte spellings for each reference.
  llvm::DenseSet<StringAttr> original, allowed, realizedEntries;
  for (const auto &entry : entries) {
    if (!work.charge(1 + entry.size()))
      return false;
    realizedEntries.insert(StringAttr::get(candidate.getContext(), entry));
  }
  for (auto &op : source.getBody().front()) {
    if (!work.charge(4))
      return false;
    auto name = SymbolTable::getSymbolName(&op);
    if (!name)
      return false;
    original.insert(name);
    if (isa<pir::OracleDefinitionOp>(op)) {
      if (candidateSymbols.lookup(name))
        return false;
      continue;
    }
    auto *actual = candidateSymbols.lookup(name);
    bool realized = realizedEntries.contains(name);
    if (actual && !realized) {
      // Equivalence traverses operations and compares interned attribute/type
      // handles. Storage was already inspected; reserve both actual subjects
      // before that comparison, without inspecting their DAGs again.
      if (!sourcePreflight.reserveTraversal(&op) ||
          !candidatePreflight.reserveTraversal(actual))
        return false;
    }
    if (!actual ||
        (!realized && !OperationEquivalence::isEquivalentTo(
                          &op, actual, OperationEquivalence::IgnoreLocations)))
      return false;
    allowed.insert(name);
  }
  SmallVector<Operation *> pending(roots.begin(), roots.end());
  for (const auto &entry : entries)
    pending.push_back(candidateSymbols.lookup(entry));
  llvm::DenseSet<Operation *> seen;
  while (!pending.empty()) {
    if (!work.charge())
      return false;
    auto *op = pending.pop_back_val();
    if (!op || !seen.insert(op).second)
      continue;
    auto name = SymbolTable::getSymbolName(op);
    if (!name || !work.charge(2) || op->getParentOp() != candidate)
      return false;
    allowed.insert(name);
    if (!original.contains(name))
      if (auto function = dyn_cast<func::FuncOp>(op)) {
        if (!function.isPrivate() ||
            (function.getNumArguments() &&
             isa<runtime::ScopeType>(function.getArgument(0).getType()) &&
             function->getAttrs().size() != 5))
          return false;
        if (function.getNumArguments() &&
            isa<runtime::ScopeType>(function.getArgument(0).getType()) &&
            !function->hasAttr("runtime.region")) {
          Builder builder(candidate.getContext());
          auto expected =
              builder.getArrayAttr({name, builder.getArrayAttr({})});
          if (function->getAttr("runtime.origin") != expected)
            return false;
        }
      }
    bool good = true;
    op->walk([&](Operation *nested) {
      if (!work.charge(1 + nested->getNumOperands() +
                       nested->getNumResults())) {
        good = false;
        return WalkResult::interrupt();
      }
      auto references =
          candidatePreflight.borrowReferences(nested->getAttrDictionary());
      if (!references) {
        consumeError(references.takeError());
        good = false;
        return WalkResult::interrupt();
      }
      for (auto symbol : *references) {
        if (!work.charge(3) || !symbol.getNestedReferences().empty()) {
          good = false;
          return WalkResult::interrupt();
        }
        auto *target = candidateSymbols.lookup(symbol.getRootReference());
        if (!target) {
          good = false;
          return WalkResult::interrupt();
        }
        auto targetName = SymbolTable::getSymbolName(target);
        if (original.contains(targetName))
          continue;
        if (!isa<func::FuncOp, runtime::BindingOp>(target)) {
          good = false;
          return WalkResult::interrupt();
        }
        pending.push_back(target);
      }
      return good ? WalkResult::advance() : WalkResult::interrupt();
    });
    if (!good)
      return false;
  }
  for (auto &op : candidate.getBody().front()) {
    if (!work.charge(2))
      return false;
    auto name = SymbolTable::getSymbolName(&op);
    if (!name || !allowed.contains(name))
      return false;
  }
  return true;
}
} // namespace
Expected<OracleCommonAnalysis>
readOracleCommon(ModuleOp prepared, ModuleOp candidate, StringRef entry,
                 const OracleCommonRequirements &requirements,
                 ArrayRef<OracleCommonController> controllers,
                 ArrayRef<std::vector<func::FuncOp>> allocators,
                 ArrayRef<OracleMerkleFunctions> merkle,
                 OracleAuthentication authentication,
                 ArrayRef<OracleCommonRemote> remotes,
                 ArrayRef<OracleCommonBatch> batches, OracleNativeWork *shared,
                 const OracleNativeSourcePreflight *sourcePreflight,
                 const OracleNativeSourcePreflight *candidatePreflight) {
  OracleNativeWork localWork;
  OracleNativeWork &work = shared ? *shared : localWork;
  std::optional<OracleNativeSourcePreflight> sourceBound, candidateBound;
  if (!sourcePreflight) {
    auto read = OracleNativeSourcePreflight::read(prepared, work);
    if (!read)
      return read.takeError();
    sourceBound.emplace(std::move(*read));
    sourcePreflight = &*sourceBound;
  }
  if (!candidatePreflight) {
    auto read = OracleNativeSourcePreflight::read(candidate, work);
    if (!read)
      return read.takeError();
    candidateBound.emplace(std::move(*read));
    candidatePreflight = &*candidateBound;
  }
  if (auto e = checkOracleNativePreflight(prepared, work, sourcePreflight))
    return std::move(e);
  if (auto e = checkOracleNativePreflight(candidate, work, candidatePreflight))
    return std::move(e);
  if (!hasSingleElement(prepared.getBody()->getOperations()) ||
      !hasSingleElement(candidate.getBody()->getOperations()))
    return refuse();
  auto sourceUnit =
      dyn_cast<pir::ProtocolModuleOp>(prepared.getBody()->front());
  auto targetUnit =
      dyn_cast<pir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!sourceUnit || !targetUnit || prepared == candidate)
    return refuse();
  auto original = dyn_cast_or_null<pir::MathematicalOp>(
      sourcePreflight->getSymbols().getSymbolTable(sourceUnit).lookup(entry));
  auto actual =
      dyn_cast_or_null<pir::MathematicalOp>(candidatePreflight->getSymbols()
                                                .getSymbolTable(targetUnit)
                                                .lookup(entry));
  if (!original || !actual ||
      allocators.size() != requirements.storage.constructors.size() ||
      merkle.size() != allocators.size())
    return refuse();
  for (auto [i, helpers] : enumerate(allocators))
    if (helpers.size() != requirements.storage.constructors[i].roles.size())
      return refuse();
  auto schedule = planOracleQueryScheduleWithWork(
      prepared, entry, requirements, controllers, merkle, authentication, work,
      *sourcePreflight);
  if (!schedule)
    return schedule.takeError();
  if (remotes.size() != schedule->remotes.size() ||
      batches.size() != schedule->batches.size())
    return refuse();
  return SourceReader(prepared, original, requirements, controllers, allocators,
                      merkle, authentication, *schedule, remotes, batches,
                      actual, work,
                      sourcePreflight->getSymbols().getSymbolTable(sourceUnit))
      .run();
}
Error checkOracleRealizationModel(
    const OracleVerificationContext &sourceContext,
    const OracleVerificationContext &targetContext,
    ArrayRef<OracleCommonEntryRealization> actualEntries,
    ArrayRef<OracleRootSelection> selections,
    OracleAuthentication authentication, OracleRealizationFacts *facts,
    OracleNativeWork *shared,
    const OracleNativeSourcePreflight *sourcePreflight,
    const OracleNativeSourcePreflight *candidatePreflight,
    std::vector<OracleCommonAnalysis> *analyses) {
  OracleNativeWork localWork;
  OracleNativeWork &commonWork = shared ? *shared : localWork;
  return oracleVerificationWithWork(commonWork, [&]() -> Error {
    std::optional<OracleNativeSourcePreflight> sourceBound, candidateBound;
    if (!sourcePreflight) {
      auto read = OracleNativeSourcePreflight::read(sourceContext.getModule(),
                                                    commonWork);
      if (!read)
        return read.takeError();
      sourceBound.emplace(std::move(*read));
      sourcePreflight = &*sourceBound;
    }
    if (!candidatePreflight) {
      auto read = OracleNativeSourcePreflight::read(targetContext.getModule(),
                                                    commonWork);
      if (!read)
        return read.takeError();
      candidateBound.emplace(std::move(*read));
      candidatePreflight = &*candidateBound;
    }
    if (auto e = checkOracleNativePreflight(sourceContext.getModule(),
                                            commonWork, sourcePreflight))
      return e;
    if (auto e = checkOracleNativePreflight(targetContext.getModule(),
                                            commonWork, candidatePreflight))
      return e;
    OracleRealizationFacts derived;
    std::vector<OracleCommonAnalysis> derivedAnalyses;
    SmallVector<detail::OracleRepeatCount, 0> repeatCounts;
    ModuleOp prepared = sourceContext.getModule(),
             actualModule = targetContext.getModule();
    auto entries = oracleEntries(prepared, &commonWork, sourcePreflight);
    if (!entries)
      return entries.takeError();
    if (!actualModule || actualModule == prepared ||
        actualModule.getContext() != prepared.getContext() ||
        actualModule->getAttrDictionary() != prepared->getAttrDictionary() ||
        !hasSingleElement(actualModule.getBody()->getOperations()) ||
        actualEntries.size() != entries->size())
      return refuse();
    auto source = sourceContext.getUnit();
    auto candidate = targetContext.getUnit();
    if (source->getAttrDictionary() != candidate->getAttrDictionary())
      return refuse();
    SmallVector<Operation *> roots;
    auto root = [&](func::FuncOp function) {
      if (function)
        roots.push_back(function);
    };
    for (auto [entry, realized] : zip(*entries, actualEntries)) {
      if (entry != realized.entry)
        return refuse();
      auto requirements = oracleRequirements(prepared, entry, selections,
                                             &commonWork, sourcePreflight);
      if (!requirements)
        return requirements.takeError();
      if (realized.controllers.size() != requirements->controllers.size() ||
          realized.allocators.size() !=
              requirements->storage.constructors.size() ||
          realized.merkle.size() != requirements->storage.constructors.size())
        return refuse();

      if (!commonWork.charge(1 + realized.controllers.size()))
        return error("oracle-common-limit");
      SmallVector<OracleCheckedController> checkedControllers;
      checkedControllers.reserve(realized.controllers.size());
      for (auto [expected, item] :
           zip(requirements->controllers, realized.controllers)) {
        if (expected.role != item.role || expected.kind != item.kind ||
            expected.access != item.access)
          return refuse();
        if (auto e = checkOracleQueryController(
                targetContext, sourceContext, requirements->storage, item.role,
                item.kind, requirements->capacity, item.body, item.access))
          return e;
        checkedControllers.push_back(OracleCheckedController(
            targetContext, sourceContext, requirements->storage, item.body));
        const auto &body = item.body;
        root(body.initialize);
        root(body.advance);
        root(body.finish);
        root(body.evaluate);
        root(body.contents);
        for (auto helper : body.resume)
          root(helper);
        for (auto helper : body.rowCounts)
          root(helper);
        for (auto helper : body.leafCounts)
          root(helper);
        for (auto helper : body.constructionCounts)
          root(helper);
        for (const auto &constructor : body.constructors) {
          root(constructor.lookup);
          root(constructor.functions.answer);
          for (const auto &query : constructor.functions.queries)
            root(query.position);
        }
      }
      for (auto [ordinal, constructor] :
           enumerate(requirements->storage.constructors)) {
        const auto &functions = realized.merkle[ordinal];
        if (constructor.scheme.empty()) {
          if (functions.position || functions.commit || functions.open ||
              functions.authenticate)
            return refuse();
        } else {
          const auto &choice = requirements->realizations[ordinal];
          if (auto e = checkOracleMerkle(targetContext, functions,
                                         constructor.kind, choice.scheme,
                                         choice.grouping, choice.order))
            return e;
          root(functions.position);
          root(functions.commit);
          root(functions.open);
          root(functions.authenticate);
        }
        if (realized.allocators[ordinal].size() != constructor.roles.size())
          return refuse();
        for (auto [role, helper] : enumerate(realized.allocators[ordinal])) {
          if (auto e = checkOracleAnchorAllocator(
                  targetContext, helper, requirements->storage, ordinal, role))
            return e;
          root(helper);
        }
      }

      auto schedule = planOracleQueryScheduleWithWork(
          prepared, entry, *requirements, realized.controllers, realized.merkle,
          authentication, commonWork, *sourcePreflight);
      if (!schedule)
        return schedule.takeError();
      if (realized.remotes.size() != schedule->remotes.size() ||
          realized.batches.size() != schedule->batches.size())
        return refuse();
      for (auto [expected, actual] : zip(schedule->remotes, realized.remotes)) {
        if (actual.receiver != expected.receiver ||
            actual.holder != expected.holder ||
            actual.window.capacity != schedule->capacity)
          return refuse();
        const auto &receiver = realized.controllers[expected.receiver];
        if (auto e = checkOracleQueryDemand(
                targetContext, sourceContext, requirements->storage,
                receiver.body, receiver.kind, actual.demand,
                checkedControllers[expected.receiver]))
          return e;
        if (auto e = checkOracleQueryResponse(targetContext, expected.exchange,
                                              actual.response))
          return e;
        if (!commonWork.charge())
          return error("oracle-common-limit");
        OracleCheckedResponse checkedResponse(targetContext, expected.exchange,
                                              actual.response);
        if (!actual.open)
          return refuse();
        OracleExchangeRecipe recipe;
        // The actual spelling is only a symbol handle. Source and checked
        // primitives determine the complete signature and dispatch body.
        func::FuncOp opening = actual.open;
        recipe.name = opening.getSymName().str();
        recipe.action = OracleExchangeAction::Open;
        recipe.exchange =
            std::make_shared<const OracleQueryExchange>(expected.exchange);
        recipe.inputs.push_back(expected.exchange.request);
        append_range(recipe.inputs, expected.exchange.holderStores);
        recipe.outputs.push_back(expected.exchange.response);
        if (!checkOracleQueryExchange(targetContext, actual.open, recipe))
          return refuse();
        if (auto e = checkOracleQueryPacket(
                targetContext, expected.exchange, actual.response, actual.open,
                realized.merkle, schedule->capacity, actual.packet))
          return e;
        if (auto e = checkOracleQueryWindow(
                targetContext, receiver.body, actual.demand, expected.exchange,
                actual.response, actual.window, checkedResponse))
          return e;
        root(actual.demand.initialize);
        root(actual.demand.advance);
        root(actual.demand.consume);
        root(actual.response.authenticate);
        root(actual.response.resume);
        root(actual.open);
        root(actual.packet.group);
        root(actual.packet.open);
        root(actual.packet.authenticate);
        root(actual.window.collect);
        root(actual.window.replay);
        root(actual.window.finish);
      }
      for (auto [expected, actual] : zip(schedule->batches, realized.batches)) {
        if (actual.remotes != expected.remotes)
          return refuse();
        SmallVector<OracleQueryBatchRoot> batchRoots;
        for (unsigned index : expected.remotes) {
          const auto &remote = realized.remotes[index];
          batchRoots.push_back({&realized.controllers[remote.receiver].body,
                                &remote.demand, &remote.window});
        }
        // Windows have already been independently checked in this immutable
        // context. The batch reader checks their exact ordered composition.
        if (auto e =
                checkOracleQueryBatch(targetContext, batchRoots, actual.body))
          return e;
        root(actual.body.collect);
        root(actual.body.checkAvailable);
        root(actual.body.replay);
        root(actual.body.finish);
      }

      auto original = dyn_cast_or_null<pir::MathematicalOp>(
          sourcePreflight->getSymbols().getSymbolTable(source).lookup(entry));
      auto program = dyn_cast_or_null<pir::MathematicalOp>(
          candidatePreflight->getSymbols().getSymbolTable(candidate).lookup(
              entry));
      if (!original || !program)
        return refuse();
      auto plan =
          SourceReader(prepared, original, *requirements, realized.controllers,
                       realized.allocators, realized.merkle, authentication,
                       *schedule, realized.remotes, realized.batches, program,
                       commonWork,
                       sourcePreflight->getSymbols().getSymbolTable(source))
              .run();
      if (!plan)
        return plan.takeError();
      for (auto &count : plan->repeatCounts) {
        if (!commonWork.charge(1 + count.counts.size() + count.queries.size() +
                               count.leafCalls.size() +
                               count.sourcePath.size() + count.ancestry.size() +
                               count.iterations.size()))
          return error("oracle-common-limit");
        repeatCounts.push_back(std::move(count));
      }
      if (realized.inputShapes != plan->inputShapes ||
          realized.resultStores != plan->resultStores ||
          realized.resultReferences != plan->resultReferences ||
          realized.locals.size() != plan->locals.size())
        return refuse();
      for (auto [recipe, helper] : zip(plan->locals, realized.locals)) {
        if (!local(recipe, helper, targetContext, commonWork,
                   candidatePreflight->getSymbols()))
          return commonWork.exhausted ? error("oracle-common-limit") : refuse();
        root(helper);
      }
      if (facts) {
        llvm::StringSet<> requests;
        for (const auto &occurrence : plan->occurrences) {
          if (!commonWork.charge(1 + occurrence.purpose.size() +
                                 occurrence.site.size()))
            return error("oracle-common-limit");
          if (occurrence.purpose == "opening_request" &&
              !requests.insert(occurrence.site).second)
            return refuse();
        }
        auto walked = program.walk([&](Operation *operation) {
          if (!commonWork.charge())
            return WalkResult::interrupt();
          auto exchange = dyn_cast<pir::ExchangeOp>(operation);
          if (!exchange)
            return WalkResult::advance();
          if (!commonWork.charge(exchange.getSite().size()))
            return WalkResult::interrupt();
          if (requests.erase(exchange.getSite()))
            derived.openingRequests.push_back(exchange);
          return WalkResult::advance();
        });
        if (walked.wasInterrupted())
          return error("oracle-common-limit");
        if (!requests.empty())
          return refuse();
        if (!commonWork.charge(1 + entry.size()))
          return error("oracle-common-limit");
        if (analyses) {
          // Facts and record analyses each retain their own storage. Reserve
          // the actual facts copy before preserving the independently read
          // plan.
          for (const auto &item : plan->occurrences)
            if (!commonWork.charge(1 + item.site.size() + item.purpose.size() +
                                   item.role.size() + item.sourcePath.size()))
              return error("oracle-common-limit");
          for (const auto &block : plan->queryBlocks) {
            if (!commonWork.charge(1 + block.queries.size()))
              return error("oracle-common-limit");
            for (const auto &path : block.queries)
              if (!commonWork.charge(path.size()))
                return error("oracle-common-limit");
          }
          derived.entries.push_back(
              {entry, plan->occurrences, plan->queryBlocks});
        } else {
          derived.entries.push_back({entry, std::move(plan->occurrences),
                                     std::move(plan->queryBlocks)});
        }
      }
      if (analyses) {
        if (!commonWork.charge())
          return error("oracle-common-limit");
        // Retain the exact independently derived layout for publication. This
        // scratch result escapes only after inventory and both completions
        // pass.
        plan->requirements = std::make_shared<const OracleCommonRequirements>(
            std::move(*requirements));
        derivedAnalyses.push_back(std::move(*plan));
      }
    }

    if (!inventory(source, candidate, *entries, roots, commonWork,
                   *sourcePreflight, *candidatePreflight))
      return commonWork.exhausted ? error("oracle-common-limit") : refuse();
    // Structural comparison is now complete. Source premises remain input
    // requirements; helper return agreement is conditional on those premises
    // and normal return at this exact source/candidate occurrence. No store,
    // table, position, root or failure/completion equality is asserted.
    zkc::facts::Work controlWork(
        [&](uint64_t amount) { return commonWork.charge(amount); });

    auto sourceRequirements =
        detail::completeCommonControl(source, controlWork);
    if (!sourceRequirements)
      return sourceRequirements.takeError();

    auto candidateRequirements =
        targetContext.complete(source, repeatCounts, controlWork);
    if (!candidateRequirements)
      return candidateRequirements.takeError();

    derived.sourceRequirements = std::move(*sourceRequirements);
    derived.candidateRequirements = std::move(*candidateRequirements);
    if (facts)
      *facts = std::move(derived);
    // Publish outputs only after every helper, declaration and both complete
    // common-control checks succeed. Partial entry analyses grant no authority.
    if (analyses)
      *analyses = std::move(derivedAnalyses);
    return Error::success();
  });
}
Expected<OracleRealizationFacts>
checkOracleRealization(ModuleOp prepared, const OracleCommonRealization &actual,
                       const OracleRealizationPolicy &policy) {
  OracleNativeWork work;
  return checkOracleRealizationWithWork(prepared, actual, policy, work);
}
Expected<OracleRealizationFacts> checkOracleRealizationWithWork(
    ModuleOp prepared, const OracleCommonRealization &actual,
    const OracleRealizationPolicy &policy, OracleNativeWork &work,
    const OracleNativeSourcePreflight *sourcePreflight,
    const OracleNativeSourcePreflight *candidatePreflight,
    std::vector<OracleCommonAnalysis> *analyses,
    std::vector<OracleRootSelection> *checkedSelections) {

  std::optional<OracleNativeSourcePreflight> sourceBound, candidateBound;
  if (!sourcePreflight) {
    auto read = OracleNativeSourcePreflight::read(prepared, work);
    if (!read)
      return read.takeError();
    sourceBound.emplace(std::move(*read));
    sourcePreflight = &*sourceBound;
  }
  if (!candidatePreflight) {
    auto read = OracleNativeSourcePreflight::read(actual.module.get(), work);
    if (!read)
      return read.takeError();
    candidateBound.emplace(std::move(*read));
    candidatePreflight = &*candidateBound;
  }
  if (auto e = checkOracleNativePreflight(prepared, work, sourcePreflight))
    return std::move(e);
  if (auto e = checkOracleNativePreflight(actual.module.get(), work,
                                          candidatePreflight))
    return std::move(e);
  auto selections = resolveOracleRealizationSelectionWithWork(
      prepared, policy, work, *sourcePreflight);
  if (!selections)
    return selections.takeError();

  auto source =
      OracleVerificationContext::read(prepared, work, *sourcePreflight);
  if (!source)
    return source.takeError();

  auto target = OracleVerificationContext::readCandidate(
      actual.module.get(), work, *candidatePreflight);
  if (!target) {
    if (work.exhausted)
      return target.takeError();
    consumeError(target.takeError());
    return refuse();
  }

  OracleRealizationFacts facts;
  if (auto e = checkOracleRealizationModel(
          *source, *target, actual.entries, *selections, policy.authentication,
          &facts, &work, sourcePreflight, candidatePreflight, analyses))
    return std::move(e);
  if (checkedSelections)
    *checkedSelections = std::move(*selections);
  return facts;
}
} // namespace zkc::protocol

#include "../ScopedExecution.h"
#include "DataPreconditions.h"
#include "EmissionBudget.h"
#include "Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Packing.h"
using namespace llvm;
namespace zkc::language {
namespace {
using Values = SmallVector<mlir::Value>;
using Types = SmallVector<mlir::Type>;
class FiniteEmitter {
  const ClosedEntry &project;
  const FiniteComputation &finite;
  const Type &resultType;
  ArrayRef<Values> values;
  mlir::OpBuilder &builder;
  mlir::Location location;
  mlir::Block &definitions;
  Layouts &layouts;
  std::string prefix;
  StringRef site;
  EmissionBudget &budget;
  uint64_t &remaining;
  Error failure = Error::success();
  std::vector<Types> itemTypes;
  std::vector<unsigned> bodyPorts, predicatePorts;
  Values domainOperands, captures, initial;
  bool local;
  protocol::detail::ScopedExecutionBuilder *scoped;
  template <class T> std::optional<T> take(Expected<T> value) {
    if (!value) {
      failure = value.takeError();
      return {};
    }
    return std::move(*value);
  }
  bool charge(uint64_t count) {
    if (count > remaining) {
      failure = error("source.limit", "finite translation work limit exceeded");
      return false;
    }
    remaining -= count;
    return true;
  }
  bool canInsert(uint64_t size = 1) {
    if (!budget.allows(size)) {
      failure =
          error("source.limit", "finite translation operation limit exceeded");
      return false;
    }
    return true;
  }
  mlir::NamedAttribute text(StringRef name, StringRef value) {
    return builder.getNamedAttr(name, builder.getStringAttr(value));
  }
  mlir::NamedAttribute symbol(StringRef name, StringRef value) {
    return builder.getNamedAttr(
        name, mlir::FlatSymbolRefAttr::get(builder.getContext(), value));
  }
  mlir::Operation *make(StringRef name, mlir::TypeRange results,
                        mlir::ValueRange operands,
                        ArrayRef<mlir::NamedAttribute> attributes = {},
                        bool region = false) {
    if (!canInsert())
      return nullptr;
    mlir::OperationState state(location, name);
    state.addTypes(results);
    state.addOperands(operands);
    state.addAttributes(attributes);
    if (region)
      state.addRegion()->push_back(new mlir::Block());
    return builder.create(state);
  }
  std::optional<Types> types(const Type &type) {
    auto layout = take(layouts.get(type));
    if (!layout)
      return {};
    Types result;
    for (const auto &leaf : (**layout).leaves) {
      if (!charge(leaf.cost()))
        return {};
      if (!leaf.data()) {
        failure =
            error("source.layout", "finite inputs require native data layouts");
        return {};
      }
      auto bound = take(protocol::parseBoundType(*leaf.data(), false));
      if (!bound)
        return {};
      auto native = protocol::decodeBoundType(builder.getContext(), *bound);
      if (!native) {
        failure = error("source.layout", "finite data dialect unavailable");
        return {};
      }
      result.push_back(native);
    }
    return result;
  }
  Values flatten(ArrayRef<ValueId> inputs) {
    Values result;
    for (auto input : inputs)
      llvm::append_range(result, values[input.index]);
    return result;
  }
  std::optional<std::vector<unsigned>> capturePorts(ArrayRef<ValueId> inputs) {
    std::vector<unsigned> result;
    for (auto value : flatten(inputs)) {
      if (!charge(domainOperands.size() + captures.size() + 1))
        return {};
      auto domain = llvm::find(domainOperands, value);
      if (domain != domainOperands.end()) {
        result.push_back(domain - domainOperands.begin());
        continue;
      }
      auto found = llvm::find(captures, value);
      if (found == captures.end()) {
        result.push_back(domainOperands.size() + captures.size());
        captures.push_back(value);
      } else
        result.push_back(domainOperands.size() + (found - captures.begin()));
    }
    return result;
  }
  // Fixed source arrays use their ordinary flattened ABI at the source
  // boundary. Materialize the existing immutable Sequence carrier once per
  // domain input, preserving product and Unit elements without a new ABI.
  std::optional<mlir::Value> array(unsigned index) {
    const auto &source = finite.domain->inputs[index];
    auto input = values[finite.domainOperands[index].index];
    auto packed = take(layouts.packed(source.arguments.front()));
    if (!packed)
      return {};
    auto element =
        protocol::decodeBoundType(builder.getContext(), packed->carrier);
    if (!element) {
      failure = error("source.layout", "array element dialect unavailable");
      return {};
    }
    auto size = source.dimension.closedValue();
    auto width = packed->flat->leaves.size();
    if ((width && size > input.size() / width) ||
        size * width != input.size()) {
      failure = error("source.layout", "array flattened extent differs");
      return {};
    }
    auto sequence = data::SequenceType::get(builder.getContext(), element);
    auto suffix = "_array_" + std::to_string(index);
    auto name = prefix + suffix;
    auto signature =
        builder.getFunctionType(mlir::ValueRange(input).getTypes(), {sequence});
    {
      mlir::OpBuilder::InsertionGuard guard(builder);
      builder.setInsertionPointToEnd(&definitions);
      auto *helper =
          make("func.func", {}, {},
               {text("sym_name", name), text("sym_visibility", "private"),
                builder.getNamedAttr("function_type",
                                     mlir::TypeAttr::get(signature))},
               true);
      if (!helper)
        return {};
      auto &block = helper->getRegion(0).front();
      for (auto value : input)
        block.addArgument(value.getType(), location);
      builder.setInsertionPointToEnd(&block);
      auto *empty = make("data.sequence_empty", {sequence}, {});
      if (!empty)
        return {};
      auto result = empty->getResult(0);
      if (!charge(size + input.size()))
        return {};
      for (uint64_t i = 0; i < size; ++i) {
        if (!canInsert(packed->product ? 1 : 0))
          return {};
        auto item = take(emitPack(builder, location, *packed,
                                  block.getArguments().slice(i * width, width),
                                  PackingMode::Mathematical));
        if (!item)
          return {};
        auto *append =
            make("data.sequence_append", {sequence}, {result, *item});
        if (!append)
          return {};
        result = append->getResult(0);
      }
      if (!make("func.return", {}, result))
        return {};
      if (local) {
        builder.setInsertionPointToEnd(&definitions);
        if (!make("local.realize", {}, {},
                  {text("sym_name", name + "_realize"), symbol("helper", name),
                   builder.getNamedAttr("function_type",
                                        mlir::TypeAttr::get(signature))}))
          return {};
      }
    }
    SmallVector<mlir::NamedAttribute> attrs{
        symbol("callee", local ? name + "_realize" : name)};
    if (scoped) {
      attrs.push_back(text("site", site.str() + suffix));
      auto result = scoped->invoke("exec.compute", {sequence},
                                   scoped->scoped(input), attrs);
      return result.front();
    }
    if (local)
      attrs.push_back(text("site", site.str() + suffix));
    auto *call =
        make(local ? "local.apply" : "func.call", {sequence}, input, attrs);
    return call ? std::optional<mlir::Value>(call->getResult(0)) : std::nullopt;
  }
  bool domainInputs() {
    for (unsigned i = 0; i < finite.domainOperands.size(); ++i) {
      if (finite.domain->inputs[i].kind == Type::Kind::Array) {
        auto adapted = array(i);
        if (!adapted)
          return false;
        domainOperands.push_back(*adapted);
      } else {
        const auto &input = values[finite.domainOperands[i].index];
        if (input.size() != 1) {
          failure = error("source.layout",
                          "domain input requires one native carrier");
          return false;
        }
        domainOperands.push_back(input.front());
      }
    }
    return true;
  }
  bool descriptor() {
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&definitions);
    const auto &shape = *finite.domain;
    std::vector<mlir::Value> nodes;
    for (const auto &node : shape.nodes) {
      Types items;
      if (node.kind == DomainBinding::Kind::Zip ||
          node.kind == DomainBinding::Kind::Product) {
        for (auto child : node.children)
          llvm::append_range(items, itemTypes.at(child));
      } else if ((node.kind == DomainBinding::Kind::Elements ||
                  node.kind == DomainBinding::Kind::SourceArray) &&
                 mlir::isa<data::SequenceType>(
                     domainOperands[node.operands.front().index].getType())) {
        items.push_back(
            mlir::cast<data::SequenceType>(
                domainOperands[node.operands.front().index].getType())
                .getElementType());
      } else {
        auto flat = types(node.item);
        if (!flat)
          return false;
        items = std::move(*flat);
      }
      if (!charge(items.size() + 1))
        return false;
      itemTypes.push_back(std::move(items));
    }
    auto output =
        data::DomainType::get(builder.getContext(), itemTypes[shape.result]);
    auto *declaration =
        make("data.domain", {}, {},
             {text("sym_name", prefix + "_domain"),
              text("sym_visibility", "private"),
              builder.getNamedAttr(
                  "function_type",
                  mlir::TypeAttr::get(builder.getFunctionType(
                      mlir::ValueRange(domainOperands).getTypes(), {output})))},
             true);
    if (!declaration)
      return false;
    auto &block = declaration->getRegion(0).front();
    for (auto value : domainOperands)
      block.addArgument(value.getType(), location);
    builder.setInsertionPointToEnd(&block);
    for (unsigned i = 0; i < shape.nodes.size(); ++i) {
      const auto &node = shape.nodes[i];
      Values operands;
      for (auto input : node.operands)
        operands.push_back(block.getArgument(input.index));
      for (auto child : node.children)
        operands.push_back(nodes[child]);
      StringRef name;
      SmallVector<mlir::NamedAttribute> attributes;
      switch (node.kind) {
      case DomainBinding::Kind::Elements:
      case DomainBinding::Kind::SourceArray:
        name = "data.domain_elements";
        break;
      case DomainBinding::Kind::Indices:
        name = "data.domain_indices";
        attributes.push_back(
            builder.getNamedAttr("axis", builder.getI64IntegerAttr(node.axis)));
        break;
      case DomainBinding::Kind::Range:
        name = "data.domain_range";
        break;
      case DomainBinding::Kind::Zip:
        name = "data.domain_zip";
        break;
      case DomainBinding::Kind::Product:
        name = "data.domain_product";
        break;
      case DomainBinding::Kind::MatrixRow:
        name = "data.domain_matrix_row";
        break;
      case DomainBinding::Kind::MatrixColumn:
        name = "data.domain_matrix_column";
        break;
      case DomainBinding::Kind::MatrixCoordinates:
        name = "data.domain_matrix_coordinates";
        attributes.push_back(
            text("order", node.axis ? "column_major" : "row_major"));
        break;
      default:
        failure =
            error("source.layout", "domain constructor has no native adapter");
        return false;
      }
      auto *operation = make(
          name, {data::DomainType::get(builder.getContext(), itemTypes[i])},
          operands, attributes);
      if (!operation)
        return false;
      nodes.push_back(operation->getResult(0));
    }
    return bool(make("data.domain_yield", {}, nodes[shape.result]));
  }
  std::optional<Values>
  item(unsigned index, mlir::ValueRange inputs, unsigned &ordinal,
       protocol::detail::ScopedExecutionBuilder *control) {
    if (!charge(inputs.size() + 1))
      return {};
    const auto &node = finite.domain->nodes[index];
    if (node.kind == DomainBinding::Kind::Zip ||
        node.kind == DomainBinding::Kind::Product) {
      Values result;
      unsigned offset = 0;
      for (auto child : node.children) {
        auto nested = item(child, inputs.slice(offset, itemTypes[child].size()),
                           ordinal, control);
        if (!nested)
          return {};
        llvm::append_range(result, *nested);
        offset += itemTypes[child].size();
      }
      return result;
    }
    if ((node.kind == DomainBinding::Kind::Elements ||
         node.kind == DomainBinding::Kind::SourceArray) &&
        mlir::isa<data::SequenceType>(
            domainOperands[node.operands.front().index].getType())) {
      auto packed = take(layouts.packed(node.item));
      if (!packed ||
          !canInsert(packed->product ? (local ? 2 : packed->flat->leaves.size())
                                     : 0))
        return {};
      if (control && packed->product) {
        auto flat = types(node.item);
        if (!flat)
          return {};
        auto itemSite = "item_" + std::to_string(ordinal++);
        auto *parent = builder.getInsertionBlock()->getParentOp();
        auto name = mlir::SymbolTable::getSymbolName(parent).getValue().str() +
                    "_" + itemSite;
        return control->match(
            inputs.front(), {}, *flat, {packed->alternative}, itemSite,
            [&](unsigned) {
              builder.setInsertionPointToEnd(&definitions);
              Types arguments{runtime::ScopeType::get(builder.getContext())};
              llvm::append_range(arguments, *flat);
              auto outcome =
                  exec::OutcomeType::get(builder.getContext(), *flat);
              auto helper = mlir::func::FuncOp::create(
                  builder, location, name,
                  builder.getFunctionType(arguments, {outcome}));
              helper.setPrivate();
              helper->setAttr("no_inline", builder.getUnitAttr());
              helper->setAttr("runtime.region", builder.getUnitAttr());
              helper.addEntryBlock();
              builder.setInsertionPointToEnd(&helper.front());
              protocol::detail::ScopedExecutionBuilder region(builder, helper);
              region.complete(helper.getArguments().drop_front());
              return helper;
            });
      }
      return take(
          emitUnpack(builder, location, *packed, inputs.front(),
                     local ? PackingMode::Local : PackingMode::Mathematical,
                     "item_" + std::to_string(ordinal++)));
    }
    return Values(inputs);
  }
  bool callback(const FiniteCallback &selected, ArrayRef<unsigned> ports,
                StringRef suffix, mlir::TypeRange states, bool collect) {
    const auto &helper = project.declarations()[selected.helper.index];
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&definitions);
    Types inputs(states.begin(), states.end());
    llvm::append_range(inputs, itemTypes[finite.domain->result]);
    llvm::append_range(inputs, mlir::ValueRange(domainOperands).getTypes());
    llvm::append_range(inputs, mlir::ValueRange(captures).getTypes());
    auto outputs = types(helper.outputs.front().type);
    if (!outputs)
      return false;
    std::optional<PackedLayout> packed;
    Types adapterOutputs = *outputs;
    if (collect && resultType.domain == "sequence") {
      packed = take(layouts.packed(helper.outputs.front().type));
      if (!packed)
        return false;
      adapterOutputs = {
          protocol::decodeBoundType(builder.getContext(), packed->carrier)};
    }
    Types actualInputs = inputs, actualOutputs = adapterOutputs;
    if (scoped) {
      actualInputs.insert(actualInputs.begin(),
                          runtime::ScopeType::get(builder.getContext()));
      actualOutputs = {
          exec::OutcomeType::get(builder.getContext(), adapterOutputs)};
    }
    SmallVector<mlir::NamedAttribute> attrs{
        text("sym_name", prefix + suffix.str()),
        text("sym_visibility", "private"),
        builder.getNamedAttr("function_type",
                             mlir::TypeAttr::get(builder.getFunctionType(
                                 actualInputs, actualOutputs)))};
    if (scoped)
      attrs.push_back(builder.getNamedAttr("no_inline", builder.getUnitAttr()));
    if (local)
      attrs.push_back(builder.getNamedAttr(
          "logical_origin",
          builder.getArrayAttr({builder.getStringAttr(prefix + suffix.str()),
                                builder.getArrayAttr({})})));
    auto *declaration =
        make(local ? "local.func" : "func.func", {}, {}, attrs, true);
    if (!declaration)
      return false;
    auto &block = declaration->getRegion(0).front();
    for (auto type : actualInputs)
      block.addArgument(type, location);
    builder.setInsertionPointToEnd(&block);
    std::optional<protocol::detail::ScopedExecutionBuilder> control;
    if (scoped)
      control.emplace(builder, mlir::cast<mlir::func::FuncOp>(declaration));
    auto logicalArguments = block.getArguments().drop_front(scoped ? 1 : 0);
    unsigned ordinal = 0;
    auto decoded =
        item(finite.domain->result,
             logicalArguments.slice(states.size(),
                                    itemTypes[finite.domain->result].size()),
             ordinal, control ? &*control : nullptr);
    if (!decoded)
      return false;
    Values operands(logicalArguments.take_front(states.size()));
    llvm::append_range(operands, *decoded);
    unsigned environment =
        states.size() + itemTypes[finite.domain->result].size();
    for (auto port : ports)
      operands.push_back(logicalArguments[environment + port]);
    auto conditions = take(flattenDataPreconditions(helper, layouts));
    if (!conditions)
      return false;
    for (auto &condition : *conditions) {
      if (condition.left >= operands.size() ||
          condition.right >= operands.size()) {
        failure =
            error("source.data-bound", "finite condition exceeds helper ABI");
        return false;
      }
      auto left = mlir::dyn_cast<mlir::BlockArgument>(operands[condition.left]);
      auto right =
          mlir::dyn_cast<mlir::BlockArgument>(operands[condition.right]);
      if (!left || !right || left.getOwner() != &block ||
          right.getOwner() != &block) {
        failure = error("source.data-bound",
                        "finite condition requires direct adapter ports");
        return false;
      }
      condition.left = left.getArgNumber();
      condition.right = right.getArgNumber();
    }
    if (!conditions->empty()) {
      if (local) {
        failure = error("source.data-bound",
                        "Local finite helper cannot assume bounds");
        return false;
      }
      declaration->setAttr(
          "data.preconditions",
          emitDataPreconditions(builder.getContext(), *conditions));
    }
    SmallVector<mlir::NamedAttribute> callAttrs{
        symbol("callee", helper.symbol)};
    if (local)
      callAttrs.push_back(text("site", "body"));
    Values result;
    if (control) {
      callAttrs.push_back(text("runtime.site", "body"));
      result = control->invoke("func.call", *outputs, control->scoped(operands),
                               callAttrs);
    } else {
      auto *call = make(local ? "local.apply" : "func.call", *outputs, operands,
                        callAttrs);
      if (!call)
        return false;
      result = Values(call->getResults());
    }
    if (packed) {
      if (!canInsert(packed->product ? 1 : 0))
        return false;
      if (control && packed->product)
        result = control->invoke(
            "exec.variant", adapterOutputs, control->scoped(result),
            {text("alternative", packed->alternative), text("site", "result")});
      else {
        auto value = take(emitPack(
            builder, location, *packed, result,
            local ? PackingMode::Local : PackingMode::Mathematical, "result"));
        if (!value)
          return false;
        result = {*value};
      }
    }
    if (control) {
      control->returned(result);
      return true;
    }
    return bool(make(local ? "local.return" : "func.return", {}, result));
  }

public:
  FiniteEmitter(const ClosedEntry &project, const Body &source,
                const FiniteComputation &finite, const Type &resultType,
                ArrayRef<Values> values, mlir::OpBuilder &builder,
                mlir::Location location, mlir::Block &definitions,
                Layouts &layouts, StringRef prefix, StringRef site,
                EmissionBudget &budget, uint64_t &remaining,
                protocol::detail::ScopedExecutionBuilder *scoped)
      : project(project), finite(finite), resultType(resultType),
        values(values), builder(builder), location(location),
        definitions(definitions), layouts(layouts), prefix(prefix), site(site),
        budget(budget), remaining(remaining),
        local(source.mode == Body::Mode::Local && !scoped), scoped(scoped) {
    (void)!!failure;
  }
  Expected<Values> run() {
    if (!domainInputs())
      return std::move(failure);
    initial = flatten(finite.operands);
    auto body = capturePorts(finite.body.captures);
    auto predicate = finite.predicate
                         ? capturePorts(finite.predicate->captures)
                         : std::optional<std::vector<unsigned>>({});
    if (!body || (finite.predicate && !predicate))
      return std::move(failure);
    bodyPorts = std::move(*body);
    if (predicate)
      predicatePorts = std::move(*predicate);
    bool fold = finite.kind == FiniteApplication::Kind::Fold;
    if (!descriptor() ||
        !callback(finite.body, bodyPorts, "_body",
                  mlir::ValueRange(initial).getTypes(), !fold) ||
        (finite.predicate &&
         !callback(*finite.predicate, predicatePorts, "_predicate", {}, false)))
      return std::move(failure);
    auto outputs = types(resultType);
    if (!outputs)
      return std::move(failure);
    Values operands = domainOperands;
    llvm::append_range(operands, initial);
    llvm::append_range(operands, captures);
    SmallVector<mlir::NamedAttribute> attrs{
        symbol("domain", prefix + "_domain"),
        symbol(fold ? "step" : "body", prefix + "_body")};
    if (finite.predicate)
      attrs.push_back(symbol("predicate", prefix + "_predicate"));
    if (scoped) {
      attrs.push_back(text("site", site));
      auto result = scoped->invoke(fold ? "exec.fold" : "exec.collect",
                                   *outputs, scoped->scoped(operands), attrs);
      if (!canInsert(0))
        return std::move(failure);
      return result;
    }
    if (local) {
      {
        mlir::OpBuilder::InsertionGuard guard(builder);
        builder.setInsertionPointToEnd(&definitions);
        attrs.push_back(text("sym_name", prefix));
        attrs.push_back(builder.getNamedAttr(
            "function_type",
            mlir::TypeAttr::get(builder.getFunctionType(
                mlir::ValueRange(operands).getTypes(), *outputs))));
        if (!make(fold ? "local.finite_fold" : "local.finite_collect", {}, {},
                  attrs))
          return std::move(failure);
      }
      attrs = {symbol("callee", prefix), text("site", site)};
    }
    auto *result = make(local  ? "local.apply"
                        : fold ? "algebra.finite_fold"
                               : "algebra.finite_collect",
                        *outputs, operands, attrs);
    if (!result)
      return std::move(failure);
    return Values(result->getResults());
  }
};
} // namespace
Expected<SmallVector<mlir::Value>>
emitFinite(const ClosedEntry &project, const Body &source,
           const FiniteComputation &finite, const Type &resultType,
           ArrayRef<SmallVector<mlir::Value>> values, mlir::OpBuilder &builder,
           mlir::Location location, mlir::Block &definitions, Layouts &layouts,
           StringRef prefix, StringRef site, EmissionBudget &budget,
           uint64_t &remaining,
           protocol::detail::ScopedExecutionBuilder *scoped) {
  if (scoped && source.mode != Body::Mode::Local)
    return error("source.emission",
                 "scoped finite emission requires an ordered body");
  return FiniteEmitter(project, source, finite, resultType, values, builder,
                       location, definitions, layouts, prefix, site, budget,
                       remaining, scoped)
      .run();
}
} // namespace zkc::language

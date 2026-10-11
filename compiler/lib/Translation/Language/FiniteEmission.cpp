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
  const Limits &limits;
  uint64_t &operations, &remaining;
  Error failure = Error::success();
  std::vector<Types> itemTypes;
  std::vector<unsigned> bodyPorts, predicatePorts;
  Values domainOperands, captures, initial;
  bool local;
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
  bool count(uint64_t size = 1) {
    if (size > limits.operations - std::min(operations, limits.operations)) {
      failure =
          error("source.limit", "finite translation operation limit exceeded");
      return false;
    }
    operations += size;
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
    if (!count())
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
  bool descriptor() {
    mlir::OpBuilder::InsertionGuard guard(builder);
    builder.setInsertionPointToEnd(&definitions);
    const auto &shape = *finite.domain;
    std::vector<mlir::Value> nodes;
    // Ordinary descriptor inputs are native containers or index values. The
    // structural-array adapter is supplied outside this declaration.
    for (unsigned i = 0; i < shape.inputs.size(); ++i)
      if (values[finite.domainOperands[i].index].size() != 1) {
        failure = error("source.layout",
                        "structural domain input needs its collection adapter");
        return false;
      }
    for (const auto &node : shape.nodes) {
      Types items;
      if (node.kind == DomainBinding::Kind::Zip ||
          node.kind == DomainBinding::Kind::Product) {
        for (auto child : node.children)
          llvm::append_range(items, itemTypes.at(child));
      } else if (node.kind == DomainBinding::Kind::Elements &&
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
  std::optional<Values> item(unsigned index, mlir::ValueRange inputs,
                             unsigned &ordinal) {
    if (!charge(inputs.size() + 1))
      return {};
    const auto &node = finite.domain->nodes[index];
    if (node.kind == DomainBinding::Kind::Zip ||
        node.kind == DomainBinding::Kind::Product) {
      Values result;
      unsigned offset = 0;
      for (auto child : node.children) {
        auto nested =
            item(child, inputs.slice(offset, itemTypes[child].size()), ordinal);
        if (!nested)
          return {};
        llvm::append_range(result, *nested);
        offset += itemTypes[child].size();
      }
      return result;
    }
    if (node.kind == DomainBinding::Kind::Elements &&
        mlir::isa<data::SequenceType>(
            domainOperands[node.operands.front().index].getType())) {
      auto packed = take(layouts.packed(node.item));
      if (!packed ||
          !count(packed->product ? (local ? 2 : packed->flat->leaves.size())
                                 : 0))
        return {};
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
    SmallVector<mlir::NamedAttribute> attrs{
        text("sym_name", prefix + suffix.str()),
        text("sym_visibility", "private"),
        builder.getNamedAttr("function_type",
                             mlir::TypeAttr::get(builder.getFunctionType(
                                 inputs, adapterOutputs)))};
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
    for (auto type : inputs)
      block.addArgument(type, location);
    builder.setInsertionPointToEnd(&block);
    unsigned ordinal = 0;
    auto decoded =
        item(finite.domain->result,
             block.getArguments().slice(
                 states.size(), itemTypes[finite.domain->result].size()),
             ordinal);
    if (!decoded)
      return false;
    Values operands(block.getArguments().take_front(states.size()));
    llvm::append_range(operands, *decoded);
    unsigned environment =
        states.size() + itemTypes[finite.domain->result].size();
    for (auto port : ports)
      operands.push_back(block.getArgument(environment + port));
    SmallVector<mlir::NamedAttribute> callAttrs{
        symbol("callee", helper.symbol)};
    if (local)
      callAttrs.push_back(text("site", "body"));
    auto *call = make(local ? "local.apply" : "func.call", *outputs, operands,
                      callAttrs);
    if (!call)
      return false;
    Values result(call->getResults());
    if (packed) {
      if (!count(packed->product ? 1 : 0))
        return false;
      auto value = take(emitPack(
          builder, location, *packed, result,
          local ? PackingMode::Local : PackingMode::Mathematical, "result"));
      if (!value)
        return false;
      result = {*value};
    }
    return bool(make(local ? "local.return" : "func.return", {}, result));
  }

public:
  FiniteEmitter(const ClosedEntry &project, const Body &source,
                const FiniteComputation &finite, const Type &resultType,
                ArrayRef<Values> values, mlir::OpBuilder &builder,
                mlir::Location location, mlir::Block &definitions,
                Layouts &layouts, StringRef prefix, StringRef site,
                const Limits &limits, uint64_t &operations, uint64_t &remaining)
      : project(project), finite(finite), resultType(resultType),
        values(values), builder(builder), location(location),
        definitions(definitions), layouts(layouts), prefix(prefix), site(site),
        limits(limits), operations(operations), remaining(remaining),
        local(source.mode == Body::Mode::Local) {
    (void)!!failure;
  }
  Expected<Values> run() {
    domainOperands = flatten(finite.domainOperands);
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
           StringRef prefix, StringRef site, const Limits &limits,
           uint64_t &operations, uint64_t &remaining) {
  return FiniteEmitter(project, source, finite, resultType, values, builder,
                       location, definitions, layouts, prefix, site, limits,
                       operations, remaining)
      .run();
}
} // namespace zkc::language

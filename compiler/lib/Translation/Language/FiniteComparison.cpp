#include "Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc::language {
namespace {
using Values = SmallVector<mlir::Value>;
using Types = SmallVector<mlir::Type>;
bool attributes(mlir::Operation &op, ArrayRef<StringRef> names) {
  return op.getAttrs().size() == names.size() &&
         llvm::all_of(names, [&](auto name) { return bool(op.getAttr(name)); });
}
bool text(mlir::Operation &op, StringRef name, StringRef value) {
  auto attr = op.getAttrOfType<mlir::StringAttr>(name);
  return attr && attr.getValue() == value;
}
bool symbol(mlir::Operation &op, StringRef name, StringRef value) {
  auto attr = op.getAttrOfType<mlir::FlatSymbolRefAttr>(name);
  return attr && attr.getValue() == value;
}
class FiniteCheck {
  const ClosedEntry &project;
  const FiniteComputation &finite;
  const Type &resultType;
  ArrayRef<Values> values;
  mlir::Operation &actual;
  const std::map<std::string, mlir::Operation *> &definitions;
  std::set<mlir::Operation *> &used;
  Layouts &layouts;
  std::string prefix;
  StringRef site;
  const Limits &limits;
  uint64_t &operations, &remaining;
  Error failure = Error::success();
  bool local;
  Values data, initial, captures;
  std::vector<unsigned> bodyPorts, predicatePorts;
  std::vector<Types> items;
  mlir::MLIRContext *context;
  bool fail(StringRef message) {
    if (!failure)
      failure = error("source.correspondence", message);
    return false;
  }
  template <class T> std::optional<T> take(Expected<T> result) {
    if (!result) {
      failure = result.takeError();
      return {};
    }
    return std::move(*result);
  }
  bool charge(uint64_t count) {
    if (count > remaining) {
      failure = error("source.limit", "finite comparison work limit exceeded");
      return false;
    }
    remaining -= count;
    return true;
  }
  bool count() {
    if (++operations > limits.operations) {
      failure =
          error("source.limit", "finite comparison operation limit exceeded");
      return false;
    }
    return true;
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
        fail("finite layout contains formal data");
        return {};
      }
      auto bound = take(protocol::parseBoundType(*leaf.data(), false));
      if (!bound)
        return {};
      auto decoded = protocol::decodeBoundType(context, *bound);
      if (!decoded) {
        fail("finite native type unavailable");
        return {};
      }
      result.push_back(decoded);
    }
    return result;
  }
  Values flatten(ArrayRef<ValueId> inputs) {
    Values result;
    for (auto input : inputs)
      llvm::append_range(result, values[input.index]);
    return result;
  }
  bool ports(ArrayRef<ValueId> inputs, std::vector<unsigned> &ports) {
    for (auto value : flatten(inputs)) {
      if (!charge(data.size() + captures.size() + 1))
        return false;
      auto argument = llvm::find(data, value);
      if (argument != data.end())
        ports.push_back(argument - data.begin());
      else {
        auto capture = llvm::find(captures, value);
        if (capture == captures.end()) {
          ports.push_back(data.size() + captures.size());
          captures.push_back(value);
        } else
          ports.push_back(data.size() + (capture - captures.begin()));
      }
    }
    return true;
  }
  mlir::Operation *definition(StringRef suffix, StringRef kind,
                              mlir::TypeRange inputs, mlir::TypeRange outputs,
                              bool region, ArrayRef<StringRef> attrs) {
    auto found = definitions.find(prefix + suffix.str());
    if (found == definitions.end()) {
      fail("missing finite auxiliary definition");
      return nullptr;
    }
    auto *op = found->second;
    auto attr = op->getAttrOfType<mlir::TypeAttr>("function_type");
    auto signature = attr ? mlir::dyn_cast<mlir::FunctionType>(attr.getValue())
                          : mlir::FunctionType();
    if (!count() || !used.insert(op).second ||
        op->getName().getStringRef() != kind || !attributes(*op, attrs) ||
        !signature || mlir::TypeRange(signature.getInputs()) != inputs ||
        mlir::TypeRange(signature.getResults()) != outputs ||
        op->getNumRegions() != unsigned(region) || op->getNumOperands() ||
        op->getNumResults() ||
        (region && (!llvm::hasSingleElement(op->getRegion(0)) ||
                    op->getRegion(0).front().getArgumentTypes() != inputs))) {
      fail("finite definition structure or signature differs");
      return nullptr;
    }
    return op;
  }
  mlir::Operation *next(mlir::Block &block, mlir::Block::iterator &cursor,
                        StringRef kind, mlir::ValueRange operands,
                        mlir::TypeRange outputs, ArrayRef<StringRef> attrs) {
    if (cursor == block.end()) {
      fail("finite auxiliary body omitted an operation");
      return nullptr;
    }
    auto *op = &*cursor++;
    if (!count() || op->getName().getStringRef() != kind ||
        !llvm::equal(op->getOperands(), operands) ||
        op->getResultTypes() != outputs || !attributes(*op, attrs)) {
      fail("finite auxiliary operation differs");
      return nullptr;
    }
    return op;
  }
  bool descriptor() {
    for (auto input : finite.domainOperands)
      if (values[input.index].size() != 1)
        return fail("structural domain input lacks an adapter");
    const auto &shape = *finite.domain;
    for (const auto &node : shape.nodes) {
      Types result;
      if (node.kind == DomainBinding::Kind::Zip ||
          node.kind == DomainBinding::Kind::Product) {
        for (auto child : node.children)
          llvm::append_range(result, items.at(child));
      } else if (node.kind == DomainBinding::Kind::Elements &&
                 mlir::isa<data::SequenceType>(
                     data[node.operands.front().index].getType()))
        result.push_back(mlir::cast<data::SequenceType>(
                             data[node.operands.front().index].getType())
                             .getElementType());
      else {
        auto layout = types(node.item);
        if (!layout)
          return false;
        result = std::move(*layout);
      }
      if (!charge(result.size() + 1))
        return false;
      items.push_back(std::move(result));
    }
    auto *op =
        definition("_domain", "data.domain", mlir::ValueRange(data).getTypes(),
                   {data::DomainType::get(context, items[shape.result])}, true,
                   {"sym_name", "sym_visibility", "function_type"});
    if (!op || !text(*op, "sym_visibility", "private"))
      return fail("domain visibility differs");
    auto &block = op->getRegion(0).front();
    auto cursor = block.begin();
    Values descriptors;
    for (unsigned i = 0; i < shape.nodes.size(); ++i) {
      const auto &node = shape.nodes[i];
      Values operands;
      for (auto input : node.operands)
        operands.push_back(block.getArgument(input.index));
      for (auto child : node.children)
        operands.push_back(descriptors[child]);
      StringRef name;
      SmallVector<StringRef> attrs;
      switch (node.kind) {
      case DomainBinding::Kind::Elements:
        name = "data.domain_elements";
        break;
      case DomainBinding::Kind::Indices:
        name = "data.domain_indices";
        attrs.push_back("axis");
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
        attrs.push_back("order");
        break;
      default:
        return fail("untranslated source domain constructor");
      }
      auto *actual = next(block, cursor, name, operands,
                          {data::DomainType::get(context, items[i])}, attrs);
      if (!actual || actual->getNumRegions())
        return fail("domain constructor structure differs");
      if (node.kind == DomainBinding::Kind::Indices) {
        auto axis = actual->getAttrOfType<mlir::IntegerAttr>("axis");
        if (!axis || !axis.getType().isInteger(64) ||
            axis.getInt() != node.axis)
          return fail("domain axis differs");
      }
      if (node.kind == DomainBinding::Kind::MatrixCoordinates &&
          !text(*actual, "order", node.axis ? "column_major" : "row_major"))
        return fail("matrix enumeration order differs");
      descriptors.push_back(actual->getResult(0));
    }
    auto *yield = next(block, cursor, "data.domain_yield",
                       descriptors[shape.result], {}, {});
    return yield && !yield->getNumRegions() &&
           (cursor == block.end() || fail("extra domain constructor"));
  }
  std::optional<Values> unpack(unsigned index, mlir::ValueRange arguments,
                               mlir::Block &block,
                               mlir::Block::iterator &cursor,
                               unsigned &ordinal) {
    if (!charge(arguments.size() + 1))
      return {};
    const auto &node = finite.domain->nodes[index];
    if (node.kind == DomainBinding::Kind::Zip ||
        node.kind == DomainBinding::Kind::Product) {
      Values result;
      unsigned offset = 0;
      for (auto child : node.children) {
        auto decoded =
            unpack(child, arguments.slice(offset, items[child].size()), block,
                   cursor, ordinal);
        if (!decoded)
          return {};
        llvm::append_range(result, *decoded);
        offset += items[child].size();
      }
      return result;
    }
    if (node.kind != DomainBinding::Kind::Elements ||
        !mlir::isa<data::SequenceType>(
            data[node.operands.front().index].getType()))
      return Values(arguments);
    auto packed = take(layouts.packed(node.item));
    auto itemSite = "item_" + std::to_string(ordinal++);
    auto flat = types(node.item);
    if (!packed || !flat)
      return {};
    if (!packed->product)
      return Values(arguments);
    if (!local) {
      Values result;
      for (unsigned i = 0; i < flat->size(); ++i) {
        auto *get =
            next(block, cursor, "data.get", arguments, {(*flat)[i]}, {"index"});
        auto index = get ? get->getAttrOfType<mlir::IntegerAttr>("index")
                         : mlir::IntegerAttr();
        if (!get || get->getNumRegions() || !index ||
            !index.getType().isInteger(64) || index.getInt() != i) {
          fail("finite item projection differs");
          return {};
        }
        result.push_back(get->getResult(0));
      }
      return result;
    }
    auto *match = next(block, cursor, "local.match", arguments, *flat,
                       {"site", "alternatives"});
    auto labels = match ? match->getAttrOfType<mlir::ArrayAttr>("alternatives")
                        : mlir::ArrayAttr();
    if (!match || !text(*match, "site", itemSite) ||
        match->getNumRegions() != 1 ||
        !llvm::hasSingleElement(match->getRegion(0)) || !labels ||
        labels.size() != 1 || !mlir::isa<mlir::StringAttr>(labels[0]) ||
        mlir::cast<mlir::StringAttr>(labels[0]).getValue() !=
            packed->alternative) {
      fail("finite item unpack differs");
      return {};
    }
    auto &arm = match->getRegion(0).front();
    auto position = arm.begin();
    if (arm.getArgumentTypes() != mlir::TypeRange(*flat)) {
      fail("finite item payload differs");
      return {};
    }
    auto *yield =
        next(arm, position, "local.yield", arm.getArguments(), {}, {});
    if (!yield || yield->getNumRegions() || position != arm.end()) {
      fail("finite item unpack yield differs");
      return {};
    }
    return Values(match->getResults());
  }
  bool callback(const FiniteCallback &selected, ArrayRef<unsigned> ports,
                StringRef suffix, mlir::TypeRange stateTypes, bool collect) {
    const auto &helper = project.declarations()[selected.helper.index];
    Types inputs(stateTypes.begin(), stateTypes.end());
    llvm::append_range(inputs, items[finite.domain->result]);
    llvm::append_range(inputs, mlir::ValueRange(data).getTypes());
    llvm::append_range(inputs, mlir::ValueRange(captures).getTypes());
    auto outputs = types(helper.outputs.front().type);
    if (!outputs)
      return false;
    Types adapterOutputs = *outputs;
    std::optional<PackedLayout> packed;
    if (collect && resultType.domain == "sequence") {
      packed = take(layouts.packed(helper.outputs.front().type));
      if (!packed)
        return false;
      adapterOutputs = {protocol::decodeBoundType(context, packed->carrier)};
    }
    SmallVector<StringRef> attrs{"sym_name", "sym_visibility", "function_type"};
    if (local)
      attrs.push_back("logical_origin");
    auto *op = definition(suffix, local ? "local.func" : "func.func", inputs,
                          adapterOutputs, true, attrs);
    if (!op || !text(*op, "sym_visibility", "private"))
      return fail("finite callback visibility differs");
    if (local) {
      auto origin = op->getAttrOfType<mlir::ArrayAttr>("logical_origin");
      if (!origin || origin.size() != 2 ||
          !mlir::isa<mlir::StringAttr>(origin[0]) ||
          mlir::cast<mlir::StringAttr>(origin[0]).getValue() !=
              prefix + suffix.str() ||
          !mlir::isa<mlir::ArrayAttr>(origin[1]) ||
          !mlir::cast<mlir::ArrayAttr>(origin[1]).empty())
        return fail("finite callback origin differs");
    }
    auto &block = op->getRegion(0).front();
    auto cursor = block.begin();
    unsigned ordinal = 0;
    auto item =
        unpack(finite.domain->result,
               block.getArguments().slice(stateTypes.size(),
                                          items[finite.domain->result].size()),
               block, cursor, ordinal);
    if (!item)
      return false;
    Values operands(block.getArguments().take_front(stateTypes.size()));
    llvm::append_range(operands, *item);
    unsigned start = stateTypes.size() + items[finite.domain->result].size();
    for (auto port : ports)
      operands.push_back(block.getArgument(start + port));
    SmallVector<StringRef> callAttrs{"callee"};
    if (local)
      callAttrs.push_back("site");
    auto *call = next(block, cursor, local ? "local.apply" : "func.call",
                      operands, *outputs, callAttrs);
    if (!call || call->getNumRegions() ||
        !symbol(*call, "callee", helper.symbol) ||
        (local && !text(*call, "site", "body")))
      return fail("finite callback target differs");
    Values result(call->getResults());
    if (packed && packed->product) {
      SmallVector<StringRef> packAttrs{"alternative"};
      if (local)
        packAttrs.push_back("site");
      auto *pack =
          next(block, cursor, local ? "local.variant_inject" : "data.make",
               result, adapterOutputs, packAttrs);
      if (!pack || pack->getNumRegions() ||
          !text(*pack, "alternative", packed->alternative) ||
          (local && !text(*pack, "site", "result")))
        return fail("finite collection packing differs");
      result = Values(pack->getResults());
    }
    auto *ret = next(block, cursor, local ? "local.return" : "func.return",
                     result, {}, {});
    return ret && !ret->getNumRegions() &&
           (cursor == block.end() || fail("extra finite callback work"));
  }

public:
  FiniteCheck(const ClosedEntry &project, const Body &source,
              const FiniteComputation &finite, const Type &resultType,
              ArrayRef<Values> values, mlir::Operation &actual,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &layouts,
              StringRef prefix, StringRef site, const Limits &limits,
              uint64_t &operations, uint64_t &remaining)
      : project(project), finite(finite), resultType(resultType),
        values(values), actual(actual), definitions(definitions), used(used),
        layouts(layouts), prefix(prefix), site(site), limits(limits),
        operations(operations), remaining(remaining),
        local(source.mode == Body::Mode::Local), context(actual.getContext()) {
    (void)!!failure;
  }
  Expected<Values> run() {
    data = flatten(finite.domainOperands);
    initial = flatten(finite.operands);
    if (!ports(finite.body.captures, bodyPorts) ||
        (finite.predicate &&
         !ports(finite.predicate->captures, predicatePorts)))
      return std::move(failure);
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
    Values operands = data;
    llvm::append_range(operands, initial);
    llvm::append_range(operands, captures);
    SmallVector<StringRef> attrs{"domain", fold ? "step" : "body"};
    if (finite.predicate)
      attrs.push_back("predicate");
    mlir::Operation *contract = &actual;
    if (local) {
      attrs.append({"sym_name", "function_type"});
      contract = definition(
          "", fold ? "local.finite_fold" : "local.finite_collect",
          mlir::ValueRange(operands).getTypes(), *outputs, false, attrs);
    }
    if (!contract || !symbol(*contract, "domain", prefix + "_domain") ||
        !symbol(*contract, fold ? "step" : "body", prefix + "_body") ||
        (finite.predicate &&
         !symbol(*contract, "predicate", prefix + "_predicate"))) {
      fail("finite selected domain or callback differs");
      return std::move(failure);
    }
    if (local)
      attrs = {"callee", "site"};
    if (!count() ||
        actual.getName().getStringRef() != (local ? "local.apply"
                                            : fold
                                                ? "algebra.finite_fold"
                                                : "algebra.finite_collect") ||
        !attributes(actual, attrs) || actual.getNumRegions() ||
        !llvm::equal(actual.getOperands(), operands) ||
        actual.getResultTypes() != mlir::TypeRange(*outputs) ||
        (local &&
         (!symbol(actual, "callee", prefix) || !text(actual, "site", site)))) {
      fail("finite computation occurrence differs");
      return std::move(failure);
    }
    return Values(actual.getResults());
  }
};
} // namespace
Expected<SmallVector<mlir::Value>>
compareFinite(const ClosedEntry &project, const Body &source,
              const FiniteComputation &finite, const Type &resultType,
              ArrayRef<SmallVector<mlir::Value>> values,
              mlir::Operation &actual,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &layouts,
              StringRef prefix, StringRef site, const Limits &limits,
              uint64_t &operations, uint64_t &remaining) {
  return FiniteCheck(project, source, finite, resultType, values, actual,
                     definitions, used, layouts, prefix, site, limits,
                     operations, remaining)
      .run();
}
} // namespace zkc::language

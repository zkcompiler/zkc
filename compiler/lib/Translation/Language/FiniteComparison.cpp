#include "DataPreconditions.h"
#include "Finite.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Exec/ControlCursor.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include <limits>
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
  mlir::Block &sourceBlock;
  mlir::Block::iterator &sourceCursor;
  const std::map<std::string, mlir::Operation *> &definitions;
  std::set<mlir::Operation *> &used;
  Layouts &layouts;
  std::string prefix;
  StringRef site;
  const Limits &limits;
  uint64_t &operations, &remaining;
  Error failure = Error::success();
  bool local;
  exec::ControlCursor *scoped;
  exec::ControlCursor *reading = nullptr;
  Values data, initial, captures;
  std::vector<unsigned> bodyPorts, predicatePorts;
  std::vector<Types> items;
  mlir::MLIRContext *context;
  bool fail(StringRef message) {
    if (!failure) {
      auto *cursor = reading ? reading : scoped;
      failure =
          cursor && cursor->exhausted()
              ? error("source.limit", "finite CFG comparison limit exceeded")
              : error("source.correspondence", message);
    }
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
  bool account(unsigned consumed) {
    if (consumed > remaining || operations > limits.operations ||
        consumed > limits.operations - operations) {
      failure = error("source.limit", "finite CFG comparison limit exceeded");
      return false;
    }
    remaining -= consumed;
    operations += consumed;
    return true;
  }
  unsigned allowance() const {
    return unsigned(std::min<uint64_t>(
        std::numeric_limits<unsigned>::max(),
        std::min(remaining,
                 limits.operations - std::min(operations, limits.operations))));
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
                              bool region, ArrayRef<StringRef> attrs,
                              bool cfg = false) {
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
        (region && ((cfg ? op->getRegion(0).empty()
                         : !llvm::hasSingleElement(op->getRegion(0))) ||
                    op->getRegion(0).front().getArgumentTypes() != inputs))) {
      fail("finite definition structure or signature differs");
      return nullptr;
    }
    return op;
  }
  mlir::Operation *next(exec::ControlCursor &control, StringRef kind,
                        mlir::ValueRange operands, mlir::TypeRange outputs,
                        ArrayRef<StringRef> attrs) {
    auto *op = control.take();
    if (!op || op->getName().getStringRef() != kind ||
        !llvm::equal(op->getOperands(), operands) ||
        op->getResultTypes() != outputs || op->getNumRegions() ||
        op->getNumSuccessors() || !attributes(*op, attrs)) {
      fail("finite scoped auxiliary operation differs");
      return nullptr;
    }
    return op;
  }
  std::optional<Values> invoke(exec::ControlCursor &control, StringRef kind,
                               mlir::ValueRange inputs, mlir::TypeRange outputs,
                               ArrayRef<StringRef> attrs,
                               mlir::Operation *&operation) {
    Values actual{control.getScope()};
    llvm::append_range(actual, inputs);
    auto outcome = exec::OutcomeType::get(context, Types(outputs));
    operation = next(control, kind, actual, {outcome}, attrs);
    Values result;
    if (!operation || !control.dispatch(operation->getResult(0), result) ||
        mlir::ValueRange(result).getTypes() != outputs) {
      fail("finite scoped dispatch differs");
      return {};
    }
    return result;
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
        op->getResultTypes() != outputs || op->getNumSuccessors() ||
        !attributes(*op, attrs)) {
      fail("finite auxiliary operation differs");
      return nullptr;
    }
    return op;
  }
  bool domainInputs() {
    for (unsigned i = 0; i < finite.domainOperands.size(); ++i) {
      const auto &source = finite.domain->inputs[i];
      const auto &input = values[finite.domainOperands[i].index];
      if (source.kind != Type::Kind::Array) {
        if (input.size() != 1)
          return fail("finite domain input carrier differs");
        data.push_back(input.front());
        continue;
      }
      auto packed = take(layouts.packed(source.arguments.front()));
      if (!packed)
        return false;
      auto element = protocol::decodeBoundType(context, packed->carrier);
      if (!element)
        return fail("array element dialect unavailable");
      auto size = source.dimension.closedValue();
      auto width = packed->flat->leaves.size();
      if ((width && size > input.size() / width) ||
          size * width != input.size())
        return fail("array flattened extent differs");
      auto sequence = data::SequenceType::get(context, element);
      auto suffix = "_array_" + std::to_string(i);
      auto *helper = definition(
          suffix, "func.func", mlir::ValueRange(input).getTypes(), {sequence},
          true, {"sym_name", "sym_visibility", "function_type"});
      if (!helper || !text(*helper, "sym_visibility", "private"))
        return fail("array adapter visibility differs");
      auto &block = helper->getRegion(0).front();
      auto cursor = block.begin();
      auto *empty =
          next(block, cursor, "data.sequence_empty", {}, {sequence}, {});
      if (!empty || empty->getNumRegions())
        return fail("array adapter initial sequence differs");
      mlir::Value result = empty->getResult(0);
      if (!charge(size + input.size()))
        return false;
      for (uint64_t j = 0; j < size; ++j) {
        auto leaves = block.getArguments().slice(j * width, width);
        mlir::Value item;
        if (packed->product) {
          auto *pack = next(block, cursor, "data.make", leaves, {element},
                            {"alternative"});
          if (!pack || pack->getNumRegions() ||
              !text(*pack, "alternative", packed->alternative))
            return fail("array element packing differs");
          item = pack->getResult(0);
        } else {
          if (leaves.size() != 1)
            return fail("array scalar element layout differs");
          item = leaves.front();
        }
        auto *append = next(block, cursor, "data.sequence_append",
                            {result, item}, {sequence}, {});
        if (!append || append->getNumRegions())
          return fail("array element order differs");
        result = append->getResult(0);
      }
      auto *ret = next(block, cursor, "func.return", result, {}, {});
      if (!ret || ret->getNumRegions() || cursor != block.end())
        return fail("array adapter result or work differs");
      if (local) {
        auto *realize =
            definition(suffix + "_realize", "local.realize",
                       mlir::ValueRange(input).getTypes(), {sequence}, false,
                       {"sym_name", "helper", "function_type"});
        if (!realize || !symbol(*realize, "helper", prefix + suffix))
          return fail("array adapter realization differs");
      }
      if (scoped) {
        mlir::Operation *call = nullptr;
        auto result = invoke(*scoped, "exec.compute", input, {sequence},
                             {"callee", "site"}, call);
        if (!result || !symbol(*call, "callee", prefix + suffix) ||
            !text(*call, "site", site.str() + suffix))
          return fail("scoped array adapter occurrence differs");
        data.push_back(result->front());
        continue;
      }
      SmallVector<StringRef> attrs{"callee"};
      if (local)
        attrs.push_back("site");
      auto *call =
          next(sourceBlock, sourceCursor, local ? "local.apply" : "func.call",
               input, {sequence}, attrs);
      if (!call || call->getNumRegions() ||
          !symbol(*call, "callee",
                  prefix + suffix + (local ? "_realize" : "")) ||
          (local && !text(*call, "site", site.str() + suffix)))
        return fail("array adapter occurrence differs");
      data.push_back(call->getResult(0));
    }
    return true;
  }
  bool descriptor() {
    const auto &shape = *finite.domain;
    for (const auto &node : shape.nodes) {
      Types result;
      if (node.kind == DomainBinding::Kind::Zip ||
          node.kind == DomainBinding::Kind::Product) {
        for (auto child : node.children)
          llvm::append_range(result, items.at(child));
      } else if ((node.kind == DomainBinding::Kind::Elements ||
                  node.kind == DomainBinding::Kind::SourceArray) &&
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
      case DomainBinding::Kind::SourceArray:
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
                               mlir::Block::iterator &cursor, unsigned &ordinal,
                               exec::ControlCursor *control,
                               StringRef adapter) {
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
                   cursor, ordinal, control, adapter);
        if (!decoded)
          return {};
        llvm::append_range(result, *decoded);
        offset += items[child].size();
      }
      return result;
    }
    if ((node.kind != DomainBinding::Kind::Elements &&
         node.kind != DomainBinding::Kind::SourceArray) ||
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
    if (control) {
      Values result;
      bool valid = control->match(
          arguments.front(), {}, {packed->alternative}, itemSite,
          [&](mlir::func::CallOp call, unsigned arm) {
            Types inputs{runtime::ScopeType::get(context)};
            llvm::append_range(inputs, *flat);
            auto outcome = exec::OutcomeType::get(context, *flat);
            auto suffix = adapter.str() + "_" + itemSite;
            auto *helper =
                definition(suffix, "func.func", inputs, {outcome}, true,
                           {"sym_name", "sym_visibility", "function_type",
                            "no_inline", "runtime.region"});
            if (!helper || arm || !text(*helper, "sym_visibility", "private") ||
                !helper->getAttrOfType<mlir::UnitAttr>("no_inline") ||
                !helper->getAttrOfType<mlir::UnitAttr>("runtime.region") ||
                call.getCallee() != prefix + suffix ||
                call.getOperandTypes() != mlir::TypeRange(inputs) ||
                call.getResultTypes() != mlir::TypeRange{outcome})
              return false;
            auto &body = helper->getRegion(0).front();
            auto position = body.begin();
            auto *complete = next(body, position, "exec.complete",
                                  body.getArguments(), {outcome}, {});
            auto *ret = complete ? next(body, position, "func.return",
                                        complete->getResults(), {}, {})
                                 : nullptr;
            return complete && !complete->getNumRegions() && ret &&
                   !ret->getNumRegions() && position == body.end();
          },
          result);
      if (!valid ||
          mlir::ValueRange(result).getTypes() != mlir::TypeRange(*flat)) {
        fail("finite scoped item unpack or transfer differs");
        return {};
      }
      return result;
    }
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
    if (!helper.dataPreconditions.empty())
      attrs.push_back("data.preconditions");
    Types actualInputs = inputs, actualOutputs = adapterOutputs;
    if (scoped) {
      attrs.push_back("no_inline");
      actualInputs.insert(actualInputs.begin(),
                          runtime::ScopeType::get(context));
      actualOutputs = {exec::OutcomeType::get(context, adapterOutputs)};
    }
    auto *op =
        definition(suffix, local ? "local.func" : "func.func", actualInputs,
                   actualOutputs, true, attrs, bool(scoped));
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
    unsigned available = allowance();
    std::optional<exec::ControlCursor> control;
    auto *previous = reading;
    llvm::scope_exit restore([&] { reading = previous; });
    if (scoped) {
      if (!op->getAttrOfType<mlir::UnitAttr>("no_inline"))
        return fail("finite scoped callback may not inline");
      control.emplace(mlir::cast<mlir::func::FuncOp>(op), available);
      reading = &*control;
      if (!control->enter(&block))
        return fail("finite scoped callback entry differs");
    }
    auto logicalArguments = block.getArguments().drop_front(scoped ? 1 : 0);
    unsigned ordinal = 0;
    auto item =
        unpack(finite.domain->result,
               logicalArguments.slice(stateTypes.size(),
                                      items[finite.domain->result].size()),
               block, cursor, ordinal, control ? &*control : nullptr, suffix);
    if (!item)
      return false;
    Values operands(logicalArguments.take_front(stateTypes.size()));
    llvm::append_range(operands, *item);
    unsigned start = stateTypes.size() + items[finite.domain->result].size();
    for (auto port : ports)
      operands.push_back(logicalArguments[start + port]);
    auto conditions = take(flattenDataPreconditions(helper, layouts));
    if (!conditions)
      return false;
    for (auto &condition : *conditions) {
      if (condition.left >= operands.size() ||
          condition.right >= operands.size())
        return fail("finite condition exceeds callback inputs");
      auto left = mlir::dyn_cast<mlir::BlockArgument>(operands[condition.left]);
      auto right =
          mlir::dyn_cast<mlir::BlockArgument>(operands[condition.right]);
      if (!left || !right || left.getOwner() != &block ||
          right.getOwner() != &block)
        return fail("finite condition is not an adapter input");
      condition.left = left.getArgNumber();
      condition.right = right.getArgNumber();
    }
    if ((local && !conditions->empty()) ||
        !compareDataPreconditions(*op, *conditions))
      return fail("finite adapter data preconditions differ");
    if (control) {
      mlir::Operation *call = nullptr;
      auto result = invoke(*control, "func.call", operands, *outputs,
                           {"callee", "runtime.site"}, call);
      if (!result || !symbol(*call, "callee", helper.symbol) ||
          !text(*call, "runtime.site", "body"))
        return fail("finite scoped callback target differs");
      if (packed && packed->product) {
        mlir::Operation *pack = nullptr;
        result = invoke(*control, "exec.variant", *result, adapterOutputs,
                        {"alternative", "site"}, pack);
        if (!result || !text(*pack, "alternative", packed->alternative) ||
            !text(*pack, "site", "result"))
          return fail("finite scoped collection packing differs");
      }
      auto *returned =
          next(*control, "exec.returned", *result, actualOutputs, {});
      auto *ret = returned ? next(*control, "func.return",
                                  returned->getResults(), {}, {})
                           : nullptr;
      return ((ret && control->complete()) ||
              fail("finite helper return or extra CFG differs")) &&
             account(control->consumed());
    }
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
              ArrayRef<Values> values, mlir::Block &sourceBlock,
              mlir::Block::iterator &sourceCursor,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &layouts,
              StringRef prefix, StringRef site, const Limits &limits,
              uint64_t &operations, uint64_t &remaining,
              exec::ControlCursor *scoped)
      : project(project), finite(finite), resultType(resultType),
        values(values), sourceBlock(sourceBlock), sourceCursor(sourceCursor),
        definitions(definitions), used(used), layouts(layouts), prefix(prefix),
        site(site), limits(limits), operations(operations),
        remaining(remaining),
        local(source.mode == Body::Mode::Local && !scoped), scoped(scoped),
        context(sourceBlock.getParentOp()->getContext()) {
    (void)!!failure;
  }
  Expected<Values> run() {
    unsigned start = scoped ? scoped->consumed() : 0;
    if (!domainInputs())
      return std::move(failure);
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
    if (scoped) {
      attrs.push_back("site");
      mlir::Operation *op = nullptr;
      auto result = invoke(*scoped, fold ? "exec.fold" : "exec.collect",
                           operands, *outputs, attrs, op);
      if (!result || !symbol(*op, "domain", prefix + "_domain") ||
          !symbol(*op, fold ? "step" : "body", prefix + "_body") ||
          (finite.predicate &&
           !symbol(*op, "predicate", prefix + "_predicate")) ||
          !text(*op, "site", site)) {
        fail("finite scoped occurrence differs");
        return std::move(failure);
      }
      if (!account(scoped->consumed() - start))
        return std::move(failure);
      return *result;
    }
    if (sourceCursor == sourceBlock.end()) {
      fail("omitted finite computation");
      return std::move(failure);
    }
    auto &actual = *sourceCursor++;
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
              ArrayRef<SmallVector<mlir::Value>> values, mlir::Block &block,
              mlir::Block::iterator &cursor,
              const std::map<std::string, mlir::Operation *> &definitions,
              std::set<mlir::Operation *> &used, Layouts &layouts,
              StringRef prefix, StringRef site, const Limits &limits,
              uint64_t &operations, uint64_t &remaining,
              exec::ControlCursor *scoped) {
  if (scoped && source.mode != Body::Mode::Local)
    return error("source.correspondence",
                 "scoped finite comparison requires an ordered body");
  return FiniteCheck(project, source, finite, resultType, values, block, cursor,
                     definitions, used, layouts, prefix, site, limits,
                     operations, remaining, scoped)
      .run();
}
} // namespace zkc::language

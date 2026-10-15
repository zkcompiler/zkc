#include "zkc/Compiler/StructuredSource.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;

namespace zkc::protocol {
namespace {
constexpr unsigned signatureLimit = 512;
constexpr unsigned instructionLimit = 4096;
constexpr unsigned depthLimit = 64;

Error attributes(Operation &op, ArrayRef<StringRef> allowed) {
  for (NamedAttribute attr : op.getAttrs()) {
    if (!llvm::is_contained(allowed, attr.getName().getValue()))
      return error("structured-source-attribute", attr.getName().getValue());
    bool valid = true, bounded = true;
    attr.getValue().walk([&](StringAttr string) {
      valid &= json::isUTF8(string.getValue());
      bounded &= string.getValue().size() <= 512;
    });
    // MLIR strings can contain arbitrary bytes. LLVM's JSON constructor
    // asserts or repairs invalid UTF-8; neither is a faithful source export.
    if (!valid)
      return error("structured-source-string");
    if (!bounded)
      return error("structured-source-limit");
  }
  return Error::success();
}

Expected<json::Value> sort(Type type) {
  if (type.isSignlessInteger(1))
    return json::Array{"bool"};
  if (type.isUnsignedInteger(64))
    return json::Array{"index"};
  if (auto field = dyn_cast<algebra::FieldType>(type)) {
    if (field.getDomain() == "bls12-381.fr")
      return json::Array{"field", field.getDomain()};
  }
  if (auto vector = dyn_cast<algebra::FieldVectorType>(type)) {
    if (vector.getDomain() == "bls12-381.fr")
      return json::Array{"vector", vector.getDomain()};
  }
  return error("structured-source-type");
}

Expected<json::Array> sorts(TypeRange types) {
  if (types.size() > signatureLimit)
    return error("structured-source-limit");
  json::Array result;
  for (Type type : types) {
    auto encoded = sort(type);
    if (!encoded)
      return encoded.takeError();
    result.push_back(std::move(*encoded));
  }
  return result;
}

// Count lexical JSON arrays, rather than only native region nesting. A native
// region contributes several wire arrays. Strings are checked as UTF-8 bytes.
bool boundedWire(const json::Value &value, unsigned depth = 0) {
  if (auto string = value.getAsString())
    return string->size() <= 512;
  if (auto array = value.getAsArray()) {
    if (++depth > depthLimit)
      return false;
    return llvm::all_of(*array, [&](const json::Value &child) {
      return boundedWire(child, depth);
    });
  }
  return true;
}

FunctionType signature(Operation &op) {
  auto attr = op.getAttrOfType<TypeAttr>("function_type");
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
}

StringRef kind(Operation &op) {
  if (isa<protocol_ir::MathematicalOp>(op))
    return "protocol";
  if (isa<func::FuncOp>(op))
    return "math";
  if (isa<local::FuncOp>(op))
    return "local";
  if (isa<local::FiniteFoldOp>(op))
    return "finite";
  if (isa<data::DomainOp>(op))
    return "domain";
  return "";
}

Expected<StringRef> visibility(Operation &op) {
  auto attr = op.getAttrOfType<StringAttr>("sym_visibility");
  if (!attr)
    return StringRef("public");
  if (attr.getValue() != "public" && attr.getValue() != "private")
    return error("structured-source-visibility");
  return attr.getValue();
}

class Exporter {
  protocol_ir::ProtocolModuleOp unit;
  protocol_ir::MathematicalOp selected;
  SymbolTable symbols;
  StringRef role;
  Operation *definition = nullptr;
  llvm::StringSet<> sites;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> dependencies;
  unsigned instructions = 0;

  Expected<StringRef> reference(Operation &op, StringRef attribute,
                                ArrayRef<StringRef> allowedKinds,
                                bool optional = false) {
    if (optional && !op.hasAttr(attribute))
      return StringRef("");
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>(attribute);
    Operation *callee = ref ? symbols.lookup(ref.getValue()) : nullptr;
    if (!callee || callee == selected.getOperation() ||
        !llvm::is_contained(allowedKinds, kind(*callee)))
      return error("structured-source-reference");
    dependencies[definition].push_back(callee);
    return ref.getValue();
  }

  Expected<StringRef> site(Operation &op) {
    auto attr = op.getAttrOfType<StringAttr>("site");
    if (!attr || attr.getValue().empty() ||
        !sites.insert(attr.getValue()).second)
      return error("structured-source-site");
    return attr.getValue();
  }

  Error scopes(protocol_ir::MathematicalOp function) {
    auto oneRole = [&](ArrayAttr values) {
      return values.size() == 1 &&
             values[0] == StringAttr::get(unit.getContext(), role);
    };
    if (!oneRole(function.getRoles()))
      return error("structured-source-role");
    for (ArrayAttr scopes :
         {function.getInputRoles(), function.getOutputRoles()})
      for (Attribute scope : scopes)
        if (!oneRole(cast<ArrayAttr>(scope)))
          return error("structured-source-role");
    return Error::success();
  }

  Expected<json::Array> fold(Operation &op) {
    auto domain = reference(op, "domain", {"domain"});
    if (!domain)
      return domain.takeError();
    StringRef helperKind = isa<local::FiniteFoldOp>(op) ? "local" : "math";
    auto step = reference(op, "step", {helperKind});
    if (!step)
      return step.takeError();
    auto predicate = reference(op, "predicate", {helperKind}, true);
    if (!predicate)
      return predicate.takeError();
    return json::Array{*domain, *step, *predicate};
  }

  Expected<json::Value> descriptor(Operation &op, StringRef owner) {
    // Each branch checks exactly the attributes represented by its descriptor.
    // Inherent attributes and discardable attributes share this whitelist.
    auto field = [&]() {
      return cast<algebra::FieldType>(op.getOperand(0).getType()).getDomain();
    };
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      return json::Array{
          "field.constant",
          cast<algebra::FieldType>(constant.getResult().getType()).getDomain(),
          constant.getValue()};
    }
    StringRef fieldOpcode;
    if (isa<algebra::FieldAddOp>(op))
      fieldOpcode = "field.add";
    else if (isa<algebra::SubtractFieldOp>(op))
      fieldOpcode = "field.subtract";
    else if (isa<algebra::FieldMultiplyOp>(op))
      fieldOpcode = "field.multiply";
    else if (isa<algebra::FieldEqualOp>(op))
      fieldOpcode = "field.equal";
    if (!fieldOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      return json::Array{fieldOpcode, field()};
    }
    if (auto constant = dyn_cast<arith::ConstantOp>(op)) {
      if (auto e = attributes(op, {"value"}))
        return std::move(e);
      if (!constant.getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{"bool.constant",
                         cast<IntegerAttr>(constant.getValue()).getInt() != 0};
    }
    if (auto constant = dyn_cast<local::BoolConstantOp>(op)) {
      if (auto e = attributes(op, {"value", "site"}))
        return std::move(e);
      return json::Array{"bool.constant", constant.getValue()};
    }
    StringRef boolOpcode;
    if (isa<arith::AndIOp>(op))
      boolOpcode = "bool.and";
    else if (isa<arith::OrIOp>(op))
      boolOpcode = "bool.or";
    else if (isa<arith::XOrIOp>(op))
      boolOpcode = "bool.xor";
    if (!boolOpcode.empty()) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      if (!op.getResult(0).getType().isSignlessInteger(1))
        return error("structured-source-operation");
      return json::Array{boolOpcode};
    }
    if (auto compare = dyn_cast<arith::CmpIOp>(op)) {
      if (auto e = attributes(op, {"predicate"}))
        return std::move(e);
      if (!compare.getLhs().getType().isSignlessInteger(1) ||
          (compare.getPredicate() != arith::CmpIPredicate::eq &&
           compare.getPredicate() != arith::CmpIPredicate::ne))
        return error("structured-source-operation");
      return json::Array{compare.getPredicate() == arith::CmpIPredicate::eq
                             ? "bool.equal"
                             : "bool.not_equal"};
    }
    if (isa<arith::SelectOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto type = sort(op.getResult(0).getType());
      if (!type)
        return type.takeError();
      return json::Array{"select", std::move(*type)};
    }
    if (isa<data::BoundedAtOp>(op)) {
      if (auto e = attributes(op, {}))
        return std::move(e);
      auto vector =
          dyn_cast<algebra::FieldVectorType>(op.getOperand(0).getType());
      if (!vector)
        return error("structured-source-type");
      return json::Array{"bounded_at", vector.getDomain()};
    }
    if (isa<func::CallOp, local::ApplyOp, protocol_ir::LocalCallOp>(op)) {
      bool math = isa<func::CallOp>(op);
      bool participant = isa<protocol_ir::LocalCallOp>(op);
      if (auto e = attributes(
              op, math          ? ArrayRef<StringRef>{"callee"}
                  : participant ? ArrayRef<StringRef>{"callee", "site", "role"}
                                : ArrayRef<StringRef>{"callee", "site"}))
        return std::move(e);
      auto callee = reference(op, "callee",
                              math ? ArrayRef<StringRef>{"math"}
                                   : ArrayRef<StringRef>{"local", "finite"});
      if (!callee)
        return callee.takeError();
      auto *target = symbols.lookup(*callee);
      auto type = signature(*target);
      if (!type || op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults() ||
          (owner == "math" && !math))
        return error("structured-source-reference");
      if (participant) {
        auto ownerRole = op.getAttrOfType<StringAttr>("role");
        if (!ownerRole || ownerRole.getValue() != role)
          return error("structured-source-role");
        return json::Array{"local_call", *callee, ownerRole.getValue()};
      }
      return json::Array{math ? "call" : "apply", *callee};
    }
    if (isa<algebra::FiniteFoldOp>(op)) {
      if (auto e = attributes(op, {"domain", "step", "predicate"}))
        return std::move(e);
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{"fold", std::move((*refs)[0]), std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    if (isa<protocol_ir::GuardOp>(op)) {
      if (auto e = attributes(op, {"site", "owner"}))
        return std::move(e);
      auto guardOwner = op.getAttrOfType<StringAttr>("owner");
      if (owner != "protocol" || !guardOwner || guardOwner.getValue() != role)
        return error("structured-source-role");
      return json::Array{"guard", guardOwner.getValue()};
    }
    if (isa<local::LocalIfOp, local::LocalForOp>(op)) {
      if (auto e = attributes(op, {"site"}))
        return std::move(e);
      if (owner != "local")
        return error("structured-source-operation");
      if (isa<local::LocalIfOp>(op))
        return json::Array{"if"};
      return json::Array{
          isa<local::LocalConditionOp>(op.getRegion(0).front().back())
              ? "for_condition"
              : "for"};
    }
    return error("structured-source-operation", op.getName().getStringRef());
  }

  // A fresh context for every closed block is essential: two equal types (or
  // even two aliased actual arguments) still occupy distinct formal positions.
  Expected<json::Value> block(Region &region, TypeRange outputs,
                              StringRef owner, StringRef terminator,
                              unsigned depth = 0) {
    if (depth > depthLimit)
      return error("structured-source-limit");
    if (!llvm::hasSingleElement(region) || region.front().empty())
      return error("structured-source-region");
    Block &body = region.front();
    if (body.getNumArguments() > signatureLimit)
      return error("structured-source-limit");
    llvm::DenseMap<Value, unsigned> refs;
    for (auto [i, arg] : llvm::enumerate(body.getArguments()))
      refs[arg] = i;
    auto operands = [&](Operation &op) -> Expected<json::Array> {
      json::Array result;
      for (Value value : op.getOperands()) {
        auto found = refs.find(value);
        if (found == refs.end())
          return error("structured-source-reference");
        if (found->second > instructionLimit)
          return error("structured-source-limit");
        result.push_back(found->second);
      }
      return result;
    };
    json::Array encoded;
    for (Operation &op : body) {
      auto args = operands(op);
      if (!args)
        return args.takeError();
      if (&op == &body.back()) {
        if (isa<local::StopOp>(op)) {
          if (auto e = attributes(op, {"reason", "site"}))
            return std::move(e);
          if (owner != "local")
            return error("structured-source-operation");
          auto occurrence = site(op);
          if (!occurrence)
            return occurrence.takeError();
          auto reason = op.getAttrOfType<StringAttr>("reason");
          if (!reason)
            return error("structured-source-operation");
          return json::Array{
              "block", std::move(encoded),
              json::Array{"stop", reason.getValue(), *occurrence}};
        }
        bool valid = terminator == "return"
                         ? (owner == "math" ? isa<func::ReturnOp>(op)
                            : owner == "local"
                                ? isa<local::ReturnOp>(op)
                                : isa<protocol_ir::MathematicalReturnOp>(op))
                     : terminator == "condition"
                         ? isa<local::LocalConditionOp>(op)
                         : isa<local::LocalYieldOp>(op);
        if (!valid || op.getOperandTypes() != outputs)
          return error("structured-source-region");
        if (auto e = attributes(op, {}))
          return std::move(e);
        return json::Array{"block", std::move(encoded),
                           json::Array{terminator, std::move(*args)}};
      }
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto inputs = sorts(op.getOperandTypes());
      if (!inputs)
        return inputs.takeError();
      auto results = sorts(op.getResultTypes());
      if (!results)
        return results.takeError();
      auto desc = descriptor(op, owner);
      if (!desc)
        return desc.takeError();
      StringRef occurrence;
      if (op.hasAttr("site")) {
        auto checked = site(op);
        if (!checked)
          return checked.takeError();
        occurrence = *checked;
      }
      json::Array regions;
      if (op.getNumRegions()) {
        bool loop = isa<local::LocalForOp>(op);
        if ((!loop && !isa<local::LocalIfOp>(op)) ||
            op.getNumRegions() != (loop ? 1u : 2u))
          return error("structured-source-region");
        for (Region &nested : op.getRegions()) {
          if (!llvm::hasSingleElement(nested) || nested.front().empty())
            return error("structured-source-region");
          Block &inner = nested.front();
          SmallVector<Type> expectedInputs;
          SmallVector<Type> expectedOutputs(op.getResultTypes());
          StringRef end = "yield";
          if (loop) {
            expectedInputs.push_back(
                IntegerType::get(unit.getContext(), 64, IntegerType::Unsigned));
            llvm::append_range(expectedInputs,
                               op.getOperands().drop_front(2).getTypes());
            auto captures = op.getOperands().drop_front(2 + op.getNumResults());
            llvm::append_range(expectedOutputs, captures.getTypes());
            Operation &last = inner.back();
            bool conditional = isa<local::LocalConditionOp>(last);
            if (conditional) {
              end = "condition";
              expectedOutputs.insert(expectedOutputs.begin(),
                                     IntegerType::get(unit.getContext(), 1));
            }
            if (!isa<local::StopOp>(last)) {
              if (last.getNumOperands() != expectedOutputs.size() ||
                  inner.getNumArguments() != expectedInputs.size())
                return error("structured-source-region");
              for (unsigned i = 0; i < captures.size(); ++i)
                if (last.getOperand(conditional + op.getNumResults() + i) !=
                    inner.getArgument(1 + op.getNumResults() + i))
                  return error("structured-source-capture");
            }
          } else {
            llvm::append_range(expectedInputs,
                               op.getOperands().drop_front().getTypes());
          }
          if (inner.getArgumentTypes() != TypeRange(expectedInputs))
            return error("structured-source-region");
          auto in = sorts(expectedInputs);
          if (!in)
            return in.takeError();
          auto out = sorts(expectedOutputs);
          if (!out)
            return out.takeError();
          auto content = block(nested, expectedOutputs, owner, end, depth + 1);
          if (!content)
            return content.takeError();
          regions.push_back(json::Array{std::move(*in), std::move(*out),
                                        std::move(*content)});
        }
      }
      encoded.push_back(json::Array{std::move(*desc), std::move(*args),
                                    std::move(*results), std::move(regions),
                                    occurrence});
      // Prepend the complete result list once. Incremental single-result
      // insertion would reverse a multi-result operation's coordinates.
      for (auto &entry : refs)
        entry.second += op.getNumResults();
      for (auto [i, result] : llvm::enumerate(op.getResults()))
        refs[result] = i;
    }
    return error("structured-source-region");
  }

  Expected<json::Value> domain(data::DomainOp op) {
    if (auto e =
            attributes(*op, {"sym_name", "sym_visibility", "function_type"}))
      return std::move(e);
    if (op.getSymVisibility() != "private" ||
        !llvm::hasSingleElement(op.getBody()))
      return error("structured-source-domain");
    Block &body = op.getBody().front();
    if (body.getOperations().size() != 2)
      return error("structured-source-domain");
    Operation &constructor = body.front();
    Operation &yield = body.back();
    bool indices = isa<data::DomainIndicesOp>(constructor);
    if ((!indices && !isa<data::DomainElementsOp>(constructor)) ||
        !isa<data::DomainYieldOp>(yield) ||
        yield.getOperand(0) != constructor.getResult(0))
      return error("structured-source-domain");
    if (auto e = attributes(constructor, indices ? ArrayRef<StringRef>{"axis"}
                                                 : ArrayRef<StringRef>{}))
      return std::move(e);
    if (auto e = attributes(yield, {}))
      return std::move(e);
    auto arg = dyn_cast<BlockArgument>(constructor.getOperand(0));
    auto vector =
        dyn_cast<algebra::FieldVectorType>(constructor.getOperand(0).getType());
    if (!arg || arg.getOwner() != &body || !vector ||
        (indices &&
         constructor.getAttrOfType<IntegerAttr>("axis").getInt() != 0))
      return error("structured-source-domain");
    auto items = cast<data::DomainType>(constructor.getResult(0).getType())
                     .getItemTypes();
    Type item = indices ? Type(IntegerType::get(unit.getContext(), 64,
                                                IntegerType::Unsigned))
                        : Type(algebra::FieldType::get(unit.getContext(),
                                                       vector.getDomain()));
    if (items.size() != 1 || items[0] != item)
      return error("structured-source-domain");
    auto inputs = sorts(signature(*op).getInputs());
    if (!inputs)
      return inputs.takeError();
    json::Array desc{indices ? "indices" : "elements", arg.getArgNumber()};
    if (indices)
      desc.push_back(0);
    return json::Array{"domain", op.getSymName(), std::move(*inputs),
                       std::move(desc)};
  }

  Expected<json::Value> function(Operation &op) {
    StringRef owner = kind(op);
    SmallVector<StringRef> allowed{"sym_name", "sym_visibility",
                                   "function_type"};
    if (owner == "math")
      allowed.push_back("data.preconditions");
    else if (owner == "local")
      allowed.push_back("logical_origin");
    else if (owner == "protocol")
      llvm::append_range(
          allowed, ArrayRef<StringRef>{"roles", "input_roles", "output_roles"});
    else if (owner == "finite")
      llvm::append_range(allowed,
                         ArrayRef<StringRef>{"domain", "step", "predicate"});
    else
      return error("structured-source-operation", op.getName().getStringRef());
    if (auto e = attributes(op, allowed))
      return std::move(e);
    auto type = signature(op);
    if (!type)
      return error("structured-source-region");
    auto inputs = sorts(type.getInputs());
    if (!inputs)
      return inputs.takeError();
    auto outputs = sorts(type.getResults());
    if (!outputs)
      return outputs.takeError();
    auto visible = visibility(op);
    if (!visible)
      return visible.takeError();
    StringRef name = SymbolTable::getSymbolName(&op).getValue();
    if (owner == "finite") {
      // The declaration lowers to one owned fold instruction in the reader.
      if (++instructions > instructionLimit)
        return error("structured-source-limit");
      auto refs = fold(op);
      if (!refs)
        return refs.takeError();
      return json::Array{"finite",
                         name,
                         *visible,
                         std::move(*inputs),
                         std::move(*outputs),
                         std::move((*refs)[0]),
                         std::move((*refs)[1]),
                         std::move((*refs)[2])};
    }
    if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op))
      if (auto e = scopes(protocol))
        return std::move(e);
    json::Array preconditions;
    if (op.hasAttr("data.preconditions")) {
      auto attrs = op.getAttrOfType<ArrayAttr>("data.preconditions");
      if (!attrs)
        return error("structured-source-precondition");
      if (attrs.size() > signatureLimit)
        return error("structured-source-limit");
      for (Attribute attr : attrs) {
        auto bound = dyn_cast<data::IndexBoundAttr>(attr);
        if (!bound || bound.getAxis() != 0 ||
            bound.getIndexArg() >= type.getNumInputs() ||
            bound.getContainerArg() >= type.getNumInputs() ||
            !type.getInput(bound.getIndexArg()).isUnsignedInteger(64) ||
            !isa<algebra::FieldVectorType>(
                type.getInput(bound.getContainerArg())))
          return error("structured-source-precondition");
        preconditions.push_back(json::Array{"index_bound", bound.getIndexArg(),
                                            bound.getContainerArg(), 0});
      }
    }
    json::Array origin;
    if (owner == "local") {
      auto attr = op.getAttrOfType<ArrayAttr>("logical_origin");
      if (!attr || attr.size() != 2 || !isa<StringAttr>(attr[0]) ||
          !isa<ArrayAttr>(attr[1]))
        return error("structured-source-origin");
      json::Array bindings;
      for (Attribute component : cast<ArrayAttr>(attr[1])) {
        auto pair = dyn_cast<ArrayAttr>(component);
        if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
            !isa<StringAttr>(pair[1]))
          return error("structured-source-origin");
        bindings.push_back(json::Array{cast<StringAttr>(pair[0]).getValue(),
                                       cast<StringAttr>(pair[1]).getValue()});
      }
      origin.push_back(cast<StringAttr>(attr[0]).getValue());
      origin.push_back(std::move(bindings));
    }
    if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)) ||
        op.getRegion(0).front().getArgumentTypes() != type.getInputs())
      return error("structured-source-region");
    auto body = block(op.getRegion(0), type.getResults(), owner, "return");
    if (!body)
      return body.takeError();
    return json::Array{"function",
                       name,
                       owner,
                       *visible,
                       std::move(*inputs),
                       std::move(*outputs),
                       std::move(preconditions),
                       std::move(origin),
                       std::move(*body)};
  }

  Error closure() {
    // Memoize heights, not only colors: a shared helper encountered first on a
    // short path must still count its whole suffix on a later, longer path.
    llvm::DenseMap<Operation *, unsigned> heights;
    llvm::DenseSet<Operation *> active;
    unsigned visits = 0;
    std::function<Expected<unsigned>(Operation *, unsigned)> visit =
        [&](Operation *op, unsigned depth) -> Expected<unsigned> {
      if (++visits > 100000 || depth > depthLimit)
        return error("structured-source-limit");
      if (auto found = heights.find(op); found != heights.end())
        return found->second;
      if (!active.insert(op).second)
        return error("structured-source-cycle");
      unsigned height = 0;
      for (Operation *callee : dependencies[op]) {
        auto nested = visit(callee, depth + 1);
        if (!nested)
          return nested.takeError();
        height = std::max(height, *nested + 1);
        if (height > depthLimit)
          return error("structured-source-limit");
      }
      active.erase(op);
      heights[op] = height;
      return height;
    };
    for (Operation &op : unit.getBody().front()) {
      auto checked = visit(&op, 0);
      if (!checked)
        return checked.takeError();
    }
    return Error::success();
  }

public:
  Exporter(protocol_ir::ProtocolModuleOp unit,
           protocol_ir::MathematicalOp selected)
      : unit(unit), selected(selected), symbols(unit) {}

  Expected<json::Value> run(StringRef bytes) {
    if (selected.getRoles().size() != 1)
      return error("structured-source-role");
    role = cast<StringAttr>(selected.getRoles()[0]).getValue();
    if (auto e = attributes(*unit, {"profile"}))
      return std::move(e);
    json::Array domains, definitions;
    for (Operation &op : unit.getBody().front()) {
      definition = &op;
      sites.clear();
      dependencies.try_emplace(&op);
      if (auto declaration = dyn_cast<data::DomainOp>(op)) {
        if (domains.size() == 128)
          return error("structured-source-limit");
        auto encoded = domain(declaration);
        if (!encoded)
          return encoded.takeError();
        domains.push_back(std::move(*encoded));
      } else {
        if (definitions.size() == 128)
          return error("structured-source-limit");
        auto encoded = function(op);
        if (!encoded)
          return encoded.takeError();
        definitions.push_back(std::move(*encoded));
      }
    }
    if (auto e = closure())
      return std::move(e);
    auto digest = SHA256::hash(arrayRefFromStringRef(bytes));
    return json::Array{
        "zkc.structured-source/0", "original", "sha256:" + toHex(digest, true),
        selected.getSymName(),     role,       std::move(domains),
        std::move(definitions)};
  }
};
} // namespace

Expected<json::Value> exportStructuredSource(StringRef bytes, StringRef name,
                                             MLIRContext &context) {
  if (bytes.size() > 16 * 1024 * 1024 || !mlirNestingWithinLimit(bytes))
    return error("structured-source-limit");
  auto original = parseSourceString<ModuleOp>(bytes, &context);
  if (!original || failed(verify(*original)))
    return error("structured-source-original");
  if (auto e = attributes(**original, {}))
    return std::move(e);
  if (!llvm::hasSingleElement(original->getBody()->getOperations()))
    return error("structured-source-module");
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return error("structured-source-profile");
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(name);
  if (!selected)
    return error("structured-source-symbol");
  auto exported = Exporter(unit, selected).run(bytes);
  if (!exported)
    return exported.takeError();
  if (!boundedWire(*exported) || printJson(*exported).size() > 1024 * 1024)
    return error("structured-source-limit");
  return exported;
}
} // namespace zkc::protocol

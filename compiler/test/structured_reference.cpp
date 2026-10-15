// Bounded, independent test evaluation of original native structured SSA.
// No structured exporter, serialized SSA coordinates, preparation, or runtime
// kernels participate. Native verification remains authoritative for admission;
// this executable supplies finite evidence, not a shipped semantic interpreter.
#include "../lib/Support/Input.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <variant>
#include <vector>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {
constexpr unsigned maxDepth = 64, maxSignature = 512, maxOperations = 4096;
constexpr uint64_t maxSteps = 1000000, maxLoopBound = 1 << 20;
constexpr size_t maxVector = 4096;
constexpr StringLiteral fieldDomain = "bls12-381.fr";

const APInt &modulus() {
  static const APInt value(512,
                           "524358751751261904794477405081859658376905525005276"
                           "37822603658699938581184513",
                           10);
  return value;
}

Expected<APInt> decimal(StringRef text, bool field, StringRef code) {
  // Check the spelling and length before APInt construction: it must neither
  // truncate an overlong integer nor allocate from an unbounded digit count.
  if (text.empty() || text.size() > (field ? 77 : 20) ||
      (text.size() > 1 && text.front() == '0') ||
      !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }))
    return error(code, "expected canonical decimal string");
  APInt value(512, text, 10);
  if (field ? value.uge(modulus()) : value.getActiveBits() > 64)
    return error(code, "value out of range");
  return value;
}

bool valueType(Type type) {
  if (type.isSignlessInteger(1) || type.isUnsignedInteger(64))
    return true;
  if (auto field = dyn_cast<algebra::FieldType>(type))
    return field.getDomain() == fieldDomain;
  if (auto vector = dyn_cast<algebra::FieldVectorType>(type))
    return vector.getDomain() == fieldDomain;
  return false;
}

enum class Kind {
  Unsupported,
  FieldConstant,
  Add,
  Subtract,
  Multiply,
  Equal,
  BoolConstant,
  And,
  Or,
  Xor,
  Compare,
  Select,
  At,
  Call,
  Apply,
  LocalCall,
  Fold,
  If,
  For,
  Guard,
  Return,
  Yield,
  Condition,
  Stop,
  Elements,
  Indices,
  DomainYield
};

Kind kind(Operation &op) {
  return llvm::StringSwitch<Kind>(op.getName().getStringRef())
      .Case("algebra.constant", Kind::FieldConstant)
      .Case("algebra.field_add", Kind::Add)
      .Case("algebra.field_subtract", Kind::Subtract)
      .Case("algebra.field_multiply", Kind::Multiply)
      .Case("algebra.field_equal", Kind::Equal)
      .Cases({"arith.constant", "local.bool_constant"}, Kind::BoolConstant)
      .Case("arith.andi", Kind::And)
      .Case("arith.ori", Kind::Or)
      .Case("arith.xori", Kind::Xor)
      .Case("arith.cmpi", Kind::Compare)
      .Case("arith.select", Kind::Select)
      .Case("data.bounded_at", Kind::At)
      .Case("func.call", Kind::Call)
      .Case("local.apply", Kind::Apply)
      .Case("protocol.local_call", Kind::LocalCall)
      .Case("algebra.finite_fold", Kind::Fold)
      .Case("local.if", Kind::If)
      .Case("local.for", Kind::For)
      .Case("protocol.guard", Kind::Guard)
      .Cases({"func.return", "local.return", "protocol.return"}, Kind::Return)
      .Case("local.yield", Kind::Yield)
      .Case("local.condition", Kind::Condition)
      .Case("local.stop", Kind::Stop)
      .Case("data.domain_elements", Kind::Elements)
      .Case("data.domain_indices", Kind::Indices)
      .Case("data.domain_yield", Kind::DomainYield)
      .Default(Kind::Unsupported);
}

Error attributes(Operation &op, ArrayRef<StringRef> allowed) {
  for (auto attr : op.getAttrs())
    if (!llvm::is_contained(allowed, attr.getName().strref()))
      return error("structured-reference-unsupported",
                   "attribute " + attr.getName().strref() + " on " +
                       op.getName().getStringRef());
  return Error::success();
}

Error attributeBounds(Attribute attr, unsigned depth = 0) {
  if (depth > maxDepth)
    return error("structured-reference-capacity", "attribute depth");
  if (auto text = dyn_cast<StringAttr>(attr)) {
    if (text.getValue().size() > 512)
      return error("structured-reference-capacity", "string length");
  } else if (auto symbol = dyn_cast<SymbolRefAttr>(attr)) {
    if (symbol.getRootReference().size() > 512 ||
        !symbol.getNestedReferences().empty())
      return error("structured-reference-unsupported", "symbol reference");
  } else if (auto array = dyn_cast<ArrayAttr>(attr)) {
    for (Attribute item : array)
      if (auto failure = attributeBounds(item, depth + 1))
        return failure;
  }
  return Error::success();
}

FunctionType signature(Operation &op) {
  auto attr = op.getAttrOfType<TypeAttr>("function_type");
  return attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType{};
}

// The profile check visits every definition and every region independently of
// evaluation. Unsupported operations in dormant branches and unused helpers
// therefore cannot acquire meaning just because one request avoids them.
class Admission {
  protocol_ir::ProtocolModuleOp unit;
  SymbolTable symbols;
  unsigned operations = 0;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> dependencies;
  llvm::DenseSet<Operation *> active;
  llvm::DenseMap<Operation *, unsigned> heights;

  Error reference(Operation &op, Operation &owner, StringRef attribute,
                  StringRef expected, bool optional = false) {
    auto name = op.getAttrOfType<FlatSymbolRefAttr>(attribute);
    if (!name)
      return optional ? Error::success()
                      : error("structured-reference-symbol", attribute);
    Operation *target = symbols.lookup(name.getValue());
    if (!target ||
        (target->getName().getStringRef() != expected &&
         !(expected == "local.func" && attribute == "callee" &&
           kind(op) == Kind::Apply && isa<local::FiniteFoldOp>(target))))
      return error("structured-reference-symbol", name.getValue());
    dependencies[&owner].push_back(target);
    if (attribute == "callee") {
      auto type = signature(*target);
      if (!type || op.getOperandTypes() != type.getInputs() ||
          op.getResultTypes() != type.getResults())
        return error("structured-reference-signature", name.getValue());
    }
    return Error::success();
  }

  Error foldReferences(Operation &op, Operation &owner, bool local) {
    if (auto failure = reference(op, owner, "domain", "data.domain"))
      return failure;
    if (auto failure =
            reference(op, owner, "step", local ? "local.func" : "func.func"))
      return failure;
    return reference(op, owner, "predicate", local ? "local.func" : "func.func",
                     true);
  }

  Error instruction(Operation &op, Operation &owner) {
    Kind code = kind(op);
    if (code == Kind::Unsupported || code == Kind::Elements ||
        code == Kind::Indices || code == Kind::DomainYield)
      return error("structured-reference-unsupported",
                   op.getName().getStringRef());
    if (op.getNumRegions() != (code == Kind::If    ? 2u
                               : code == Kind::For ? 1u
                                                   : 0u))
      return error("structured-reference-unsupported", "region count");
    for (Type type : op.getOperandTypes())
      if (!valueType(type))
        return error("structured-reference-unsupported", "operand type");
    for (Type type : op.getResultTypes())
      if (!valueType(type))
        return error("structured-reference-unsupported", "result type");
    switch (code) {
    case Kind::FieldConstant: {
      if (auto failure = attributes(op, {"value"}))
        return failure;
      auto parsed = decimal(cast<algebra::ConstantFieldOp>(op).getValue(), true,
                            "structured-reference-unsupported");
      if (!parsed)
        return parsed.takeError();
      break;
    }
    case Kind::BoolConstant:
      if (auto failure =
              attributes(op, isa<local::BoolConstantOp>(op)
                                 ? ArrayRef<StringRef>{"value", "site"}
                                 : ArrayRef<StringRef>{"value"}))
        return failure;
      if (op.getNumResults() != 1 ||
          !op.getResult(0).getType().isSignlessInteger(1))
        return error("structured-reference-unsupported",
                     "non-boolean constant");
      break;
    case Kind::And:
    case Kind::Or:
    case Kind::Xor:
    case Kind::Compare:
      if (!llvm::all_of(op.getOperandTypes(),
                        [](Type t) { return t.isSignlessInteger(1); }))
        return error("structured-reference-unsupported",
                     "non-boolean arithmetic");
      if (code == Kind::Compare) {
        auto predicate = cast<arith::CmpIOp>(op).getPredicate();
        if (predicate != arith::CmpIPredicate::eq &&
            predicate != arith::CmpIPredicate::ne)
          return error("structured-reference-unsupported",
                       "comparison predicate");
        return attributes(op, {"predicate"});
      }
      return attributes(op, {});
    case Kind::Call:
    case Kind::Apply:
    case Kind::LocalCall:
      if (auto failure = attributes(
              op, code == Kind::Call ? ArrayRef<StringRef>{"callee"}
                  : code == Kind::Apply
                      ? ArrayRef<StringRef>{"callee", "site"}
                      : ArrayRef<StringRef>{"callee", "site", "role"}))
        return failure;
      return reference(op, owner, "callee",
                       code == Kind::Call ? "func.func" : "local.func");
    case Kind::Fold:
      if (auto failure = attributes(op, {"domain", "step", "predicate"}))
        return failure;
      return foldReferences(op, owner, false);
    case Kind::If:
    case Kind::For:
      return attributes(op, {"site"});
    case Kind::Guard:
      return attributes(op, {"site", "owner"});
    case Kind::Stop:
      if (auto failure = attributes(op, {"site", "reason"}))
        return failure;
      if (!llvm::is_contained(ArrayRef<StringRef>{"reject", "abort",
                                                  "exhausted", "incomplete",
                                                  "refused"},
                              cast<local::StopOp>(op).getReason()))
        return error("structured-reference-unsupported", "stop reason");
      break;
    default:
      return attributes(op, {});
    }
    return Error::success();
  }

  Error block(Block &body, Operation &owner, unsigned depth) {
    if (depth > maxDepth || body.getNumArguments() > maxSignature)
      return error("structured-reference-capacity", "block depth or arguments");
    llvm::DenseSet<Value> defined;
    for (Value argument : body.getArguments()) {
      if (!valueType(argument.getType()))
        return error("structured-reference-unsupported", "block argument type");
      defined.insert(argument);
    }
    for (Operation &op : body) {
      // Structural instructions exclude terminators. Interpreter work has a
      // separate budget and still charges every executed native operation.
      if ((!op.hasTrait<OpTrait::IsTerminator>() &&
           ++operations > maxOperations) ||
          op.getNumOperands() > maxSignature ||
          op.getNumResults() > maxSignature)
        return error("structured-reference-capacity",
                     "operations or signature");
      for (Value operand : op.getOperands())
        if (!defined.contains(operand))
          return error("structured-reference-ssa",
                       "operand outside closed block");
      for (auto attr : op.getAttrs())
        if (auto failure = attributeBounds(attr.getValue()))
          return failure;
      if (auto failure = instruction(op, owner))
        return failure;
      for (Region &region : op.getRegions()) {
        if (!llvm::hasSingleElement(region) || region.front().empty())
          return error("structured-reference-unsupported", "non-single block");
        if (auto failure = block(region.front(), owner, depth + 1))
          return failure;
      }
      // Preserve the complete native yield ABI, including invariant identity.
      if (kind(op) == Kind::For) {
        Block &inner = op.getRegion(0).front();
        Operation &end = inner.back();
        if (kind(end) != Kind::Stop) {
          unsigned offset = kind(end) == Kind::Condition ? 1 : 0;
          unsigned count = op.getNumResults();
          unsigned captures = op.getNumOperands() - 2 - count;
          if (end.getNumOperands() != offset + count + captures)
            return error("structured-reference-signature", "loop yield");
          for (unsigned i = 0; i < captures; ++i)
            if (end.getOperand(offset + count + i) !=
                inner.getArgument(1 + count + i))
              return error("structured-reference-ssa",
                           "loop capture forwarding");
        }
      }
      for (Value result : op.getResults())
        defined.insert(result);
    }
    return Error::success();
  }

  Error domain(Operation &op) {
    if (auto failure =
            attributes(op, {"sym_name", "sym_visibility", "function_type"}))
      return failure;
    if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)))
      return error("structured-reference-unsupported", "domain body");
    Block &body = op.getRegion(0).front();
    if (std::distance(body.begin(), body.end()) != 2)
      return error("structured-reference-unsupported",
                   "domain must have exactly one constructor and yield");
    Operation &constructor = body.front(), &end = body.back();
    Kind code = kind(constructor);
    if ((code != Kind::Elements && code != Kind::Indices) ||
        kind(end) != Kind::DomainYield || constructor.getNumOperands() != 1 ||
        constructor.getNumResults() != 1 || end.getNumOperands() != 1 ||
        end.getOperand(0) != constructor.getResult(0))
      return error("structured-reference-unsupported",
                   "domain constructor or yield");
    auto container = dyn_cast<BlockArgument>(constructor.getOperand(0));
    if (!container || container.getOwner() != &body ||
        !isa<algebra::FieldVectorType>(container.getType()) ||
        !valueType(container.getType()))
      return error("structured-reference-unsupported", "domain container");
    if (auto failure = attributes(constructor, code == Kind::Indices
                                                   ? ArrayRef<StringRef>{"axis"}
                                                   : ArrayRef<StringRef>{}))
      return failure;
    if (auto failure = attributes(end, {}))
      return failure;
    if (code == Kind::Indices &&
        cast<IntegerAttr>(constructor.getAttr("axis")).getInt() != 0)
      return error("structured-reference-unsupported", "domain axis");
    return Error::success();
  }

  Expected<unsigned> height(Operation *op, unsigned depth) {
    if (depth > maxDepth)
      return error("structured-reference-capacity", "reference depth");
    if (active.contains(op))
      return error("structured-reference-symbol", "cyclic reference");
    auto found = heights.find(op);
    if (found != heights.end())
      return found->second;
    active.insert(op);
    unsigned result = 1;
    auto edges = dependencies.find(op);
    if (edges != dependencies.end())
      for (Operation *target : edges->second) {
        auto nested = height(target, depth + 1);
        if (!nested)
          return nested.takeError();
        result = std::max(result, *nested + 1);
      }
    active.erase(op);
    if (result > maxDepth)
      return error("structured-reference-capacity", "reference depth");
    heights[op] = result;
    return result;
  }

public:
  explicit Admission(protocol_ir::ProtocolModuleOp unit)
      : unit(unit), symbols(unit) {}

  Error check() {
    unsigned domains = 0, definitions = 0;
    for (Operation &op : unit.getBody().front()) {
      bool isDomain = isa<data::DomainOp>(op);
      bool finite = isa<local::FiniteFoldOp>(op);
      if (!isDomain && !finite &&
          !isa<func::FuncOp, local::FuncOp, protocol_ir::MathematicalOp>(op))
        return error("structured-reference-unsupported",
                     op.getName().getStringRef());
      if (++(isDomain ? domains : definitions) > 128)
        return error("structured-reference-capacity", "definitions");
      auto type = signature(op);
      if (!type || type.getNumInputs() > maxSignature ||
          type.getNumResults() > maxSignature)
        return error("structured-reference-capacity", "function signature");
      for (Type input : type.getInputs())
        if (!valueType(input))
          return error("structured-reference-unsupported", "input type");
      if (!isDomain)
        for (Type output : type.getResults())
          if (!valueType(output))
            return error("structured-reference-unsupported", "output type");
      for (auto attr : op.getAttrs())
        if (auto failure = attributeBounds(attr.getValue()))
          return failure;
      if (auto visibility = op.getAttrOfType<StringAttr>("sym_visibility"))
        if (visibility != "private" && visibility != "public")
          return error("structured-reference-unsupported", "visibility");
      if (isDomain) {
        if (auto failure = domain(op))
          return failure;
        continue;
      }
      if (finite) {
        if (++operations > maxOperations)
          return error("structured-reference-capacity", "finite instructions");
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "function_type",
                                "domain", "step", "predicate"}))
          return failure;
        if (auto failure = foldReferences(op, op, true))
          return failure;
        continue;
      }
      if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "function_type",
                                "roles", "input_roles", "output_roles"}))
          return failure;
        if (protocol.getRoles().size() != 1)
          return error("structured-reference-unsupported", "multiple roles");
        for (auto scopes :
             {protocol.getInputRoles(), protocol.getOutputRoles()})
          for (Attribute scope : scopes)
            if (scope != protocol.getRoles())
              return error("structured-reference-unsupported", "role scope");
      } else if (isa<func::FuncOp>(op)) {
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "function_type",
                                "data.preconditions"}))
          return failure;
        if (auto conditions = op.getAttrOfType<ArrayAttr>("data.preconditions"))
          for (Attribute attr : conditions) {
            auto bound = dyn_cast<data::IndexBoundAttr>(attr);
            if (!bound || bound.getAxis() != 0 ||
                bound.getIndexArg() >= type.getNumInputs() ||
                bound.getContainerArg() >= type.getNumInputs() ||
                !type.getInput(bound.getIndexArg()).isUnsignedInteger(64) ||
                !isa<algebra::FieldVectorType>(
                    type.getInput(bound.getContainerArg())))
              return error("structured-reference-unsupported", "precondition");
          }
      } else if (auto failure =
                     attributes(op, {"sym_name", "sym_visibility",
                                     "function_type", "logical_origin"})) {
        return failure;
      }
      if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)) ||
          op.getRegion(0).front().empty())
        return error("structured-reference-unsupported", "function body");
      if (auto failure = block(op.getRegion(0).front(), op, 1))
        return failure;
    }
    for (Operation &op : unit.getBody().front()) {
      auto checked = height(&op, 1);
      if (!checked)
        return checked.takeError();
    }
    return Error::success();
  }
};

using Vector = std::shared_ptr<const std::vector<APInt>>;
struct Domain {
  Vector container;
  bool indices;
};
using Datum = std::variant<bool, uint64_t, APInt, Vector, Domain>;
using Values = std::vector<Datum>;
struct Outcome {
  Kind terminator = Kind::Return;
  Values values;
  std::string reason;
  bool stopped() const { return terminator == Kind::Stop; }
};

Expected<Datum> decode(Type type, const json::Value &input) {
  if (type.isSignlessInteger(1)) {
    auto value = input.getAsBoolean();
    if (!value)
      return error("structured-reference-input", "expected Boolean");
    return Datum(*value);
  }
  if (isa<algebra::FieldVectorType>(type)) {
    auto array = input.getAsArray();
    if (!array)
      return error("structured-reference-input", "expected vector");
    if (array->size() > maxVector)
      return error("structured-reference-capacity", "vector length");
    auto values = std::make_shared<std::vector<APInt>>();
    values->reserve(array->size());
    for (const auto &item : *array) {
      auto text = item.getAsString();
      if (!text)
        return error("structured-reference-input", "expected field string");
      auto value = decimal(*text, true, "structured-reference-input");
      if (!value)
        return value.takeError();
      values->push_back(std::move(*value));
    }
    return Datum(Vector(std::move(values)));
  }
  auto text = input.getAsString();
  if (!text)
    return error("structured-reference-input", "expected decimal string");
  bool field = isa<algebra::FieldType>(type);
  auto value = decimal(*text, field, "structured-reference-input");
  if (!value)
    return value.takeError();
  if (field)
    return Datum(std::move(*value));
  if (type.isUnsignedInteger(64))
    return Datum(value->getZExtValue());
  return error("structured-reference-unsupported", "input type");
}

std::string digits(const APInt &value) {
  SmallString<80> text;
  value.toString(text, 10, false);
  return text.str().str();
}

Expected<json::Value> encode(const Datum &value) {
  if (auto boolean = std::get_if<bool>(&value))
    return json::Value(*boolean);
  if (auto index = std::get_if<uint64_t>(&value))
    return json::Value(std::to_string(*index));
  if (auto field = std::get_if<APInt>(&value))
    return json::Value(digits(*field));
  if (auto vector = std::get_if<Vector>(&value)) {
    json::Array items;
    for (const APInt &field : **vector)
      items.push_back(digits(field));
    return json::Value(std::move(items));
  }
  return error("structured-reference-signature",
               "cannot return domain descriptor");
}

bool matches(Type type, const Datum &value) {
  if (type.isSignlessInteger(1))
    return std::holds_alternative<bool>(value);
  if (type.isUnsignedInteger(64))
    return std::holds_alternative<uint64_t>(value);
  if (isa<algebra::FieldType>(type))
    return std::holds_alternative<APInt>(value);
  if (isa<algebra::FieldVectorType>(type))
    return std::holds_alternative<Vector>(value);
  return isa<data::DomainType>(type) && std::holds_alternative<Domain>(value);
}

class Reference {
  SymbolTable symbols;
  uint64_t steps = 0;

  Error tick(unsigned depth) {
    if (depth > maxDepth || ++steps > maxSteps)
      return error("structured-reference-capacity",
                   "evaluation steps or depth");
    return Error::success();
  }

  Operation *target(Operation &op, StringRef attr) {
    auto name = op.getAttrOfType<FlatSymbolRefAttr>(attr);
    return name ? symbols.lookup(name.getValue()) : nullptr;
  }

  Expected<Outcome> invoke(Operation *callee, ArrayRef<Datum> args,
                           unsigned depth) {
    if (auto failure = tick(depth))
      return failure;
    if (!callee)
      return error("structured-reference-symbol");
    auto type = signature(*callee);
    if (!type || args.size() != type.getNumInputs())
      return error("structured-reference-signature", "call arguments");
    for (auto [type, value] : llvm::zip(type.getInputs(), args))
      if (!matches(type, value))
        return error("structured-reference-signature", "call argument type");
    // Native closure proves the corresponding static provenance. Checking the
    // actual request again keeps a bad bounded read from ever defaulting to
    // zero.
    if (auto conditions =
            callee->getAttrOfType<ArrayAttr>("data.preconditions"))
      for (Attribute attr : conditions) {
        auto bound = cast<data::IndexBoundAttr>(attr);
        if (std::get<uint64_t>(args[bound.getIndexArg()]) >=
            std::get<Vector>(args[bound.getContainerArg()])->size())
          return error("structured-reference-bounds", "helper precondition");
      }
    auto result = isa<local::FiniteFoldOp>(callee)
                      ? fold(*callee, args, type.getNumResults(), depth)
                      : block(callee->getRegion(0).front(), args, depth);
    if (!result || result->stopped())
      return result;
    if (result->values.size() != type.getNumResults())
      return error("structured-reference-signature", "call results");
    for (auto [type, value] : llvm::zip(type.getResults(), result->values))
      if (!matches(type, value))
        return error("structured-reference-signature", "call result type");
    return result;
  }

  Expected<Outcome> fold(Operation &op, ArrayRef<Datum> args, unsigned count,
                         unsigned depth) {
    Operation *domain = target(op, "domain");
    if (!domain)
      return error("structured-reference-symbol", "domain");
    unsigned arity = signature(*domain).getNumInputs();
    if (args.size() < arity + count)
      return error("structured-reference-signature", "fold inputs");
    auto enumerated = invoke(domain, args.take_front(arity), depth + 1);
    if (!enumerated)
      return enumerated.takeError();
    if (enumerated->values.size() != 1 ||
        !std::holds_alternative<Domain>(enumerated->values[0]))
      return error("structured-reference-signature", "domain result");
    Domain items = std::get<Domain>(enumerated->values[0]);
    // Initial seeds are read once. Every subsequent step uses the actual
    // preceding results, including same-typed positions and aliases.
    auto initial = args.slice(arity, count);
    Outcome state{Kind::Return, Values(initial.begin(), initial.end()), {}};
    for (size_t i = 0; i < items.container->size(); ++i) {
      if (auto failure = tick(depth))
        return failure;
      Values callback{items.indices ? Datum(uint64_t(i))
                                    : Datum((*items.container)[i])};
      llvm::append_range(callback, args.take_front(arity));
      llvm::append_range(callback, args.drop_front(arity + count));
      // Predicate ABI: I,A,C. Step ABI: S,I,A,C. The state is not a predicate
      // input.
      if (Operation *predicate = target(op, "predicate")) {
        auto admitted = invoke(predicate, callback, depth + 1);
        if (!admitted || admitted->stopped())
          return admitted;
        if (admitted->values.size() != 1 ||
            !std::holds_alternative<bool>(admitted->values[0]))
          return error("structured-reference-signature", "predicate result");
        if (!std::get<bool>(admitted->values[0]))
          continue;
      }
      callback.insert(callback.begin(), state.values.begin(),
                      state.values.end());
      auto next = invoke(target(op, "step"), callback, depth + 1);
      if (!next || next->stopped())
        return next;
      if (next->values.size() != count)
        return error("structured-reference-signature", "fold state");
      state = std::move(*next);
    }
    return state;
  }

  Expected<Outcome> evaluate(Operation &op, ArrayRef<Datum> args,
                             unsigned depth) {
    Kind code = kind(op);
    switch (code) {
    case Kind::Return:
    case Kind::Yield:
    case Kind::Condition:
    case Kind::DomainYield:
      return Outcome{code, Values(args.begin(), args.end()), {}};
    case Kind::Stop:
      return Outcome{Kind::Stop, {}, cast<local::StopOp>(op).getReason().str()};
    case Kind::Guard:
      return std::get<bool>(args[0]) ? Outcome{}
                                     : Outcome{Kind::Stop, {}, "reject"};
    case Kind::Call:
    case Kind::Apply:
    case Kind::LocalCall:
      return invoke(target(op, "callee"), args, depth + 1);
    case Kind::Fold:
      return fold(op, args, op.getNumResults(), depth);
    case Kind::If:
      return block(op.getRegion(std::get<bool>(args[0]) ? 0 : 1).front(),
                   args.drop_front(), depth + 1);
    case Kind::For: {
      uint64_t lower = std::get<uint64_t>(args[0]),
               upper = std::get<uint64_t>(args[1]);
      if (lower > maxLoopBound || upper > maxLoopBound)
        return error("structured-reference-capacity", "loop bounds");
      size_t count = op.getNumResults();
      auto initial = args.slice(2, count),
           captures = args.drop_front(2 + count);
      Outcome state{Kind::Return, Values(initial.begin(), initial.end()), {}};
      for (uint64_t i = lower; i < upper; ++i) {
        if (auto failure = tick(depth))
          return failure;
        Values inputs{Datum(i)};
        llvm::append_range(inputs, state.values);
        llvm::append_range(inputs, captures);
        auto next = block(op.getRegion(0).front(), inputs, depth + 1);
        if (!next || next->stopped())
          return next;
        size_t offset = next->terminator == Kind::Condition ? 1 : 0;
        if (next->values.size() != offset + count + captures.size())
          return error("structured-reference-signature", "loop yield");
        state.values.assign(next->values.begin() + offset,
                            next->values.begin() + offset + count);
        if (offset && !std::get<bool>(next->values[0]))
          break;
      }
      return state;
    }
    default:
      break;
    }
    Outcome result;
    switch (code) {
    case Kind::FieldConstant: {
      auto parsed = decimal(cast<algebra::ConstantFieldOp>(op).getValue(), true,
                            "structured-reference-unsupported");
      if (!parsed)
        return parsed.takeError();
      result.values.emplace_back(std::move(*parsed));
      break;
    }
    case Kind::BoolConstant:
      result.values.emplace_back(
          !cast<IntegerAttr>(op.getAttr("value")).getValue().isZero());
      break;
    case Kind::Add:
    case Kind::Subtract:
    case Kind::Multiply:
    case Kind::Equal: {
      const APInt &a = std::get<APInt>(args[0]), &b = std::get<APInt>(args[1]);
      if (code == Kind::Equal)
        result.values.emplace_back(a == b);
      // Both operands are < p < 2^255. 512 bits hold the full product and
      // the addition/subtraction intermediates before exact reduction.
      else if (code == Kind::Add)
        result.values.emplace_back((a + b).urem(modulus()));
      else if (code == Kind::Subtract)
        result.values.emplace_back((a + modulus() - b).urem(modulus()));
      else
        result.values.emplace_back((a * b).urem(modulus()));
      break;
    }
    case Kind::And:
    case Kind::Or:
    case Kind::Xor:
    case Kind::Compare: {
      bool a = std::get<bool>(args[0]), b = std::get<bool>(args[1]);
      bool output = code == Kind::And  ? a && b
                    : code == Kind::Or ? a || b
                                       : a != b;
      if (code == Kind::Compare)
        output =
            cast<arith::CmpIOp>(op).getPredicate() == arith::CmpIPredicate::eq
                ? a == b
                : a != b;
      result.values.emplace_back(output);
      break;
    }
    case Kind::Select:
      result.values.push_back(args[std::get<bool>(args[0]) ? 1 : 2]);
      break;
    case Kind::At: {
      const auto &container = std::get<Vector>(args[0]);
      uint64_t index = std::get<uint64_t>(args[1]);
      if (index >= container->size())
        return error("structured-reference-bounds", "bounded_at");
      result.values.emplace_back((*container)[index]);
      break;
    }
    case Kind::Elements:
    case Kind::Indices:
      result.values.emplace_back(
          Domain{std::get<Vector>(args[0]), code == Kind::Indices});
      break;
    default:
      return error("structured-reference-unsupported",
                   op.getName().getStringRef());
    }
    return result;
  }

  Expected<Outcome> block(Block &body, ArrayRef<Datum> inputs, unsigned depth) {
    if (auto failure = tick(depth))
      return failure;
    if (body.getNumArguments() != inputs.size())
      return error("structured-reference-signature", "block inputs");
    // Each invocation owns a fresh map. Missing SSA values are errors, never
    // default-constructed field zeros or remnants from another helper call.
    llvm::DenseMap<Value, Datum> values;
    for (auto [argument, input] : llvm::zip(body.getArguments(), inputs)) {
      if (!matches(argument.getType(), input))
        return error("structured-reference-signature", "block input type");
      values.try_emplace(argument, input);
    }
    for (Operation &op : body) {
      if (auto failure = tick(depth))
        return failure;
      Values args;
      for (Value operand : op.getOperands()) {
        auto found = values.find(operand);
        if (found == values.end())
          return error("structured-reference-ssa", "missing operand");
        args.push_back(found->second);
      }
      auto result = evaluate(op, args, depth);
      if (!result || result->stopped() || op.hasTrait<OpTrait::IsTerminator>())
        return result;
      if (op.getNumResults() != result->values.size())
        return error("structured-reference-signature", "operation results");
      for (auto [output, value] : llvm::zip(op.getResults(), result->values)) {
        if (!matches(output.getType(), value))
          return error("structured-reference-signature",
                       "operation result type");
        if (!values.try_emplace(output, std::move(value)).second)
          return error("structured-reference-ssa", "duplicate result");
      }
    }
    return error("structured-reference-ssa", "missing terminator");
  }

public:
  explicit Reference(Operation *unit) : symbols(unit) {}
  Expected<json::Value> run(protocol_ir::MathematicalOp source,
                            const json::Array &request) {
    auto type = source.getFunctionType();
    if (request.size() != type.getNumInputs())
      return error("structured-reference-input", "input arity");
    Values inputs;
    for (auto [type, input] : llvm::zip(type.getInputs(), request)) {
      auto value = decode(type, input);
      if (!value)
        return value.takeError();
      inputs.push_back(std::move(*value));
    }
    auto result = invoke(source, inputs, 1);
    if (!result)
      return result.takeError();
    if (result->stopped())
      return json::Value(json::Array{"stopped", result->reason});
    json::Array outputs;
    for (const Datum &value : result->values) {
      auto output = encode(value);
      if (!output)
        return output.takeError();
      outputs.push_back(std::move(*output));
    }
    return json::Value(json::Array{"returned", std::move(outputs)});
  }
};

Expected<std::string> input(StringRef path, size_t limit) {
  auto text = readInput(path, limit);
  if (text)
    return text;
  Error mapped = Error::success();
  handleAllErrors(
      text.takeError(),
      [&](const Refusal &failure) {
        mapped =
            error(failure.code == "byte-limit" ? "structured-reference-capacity"
                                               : "structured-reference-io",
                  failure.code);
      },
      [&](const ErrorInfoBase &failure) {
        mapped = error("structured-reference-io", failure.message());
      });
  return std::move(mapped);
}
} // namespace

int main(int argc, char **argv) {
  auto fail = [](Error failure) {
    errs() << toString(std::move(failure)) << '\n';
    return 1;
  };
  if (argc != 4)
    return fail(error("structured-reference-arguments"));
  auto source = input(argv[1], 16 * 1024 * 1024);
  if (!source)
    return fail(source.takeError());
  if (!mlirNestingWithinLimit(*source, maxDepth))
    return fail(error("structured-reference-capacity", "MLIR nesting"));
  auto request = input(argv[3], 1024 * 1024);
  if (!request)
    return fail(request.takeError());
  auto parsed = parseNaturalJson(*request, 1024 * 1024, maxDepth,
                                 "structured-reference-input",
                                 "structured-reference-capacity");
  if (!parsed)
    return fail(parsed.takeError());
  auto array = parsed->getAsArray();
  if (!array)
    return fail(error("structured-reference-input", "expected input array"));
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  auto module = parseSourceString<ModuleOp>(*source, &context);
  if (!module || failed(verify(*module)))
    return fail(error("structured-reference-source"));
  if (!module->getOperation()->getAttrs().empty() ||
      !llvm::hasSingleElement(module->getBody()->getOperations()))
    return fail(error("structured-reference-unsupported", "module shell"));
  auto unit =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
  if (!unit || unit.getProfile() != protocol_ir::Profile::Protocol)
    return fail(error("structured-reference-unsupported", "protocol profile"));
  if (auto failure = Admission(unit).check())
    return fail(std::move(failure));
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(argv[2]);
  if (!selected)
    return fail(error("structured-reference-symbol", argv[2]));
  auto result = Reference(unit).run(selected, *array);
  if (!result)
    return fail(result.takeError());
  outs() << printJson(*result) << '\n';
  return 0;
}

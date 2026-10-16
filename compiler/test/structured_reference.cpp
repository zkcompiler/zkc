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
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <variant>
#include <vector>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {
constexpr unsigned maxDepth = 64, maxSignature = 512, maxOperations = 4096;
constexpr uint64_t maxSteps = 1000000, maxLoopBound = 1 << 20;
constexpr uint64_t maxStaticVisits = 100000;
constexpr size_t maxEffectiveSiteBytes = 4096;
constexpr uint64_t maxStaticSiteBytes = 16 * 1024 * 1024;
constexpr size_t maxVector = 4096;
constexpr StringLiteral fieldDomain = "bls12-381.fr";
constexpr StringLiteral groupDomain = "bls12-381.g1";
constexpr StringLiteral randomContract = "random.bls12-381.fr/0";

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
  if (auto group = dyn_cast<algebra::GroupType>(type))
    return group.getDomain() == groupDomain;
  if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type))
    return service.getContract() == randomContract;
  return false;
}

enum class Kind {
  Unsupported,
  Exec,
  IndexConstant,
  IndexEqual,
  FieldConstant,
  Add,
  Subtract,
  Multiply,
  Equal,
  GroupIdentity,
  GroupAdd,
  GroupScale,
  GroupEqual,
  Restrict,
  Exchange,
  Draw,
  Statement,
  BoolConstant,
  And,
  Or,
  Xor,
  Compare,
  Select,
  At,
  Call,
  Apply,
  ProtocolApply,
  ProtocolRepeat,
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

// Independent of the exporter and native operation catalogue. Resolve every
// declaration and occurrence before evaluation; the evaluator receives only
// a closed primitive and its checked literal, never an arbitrary helper name.
enum class Primitive {
  Constant,
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Equal,
  Less,
  Empty,
  Length,
  Sum,
  Split,
  Append,
  VectorEqual,
  FieldEqual
};
struct PrimitiveSpec {
  StringLiteral operation, contract, inputs, outputs;
  Primitive primitive;
  bool field;
};
constexpr PrimitiveSpec primitiveSpecs[] = {
    {"algebra.exec.index_constant", "index.constant", "", "i",
     Primitive::Constant, false},
    {"algebra.exec.index_add", "index.add", "ii", "i", Primitive::Add, false},
    {"algebra.exec.index_sub", "index.sub", "ii", "i", Primitive::Sub, false},
    {"algebra.exec.index_mul", "index.mul", "ii", "i", Primitive::Mul, false},
    {"algebra.exec.index_div", "index.div", "ii", "i", Primitive::Div, false},
    {"algebra.exec.index_mod", "index.mod", "ii", "i", Primitive::Mod, false},
    {"algebra.exec.index_equal", "index.equal", "ii", "b", Primitive::Equal,
     false},
    {"algebra.exec.index_less", "index.less", "ii", "b", Primitive::Less,
     false},
    {"algebra.exec.vector_empty", "vector.empty", "", "v", Primitive::Empty,
     true},
    {"algebra.exec.vector_length", "vector.length", "v", "i", Primitive::Length,
     true},
    {"algebra.exec.vector_sum", "vector.sum", "v", "f", Primitive::Sum, true},
    {"algebra.exec.vector_split", "vector.split", "v", "vv", Primitive::Split,
     true},
    {"algebra.exec.vector_append", "vector.append", "vf", "v",
     Primitive::Append, true},
    {"algebra.exec.vector_equal", "vector.equal", "vv", "b",
     Primitive::VectorEqual, true},
    {"algebra.exec.field_equal", "field.equal", "ff", "b",
     Primitive::FieldEqual, true},
};
struct CheckedPrimitive {
  Primitive primitive;
  uint64_t literal = 0;
};
using PrimitiveMap = llvm::DenseMap<Operation *, CheckedPrimitive>;

enum class PreparationKind { Realize, Map };
struct CheckedPreparation {
  PreparationKind kind;
  func::FuncOp helper;
  SmallVector<bool> rowwise;
};
using PreparationMap = llvm::DenseMap<Operation *, CheckedPreparation>;

bool primitivePorts(TypeRange types, StringRef ports) {
  if (types.size() != ports.size())
    return false;
  for (auto [type, port] : llvm::zip(types, ports)) {
    bool valid = port == 'i'   ? type.isUnsignedInteger(64)
                 : port == 'b' ? type.isSignlessInteger(1)
                 : port == 'v' ? isa<algebra::FieldVectorType>(type)
                               : isa<algebra::FieldType>(type);
    if (!valid || !valueType(type))
      return false;
  }
  return true;
}

Kind kind(Operation &op) {
  for (const auto &spec : primitiveSpecs)
    if (op.getName().getStringRef() == spec.operation)
      return Kind::Exec;
  return llvm::StringSwitch<Kind>(op.getName().getStringRef())
      .Case("data.index", Kind::IndexConstant)
      .Case("data.index_equal", Kind::IndexEqual)
      .Case("algebra.constant", Kind::FieldConstant)
      .Case("algebra.field_add", Kind::Add)
      .Case("algebra.field_subtract", Kind::Subtract)
      .Case("algebra.field_multiply", Kind::Multiply)
      .Case("algebra.field_equal", Kind::Equal)
      .Case("algebra.group_identity", Kind::GroupIdentity)
      .Case("algebra.group_add", Kind::GroupAdd)
      .Case("algebra.group_scale", Kind::GroupScale)
      .Case("algebra.group_equal", Kind::GroupEqual)
      .Case("protocol.restrict_roles", Kind::Restrict)
      .Case("protocol.exchange", Kind::Exchange)
      .Case("protocol.query", Kind::Draw)
      .Case("protocol.statement", Kind::Statement)
      .Cases({"arith.constant", "local.bool_constant"}, Kind::BoolConstant)
      .Case("arith.andi", Kind::And)
      .Case("arith.ori", Kind::Or)
      .Case("arith.xori", Kind::Xor)
      .Case("arith.cmpi", Kind::Compare)
      .Case("arith.select", Kind::Select)
      .Case("data.bounded_at", Kind::At)
      .Case("func.call", Kind::Call)
      .Case("local.apply", Kind::Apply)
      .Case("protocol.apply", Kind::ProtocolApply)
      .Case("protocol.repeat", Kind::ProtocolRepeat)
      .Case("protocol.local_call", Kind::LocalCall)
      .Case("algebra.finite_fold", Kind::Fold)
      .Case("local.if", Kind::If)
      .Case("local.for", Kind::For)
      .Case("protocol.guard", Kind::Guard)
      .Cases({"func.return", "local.return", "protocol.return"}, Kind::Return)
      .Cases({"local.yield", "protocol.yield"}, Kind::Yield)
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
    if (!json::isUTF8(text.getValue()))
      return error("structured-reference-unsupported", "invalid UTF-8");
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
  llvm::DenseMap<Operation *, const PrimitiveSpec *> bindings;
  PrimitiveMap primitives;
  PreparationMap preparations;
  llvm::StringSet<> sites;

  Error binding(Operation &op) {
    if (auto failure = attributes(
            op, {"sym_name", "contract", "arguments", "implementation"}))
      return failure;
    auto name = op.getAttrOfType<StringAttr>("sym_name");
    auto contract = op.getAttrOfType<StringAttr>("contract");
    auto arguments = op.getAttrOfType<ArrayAttr>("arguments");
    auto implementation = op.getAttrOfType<StringAttr>("implementation");
    auto alpha = [](char c) {
      return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
    };
    if (!name || name.getValue().empty() || name.getValue().size() > 256 ||
        !alpha(name.getValue().front()) ||
        !llvm::all_of(name.getValue(),
                      [&](char c) {
                        return alpha(c) || (c >= '0' && c <= '9') || c == '.' ||
                               c == '-';
                      }) ||
        !contract || !arguments || !implementation || op.getNumOperands() ||
        op.getNumResults() || op.getNumRegions())
      return error("structured-reference-binding");
    if (!implementation.getValue().empty())
      return error("structured-reference-implementation");
    for (const auto &spec : primitiveSpecs) {
      if (contract.getValue() != spec.contract)
        continue;
      if (spec.field
              ? (arguments.size() != 1 ||
                 arguments[0] != StringAttr::get(op.getContext(), fieldDomain))
              : !arguments.empty())
        return error("structured-reference-binding", "domain arguments");
      bindings[&op] = &spec;
      return Error::success();
    }
    return error("structured-reference-binding", "unsupported contract");
  }

  Error execution(Operation &op, Operation &owner) {
    if (auto failure = attributes(op, {"binding", "parameters", "site"}))
      return failure;
    auto name = op.getAttrOfType<FlatSymbolRefAttr>("binding");
    auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
    auto site = op.getAttrOfType<StringAttr>("site");
    auto found =
        bindings.find(name ? symbols.lookup(name.getValue()) : nullptr);
    if (!isa<local::FuncOp>(owner) || !site || site.getValue().empty() ||
        found == bindings.end() || !parameters)
      return error("structured-reference-binding", "owner, reference or site");
    const auto &spec = *found->second;
    if (op.getName().getStringRef() != spec.operation ||
        !primitivePorts(op.getOperandTypes(), spec.inputs) ||
        !primitivePorts(op.getResultTypes(), spec.outputs))
      return error("structured-reference-binding", "operation or ports");
    CheckedPrimitive checked{spec.primitive};
    bool constant = spec.primitive == Primitive::Constant;
    if (parameters.size() != (constant ? 1u : 0u))
      return error("structured-reference-binding", "parameters");
    if (constant) {
      auto text = dyn_cast<StringAttr>(parameters[0]);
      if (!text)
        return error("structured-reference-binding", "literal type");
      auto parsed =
          decimal(text.getValue(), false, "structured-reference-binding");
      if (!parsed)
        return parsed.takeError();
      checked.literal = parsed->getZExtValue();
    }
    primitives.try_emplace(&op, checked);
    return Error::success();
  }

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
           kind(op) == Kind::Apply &&
           isa<local::FiniteFoldOp, local::RealizeOp, algebra::MapRealizeOp>(
               target))))
      return error("structured-reference-symbol", name.getValue());
    dependencies[&owner].push_back(target);
    if (attribute == "callee") {
      if ((kind(op) == Kind::Apply && !isa<local::FuncOp>(owner)) ||
          (kind(op) == Kind::LocalCall &&
           !isa<protocol_ir::MathematicalOp>(owner)) ||
          (kind(op) == Kind::Call &&
           (!isa<func::FuncOp, protocol_ir::MathematicalOp>(owner) ||
            !cast<func::FuncOp>(target).isPrivate())))
        return error("structured-reference-symbol", "call owner or kind");
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

  Error preparation(Operation &op) {
    bool mapped = isa<algebra::MapRealizeOp>(op);
    StringRef code = mapped ? "structured-reference-map"
                            : "structured-reference-realization";
    SmallVector<StringRef> allowed{"sym_name", "function_type", "helper"};
    if (mapped)
      allowed.push_back("rowwise");
    if (auto failure = attributes(op, allowed))
      return failure;
    if (op.getNumOperands() || op.getNumResults() || op.getNumRegions())
      return error(code, "declaration shape");
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>("helper");
    auto helper =
        ref ? dyn_cast_or_null<func::FuncOp>(symbols.lookup(ref.getValue()))
            : func::FuncOp{};
    if (!helper || !helper.isPrivate() || helper.isExternal() ||
        helper->getParentOp() != op.getParentOp())
      return error(code, "private sibling Math helper");
    CheckedPreparation checked{
        mapped ? PreparationKind::Map : PreparationKind::Realize, helper, {}};
    auto type = signature(op), scalar = helper.getFunctionType();
    if (mapped) {
      auto mask = op.getAttrOfType<DenseBoolArrayAttr>("rowwise");
      if (!mask || mask.size() != type.getNumInputs() ||
          !llvm::is_contained(mask.asArrayRef(), true) ||
          type.getNumResults() != 1 ||
          !primitivePorts(type.getResults(), "v") ||
          scalar.getNumInputs() != type.getNumInputs() ||
          !primitivePorts(scalar.getResults(), "f"))
        return error(code, "root ABI or row mask");
      for (unsigned i = 0; i < type.getNumInputs(); ++i) {
        bool row = mask[i];
        if (!primitivePorts(TypeRange{type.getInput(i)}, row ? "v" : "f") ||
            !primitivePorts(TypeRange{scalar.getInput(i)}, "f"))
          return error(code, "lifted input ABI");
        checked.rowwise.push_back(row);
      }
    } else if (type != scalar) {
      return error(code, "full realization ABI");
    }
    dependencies[&op].push_back(helper);
    preparations.try_emplace(&op, std::move(checked));
    return Error::success();
  }

  Error preparationClosures() {
    // Separate total and ring caches: passing the former cannot authorize the
    // latter. Graph cycles/depth and all ordinary bodies were checked first.
    llvm::DenseSet<Operation *> total, ring;
    for (Operation &declaration : unit.getBody().front()) {
      auto found = preparations.find(&declaration);
      if (found == preparations.end())
        continue;
      bool mapped = found->second.kind == PreparationKind::Map;
      auto &visited = mapped ? ring : total;
      StringRef code = mapped ? "structured-reference-map"
                              : "structured-reference-realization";
      SmallVector<Operation *> pending{found->second.helper};
      while (!pending.empty()) {
        auto *current = pending.pop_back_val();
        if (!visited.insert(current).second)
          continue;
        auto helper = dyn_cast<func::FuncOp>(current);
        if (!helper || !helper.isPrivate() || helper.isExternal() ||
            helper->getParentOp() != unit.getOperation())
          return error(code, "private Math closure");
        auto premises = helper->getAttrOfType<ArrayAttr>("data.preconditions");
        if (premises && !premises.empty())
          return error(code, "nonempty helper preconditions");
        if (mapped) {
          auto type = helper.getFunctionType();
          for (Type port :
               llvm::concat<const Type>(type.getInputs(), type.getResults()))
            if (!primitivePorts(TypeRange{port}, "f"))
              return error(code, "non-scalar closure port");
        }
        for (Operation &op : helper.getBody().front()) {
          Kind operation = kind(op);
          if (operation == Kind::Call) {
            pending.push_back(
                symbols.lookup(cast<func::CallOp>(op).getCallee()));
            continue;
          }
          bool allowed =
              operation == Kind::FieldConstant || operation == Kind::Add ||
              operation == Kind::Subtract || operation == Kind::Multiply ||
              operation == Kind::Return;
          if (!mapped)
            allowed |= llvm::is_contained(
                ArrayRef<Kind>{Kind::Equal, Kind::GroupIdentity, Kind::GroupAdd,
                               Kind::GroupScale, Kind::GroupEqual,
                               Kind::IndexConstant, Kind::IndexEqual,
                               Kind::BoolConstant, Kind::And, Kind::Or,
                               Kind::Xor, Kind::Compare, Kind::Select},
                operation);
          if (!allowed || op.getNumRegions())
            return error(code, op.getName().getStringRef());
        }
      }
    }
    return Error::success();
  }

  Error instruction(Operation &op, Operation &owner) {
    Kind code = kind(op);
    if (code == Kind::Unsupported || code == Kind::Elements ||
        code == Kind::Indices || code == Kind::DomainYield)
      return error("structured-reference-unsupported",
                   op.getName().getStringRef());
    if (op.getNumRegions() !=
        (code == Kind::If                                    ? 2u
         : code == Kind::For || code == Kind::ProtocolRepeat ? 1u
                                                             : 0u))
      return error("structured-reference-unsupported", "region count");
    for (Type type : op.getOperandTypes())
      if (!valueType(type) ||
          (isa<protocol_ir::ServiceReferenceType>(type) && code != Kind::Draw &&
           code != Kind::ProtocolApply && code != Kind::ProtocolRepeat))
        return error("structured-reference-unsupported", "operand type");
    for (Type type : op.getResultTypes())
      if (!valueType(type) || isa<protocol_ir::ServiceReferenceType>(type))
        return error("structured-reference-unsupported", "result type");
    switch (code) {
    case Kind::ProtocolRepeat: {
      if (auto failure = attributes(
              op, {"site", "carried", "maximum", "roles", "carried_roles"}))
        return failure;
      auto repeat = cast<protocol_ir::RepeatOp>(op);
      // These I64Attr getters are unsigned: bounds and arity reject negative
      // encodings. Native formation already checked nested rosters/state
      // scopes.
      if (!isa<protocol_ir::MathematicalOp>(owner) ||
          repeat.getMaximum() > maxLoopBound ||
          repeat.getCarried() != op.getNumResults() ||
          op.getNumOperands() <= op.getNumResults() ||
          !op.getOperand(0).getType().isUnsignedInteger(64) ||
          !llvm::hasSingleElement(repeat.getBody()))
        return error("structured-reference-signature", "protocol repeat");
      Block &body = repeat.getBody().front();
      if (body.empty() || body.getArgumentTypes() != op.getOperandTypes() ||
          !isa<protocol_ir::ProtocolYieldOp>(body.back()) ||
          body.back().getOperandTypes() != op.getResultTypes())
        return error("structured-reference-signature", "protocol callback");
      break;
    }
    case Kind::ProtocolApply:
      return application(op, owner);
    case Kind::Exec:
      return execution(op, owner);
    case Kind::IndexConstant:
    case Kind::IndexEqual: {
      bool constant = code == Kind::IndexConstant;
      if (!isa<func::FuncOp, protocol_ir::MathematicalOp>(owner) ||
          !primitivePorts(op.getOperandTypes(), constant ? "" : "ii") ||
          !primitivePorts(op.getResultTypes(), constant ? "i" : "b"))
        return error("structured-reference-signature", "pure index operation");
      if (auto failure = attributes(op, constant ? ArrayRef<StringRef>{"value"}
                                                 : ArrayRef<StringRef>{}))
        return failure;
      if (constant) {
        auto parsed = decimal(cast<data::IndexOp>(op).getValue(), false,
                              "structured-reference-unsupported");
        if (!parsed)
          return parsed.takeError();
      }
      break;
    }
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
    case Kind::Restrict:
      return attributes(op, {"roles"});
    case Kind::Exchange:
      return attributes(op, {"site", "sender", "receiver"});
    case Kind::Draw:
      if (cast<protocol_ir::QueryOp>(op).getMethod() != "draw" ||
          op.getNumOperands() != 1 || op.getNumResults() != 1 ||
          !isa<algebra::FieldType>(op.getResult(0).getType()))
        return error("structured-reference-unsupported", "service method");
      if (auto failure =
              serviceOrigin(op.getOperand(0), owner,
                            cast<protocol_ir::QueryOp>(op).getOwner()))
        return failure;
      return attributes(op, {"site", "owner", "method"});
    case Kind::Statement:
      return attributes(op, {"relation", "selectors", "acceptance"});
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

  Error serviceOrigin(Value value, Operation &owner, StringRef expectedOwner) {
    auto protocol = dyn_cast<protocol_ir::MathematicalOp>(owner);
    auto argument = dyn_cast<BlockArgument>(value);
    // Only immutable service captures carry lexical entry-port identity.
    // Index and state arguments never acquire the origin of their initials.
    unsigned depth = 0;
    while (argument &&
           isa<protocol_ir::RepeatOp>(argument.getOwner()->getParentOp())) {
      auto repeat =
          cast<protocol_ir::RepeatOp>(argument.getOwner()->getParentOp());
      unsigned position = argument.getArgNumber();
      if (++depth > maxDepth || position <= repeat.getNumResults() ||
          position >= repeat.getNumOperands() ||
          !isa<protocol_ir::ServiceReferenceType>(argument.getType()))
        return error("structured-reference-application", "service capture");
      argument = dyn_cast<BlockArgument>(repeat.getInputs()[position]);
    }
    if (!protocol || !argument ||
        argument.getOwner() != &protocol.getBody().front())
      return error("structured-reference-application", "lexical service input");
    auto scope =
        cast<ArrayAttr>(protocol.getInputRoles()[argument.getArgNumber()]);
    if (scope.size() != 1 ||
        cast<StringAttr>(scope[0]).getValue() != expectedOwner)
      return error("structured-reference-application", "service owner");
    return Error::success();
  }

  Error application(Operation &op, Operation &owner) {
    if (auto failure = attributes(op, {"callee", "roles", "site"}))
      return failure;
    auto caller = dyn_cast<protocol_ir::MathematicalOp>(owner);
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>("callee");
    auto callee =
        ref ? symbols.lookup<protocol_ir::MathematicalOp>(ref.getValue())
            : protocol_ir::MathematicalOp{};
    if (!caller || !callee || callee->getParentOp() != caller->getParentOp())
      return error("structured-reference-symbol",
                   "protocol application target");
    auto roles = op.getAttrOfType<ArrayAttr>("roles");
    auto type = callee.getFunctionType();
    if (!roles || roles.size() != callee.getRoles().size() ||
        op.getOperandTypes() != type.getInputs() ||
        op.getResultTypes() != type.getResults() || op.getNumRegions())
      return error("structured-reference-application", "full protocol ABI");
    llvm::DenseSet<Attribute> seen;
    for (Attribute role : roles)
      if (!isa<StringAttr>(role) ||
          !llvm::is_contained(caller.getRoles(), role) ||
          !seen.insert(role).second)
        return error("structured-reference-application", "role injection");
    if (!callee.getBody().front().getOps<protocol_ir::StatementOp>().empty())
      return error("structured-reference-application", "entry statement");
    for (auto [i, operand] : llvm::enumerate(op.getOperands())) {
      if (!isa<protocol_ir::ServiceReferenceType>(operand.getType()))
        continue;
      auto scope = cast<ArrayAttr>(callee.getInputRoles()[i]);
      if (scope.size() != 1)
        return error("structured-reference-application", "service scope");
      auto position = llvm::find(callee.getRoles(), scope[0]);
      if (position == callee.getRoles().end())
        return error("structured-reference-application", "service role");
      auto mapped =
          cast<StringAttr>(roles[position - callee.getRoles().begin()]);
      if (auto failure = serviceOrigin(operand, owner, mapped.getValue()))
        return failure;
    }
    dependencies[&owner].push_back(callee);
    return Error::success();
  }

  Error effectiveSites() {
    // A separate bounded walk of admitted original SSA, not an exporter receipt
    // or a production-expanded body. Native formation owns conservative
    // budgets.
    struct Frame {
      Block *body;
      std::string prefix;
      unsigned applicationDepth;
      unsigned repeatDepth;
    };
    uint64_t remainingVisits = maxStaticVisits,
             remainingBytes = maxStaticSiteBytes;
    for (auto root :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      llvm::StringSet<> effective;
      SmallVector<Frame> pending{{&root.getBody().front(), {}, 1, 0}};
      while (!pending.empty()) {
        Frame frame = pending.pop_back_val();
        if (frame.applicationDepth > maxDepth || frame.repeatDepth > maxDepth)
          return error("structured-reference-capacity",
                       "application or repeat depth");
        for (Operation &op : *frame.body) {
          if (!remainingVisits)
            return error("structured-reference-capacity", "static visits");
          --remainingVisits;
          auto site = op.getAttrOfType<StringAttr>("site");
          if (!site)
            continue;
          auto digits = std::to_string(frame.prefix.size());
          size_t prefixBytes = frame.prefix.empty()
                                   ? 0
                                   : 8 + digits.size() + frame.prefix.size();
          if (prefixBytes > maxEffectiveSiteBytes ||
              site.size() > maxEffectiveSiteBytes - prefixBytes)
            return error("structured-reference-capacity", "generated site");
          size_t size = prefixBytes + site.size();
          if (size > remainingBytes)
            return error("structured-reference-capacity", "static site bytes");
          remainingBytes -= size;
          std::string label;
          if (!frame.prefix.empty())
            label = "apply_" + digits + "_" + frame.prefix + "_";
          label.append(site.getValue().data(), site.size());
          if (kind(op) == Kind::ProtocolApply) {
            auto call = cast<protocol_ir::ApplyOp>(op);
            pending.push_back(
                {&symbols.lookup<protocol_ir::MathematicalOp>(call.getCallee())
                      .getBody()
                      .front(),
                 std::move(label), frame.applicationDepth + 1,
                 frame.repeatDepth});
          } else if (!effective.insert(label).second) {
            return error("structured-reference-site", "expanded collision");
          }
          if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op))
            pending.push_back({&repeat.getBody().front(), frame.prefix,
                               frame.applicationDepth, frame.repeatDepth + 1});
        }
      }
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
      if (auto site = op.getAttrOfType<StringAttr>("site"))
        if (site.getValue().empty() || !sites.insert(site.getValue()).second)
          return error("structured-reference-unsupported", "execution site");
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
    // Height counts reference edges, with a leaf at zero. Keep this separate
    // from the interpreter's one-based invocation/region depth budget.
    unsigned result = 0;
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
  const PrimitiveMap &checkedPrimitives() const { return primitives; }
  const PreparationMap &checkedPreparations() const { return preparations; }

  Error check() {
    unsigned domains = 0, definitions = 0, relations = 0;
    if (auto failure = attributes(*unit, {"profile"}))
      return failure;
    llvm::StringSet<> names;
    // Pre-admit even unused declarations, including forward references. Binding
    // rows are metadata, not graph nodes or callable function signatures.
    for (Operation &op : unit.getBody().front()) {
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name || !names.insert(name.getValue()).second)
        return error("structured-reference-symbol");
      if (isa<local::OperationBindingOp>(op)) {
        if (bindings.size() == 128)
          return error("structured-reference-capacity", "bindings");
        if (auto failure = binding(op))
          return failure;
      }
    }
    for (Operation &op : unit.getBody().front()) {
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name || name.getValue().empty())
        return error("structured-reference-symbol");
      for (auto attr : op.getAttrs())
        if (auto failure = attributeBounds(attr.getValue()))
          return failure;
      if (auto visibility = op.getAttrOfType<StringAttr>("sym_visibility"))
        if (visibility != "private" && visibility != "public")
          return error("structured-reference-unsupported", "visibility");
      if (isa<local::OperationBindingOp>(op))
        continue;
      if (auto declaration = dyn_cast<relation::DeclareOp>(op)) {
        if (++relations > 128)
          return error("structured-reference-capacity", "relations");
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "kind", "key",
                                "revision", "signature", "purposes"}))
          return failure;
        auto type = declaration.getSignature();
        if (type.getNumInputs() > maxSignature ||
            type.getNumResults() > maxSignature)
          return error("structured-reference-capacity", "relation signature");
        for (Type t :
             llvm::concat<const Type>(type.getInputs(), type.getResults()))
          if (!valueType(t) || isa<protocol_ir::ServiceReferenceType>(t))
            return error("structured-reference-unsupported", "relation type");
        continue;
      }
      bool isDomain = isa<data::DomainOp>(op);
      bool finite = isa<local::FiniteFoldOp>(op);
      bool prepared = isa<local::RealizeOp, algebra::MapRealizeOp>(op);
      if (!isDomain && !finite && !prepared &&
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
        if (!valueType(input) ||
            (isa<protocol_ir::ServiceReferenceType>(input) &&
             !isa<protocol_ir::MathematicalOp>(op)))
          return error("structured-reference-unsupported", "input type");
      if (!isDomain)
        for (Type output : type.getResults())
          if (!valueType(output) ||
              isa<protocol_ir::ServiceReferenceType>(output))
            return error("structured-reference-unsupported", "output type");
      if (isDomain) {
        if (auto failure = domain(op))
          return failure;
        continue;
      }
      if (prepared) {
        if (++operations > maxOperations)
          return error("structured-reference-capacity",
                       "preparation instructions");
        if (auto failure = preparation(op))
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
        if (protocol.getRoles().empty() || protocol.getRoles().size() > 16)
          return error("structured-reference-unsupported", "role count");
      } else if (isa<func::FuncOp>(op)) {
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "function_type",
                                "data.preconditions"}))
          return failure;
        if (auto conditions =
                op.getAttrOfType<ArrayAttr>("data.preconditions")) {
          if (conditions.size() > maxSignature)
            return error("structured-reference-capacity", "preconditions");
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
        }
      } else if (auto failure =
                     attributes(op, {"sym_name", "sym_visibility",
                                     "function_type", "logical_origin"})) {
        return failure;
      }
      if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)) ||
          op.getRegion(0).front().empty())
        return error("structured-reference-unsupported", "function body");
      sites.clear();
      if (auto failure = block(op.getRegion(0).front(), op, 1))
        return failure;
    }
    for (Operation &op : unit.getBody().front()) {
      auto checked = height(&op, 0);
      if (!checked)
        return checked.takeError();
    }
    if (auto failure = preparationClosures())
      return failure;
    if (auto failure = effectiveSites())
      return failure;
    llvm::DenseSet<Operation *> checked;
    std::function<Error(Operation *)> scalarMath =
        [&](Operation *function) -> Error {
      if (!checked.insert(function).second)
        return Error::success();
      SmallVector<Block *> pending{&function->getRegion(0).front()};
      while (!pending.empty()) {
        for (Operation &op : *pending.pop_back_val()) {
          if (kind(op) == Kind::Fold || kind(op) == Kind::At)
            return error("structured-reference-unsupported",
                         "multi-role Math finite work");
          if (kind(op) == Kind::Call)
            if (auto failure = scalarMath(
                    symbols.lookup(cast<func::CallOp>(op).getCallee())))
              return failure;
          for (Region &region : op.getRegions())
            pending.push_back(&region.front());
        }
      }
      return Error::success();
    };
    for (auto protocol :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>())
      if (protocol.getRoles().size() > 1)
        if (auto failure = scalarMath(protocol))
          return failure;
    return Error::success();
  }
};

using Vector = std::shared_ptr<const std::vector<APInt>>;
struct Domain {
  Vector container;
  bool indices;
};
// monostate is an absent participant component, never a missing SSA binding.
using Datum =
    std::variant<std::monostate, bool, uint64_t, APInt, Vector, Domain>;
using Values = std::vector<Datum>;
bool present(const Datum &value) {
  return !std::holds_alternative<std::monostate>(value);
}
struct Outcome {
  Kind terminator = Kind::Return;
  Values values;
  std::string reason;
  std::string site = {};
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
  bool field = isa<algebra::FieldType, algebra::GroupType>(type);
  auto value = decimal(*text, field, "structured-reference-input");
  if (!value)
    return value.takeError();
  if (field)
    return Datum(std::move(*value));
  if (type.isUnsignedInteger(64) ||
      isa<protocol_ir::ServiceReferenceType>(type))
    return Datum(value->getZExtValue());
  return error("structured-reference-unsupported", "input type");
}

std::string digits(const APInt &value) {
  SmallString<80> text;
  value.toString(text, 10, false);
  return text.str().str();
}

Expected<json::Value> encode(const Datum &value) {
  if (!present(value))
    return json::Value(nullptr);
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
  if (!present(value))
    return true;
  if (type.isSignlessInteger(1))
    return std::holds_alternative<bool>(value);
  if (type.isUnsignedInteger(64) ||
      isa<protocol_ir::ServiceReferenceType>(type))
    return std::holds_alternative<uint64_t>(value);
  if (isa<algebra::FieldType, algebra::GroupType>(type))
    return std::holds_alternative<APInt>(value);
  if (isa<algebra::FieldVectorType>(type))
    return std::holds_alternative<Vector>(value);
  return isa<data::DomainType>(type) && std::holds_alternative<Domain>(value);
}

// Immutable per-invocation configuration. Root self and replay state never move
// into a child; closed helper bodies receive no protocol configuration.
struct ProtocolContext {
  SmallVector<std::pair<StringRef, StringRef>> roles;
  std::optional<std::string> applicationPrefix;

  StringRef role(StringRef local) const {
    for (const auto &[source, root] : roles)
      if (source == local)
        return root;
    llvm_unreachable("admitted protocol role must have a root mapping");
  }

  std::string site(StringRef raw) const {
    // The empty string is a synthetic siteless mark, never an apply boundary.
    if (raw.empty() || !applicationPrefix)
      return raw.str();
    const auto &prefix = *applicationPrefix;
    return "apply_" + std::to_string(prefix.size()) + "_" + prefix + "_" +
           raw.str();
  }
};

class Reference {
  SymbolTable symbols;
  const PrimitiveMap &primitives;
  const PreparationMap &preparations;
  uint64_t steps = 0;
  uint64_t capacity = maxSteps;
  bool open = false;
  StringRef self;
  const json::Array *replies = nullptr;
  size_t replyPosition = 0;
  json::Array records;
  size_t recordBytes = 2;

  Error record(json::Array event) {
    json::Value value(std::move(event));
    size_t size = printJson(value).size() + (records.empty() ? 0 : 1);
    if (size > 1024 * 1024 - recordBytes)
      return error("structured-reference-capacity", "replay record bytes");
    recordBytes += size;
    records.push_back(std::move(value));
    return Error::success();
  }

  Error tick(unsigned depth) {
    if (depth > maxDepth || ++steps > capacity)
      return error("structured-reference-capacity",
                   "evaluation steps or depth");
    return Error::success();
  }

  Error vectorWork(size_t count) {
    // Linear vector work is observer fuel, not a source stop or a native
    // backend allocation law. Check before copying or traversing elements.
    if (count > maxVector || count > capacity - steps)
      return error("structured-reference-capacity", "vector work or length");
    steps += count;
    return Error::success();
  }

  Error argumentWork(size_t count) {
    // Tuple construction is work, not a vector-length bound. In particular,
    // arity times rows may exceed maxVector without exceeding observer fuel.
    if (count > capacity - steps)
      return error("structured-reference-capacity", "map argument work");
    steps += count;
    return Error::success();
  }

  Expected<Outcome> execute(Operation &op, ArrayRef<Datum> args) {
    auto found = primitives.find(&op);
    if (found == primitives.end())
      return error("structured-reference-binding", "unchecked execution");
    Primitive code = found->second.primitive;
    Outcome result;
    switch (code) {
    case Primitive::Constant:
      result.values.emplace_back(found->second.literal);
      break;
    case Primitive::Add:
    case Primitive::Sub:
    case Primitive::Mul:
    case Primitive::Div:
    case Primitive::Mod:
    case Primitive::Equal:
    case Primitive::Less: {
      uint64_t a = std::get<uint64_t>(args[0]), b = std::get<uint64_t>(args[1]);
      constexpr uint64_t maximum = std::numeric_limits<uint64_t>::max();
      if ((code == Primitive::Add && b > maximum - a) ||
          (code == Primitive::Sub && a < b) ||
          (code == Primitive::Mul && b && a > maximum / b) ||
          ((code == Primitive::Div || code == Primitive::Mod) && b == 0))
        return stopped(op, "refused");
      if (code == Primitive::Equal || code == Primitive::Less)
        result.values.emplace_back(code == Primitive::Equal ? a == b : a < b);
      else
        result.values.emplace_back(code == Primitive::Add   ? a + b
                                   : code == Primitive::Sub ? a - b
                                   : code == Primitive::Mul ? a * b
                                   : code == Primitive::Div ? a / b
                                                            : a % b);
      break;
    }
    case Primitive::Empty:
      result.values.emplace_back(
          Vector(std::make_shared<std::vector<APInt>>()));
      break;
    case Primitive::Length:
      // All reference vectors are bounded by maxVector, well within u64.
      // Logical unrepresentable length is exhausted, not a shape refusal;
      // this bounded observer cannot reach that semantic branch.
      result.values.emplace_back(uint64_t(std::get<Vector>(args[0])->size()));
      break;
    case Primitive::Sum: {
      const auto &items = *std::get<Vector>(args[0]);
      if (auto failure = vectorWork(items.size()))
        return failure;
      APInt sum(512, 0);
      for (const APInt &item : items)
        sum = (sum + item).urem(modulus());
      result.values.emplace_back(std::move(sum));
      break;
    }
    case Primitive::Split: {
      const auto &items = *std::get<Vector>(args[0]);
      if (items.empty() || items.size() % 2)
        return stopped(op, "refused");
      if (auto failure = vectorWork(items.size()))
        return failure;
      auto middle = items.begin() + items.size() / 2;
      result.values.emplace_back(
          Vector(std::make_shared<std::vector<APInt>>(items.begin(), middle)));
      result.values.emplace_back(
          Vector(std::make_shared<std::vector<APInt>>(middle, items.end())));
      break;
    }
    case Primitive::Append: {
      const auto &items = *std::get<Vector>(args[0]);
      // Guard addition and allocation before constructing the result.
      if (items.size() >= maxVector)
        return error("structured-reference-capacity", "append length");
      if (auto failure = vectorWork(items.size() + 1))
        return failure;
      auto output = std::make_shared<std::vector<APInt>>(items);
      output->push_back(std::get<APInt>(args[1]));
      result.values.emplace_back(Vector(std::move(output)));
      break;
    }
    case Primitive::VectorEqual: {
      const auto &a = *std::get<Vector>(args[0]),
                 &b = *std::get<Vector>(args[1]);
      if (a.size() == b.size())
        if (auto failure = vectorWork(a.size()))
          return failure;
      result.values.emplace_back(a == b);
      break;
    }
    case Primitive::FieldEqual:
      result.values.emplace_back(std::get<APInt>(args[0]) ==
                                 std::get<APInt>(args[1]));
      break;
    }
    return result;
  }

  Operation *target(Operation &op, StringRef attr) {
    auto name = op.getAttrOfType<FlatSymbolRefAttr>(attr);
    return name ? symbols.lookup(name.getValue()) : nullptr;
  }

  Expected<Outcome> invokeProtocol(protocol_ir::MathematicalOp callee,
                                   ArrayRef<Datum> args,
                                   const ProtocolContext &context,
                                   unsigned depth) {
    if (auto failure = tick(depth))
      return failure;
    auto type = callee.getFunctionType();
    if (args.size() != type.getNumInputs())
      return error("structured-reference-signature", "protocol arguments");
    for (auto [port, value] : llvm::zip(type.getInputs(), args))
      if (!matches(port, value))
        return error("structured-reference-signature",
                     "protocol argument type");
    if (!inScope(callee.getRoles(), &context))
      return Outcome{
          Kind::Return, Values(type.getNumResults(), std::monostate{}), {}};
    Values inputs(args.begin(), args.end());
    for (auto [i, scope] : llvm::enumerate(callee.getInputRoles()))
      if (!inScope(cast<ArrayAttr>(scope), &context))
        inputs[i] = std::monostate{};
    auto result = block(callee.getBody().front(), inputs, depth, &context);
    if (!result || result->stopped())
      return result;
    if (result->values.size() != type.getNumResults())
      return error("structured-reference-signature", "protocol results");
    for (auto [i, port, value] :
         llvm::enumerate(type.getResults(), result->values)) {
      if (!matches(port, value))
        return error("structured-reference-signature", "protocol result type");
      if (!inScope(cast<ArrayAttr>(callee.getOutputRoles()[i]), &context))
        value = std::monostate{};
    }
    return result;
  }

  Expected<Outcome> invoke(Operation *callee, ArrayRef<Datum> args,
                           unsigned depth, StringRef invocationSite = {}) {
    if (auto failure = tick(depth))
      return failure;
    if (!callee)
      return error("structured-reference-symbol");
    if (isa<protocol_ir::MathematicalOp>(callee))
      return error("structured-reference-symbol", "protocol context required");
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
        if (!present(args[bound.getIndexArg()]) ||
            !present(args[bound.getContainerArg()]))
          continue;
        if (std::get<uint64_t>(args[bound.getIndexArg()]) >=
            std::get<Vector>(args[bound.getContainerArg()])->size())
          return error("structured-reference-bounds", "helper precondition");
      }
    auto result = [&]() -> Expected<Outcome> {
      if (auto found = preparations.find(callee); found != preparations.end()) {
        const auto &checked = found->second;
        if (!llvm::all_of(args, present))
          return Outcome{Kind::Stop, {}, "incomplete", invocationSite.str()};
        if (checked.kind == PreparationKind::Realize)
          return invoke(checked.helper, args, depth + 1);
        return map(checked, args, depth, invocationSite);
      }
      if (isa<local::FiniteFoldOp>(callee))
        return fold(*callee, args, type.getNumResults(), depth);
      return block(callee->getRegion(0).front(), args, depth);
    }();
    if (!result || result->stopped())
      return result;
    if (result->values.size() != type.getNumResults())
      return error("structured-reference-signature", "call results");
    for (auto [type, value] : llvm::zip(type.getResults(), result->values))
      if (!matches(type, value))
        return error("structured-reference-signature", "call result type");
    return result;
  }

  Expected<Outcome> map(const CheckedPreparation &checked, ArrayRef<Datum> args,
                        unsigned depth, StringRef site) {
    std::optional<size_t> count;
    for (auto [argument, row] : llvm::zip(args, checked.rowwise)) {
      if (auto failure = tick(depth))
        return failure;
      if (!row)
        continue;
      size_t length = std::get<Vector>(argument)->size();
      // Every stored vector is <=4096: logical length >=2^64 is exhausted,
      // but cannot be represented by this bounded observer. Compare rows in
      // source order, including unused rows and the zero-length case.
      if (count && length != *count)
        return Outcome{Kind::Stop, {}, "refused", site.str()};
      count = length;
    }
    if (!count)
      return error("structured-reference-map", "unchecked row mask");
    if (auto failure = vectorWork(*count))
      return failure;
    auto output = std::make_shared<std::vector<APInt>>();
    output->reserve(*count);
    for (size_t i = 0; i < *count; ++i) {
      if (auto failure = argumentWork(args.size()))
        return failure;
      Values scalar;
      scalar.reserve(args.size());
      for (auto [argument, row] : llvm::zip(args, checked.rowwise))
        scalar.push_back(row ? Datum((*std::get<Vector>(argument))[i])
                             : argument);
      auto value = invoke(checked.helper, scalar, depth + 1);
      if (!value || value->stopped())
        return value;
      output->push_back(std::get<APInt>(value->values[0]));
    }
    return Outcome{Kind::Return, {Vector(std::move(output))}, {}};
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

  bool inScope(ArrayAttr scope,
               const ProtocolContext *context = nullptr) const {
    return llvm::any_of(scope, [&](Attribute role) {
      auto name = cast<StringAttr>(role).getValue();
      return self == (context ? context->role(name) : name);
    });
  }

  StringRef role(StringRef name, const ProtocolContext *context) const {
    return context ? context->role(name) : name;
  }

  Outcome absent(Operation &op) {
    return {Kind::Return, Values(op.getNumResults(), std::monostate{}), {}};
  }

  Outcome stopped(Operation &op, StringRef reason,
                  const ProtocolContext *context = nullptr) {
    auto site = op.getAttrOfType<StringAttr>("site");
    StringRef raw = site ? site.getValue() : StringRef{};
    return {
        Kind::Stop, {}, reason.str(), context ? context->site(raw) : raw.str()};
  }

  json::Array messageType(Type type) {
    if (type.isSignlessInteger(1))
      return json::Array{"bool"};
    if (type.isUnsignedInteger(64))
      return json::Array{"index"};
    if (auto field = dyn_cast<algebra::FieldType>(type))
      return json::Array{"field", field.getDomain()};
    if (auto group = dyn_cast<algebra::GroupType>(type))
      return json::Array{"group", group.getDomain()};
    return json::Array{"vector",
                       cast<algebra::FieldVectorType>(type).getDomain()};
  }

  Expected<Outcome> replay(Operation &op, json::Array action, Type replyType,
                           const ProtocolContext *context) {
    if (!open)
      return error("structured-reference-input", "open command required");
    json::Value request(std::move(action));
    if (auto failure = record(json::Array{"request", replyPosition, request}))
      return std::move(failure);
    if (replyPosition == replies->size())
      return stopped(op, "incomplete", context);
    const auto &reply = *(*replies)[replyPosition].getAsArray();
    const auto &response = *reply[2].getAsArray();
    if (reply[1] != request)
      return stopped(op, "refused", context);
    Outcome result;
    if (response.size() == 2 && response[0].getAsString() == "stop" &&
        response[1].getAsString() &&
        llvm::is_contained(ArrayRef<StringRef>{"reject", "abort", "exhausted",
                                               "incomplete", "refused"},
                           *response[1].getAsString())) {
      result = stopped(op, *response[1].getAsString(), context);
    } else if (!replyType && response.size() == 1 &&
               response[0].getAsString() == "unit") {
      result = Outcome{};
    } else if (replyType && response.size() == 2 &&
               response[0].getAsString() == "value") {
      auto value = decode(replyType, response[1]);
      if (!value) {
        // A malformed value is a refused reply; exhausting the reference's
        // resource bound remains a diagnostic, not a protocol stop.
        auto failure = handleErrors(value.takeError(), [](const Refusal &e) {
          return e.code == "structured-reference-input"
                     ? Error::success()
                     : error(e.code, e.detail);
        });
        if (failure)
          return std::move(failure);
        return stopped(op, "refused", context);
      }
      result.values.push_back(std::move(*value));
    } else {
      return stopped(op, "refused", context);
    }
    if (auto failure = record(json::Array{"reply", replyPosition, reply[2]}))
      return std::move(failure);
    ++replyPosition;
    return result;
  }

  Expected<Outcome> interaction(Operation &op, ArrayRef<Datum> args,
                                const ProtocolContext *context) {
    auto site = [&](StringRef raw) {
      return context ? context->site(raw) : raw.str();
    };
    if (auto exchange = dyn_cast<protocol_ir::ExchangeOp>(op)) {
      Type type = op.getResult(0).getType();
      auto sender = role(exchange.getSender(), context);
      auto receiver = role(exchange.getReceiver(), context);
      if (self == sender) {
        if (!present(args[0]))
          return stopped(op, "incomplete", context);
        auto value = encode(args[0]);
        if (!value)
          return value.takeError();
        auto result =
            replay(op,
                   json::Array{"send", site(exchange.getSite()), sender,
                               receiver, messageType(type), std::move(*value)},
                   {}, context);
        if (result && !result->stopped())
          result->values.push_back(args[0]);
        return result;
      }
      if (self == receiver)
        return replay(op,
                      json::Array{"receive", site(exchange.getSite()), sender,
                                  receiver, messageType(type)},
                      type, context);
      return absent(op);
    }
    auto query = cast<protocol_ir::QueryOp>(op);
    auto owner = role(query.getOwner(), context);
    if (self != owner)
      return absent(op);
    if (!present(args[0]))
      return stopped(op, "incomplete", context);
    return replay(
        op,
        json::Array{"draw", site(query.getSite()), owner, randomContract,
                    std::to_string(std::get<uint64_t>(args[0])), fieldDomain},
        op.getResult(0).getType(), context);
  }

  Expected<Outcome> evaluate(Operation &op, ArrayRef<Datum> args,
                             unsigned depth, const ProtocolContext *context) {
    Kind code = kind(op);
    switch (code) {
    case Kind::Exec:
      // Local execution sequences every operand even when all results are
      // discarded. It cannot use the pure absent-component propagation below.
      if (!llvm::all_of(args, present))
        return stopped(op, "incomplete", context);
      return execute(op, args);
    case Kind::Return:
    case Kind::Yield:
    case Kind::Condition:
    case Kind::DomainYield:
      return Outcome{code, Values(args.begin(), args.end()), {}};
    case Kind::Stop:
      return stopped(op, cast<local::StopOp>(op).getReason(), context);
    case Kind::Guard:
      if (role(op.getAttrOfType<StringAttr>("owner").getValue(), context) !=
          self)
        return Outcome{};
      if (!present(args[0]))
        return stopped(op, "incomplete", context);
      return std::get<bool>(args[0]) ? Outcome{}
                                     : stopped(op, "reject", context);
    case Kind::Call:
      // Do not sequence Math arguments: an ignored absent input is legal.
      return invoke(target(op, "callee"), args, depth + 1);
    case Kind::LocalCall:
      if (role(op.getAttrOfType<StringAttr>("role").getValue(), context) !=
          self)
        return absent(op);
      [[fallthrough]];
    case Kind::Apply:
      if (!llvm::all_of(args, present))
        return stopped(op, "incomplete", context);
      return invoke(
          target(op, "callee"), args, depth + 1,
          context
              ? context->site(op.getAttrOfType<StringAttr>("site").getValue())
              : op.getAttrOfType<StringAttr>("site").getValue().str());
    case Kind::ProtocolApply: {
      auto call = cast<protocol_ir::ApplyOp>(op);
      auto callee = cast<protocol_ir::MathematicalOp>(target(op, "callee"));
      ProtocolContext child;
      child.applicationPrefix = context->site(call.getSite());
      for (auto [source, replacement] :
           llvm::zip(callee.getRoles(), call.getRoles()))
        child.roles.emplace_back(
            cast<StringAttr>(source).getValue(),
            context->role(cast<StringAttr>(replacement).getValue()));
      return invokeProtocol(callee, args, child, depth + 1);
    }
    case Kind::ProtocolRepeat: {
      auto repeat = cast<protocol_ir::RepeatOp>(op);
      if (!inScope(repeat.getRoles(), context))
        return absent(op);
      if (!present(args[0]))
        return stopped(op, "incomplete", context);
      uint64_t count = std::get<uint64_t>(args[0]);
      if (count > uint64_t(repeat.getMaximum()))
        return stopped(op, "refused", context);
      size_t carried = op.getNumResults();
      auto initial = args.slice(1, carried);
      auto captures = args.drop_front(1 + carried);
      Outcome state{Kind::Return, Values(initial.begin(), initial.end()), {}};
      auto mask = [&]() {
        for (auto [i, scope] : llvm::enumerate(repeat.getCarriedRoles()))
          if (!inScope(cast<ArrayAttr>(scope), context))
            state.values[i] = std::monostate{};
      };
      mask();
      for (uint64_t index = 0; index < count; ++index) {
        if (auto failure = tick(depth))
          return failure;
        Values inputs{Datum(index)};
        llvm::append_range(inputs, state.values);
        llvm::append_range(inputs, captures);
        auto next = block(repeat.getBody().front(), inputs, depth + 1, context);
        if (!next || next->stopped())
          return next;
        if (next->terminator != Kind::Yield || next->values.size() != carried)
          return error("structured-reference-signature", "protocol yield");
        state.values = std::move(next->values);
        mask();
      }
      return state;
    }
    case Kind::Statement:
      return Outcome{}; // Retained metadata, not relation evaluation.
    case Kind::Restrict:
      return inScope(cast<protocol_ir::RestrictRolesOp>(op).getRoles(), context)
                 ? Outcome{Kind::Return, Values(args.begin(), args.end()), {}}
                 : absent(op);
    case Kind::Exchange:
    case Kind::Draw:
      return interaction(op, args, context);
    default:
      break;
    }
    if (!llvm::all_of(args, present))
      return absent(op);
    switch (code) {
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
    case Kind::IndexConstant: {
      auto parsed = decimal(cast<data::IndexOp>(op).getValue(), false,
                            "structured-reference-unsupported");
      if (!parsed)
        return parsed.takeError();
      result.values.emplace_back(parsed->getZExtValue());
      break;
    }
    case Kind::IndexEqual:
      result.values.emplace_back(std::get<uint64_t>(args[0]) ==
                                 std::get<uint64_t>(args[1]));
      break;
    case Kind::FieldConstant: {
      auto parsed = decimal(cast<algebra::ConstantFieldOp>(op).getValue(), true,
                            "structured-reference-unsupported");
      if (!parsed)
        return parsed.takeError();
      result.values.emplace_back(std::move(*parsed));
      break;
    }
    case Kind::GroupIdentity:
      result.values.emplace_back(APInt(512, 0));
      break;
    case Kind::BoolConstant:
      result.values.emplace_back(
          !cast<IntegerAttr>(op.getAttr("value")).getValue().isZero());
      break;
    case Kind::Add:
    case Kind::Subtract:
    case Kind::Multiply:
    case Kind::Equal:
    case Kind::GroupAdd:
    case Kind::GroupScale:
    case Kind::GroupEqual: {
      const APInt &a = std::get<APInt>(args[0]), &b = std::get<APInt>(args[1]);
      if (code == Kind::Equal || code == Kind::GroupEqual)
        result.values.emplace_back(a == b);
      // Both operands are < p < 2^255. 512 bits hold the full product and
      // the addition/subtraction intermediates before exact reduction.
      else if (code == Kind::Add || code == Kind::GroupAdd)
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

  Expected<Outcome> block(Block &body, ArrayRef<Datum> inputs, unsigned depth,
                          const ProtocolContext *context = nullptr) {
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
      auto result = evaluate(op, args, depth, context);
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
  Reference(Operation *unit, const PrimitiveMap &primitives,
            const PreparationMap &preparations)
      : symbols(unit), primitives(primitives), preparations(preparations) {}
  Expected<json::Value> run(protocol_ir::MathematicalOp source,
                            const json::Array &request, bool openRequest) {
    open = openRequest;
    const json::Array *arguments = &request;
    if (open) {
      if (request.size() != 5 ||
          request[0].getAsString() != "zkc.structured-open-request/0" ||
          !request[1].getAsString() || !request[2].getAsArray() ||
          !request[3].getAsArray() || !request[4].getAsUINT64())
        return error("structured-reference-input", "open request shape");
      self = *request[1].getAsString();
      arguments = request[2].getAsArray();
      replies = request[3].getAsArray();
      capacity = *request[4].getAsUINT64();
      if (!capacity || capacity > maxSteps || replies->size() > maxOperations)
        return error("structured-reference-capacity", "request capacity");
      for (const json::Value &reply : *replies) {
        auto row = reply.getAsArray();
        if (!row || row->size() != 3 || (*row)[0].getAsString() != "reply" ||
            !(*row)[1].getAsArray() || !(*row)[2].getAsArray())
          return error("structured-reference-input", "reply shape");
      }
    } else {
      if (source.getRoles().size() != 1)
        return error("structured-reference-input", "open command required");
      self = cast<StringAttr>(source.getRoles()[0]).getValue();
    }
    if (!inScope(source.getRoles()))
      return error("structured-reference-input", "unknown participant");
    auto type = source.getFunctionType();
    if (arguments->size() != type.getNumInputs())
      return error("structured-reference-input", "input arity");
    Values inputs;
    llvm::DenseMap<uint64_t, StringRef> serviceOwners;
    for (auto [i, type, input] :
         llvm::enumerate(type.getInputs(), *arguments)) {
      if (open && input.getAsNull()) {
        inputs.emplace_back(std::monostate{});
        continue;
      }
      auto value = decode(type, input);
      if (!value)
        return value.takeError();
      auto scope = cast<ArrayAttr>(source.getInputRoles()[i]);
      if (isa<protocol_ir::ServiceReferenceType>(type)) {
        auto owner = cast<StringAttr>(scope[0]).getValue();
        auto [found, inserted] =
            serviceOwners.try_emplace(std::get<uint64_t>(*value), owner);
        if (!inserted && found->second != owner)
          return error("structured-reference-input",
                       "cross-owner service alias");
      }
      inputs.push_back(inScope(scope) ? std::move(*value)
                                      : Datum(std::monostate{}));
    }
    ProtocolContext context;
    for (Attribute role : source.getRoles()) {
      auto name = cast<StringAttr>(role).getValue();
      context.roles.emplace_back(name, name);
    }
    auto result = invokeProtocol(source, inputs, context, 1);
    if (!result)
      return result.takeError();
    if (result->stopped()) {
      if (!open)
        return json::Value(json::Array{"stopped", result->reason});
      if (auto failure = record(
              json::Array{"stop", result->reason, result->site, replyPosition}))
        return std::move(failure);
      return json::Value(
          json::Array{"zkc.structured-open-result/0",
                      json::Array{"stopped", result->reason, result->site},
                      std::move(records), replyPosition});
    }
    json::Array outputs;
    for (auto [i, value] : llvm::enumerate(result->values)) {
      auto output = encode(inScope(cast<ArrayAttr>(source.getOutputRoles()[i]))
                               ? value
                               : Datum(std::monostate{}));
      if (!output)
        return output.takeError();
      outputs.push_back(std::move(*output));
    }
    json::Value outcome(json::Array{"returned", std::move(outputs)});
    if (!open)
      return outcome;
    return json::Value(json::Array{"zkc.structured-open-result/0",
                                   std::move(outcome), std::move(records),
                                   replyPosition});
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
  bool open = argc == 5 && StringRef(argv[1]) == "open";
  if (argc != (open ? 5 : 4))
    return fail(error("structured-reference-arguments"));
  unsigned offset = open ? 1 : 0;
  auto source = input(argv[1 + offset], 16 * 1024 * 1024);
  if (!source)
    return fail(source.takeError());
  if (!mlirNestingWithinLimit(*source, maxDepth))
    return fail(error("structured-reference-capacity", "MLIR nesting"));
  auto request = input(argv[3 + offset], 1024 * 1024);
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
  Admission admission(unit);
  if (auto failure = admission.check())
    return fail(std::move(failure));
  SymbolTable symbols(unit);
  auto selected = symbols.lookup<protocol_ir::MathematicalOp>(argv[2 + offset]);
  if (!selected)
    return fail(error("structured-reference-symbol", argv[2 + offset]));
  auto result = Reference(unit, admission.checkedPrimitives(),
                          admission.checkedPreparations())
                    .run(selected, *array, open);
  if (!result)
    return fail(result.takeError());
  outs() << printJson(*result) << '\n';
  return 0;
}

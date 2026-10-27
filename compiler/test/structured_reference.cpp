// Bounded, independent test evaluation of original native structured SSA.
// No structured exporter, serialized SSA coordinates, preparation, or runtime
// kernels participate. Native verification remains authoritative for admission;
// this executable supplies finite evidence, not a shipped semantic interpreter.
#include "../lib/Support/Input.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
  IndexLess,
  IndexPowerOfTwo,
  VectorLength,
  MultilinearRestrictPrefix,
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
  ProtocolApply,
  ProtocolRepeat,
  LocalCall,
  Fold,
  Guard,
  Return,
  Yield,
  Stop,
  Elements,
  Indices,
  DomainYield,
  DomainRange,
  Zip,
  Product,
  Compute,
  ScopedFold,
  Collect,
  Complete,
  Test,
  Range,
  Returned,
  Failed,
  Dispatch,
  Branch,
  CondBranch,
  EnterScope,
  ExitScope,
  AcceptTransfer,
  BorrowTransfer,
  TransferValues,
  ReleaseTransfer,
  TakeCondition,
  Iteration,
  ReleaseBindings,
  IntegerConstant,
  IntegerAdd
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
  StringLiteral contract, inputs, outputs;
  Primitive primitive;
  bool field;
};
constexpr PrimitiveSpec primitiveSpecs[] = {
    {"index.constant", "", "i", Primitive::Constant, false},
    {"index.add", "ii", "i", Primitive::Add, false},
    {"index.sub", "ii", "i", Primitive::Sub, false},
    {"index.mul", "ii", "i", Primitive::Mul, false},
    {"index.div", "ii", "i", Primitive::Div, false},
    {"index.mod", "ii", "i", Primitive::Mod, false},
    {"index.equal", "ii", "b", Primitive::Equal, false},
    {"index.less", "ii", "b", Primitive::Less, false},
    {"vector.empty", "", "v", Primitive::Empty, true},
    {"vector.length", "v", "i", Primitive::Length, true},
    {"vector.sum", "v", "f", Primitive::Sum, true},
    {"vector.split", "v", "vv", Primitive::Split, true},
    {"vector.append", "vf", "v", Primitive::Append, true},
    {"vector.equal", "vv", "b", Primitive::VectorEqual, true},
    {"field.equal", "ff", "b", Primitive::FieldEqual, true},
};
struct CheckedPrimitive {
  Primitive primitive;
  uint64_t literal = 0;
};
using PrimitiveMap = llvm::DenseMap<Operation *, CheckedPrimitive>;

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
  if (isa<arith::ConstantOp>(op))
    return op.getResult(0).getType().isSignlessInteger(1)
               ? Kind::BoolConstant
               : Kind::IntegerConstant;
  return llvm::StringSwitch<Kind>(op.getName().getStringRef())
      .Case("data.index", Kind::IndexConstant)
      .Case("data.index_equal", Kind::IndexEqual)
      .Case("data.index_less", Kind::IndexLess)
      .Case("data.index_power_of_two", Kind::IndexPowerOfTwo)
      .Case("data.dim", Kind::VectorLength)
      .Case("algebra.multilinear_restrict_prefix",
            Kind::MultilinearRestrictPrefix)
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
      .Case("exec.boolean", Kind::BoolConstant)
      .Case("arith.andi", Kind::And)
      .Case("arith.ori", Kind::Or)
      .Case("arith.xori", Kind::Xor)
      .Case("arith.cmpi", Kind::Compare)
      .Case("arith.select", Kind::Select)
      .Case("data.bounded_at", Kind::At)
      .Case("func.call", Kind::Call)
      .Case("protocol.apply", Kind::ProtocolApply)
      .Case("protocol.repeat", Kind::ProtocolRepeat)
      .Case("protocol.local_call", Kind::LocalCall)
      .Case("algebra.finite_fold", Kind::Fold)
      .Case("protocol.guard", Kind::Guard)
      .Cases({"func.return", "protocol.return"}, Kind::Return)
      .Case("protocol.yield", Kind::Yield)
      .Case("exec.reject", Kind::Stop)
      .Case("exec.apply", Kind::Exec)
      .Case("exec.compute", Kind::Compute)
      .Case("exec.fold", Kind::ScopedFold)
      .Case("exec.collect", Kind::Collect)
      .Case("exec.complete", Kind::Complete)
      .Case("exec.test", Kind::Test)
      .Case("exec.range", Kind::Range)
      .Case("exec.returned", Kind::Returned)
      .Case("exec.failed", Kind::Failed)
      .Case("exec.dispatch", Kind::Dispatch)
      .Case("cf.br", Kind::Branch)
      .Case("cf.cond_br", Kind::CondBranch)
      .Case("runtime.enter_scope", Kind::EnterScope)
      .Case("runtime.exit_scope", Kind::ExitScope)
      .Case("runtime.accept_transfer", Kind::AcceptTransfer)
      .Case("runtime.borrow_transfer", Kind::BorrowTransfer)
      .Case("runtime.transfer_values", Kind::TransferValues)
      .Case("runtime.release_transfer", Kind::ReleaseTransfer)
      .Case("runtime.take_condition", Kind::TakeCondition)
      .Case("runtime.iteration", Kind::Iteration)
      .Case("runtime.release_bindings", Kind::ReleaseBindings)
      .Case("arith.addi", Kind::IntegerAdd)
      .Case("data.domain_elements", Kind::Elements)
      .Case("data.domain_indices", Kind::Indices)
      .Case("data.domain_yield", Kind::DomainYield)
      .Case("data.domain_range", Kind::DomainRange)
      .Case("data.domain_zip", Kind::Zip)
      .Case("data.domain_product", Kind::Product)
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

bool isScoped(Operation &op) {
  auto type = signature(op);
  return type && type.getNumInputs() &&
         isa<runtime::ScopeType>(type.getInput(0)) &&
         type.getNumResults() == 1 && isa<exec::OutcomeType>(type.getResult(0));
}

bool referenceType(Type type, bool scoped) {
  if (valueType(type))
    return true;
  if (!scoped)
    return false;
  if (type.isSignlessInteger(64) ||
      isa<runtime::ScopeType, exec::StopType>(type))
    return true;
  if (auto outcome = dyn_cast<exec::OutcomeType>(type))
    return outcome.getPayload().size() <= maxSignature &&
           llvm::all_of(outcome.getPayload(),
                        [](Type t) { return referenceType(t, true); });
  if (auto transfer = dyn_cast<runtime::TransferType>(type))
    return transfer.getPayload().size() <= maxSignature &&
           llvm::all_of(transfer.getPayload(), valueType);
  return false;
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
    if (!isScoped(owner) || !site || site.getValue().empty() ||
        found == bindings.end() || !parameters)
      return error("structured-reference-binding", "owner, reference or site");
    const auto &spec = *found->second;
    if (!primitivePorts(op.getOperands().drop_front().getTypes(),
                        spec.inputs) ||
        !primitivePorts(
            cast<exec::OutcomeType>(op.getResult(0).getType()).getPayload(),
            spec.outputs))
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
    if (!target || target->getName().getStringRef() != expected)
      return error("structured-reference-symbol", name.getValue());
    dependencies[&owner].push_back(target);
    if (attribute == "callee") {
      auto type = signature(*target);
      bool bridge = kind(op) == Kind::LocalCall;
      bool computation = kind(op) == Kind::Compute;
      auto inputs = type.getInputs();
      auto outputs = type.getResults();
      if (bridge) {
        if (!isa<protocol_ir::MathematicalOp>(owner) || !isScoped(*target))
          return error("structured-reference-symbol", "local call scope");
        inputs = inputs.drop_front();
        outputs = cast<exec::OutcomeType>(outputs[0]).getPayload();
      } else if (kind(op) == Kind::Call) {
        // Scoped helper calls retain the ordinary execution interface,
        // including public roots. Private visibility constrains plain
        // mathematical calls; scope crossing requires an explicit boundary.
        if (!isa<func::FuncOp, protocol_ir::MathematicalOp>(owner) ||
            isScoped(*target) != isScoped(owner) ||
            (!isScoped(*target) && !cast<func::FuncOp>(target).isPrivate()))
          return error("structured-reference-symbol", "call owner or kind");
      } else if (computation && (isScoped(*target) || !isScoped(owner))) {
        return error("structured-reference-symbol", "computation boundary");
      }
      TypeRange actualInputs = op.getOperandTypes();
      if (computation)
        actualInputs = actualInputs.drop_front();
      if (actualInputs != inputs ||
          (computation
               ? TypeRange(cast<exec::OutcomeType>(op.getResult(0).getType())
                               .getPayload())
               : TypeRange(op.getResultTypes())) != outputs)
        return error("structured-reference-signature", name.getValue());
    }
    return Error::success();
  }

  Error foldReferences(Operation &op, Operation &owner) {
    if (auto failure = reference(op, owner, "domain", "data.domain"))
      return failure;
    if (auto failure =
            reference(op, owner, kind(op) == Kind::Collect ? "body" : "step",
                      "func.func"))
      return failure;
    return reference(op, owner, "predicate", "func.func", true);
  }

  Error instruction(Operation &op, Operation &owner) {
    Kind code = kind(op);
    if (code == Kind::Unsupported || code == Kind::Elements ||
        code == Kind::Indices || code == Kind::DomainYield)
      return error("structured-reference-unsupported",
                   op.getName().getStringRef());
    if (op.getNumRegions() != (code == Kind::ProtocolRepeat ? 1u : 0u))
      return error("structured-reference-unsupported", "region count");
    for (Type type : op.getOperandTypes())
      if (!referenceType(type, isScoped(owner)) ||
          (isa<protocol_ir::ServiceReferenceType>(type) && code != Kind::Draw &&
           code != Kind::ProtocolApply && code != Kind::ProtocolRepeat))
        return error("structured-reference-unsupported", "operand type");
    for (Type type : op.getResultTypes())
      if (!referenceType(type, isScoped(owner)) ||
          isa<protocol_ir::ServiceReferenceType>(type))
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
    case Kind::IndexLess:
    case Kind::IndexPowerOfTwo:
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
    case Kind::VectorLength: {
      auto dim = cast<data::DimOp>(op);
      if (!isa<func::FuncOp, protocol_ir::MathematicalOp>(owner) ||
          dim.getAxis() != 0 || !primitivePorts(op.getOperandTypes(), "v") ||
          !primitivePorts(op.getResultTypes(), "i"))
        return error("structured-reference-signature", "vector length");
      return attributes(op, {"axis"});
    }
    case Kind::MultilinearRestrictPrefix:
      if (!isa<func::FuncOp, protocol_ir::MathematicalOp>(owner) ||
          !primitivePorts(op.getOperandTypes(), "vv") ||
          !primitivePorts(op.getResultTypes(), "v"))
        return error("structured-reference-signature", "prefix restriction");
      return attributes(op, {});
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
      return attributes(op, isa<exec::BooleanOp>(op)
                                ? ArrayRef<StringRef>{"value", "site"}
                                : ArrayRef<StringRef>{"value"});
    case Kind::IntegerConstant:
      if (!isScoped(owner) || !op.getResult(0).getType().isSignlessInteger(64))
        return error("structured-reference-unsupported", "integer constant");
      return attributes(op, {"value"});
    case Kind::IntegerAdd:
      if (!isScoped(owner) ||
          !op.getResult(0).getType().isSignlessInteger(64) ||
          cast<arith::AddIOp>(op).getOverflowFlags() !=
              arith::IntegerOverflowFlags::none)
        return error("structured-reference-unsupported", "integer addition");
      return attributes(op, {"overflowFlags"});
    case Kind::And:
    case Kind::Or:
    case Kind::Xor:
      if (!llvm::all_of(op.getOperandTypes(),
                        [](Type t) { return t.isSignlessInteger(1); }))
        return error("structured-reference-unsupported",
                     "non-boolean arithmetic");
      return attributes(op, {});
    case Kind::Compare: {
      auto type = op.getOperand(0).getType();
      auto predicate = cast<arith::CmpIOp>(op).getPredicate();
      if (!(type.isSignlessInteger(1) &&
            (predicate == arith::CmpIPredicate::eq ||
             predicate == arith::CmpIPredicate::ne)) &&
          !(isScoped(owner) && type.isSignlessInteger(64) &&
            predicate == arith::CmpIPredicate::ult))
        return error("structured-reference-unsupported",
                     "comparison predicate");
      return attributes(op, {"predicate"});
    }
    case Kind::Call:
    case Kind::LocalCall:
    case Kind::Compute:
      if (auto failure = attributes(
              op, code == Kind::Call
                      ? ArrayRef<StringRef>{"callee", "runtime.site"}
                  : code == Kind::Compute
                      ? ArrayRef<StringRef>{"callee", "site", "policy"}
                      : ArrayRef<StringRef>{"callee", "site", "role"}))
        return failure;
      if (code == Kind::Compute)
        if (auto attribute = op.getAttr("policy")) {
          auto policy = dyn_cast<ArrayAttr>(attribute);
          if (!policy || policy.size() != 3 ||
              !llvm::all_of(
                  policy, [](Attribute value) { return isa<BoolAttr>(value); }))
            return error("structured-reference-unsupported",
                         "computation policy");
        }
      return reference(op, owner, "callee", "func.func");
    case Kind::Fold:
    case Kind::ScopedFold:
    case Kind::Collect:
      if (auto failure = attributes(
              op,
              code == Kind::Collect
                  ? ArrayRef<StringRef>{"domain", "body", "predicate", "site"}
              : code == Kind::ScopedFold
                  ? ArrayRef<StringRef>{"domain", "step", "predicate", "site"}
                  : ArrayRef<StringRef>{"domain", "step", "predicate"}))
        return failure;
      return foldReferences(op, owner);
    case Kind::Test:
    case Kind::Range:
    case Kind::Iteration:
      return attributes(op, {"site"});
    case Kind::EnterScope:
      return attributes(
          op, {"kind", "site", "selection", "callee", "operandSegmentSizes"});
    case Kind::CondBranch:
      return attributes(op, {"operandSegmentSizes"});
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
      return attributes(op, {"relation", "selectors", "acceptance", "target"});
    case Kind::Stop:
      if (auto failure = attributes(op, {"site", "reason"}))
        return failure;
      if (!llvm::is_contained(ArrayRef<StringRef>{"reject", "abort",
                                                  "exhausted", "incomplete",
                                                  "refused"},
                              cast<exec::RejectOp>(op).getReason()))
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
    for (Value argument : body.getArguments())
      if (!referenceType(argument.getType(), isScoped(owner)))
        return error("structured-reference-unsupported", "block argument type");
    // Native verification checked dominance; independently reject cross-region
    // captures. CFG values may dominate several blocks in this one function.
    for (Operation &op : body) {
      if ((!op.hasTrait<OpTrait::IsTerminator>() &&
           ++operations > maxOperations) ||
          op.getNumOperands() > maxSignature ||
          op.getNumResults() > maxSignature)
        return error("structured-reference-capacity",
                     "operations or signature");
      for (Value operand : op.getOperands()) {
        auto *region = operand.getParentRegion();
        if (region != body.getParent())
          return error("structured-reference-ssa",
                       "operand outside closed region");
      }
      for (auto attr : op.getAttrs())
        if (auto failure = attributeBounds(attr.getValue()))
          return failure;
      if (auto failure = instruction(op, owner))
        return failure;
      for (Region &region : op.getRegions()) {
        if (!llvm::hasSingleElement(region) || region.front().empty())
          return error("structured-reference-unsupported",
                       "nested block count");
        if (auto failure = block(region.front(), owner, depth + 1))
          return failure;
      }
    }
    return Error::success();
  }

  Error domain(Operation &op) {
    if (auto failure =
            attributes(op, {"sym_name", "sym_visibility", "function_type"}))
      return failure;
    if (op.getNumRegions() != 1 || !llvm::hasSingleElement(op.getRegion(0)))
      return error("structured-reference-unsupported", "domain body");
    auto &body = op.getRegion(0).front();
    llvm::DenseSet<Value> defined(body.getArguments().begin(),
                                  body.getArguments().end());
    for (Operation &item : body) {
      if (++operations > maxOperations)
        return error("structured-reference-capacity", "domain instructions");
      auto code = kind(item);
      if (!llvm::is_contained(ArrayRef<Kind>{Kind::Elements, Kind::Indices,
                                             Kind::DomainRange, Kind::Zip,
                                             Kind::Product, Kind::DomainYield},
                              code))
        return error("structured-reference-unsupported", "domain constructor");
      for (Value operand : item.getOperands())
        if (!defined.contains(operand))
          return error("structured-reference-ssa", "domain operand");
      if (auto failure = attributes(item, code == Kind::Indices
                                              ? ArrayRef<StringRef>{"axis"}
                                              : ArrayRef<StringRef>{}))
        return failure;
      if (code == Kind::Indices &&
          cast<data::DomainIndicesOp>(item).getAxis() != 0)
        return error("structured-reference-unsupported", "domain axis");
      for (Type type : item.getResultTypes()) {
        auto domain = dyn_cast<data::DomainType>(type);
        if (!domain || !llvm::all_of(domain.getItemTypes(), valueType))
          return error("structured-reference-unsupported",
                       "domain element type");
      }
      for (Value value : item.getResults())
        defined.insert(value);
    }
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

  Error check() {
    unsigned domains = 0, definitions = 0, relations = 0;
    if (auto failure = attributes(*unit, {"profile", "source_declarations"}))
      return failure;
    // Source declarations are retained metadata, not executable instructions.
    // Native ownership admission checks their meaning; the observer bounds and
    // parses the carrier without using it to supply values or control flow.
    if (auto attr = unit->getAttr("source_declarations")) {
      auto text = dyn_cast<StringAttr>(attr);
      if (!text)
        return error("structured-reference-unsupported", "source declarations");
      auto parsed = parseNaturalJson(text.getValue(), 16 * 1024 * 1024, 256,
                                     "structured-reference-unsupported",
                                     "structured-reference-capacity");
      if (!parsed)
        return parsed.takeError();
      auto rows = parsed->getAsArray();
      if (!rows || rows->size() != 2 || !(*rows)[0].getAsArray() ||
          !(*rows)[1].getAsArray())
        return error("structured-reference-unsupported", "source declarations");
    }
    llvm::StringSet<> names;
    // Pre-admit even unused declarations, including forward references. Binding
    // rows are metadata, not graph nodes or callable function signatures.
    for (Operation &op : unit.getBody().front()) {
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name || !names.insert(name.getValue()).second)
        return error("structured-reference-symbol");
      if (isa<runtime::BindingOp>(op)) {
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
      if (isa<runtime::BindingOp>(op))
        continue;
      if (auto declaration = dyn_cast<relation::DeclareOp>(op)) {
        if (++relations > 128)
          return error("structured-reference-capacity", "relations");
        if (auto failure = attributes(
                op, {"sym_name", "sym_visibility", "kind", "key", "revision",
                     "static_arguments", "signature", "purposes", "formula"}))
          return failure;
        auto type = declaration.getSignature();
        auto formula = declaration.getFormulaAttr();
        if ((declaration.getKind() == "zkc.language.formula/0") !=
            bool(formula))
          return error("structured-reference-contract", "formula presence");
        if (formula) {
          auto *target = SymbolTable::lookupSymbolIn(unit, formula);
          auto helper = dyn_cast_or_null<func::FuncOp>(target);
          if (!helper || helper.isExternal() ||
              helper.getFunctionType() != type)
            return error("structured-reference-contract",
                         "formula kind or ABI");
        }
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
      if (!isDomain && !isa<func::FuncOp, protocol_ir::MathematicalOp>(op))
        return error("structured-reference-unsupported",
                     op.getName().getStringRef());
      if (++(isDomain ? domains : definitions) > 128)
        return error("structured-reference-capacity", "definitions");
      auto type = signature(op);
      if (!type || type.getNumInputs() > maxSignature ||
          type.getNumResults() > maxSignature)
        return error("structured-reference-capacity", "function signature");
      for (Type input : type.getInputs())
        if (!referenceType(input, isScoped(op)) ||
            (isa<protocol_ir::ServiceReferenceType>(input) &&
             !isa<protocol_ir::MathematicalOp>(op)))
          return error("structured-reference-unsupported", "input type");
      if (!isDomain)
        for (Type output : type.getResults())
          if (!referenceType(output, isScoped(op)) ||
              isa<protocol_ir::ServiceReferenceType>(output))
            return error("structured-reference-unsupported", "output type");
      if (isDomain) {
        if (auto failure = domain(op))
          return failure;
        continue;
      }
      if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
        if (protocol.getContractsAttr() &&
            protocol.getContractsAttr().size() > maxSignature)
          return error("structured-reference-capacity", "contract clauses");
        if (auto failure = attributes(
                op, {"sym_name", "sym_visibility", "function_type", "roles",
                     "input_roles", "output_roles", "contracts", "origin"}))
          return failure;
        if (protocol.getRoles().empty() || protocol.getRoles().size() > 16)
          return error("structured-reference-unsupported", "role count");
      } else if (isa<func::FuncOp>(op)) {
        if (auto failure =
                attributes(op, {"sym_name", "sym_visibility", "function_type",
                                "data.preconditions", "runtime.origin",
                                "runtime.region", "no_inline"}))
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
      }
      if (op.getNumRegions() != 1 || op.getRegion(0).empty() ||
          (!isScoped(op) && !llvm::hasSingleElement(op.getRegion(0))))
        return error("structured-reference-unsupported", "function body");
      for (Block &body : op.getRegion(0)) {
        if (body.empty())
          return error("structured-reference-unsupported", "empty block");
        if (auto failure = block(body, op, 1))
          return failure;
      }
    }
    for (Operation &op : unit.getBody().front()) {
      auto checked = height(&op, 0);
      if (!checked)
        return checked.takeError();
    }
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
struct DomainRows;
struct Outcome;
struct ScopeState;
struct HeldValues;
using Domain = std::shared_ptr<const DomainRows>;
using Result = std::shared_ptr<const Outcome>;
using Scope = std::shared_ptr<ScopeState>;
using Transfer = std::shared_ptr<HeldValues>;
struct Stop {
  std::string reason, site;
};
// monostate is an absent participant component, never a missing SSA binding.
using Datum = std::variant<std::monostate, bool, uint64_t, APInt, Vector,
                           Domain, Result, Scope, Transfer, Stop>;
using Values = std::vector<Datum>;
struct DomainRows {
  std::vector<Values> rows;
};
// These are the observer's control/custody identities, not backend resources,
// frame limits, allocation budgets or a second native resource ledger.
struct ScopeState {
  Scope parent;
  bool active = true;
};
struct HeldValues {
  Scope parent;
  Values values;
  bool live = true;
};
bool present(const Datum &value) {
  return !std::holds_alternative<std::monostate>(value);
}
struct Outcome {
  Kind terminator = Kind::Return;
  Values values;
  std::string reason;
  std::string site = {};
  Block *destination = nullptr;
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
  if (type.isUnsignedInteger(64) || type.isSignlessInteger(64) ||
      isa<protocol_ir::ServiceReferenceType>(type))
    return std::holds_alternative<uint64_t>(value);
  if (isa<runtime::ScopeType>(type))
    return std::holds_alternative<Scope>(value);
  if (isa<exec::StopType>(type))
    return std::holds_alternative<Stop>(value);
  if (auto outcome = dyn_cast<exec::OutcomeType>(type)) {
    auto result = std::get_if<Result>(&value);
    if (!result)
      return false;
    if ((*result)->stopped())
      return true;
    auto payload = outcome.getPayload();
    return payload.size() == (*result)->values.size() &&
           llvm::all_of(llvm::zip(payload, (*result)->values), [](auto entry) {
             return matches(std::get<0>(entry), std::get<1>(entry));
           });
  }
  if (auto transfer = dyn_cast<runtime::TransferType>(type)) {
    auto held = std::get_if<Transfer>(&value);
    if (!held || transfer.getPayload().size() != (*held)->values.size())
      return false;
    return llvm::all_of(
        llvm::zip(transfer.getPayload(), (*held)->values), [](auto entry) {
          return matches(std::get<0>(entry), std::get<1>(entry));
        });
  }
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
                           unsigned depth) {
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
    auto result = block(callee->getRegion(0).front(), args, depth);
    if (!result || result->stopped())
      return result;
    if (result->values.size() != type.getNumResults())
      return error("structured-reference-signature", "call results");
    for (auto [type, value] : llvm::zip(type.getResults(), result->values))
      if (!matches(type, value))
        return error("structured-reference-signature", "call result type");
    return result;
  }

  Expected<Outcome> packed(Expected<Outcome> result) {
    if (!result)
      return result.takeError();
    return Outcome{Kind::Return,
                   {Result(std::make_shared<Outcome>(std::move(*result)))},
                   {}};
  }

  Expected<Outcome> invokeScoped(Operation *callee, Scope scope,
                                 ArrayRef<Datum> args, unsigned depth) {
    if (!scope->active)
      return error("structured-reference-custody", "inactive invocation scope");
    Values inputs{scope};
    llvm::append_range(inputs, args);
    auto result = invoke(callee, inputs, depth);
    if (!result)
      return result.takeError();
    if (result->stopped() || result->values.size() != 1 ||
        !std::holds_alternative<Result>(result->values[0]))
      return error("structured-reference-signature", "scoped call result");
    return *std::get<Result>(result->values[0]);
  }

  Expected<Outcome> finite(Operation &op, ArrayRef<Datum> args, unsigned count,
                           unsigned depth, Scope scope = {}) {
    Operation *domain = target(op, "domain");
    if (!domain)
      return error("structured-reference-symbol", "domain");
    unsigned arity = signature(*domain).getNumInputs();
    if (args.size() < arity + count)
      return error("structured-reference-signature", "finite inputs");
    auto enumerated = invoke(domain, args.take_front(arity), depth + 1);
    if (!enumerated)
      return enumerated.takeError();
    if (enumerated->stopped())
      return stopped(op, enumerated->reason);
    if (enumerated->values.size() != 1 ||
        !std::holds_alternative<Domain>(enumerated->values[0]))
      return error("structured-reference-signature", "domain result");
    Domain items = std::get<Domain>(enumerated->values[0]);
    bool collect = kind(op) == Kind::Collect;
    auto initial = args.slice(arity, count);
    Outcome state{Kind::Return, Values(initial.begin(), initial.end()), {}};
    auto output = std::make_shared<std::vector<APInt>>();
    auto callback = [&](Operation *callee, ArrayRef<Datum> inputs) {
      return scope ? invokeScoped(callee, scope, inputs, depth + 1)
                   : invoke(callee, inputs, depth + 1);
    };
    for (const auto &row : items->rows) {
      if (auto failure = tick(depth))
        return failure;
      if (auto failure = argumentWork(row.size() + args.size()))
        return failure;
      Values inputs(row.begin(), row.end());
      llvm::append_range(inputs, args.take_front(arity));
      llvm::append_range(inputs, args.drop_front(arity + count));
      // All domain constructors have completed before the first callback.
      // Predicate receives I,A,C; fold step receives S,I,A,C; collect receives
      // I,A,C.
      if (Operation *predicate = target(op, "predicate")) {
        auto admitted = callback(predicate, inputs);
        if (!admitted || admitted->stopped())
          return admitted;
        if (admitted->values.size() != 1 ||
            !std::holds_alternative<bool>(admitted->values[0]))
          return error("structured-reference-signature", "predicate result");
        if (!std::get<bool>(admitted->values[0]))
          continue;
      }
      if (!collect)
        inputs.insert(inputs.begin(), state.values.begin(), state.values.end());
      auto next = callback(target(op, collect ? "body" : "step"), inputs);
      if (!next || next->stopped())
        return next;
      if (collect) {
        if (next->values.size() != 1 ||
            !std::holds_alternative<APInt>(next->values[0]))
          return error("structured-reference-signature", "collection item");
        if (output->size() == maxVector)
          return error("structured-reference-capacity", "collection length");
        output->push_back(std::get<APInt>(next->values[0]));
      } else {
        if (next->values.size() != count)
          return error("structured-reference-signature", "fold state");
        state = std::move(*next);
      }
    }
    if (collect)
      return Outcome{Kind::Return, {Vector(std::move(output))}, {}};
    return state;
  }

  Expected<Outcome> domainInstruction(Operation &op, ArrayRef<Datum> args) {
    if (!llvm::all_of(args, present))
      return stopped(op, "incomplete");
    auto rows = std::make_shared<DomainRows>();
    auto code = kind(op);
    if (code == Kind::Elements || code == Kind::Indices) {
      auto vector = std::get<Vector>(args[0]);
      if (auto failure = vectorWork(vector->size()))
        return failure;
      for (size_t i = 0; i < vector->size(); ++i)
        rows->rows.push_back(
            {code == Kind::Indices ? Datum(uint64_t(i)) : Datum((*vector)[i])});
    } else if (code == Kind::DomainRange) {
      uint64_t lower = std::get<uint64_t>(args[0]),
               upper = std::get<uint64_t>(args[1]);
      uint64_t count = upper > lower ? upper - lower : 0;
      if (auto failure = vectorWork(count))
        return failure;
      for (uint64_t i = 0; i < count; ++i)
        rows->rows.push_back({lower + i});
    } else {
      if (args.empty())
        return error("structured-reference-signature",
                     "empty domain combination");
      size_t count =
          code == Kind::Zip ? std::get<Domain>(args[0])->rows.size() : 1;
      size_t width = 0;
      for (const auto &arg : args) {
        const auto &part = std::get<Domain>(arg)->rows;
        if (code == Kind::Zip && part.size() != count)
          return stopped(op, "refused");
        if (code == Kind::Product) {
          if (part.size() && count > maxVector / part.size())
            return error("structured-reference-capacity", "domain product");
          count *= part.size();
        }
        if (!part.empty())
          width += part.front().size();
      }
      if (auto failure = vectorWork(count))
        return failure;
      if (width && count > (capacity - steps) / width)
        return error("structured-reference-capacity", "domain tuple work");
      if (auto failure = argumentWork(count * width))
        return failure;
      for (size_t i = 0; i < count; ++i) {
        Values row;
        size_t stride = count;
        for (const auto &arg : args) {
          const auto &part = std::get<Domain>(arg)->rows;
          if (code == Kind::Product)
            stride /= part.size();
          const auto &item =
              part[code == Kind::Zip ? i : (i / stride) % part.size()];
          llvm::append_range(row, item);
        }
        rows->rows.push_back(std::move(row));
      }
    }
    return Outcome{Kind::Return, {Domain(std::move(rows))}, {}};
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
      if (!llvm::all_of(args, present))
        return packed(stopped(op, "incomplete", context));
      if (!std::get<Scope>(args[0])->active)
        return error("structured-reference-custody",
                     "inactive primitive scope");
      return packed(execute(op, args.drop_front()));
    case Kind::Return:
    case Kind::Yield:
    case Kind::DomainYield:
      return Outcome{code, Values(args.begin(), args.end()), {}};
    case Kind::Stop: {
      auto stop = stopped(op, cast<exec::RejectOp>(op).getReason(), context);
      return Outcome{Kind::Return, {Stop{stop.reason, stop.site}}, {}};
    }
    case Kind::Failed: {
      const auto &stop = std::get<Stop>(args[0]);
      return packed(Outcome{Kind::Stop, {}, stop.reason, stop.site});
    }
    case Kind::Returned:
      return packed(
          Outcome{Kind::Return, Values(args.begin(), args.end()), {}});
    case Kind::Compute:
    case Kind::ScopedFold:
    case Kind::Collect:
    case Kind::Complete:
    case Kind::Test:
    case Kind::Range:
    case Kind::Iteration: {
      if (!llvm::all_of(args, present))
        return packed(stopped(op, "incomplete", context));
      auto scope = std::get<Scope>(args[0]);
      if (!scope->active)
        return error("structured-reference-custody", "inactive scope");
      auto data = args.drop_front();
      if (code == Kind::Compute)
        return packed(invoke(target(op, "callee"), data, depth + 1));
      if (code == Kind::ScopedFold || code == Kind::Collect) {
        unsigned count =
            code == Kind::Collect
                ? 0
                : cast<exec::OutcomeType>(op.getResult(0).getType())
                      .getPayload()
                      .size();
        return packed(finite(op, data, count, depth, scope));
      }
      return packed(
          Outcome{Kind::Return, Values(data.begin(), data.end()), {}});
    }
    case Kind::EnterScope: {
      if (!llvm::all_of(args, present))
        return packed(stopped(op, "incomplete", context));
      auto parent = std::get<Scope>(args[0]);
      if (!parent->active)
        return error("structured-reference-custody", "inactive parent");
      return packed(
          Outcome{Kind::Return,
                  {Scope(std::make_shared<ScopeState>(ScopeState{parent}))},
                  {}});
    }
    case Kind::ExitScope: {
      auto scope = std::get<Scope>(args[0]);
      auto result = std::get<Result>(args[1]);
      if (!scope->active || !scope->parent)
        return error("structured-reference-custody", "scope exit");
      scope->active = false;
      if (result->stopped())
        return packed(*result);
      return packed(Outcome{Kind::Return,
                            {Transfer(std::make_shared<HeldValues>(
                                HeldValues{scope->parent, result->values}))},
                            {}});
    }
    case Kind::BorrowTransfer: {
      auto parent = std::get<Scope>(args[0]);
      if (!parent->active)
        return error("structured-reference-custody", "borrow parent");
      return Outcome{Kind::Return,
                     {Transfer(std::make_shared<HeldValues>(HeldValues{
                         parent, Values(args.begin() + 1, args.end())}))},
                     {}};
    }
    case Kind::AcceptTransfer:
    case Kind::TransferValues:
    case Kind::ReleaseTransfer:
    case Kind::TakeCondition: {
      auto transfer =
          std::get<Transfer>(args[code == Kind::AcceptTransfer ? 1 : 0]);
      if (!transfer->live || !transfer->parent->active)
        return error("structured-reference-custody", "expired transfer");
      if (code == Kind::AcceptTransfer) {
        if (std::get<Scope>(args[0]) != transfer->parent)
          return error("structured-reference-custody", "transfer parent");
        transfer->live = false;
        return packed(Outcome{Kind::Return, transfer->values, {}});
      }
      if (code == Kind::ReleaseTransfer) {
        transfer->live = false;
        return Outcome{};
      }
      if (code == Kind::TakeCondition) {
        if (transfer->values.empty() ||
            !std::holds_alternative<bool>(transfer->values[0]))
          return error("structured-reference-signature", "condition transfer");
        auto rest = std::make_shared<HeldValues>(
            HeldValues{transfer->parent, Values(transfer->values.begin() + 1,
                                                transfer->values.end())});
        transfer->live = false;
        return packed(Outcome{Kind::Return,
                              {transfer->values[0], Transfer(std::move(rest))},
                              {}});
      }
      return Outcome{Kind::Return, transfer->values, {}};
    }
    case Kind::ReleaseBindings:
      if (!std::get<Scope>(args[0])->active)
        return error("structured-reference-custody", "release scope");
      return Outcome{};
    case Kind::Dispatch: {
      auto result = std::get<Result>(args[0]);
      return Outcome{Kind::Return,
                     result->stopped()
                         ? Values{Stop{result->reason, result->site}}
                         : result->values,
                     {},
                     {},
                     op.getSuccessor(result->stopped() ? 1 : 0)};
    }
    case Kind::Branch:
      return Outcome{Kind::Return,
                     Values(args.begin(), args.end()),
                     {},
                     {},
                     op.getSuccessor(0)};
    case Kind::CondBranch: {
      if (!present(args[0]))
        return stopped(op, "incomplete", context);
      auto branch = cast<cf::CondBranchOp>(op);
      bool condition = std::get<bool>(args[0]);
      unsigned count = condition ? branch.getTrueDestOperands().size()
                                 : branch.getFalseDestOperands().size();
      unsigned offset = condition ? 1 : 1 + branch.getTrueDestOperands().size();
      auto forwarded = args.slice(offset, count);
      return Outcome{Kind::Return,
                     Values(forwarded.begin(), forwarded.end()),
                     {},
                     {},
                     op.getSuccessor(condition ? 0 : 1)};
    }
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
    case Kind::LocalCall: {
      if (role(op.getAttrOfType<StringAttr>("role").getValue(), context) !=
          self)
        return absent(op);
      if (!llvm::all_of(args, present))
        return stopped(op, "incomplete", context);
      auto scope = std::make_shared<ScopeState>();
      auto result = invokeScoped(target(op, "callee"), scope, args, depth + 1);
      scope->active = false;
      return result;
    }
    case Kind::Elements:
    case Kind::Indices:
    case Kind::DomainRange:
    case Kind::Zip:
    case Kind::Product:
      return domainInstruction(op, args);
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
      return finite(op, args, op.getNumResults(), depth);
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
    case Kind::IndexLess:
      result.values.emplace_back(std::get<uint64_t>(args[0]) <
                                 std::get<uint64_t>(args[1]));
      break;
    case Kind::IndexPowerOfTwo: {
      auto exponent = std::get<uint64_t>(args[1]);
      result.values.emplace_back(exponent < 64 &&
                                 std::get<uint64_t>(args[0]) ==
                                     (uint64_t(1) << exponent));
      break;
    }
    case Kind::VectorLength:
      result.values.emplace_back(uint64_t(std::get<Vector>(args[0])->size()));
      break;
    case Kind::MultilinearRestrictPrefix: {
      const auto &input = *std::get<Vector>(args[0]);
      const auto &fixed = *std::get<Vector>(args[1]);
      if (auto failure = vectorWork(input.size()))
        return std::move(failure);
      if (auto failure = vectorWork(fixed.size()))
        return std::move(failure);
      auto values = std::make_shared<std::vector<APInt>>(input);
      // Raw restriction uses contiguous halves, truncated to the shorter half.
      // A relation's exact shape law is separate from this total operation.
      for (const APInt &coordinate : fixed) {
        size_t middle = values->size() / 2;
        if (auto failure = vectorWork(middle))
          return std::move(failure);
        for (size_t i = 0; i < middle; ++i) {
          const APInt &low = (*values)[i];
          const APInt &high = (*values)[middle + i];
          APInt difference = (high + modulus() - low).urem(modulus());
          (*values)[i] =
              (low + (difference * coordinate).urem(modulus())).urem(modulus());
        }
        values->resize(middle);
      }
      result.values.emplace_back(std::move(values));
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
      if (isa<exec::BooleanOp>(op)) {
        if (!std::get<Scope>(args[0])->active)
          return error("structured-reference-custody", "boolean scope");
        return packed(std::move(result));
      }
      break;
    case Kind::IntegerConstant:
      result.values.emplace_back(
          cast<IntegerAttr>(op.getAttr("value")).getValue().getZExtValue());
      break;
    case Kind::IntegerAdd:
      result.values.emplace_back(std::get<uint64_t>(args[0]) +
                                 std::get<uint64_t>(args[1]));
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
      if (code == Kind::Compare &&
          op.getOperand(0).getType().isSignlessInteger(64)) {
        result.values.emplace_back(std::get<uint64_t>(args[0]) <
                                   std::get<uint64_t>(args[1]));
        break;
      }
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
    default:
      return error("structured-reference-unsupported",
                   op.getName().getStringRef());
    }
    return result;
  }

  Expected<Outcome> block(Block &body, ArrayRef<Datum> inputs, unsigned depth,
                          const ProtocolContext *context = nullptr) {
    // The CFG loop charges each entered block, including the entry exactly
    // once. A second entry debit would change straight-line observer fuel.
    if (body.getNumArguments() != inputs.size())
      return error("structured-reference-signature", "block inputs");
    // Each invocation owns a fresh map. Missing SSA values are errors, never
    // default-constructed field zeros or remnants from another helper call.
    llvm::DenseMap<Value, Datum> values;
    Block *current = &body;
    Values incoming(inputs.begin(), inputs.end());
    while (true) {
      if (auto failure = tick(depth))
        return failure;
      if (current->getNumArguments() != incoming.size())
        return error("structured-reference-signature", "successor inputs");
      for (auto [argument, input] :
           llvm::zip(current->getArguments(), incoming)) {
        if (!matches(argument.getType(), input))
          return error("structured-reference-signature", "block input type");
        values[argument] = input;
      }
      Block *destination = nullptr;
      for (Operation &op : *current) {
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
        if (!result || result->stopped())
          return result;
        if (result->destination) {
          destination = result->destination;
          incoming = std::move(result->values);
          break;
        }
        if (op.hasTrait<OpTrait::IsTerminator>())
          return result;
        if (op.getNumResults() != result->values.size())
          return error("structured-reference-signature", "operation results");
        for (auto [output, value] :
             llvm::zip(op.getResults(), result->values)) {
          if (!matches(output.getType(), value))
            return error("structured-reference-signature",
                         "operation result type");
          values[output] = std::move(value);
        }
      }
      if (!destination || destination->getParent() != body.getParent())
        return error("structured-reference-ssa",
                     "missing or foreign successor");
      current = destination;
    }
  }

public:
  Reference(Operation *unit, const PrimitiveMap &primitives)
      : symbols(unit), primitives(primitives) {}
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
  auto result = Reference(unit, admission.checkedPrimitives())
                    .run(selected, *array, open);
  if (!result)
    return fail(result.takeError());
  outs() << printJson(*result) << '\n';
  return 0;
}

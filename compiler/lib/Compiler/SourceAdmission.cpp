#include "ComponentContracts.h"
#include "SourceView.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/ResourceUnit.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Operations.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Protocol/Services.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/SemanticFields.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include <functional>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol {
namespace {
StringRef sourceKind(Operation &op) {
  if (isa<protocol_ir::MathematicalOp>(op))
    return "protocol";
  if (auto function = dyn_cast<func::FuncOp>(op))
    return isScopedExecutionFunction(function) ? "local" : "math";
  if (isa<protocol_ir::OracleDefinitionOp>(op))
    return "oracle";
  if (isa<data::DomainOp>(op))
    return "domain";
  return {};
}
FunctionType sourceSignature(Operation &op) {
  auto attr = op.getAttrOfType<TypeAttr>("function_type");
  auto type = attr ? dyn_cast<FunctionType>(attr.getValue()) : FunctionType();
  if (auto function = dyn_cast<func::FuncOp>(op);
      function && isScopedExecutionFunction(function)) {
    if (!type || type.getNumInputs() == 0 || type.getNumResults() != 1)
      return {};
    auto outcome = dyn_cast<exec::OutcomeType>(type.getResult(0));
    if (!outcome || !isa<runtime::ScopeType>(type.getInput(0)))
      return {};
    return FunctionType::get(op.getContext(), type.getInputs().drop_front(),
                             outcome.getPayload());
  }
  return type;
}

// This is the supported source-analysis subset of native stage admission.
// Resource allowances count actual native work, never serialized rows, escaped
// text, publication depth or the size of an optional JSON snapshot.
class Admission {
  SourceView &view;
  SourceAllowance &allowance;
  protocol_ir::ProtocolModuleOp unit;
  SymbolTable symbols;
  Operation *definition = nullptr;
  ArrayAttr roles;
  llvm::StringSet<> sites;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> dependencies;

  Error metadata() {
    bool bounded = true;
    auto result = unit->walk([&](Operation *op) {
      if (!allowance.charge(1 + op->getNumOperands() + op->getNumResults()))
        return WalkResult::interrupt();
      for (auto named : op->getAttrs()) {
        if (!allowance.charge(1 + named.getName().getValue().size()))
          return WalkResult::interrupt();
        SmallVector<std::pair<Attribute, unsigned>> pending{
            {named.getValue(), 0}};
        while (!pending.empty()) {
          auto item = pending.pop_back_val();
          auto attr = item.first;
          unsigned depth = item.second;
          if (depth > 128)
            return WalkResult::interrupt();
          if (auto text = dyn_cast<StringAttr>(attr))
            if (!allowance.charge(text.getValue().size()))
              return WalkResult::interrupt();
          attr.walkImmediateSubElements(
              [&](Attribute child) {
                if (bounded && (bounded = allowance.charge()))
                  pending.emplace_back(child, depth + 1);
              },
              [](Type) {});
          if (!bounded)
            return WalkResult::interrupt();
        }
      }
      return WalkResult::advance();
    });
    return result.wasInterrupted() ? error("source-view-limit")
                                   : Error::success();
  }

  Error attributes(Operation &op, ArrayRef<StringRef> named = {}) {
    for (auto attr : op.getAttrs())
      if (!admitsField(&op, attr, named))
        return error("structured-source-attribute", attr.getName().getValue());
    return Error::success();
  }
  Error sort(Type type, unsigned depth = 0) {
    if (depth >= 128 || !allowance.charge())
      return error("source-view-limit");
    const auto &catalog = installedDomains();
    auto nominal = [&](StringRef kind, StringRef sort, StringRef identity) {
      return catalog.identitySort(identity) == sort &&
                     catalog.admitsLogicalType(kind, identity)
                 ? Error::success()
                 : error("structured-source-type");
    };
    if (type.isSignlessInteger(1) || type.isUnsignedInteger(64) ||
        isa<data::IndicesType>(type))
      return Error::success();
    if (auto field = dyn_cast<algebra::FieldType>(type))
      return nominal("field", "Field", field.getDomain());
    if (auto vector = dyn_cast<data::FieldVectorType>(type))
      return nominal("vector", "Field", vector.getDomain());
    if (auto polynomial = dyn_cast<poly::UnivariateType>(type))
      return nominal("polynomial", "Field", polynomial.getDomain());
    if (auto group = dyn_cast<algebra::GroupType>(type))
      return nominal("group", "Group", group.getDomain());
    if (auto vector = dyn_cast<data::GroupVectorType>(type))
      return nominal("groups", "Group", vector.getDomain());
    if (auto capability = dyn_cast<runtime::CapabilityType>(type);
        capability &&
        capability.getKind() == runtime::CapabilityKind::ResourceUnit)
      return resourceUnitDomain(capability.getIdentity())
                 ? Error::success()
                 : error("structured-source-type");
    auto kind = protocol_ir::getOracleFamilyKind(type);
    if (kind) {
      for (auto argument : kind.getArguments()) {
        if (auto child = dyn_cast<TypeAttr>(argument)) {
          if (auto e = sort(child.getValue(), depth + 1))
            return e;
        } else if (auto natural = dyn_cast<IntegerAttr>(argument);
                   !natural || !natural.getType().isUnsignedInteger(64))
          return error("structured-source-oracle-kind");
      }
      return Error::success();
    }
    if (auto sequence = dyn_cast<data::SequenceType>(type))
      return sort(sequence.getElementType(), depth + 1);
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      for (auto alternative : variant.getAlternatives())
        for (Type child : alternative.getPayload())
          if (auto e = sort(child, depth + 1))
            return e;
      return Error::success();
    }
    if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(type))
      return !depth && !randomServiceField(service.getContract()).empty()
                 ? Error::success()
                 : error("structured-source-service");
    return error("structured-source-type");
  }
  Error sorts(TypeRange values, bool services = false) {
    for (auto type : values) {
      if (!services && isa<protocol_ir::ServiceReferenceType>(type))
        return error("structured-source-service");
      if (auto e = sort(type))
        return e;
    }
    return Error::success();
  }
  Error reference(Operation &op, StringRef attr, ArrayRef<StringRef> kinds,
                  bool optional = false) {
    auto ref = op.getAttrOfType<FlatSymbolRefAttr>(attr);
    if (!ref && optional)
      return Error::success();
    auto *target = ref ? symbols.lookup(ref.getValue()) : nullptr;
    if (!target || !is_contained(kinds, sourceKind(*target)))
      return error("structured-source-reference");
    dependencies[definition].push_back(target);
    return Error::success();
  }
  Error fold(Operation &op) {
    if (auto e = reference(op, "domain", {"domain"}))
      return e;
    StringRef kind = isa<data::FiniteFoldOp>(op) ? "math" : "local";
    if (auto e =
            reference(op, isa<exec::CollectOp>(op) ? "body" : "step", {kind}))
      return e;
    return reference(op, "predicate", {kind}, true);
  }
  Error binding(runtime::BindingOp declaration) {
    auto emit = [&] {
      auto diagnostic = declaration.emitError();
      diagnostic.abandon();
      return diagnostic;
    };
    if (failed(readNativeBinding(emit, declaration, false)))
      return error("structured-source-binding");
    auto *profile = consumerProfileOperation("structured-source-primitives",
                                             declaration.getContract());
    if (!profile ||
        declaration.getArguments().size() != profile->staticParameters.size())
      return error("structured-source-binding");
    for (auto [argument, parameter] :
         zip(declaration.getArguments(), profile->staticParameters)) {
      auto domain = dyn_cast<StringAttr>(argument);
      if (parameter.kind != StaticKind::Domain || !domain ||
          (parameter.sort == "Slot" ? !resourceUnitDomain(domain.getValue())
                                    : installedDomains().identitySort(
                                          domain.getValue()) != parameter.sort))
        return error("structured-source-binding");
    }
    if (!declaration.getImplementation().empty())
      return error("structured-source-implementation");
    return attributes(*declaration);
  }
  bool hasRole(StringRef name) const {
    return roles &&
           is_contained(roles, StringAttr::get(roles.getContext(), name));
  }
  Error instruction(Operation &op, StringRef owner) {
    if (owner == "local") {
      // The native CFG reader owns complete scoped attribute and edge checks.
      if (isa<exec::ApplyOp, exec::BooleanOp, exec::TestOp, exec::RangeOp>(op))
        return Error::success();
      if (isa<func::CallOp>(op))
        return reference(op, "callee", {"local"});
      if (isa<exec::ComputeOp>(op))
        return reference(op, "callee", {"math"});
      if (isa<exec::FoldOp, exec::CollectOp>(op))
        return fold(op);
      return error("structured-source-operation", op.getName().getStringRef());
    }
    if (auto e = attributes(op))
      return e;
    StringRef name = op.getName().getStringRef();
    if (name == "protocol.branch" || name == "data.branch")
      return (owner == "protocol" || (owner == "math" && name == "data.branch"))
                 ? Error::success()
                 : error("structured-source-operation");
    if (isa<protocol_ir::RepeatOp>(op))
      return owner == "protocol" ? Error::success()
                                 : error("structured-source-operation");
    if (auto application = dyn_cast<protocol_ir::ApplyOp>(op)) {
      auto target =
          symbols.lookup<protocol_ir::MathematicalOp>(application.getCallee());
      if (owner != "protocol" || !target ||
          !target.getBody().front().getOps<protocol_ir::StatementOp>().empty())
        return error("structured-source-application");
      return reference(op, "callee", {"protocol"});
    }
    if (isa<data::IndexOp, data::EqualOp, data::LessOp, data::PowerOfTwoOp,
            data::IndexWrappingAddOp, data::IndexWrappingSubtractOp,
            data::IndexBitAndOp, data::IndexLogicalShiftRightOp,
            algebra::MultilinearRestrictPrefixOp, algebra::ConstantFieldOp,
            algebra::FieldAddOp, algebra::SubtractFieldOp,
            algebra::FieldMultiplyOp, algebra::FieldEqualOp,
            algebra::GroupIdentityOp, algebra::GroupAddOp,
            algebra::GroupScaleOp, algebra::GroupEqualOp, data::MakeOp,
            data::GetOp>(op))
      return Error::success();
    if (auto dim = dyn_cast<data::DimOp>(op))
      return dim.getAxis() == 0 &&
                     isa<data::FieldVectorType>(dim.getInput().getType())
                 ? Error::success()
                 : error("structured-source-operation");
    if (isa<protocol_ir::OracleSendOp, protocol_ir::OracleInputOp,
            protocol_ir::OracleComponentsOp, protocol_ir::OracleSequenceEmptyOp,
            protocol_ir::OracleSequenceAppendOp,
            protocol_ir::OracleSequenceAtOp,
            protocol_ir::OracleSequenceLengthOp, protocol_ir::OracleContentsOp,
            protocol_ir::OracleShapeOp, protocol_ir::OracleForgetShapeOp,
            protocol_ir::AssembleRolesOp, protocol_ir::RestrictRolesOp,
            protocol_ir::ExchangeOp, protocol_ir::StatementOp>(op))
      return owner == "protocol" ? Error::success()
                                 : error("structured-source-operation");
    if (isa<protocol_ir::OracleVirtualOp>(op)) {
      if (owner != "protocol")
        return error("structured-source-operation");
      return reference(op, "callee", {"oracle"});
    }
    if (isa<protocol_ir::OracleQueryOp>(op))
      return owner == "protocol" || owner == "oracle"
                 ? Error::success()
                 : error("structured-source-operation");
    if (auto query = dyn_cast<protocol_ir::QueryOp>(op)) {
      auto service = dyn_cast<protocol_ir::ServiceReferenceType>(
          query.getReference().getType());
      auto method =
          service ? serviceMethod(service.getContract(), query.getMethod())
                  : std::nullopt;
      if (owner != "protocol" || !method ||
          !protocol_ir::matchesServiceSignature(
              query.getInputs().getTypes(), query.getResultTypes(), *method))
        return error("structured-source-service");
      // Preserve the source rule: bounds/counts are positive constant u64s,
      // not values selected by an earlier message or a sampled result.
      if (query.getMethod() == "index" || query.getMethod() == "indices")
        for (Value input : query.getInputs()) {
          auto bound = input.getDefiningOp<data::IndexOp>();
          if (!bound || !uniformIndexBound(bound.getValue()))
            return error("structured-source-service");
        }
      return query.getMethod() == "draw" || query.getMethod() == "index" ||
                     query.getMethod() == "indices"
                 ? Error::success()
                 : error("structured-source-service");
    }
    if (isa<arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp>(op))
      return op.getResult(0).getType().isSignlessInteger(1)
                 ? Error::success()
                 : error("structured-source-operation");
    if (auto compare = dyn_cast<arith::CmpIOp>(op))
      return compare.getLhs().getType().isSignlessInteger(1) &&
                     (compare.getPredicate() == arith::CmpIPredicate::eq ||
                      compare.getPredicate() == arith::CmpIPredicate::ne)
                 ? Error::success()
                 : error("structured-source-operation");
    if (isa<arith::SelectOp>(op))
      return Error::success();
    if (isa<data::BoundedAtOp>(op))
      return isa<data::FieldVectorType>(op.getOperand(0).getType())
                 ? Error::success()
                 : error("structured-source-type");
    if (auto call = dyn_cast<func::CallOp>(op)) {
      auto target = symbols.lookup<func::FuncOp>(call.getCallee());
      if (!target || !target.isPrivate())
        return error("structured-source-reference");
      return reference(op, "callee", {"math"});
    }
    if (isa<protocol_ir::LocalCallOp>(op)) {
      auto role = op.getAttrOfType<StringAttr>("role");
      if (owner != "protocol" || !role || !hasRole(role.getValue()))
        return error("structured-source-role");
      return reference(op, "callee", {"local"});
    }
    if (isa<data::FiniteFoldOp>(op))
      return fold(op);
    if (auto guard = dyn_cast<protocol_ir::GuardOp>(op))
      return owner == "protocol" && hasRole(guard.getOwner())
                 ? Error::success()
                 : error("structured-source-role");
    return error("structured-source-operation", name);
  }
  Error body(const SourceBlock &block, StringRef owner, unsigned depth = 0) {
    if (depth > 128 || !allowance.charge())
      return error("source-view-limit");
    if (auto e = sorts(block.inputs, owner == "protocol"))
      return e;
    if (auto e = sorts(block.outputs))
      return e;
    auto site = [&](Operation &op, bool required) -> Error {
      auto attr = op.getAttrOfType<StringAttr>(
          isa<func::CallOp>(op) ? "runtime.site" : "site");
      if (attr) {
        if (!allowance.charge(attr.getValue().size()))
          return error("source-view-limit");
        if (!attr.getValue().empty() && sites.insert(attr.getValue()).second)
          return Error::success();
      } else if (!required)
        return Error::success();
      return error("structured-source-site");
    };
    for (const auto &step : block.instructions) {
      auto &op = *step.operation;
      if (auto e = sorts(step.results))
        return e;
      if (owner != "local")
        if (auto e =
                sorts(op.getOperandTypes(),
                      isa<protocol_ir::QueryOp, protocol_ir::ApplyOp,
                          protocol_ir::RepeatOp>(op) ||
                          op.getName().getStringRef() == "protocol.branch"))
          return e;
      if (auto e = instruction(op, owner))
        return e;
      if (auto e =
              site(op, owner == "local" ||
                           isa<protocol_ir::ExchangeOp, protocol_ir::QueryOp,
                               protocol_ir::GuardOp, protocol_ir::LocalCallOp,
                               protocol_ir::RepeatOp>(op)))
        return e;
      for (const auto &nested : step.regions)
        if (auto e = body(nested, owner, depth + 1))
          return e;
    }
    if (block.terminator == SourceTerminator::Stop)
      return site(*block.terminal, true);
    if (owner != "local")
      return attributes(*block.terminal);
    return Error::success();
  }
  Error function(Operation &op, StringRef kind) {
    SmallVector<StringRef> named;
    if (kind == "math")
      named = {"data.preconditions"};
    else if (kind == "local")
      named = {"runtime.origin", "no_inline", "data.preconditions"};
    else if (kind == "protocol")
      named = {"sym_visibility"};
    if (auto e = attributes(op, named))
      return e;
    auto type = sourceSignature(op);
    if (!type)
      return error("structured-source-region");
    if (kind != "local" &&
        (op.getNumRegions() != 1 || !hasSingleElement(op.getRegion(0)) ||
         op.getRegion(0).front().empty()))
      return error("structured-source-region");
    if (auto visibility = op.getAttrOfType<StringAttr>("sym_visibility");
        visibility && visibility.getValue() != "public" &&
        visibility.getValue() != "private")
      return error("structured-source-visibility");
    if (auto e = sorts(type.getInputs(), kind == "protocol"))
      return e;
    if (auto e = sorts(type.getResults()))
      return e;
    if (op.hasAttr("data.preconditions")) {
      auto premises = op.getAttrOfType<ArrayAttr>("data.preconditions");
      if (!premises)
        return error("structured-source-precondition");
      unsigned offset = kind == "local" ? 1 : 0;
      for (auto attr : premises) {
        auto bound = dyn_cast<data::IndexBoundAttr>(attr);
        if (!bound || bound.getAxis() != 0 || bound.getIndexArg() < offset ||
            bound.getContainerArg() < offset ||
            bound.getIndexArg() - offset >= type.getNumInputs() ||
            bound.getContainerArg() - offset >= type.getNumInputs() ||
            !type.getInput(bound.getIndexArg() - offset)
                 .isUnsignedInteger(64) ||
            !isa<data::FieldVectorType>(
                type.getInput(bound.getContainerArg() - offset)))
          return error("structured-source-precondition");
      }
    }
    roles = {};
    if (auto protocol = dyn_cast<protocol_ir::MathematicalOp>(op)) {
      roles = protocol.getRoles();
      auto origin = protocol_ir::readProtocolOrigin(op.getAttr("origin"));
      if (!origin)
        return origin.takeError();
    }
    if (kind == "local") {
      auto origin = op.getAttrOfType<ArrayAttr>("runtime.origin");
      if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
          !isa<ArrayAttr>(origin[1]))
        return error("structured-source-origin");
      for (auto component : cast<ArrayAttr>(origin[1])) {
        auto pair = dyn_cast<ArrayAttr>(component);
        if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
            !isa<StringAttr>(pair[1]))
          return error("structured-source-origin");
      }
    }
    auto indexed =
        buildSourceDefinition(op, SymbolTable::getSymbolName(&op).getValue(),
                              kind, view.execution, allowance);
    if (!indexed)
      return indexed.takeError();
    if (auto e = body(indexed->body, kind))
      return e;
    view.names.emplace(indexed->name, view.definitions.size());
    view.definitions.push_back(std::move(*indexed));
    return Error::success();
  }
  Error preparationProfiles() {
    llvm::DenseSet<Operation *> computationChecked;
    std::function<Error(Operation *)> check = [&](Operation *op) -> Error {
      if (!allowance.charge())
        return error("source-view-limit");
      if (computationChecked.contains(op))
        return Error::success();
      StringRef code = "structured-source-realization";
      auto helper = dyn_cast<func::FuncOp>(op);
      if (!helper || helper.isExternal() || !helper.isPrivate() ||
          helper->getParentOp() != unit.getOperation())
        return error(code, "private Math closure required");
      SmallVector<Operation *> actual;
      helper.getBody().walk<WalkOrder::PreOrder>(
          [&](Operation *op) { actual.push_back(op); });
      for (Operation *nested : actual) {
        if (!allowance.charge())
          return error("source-view-limit");
        Operation &instruction = *nested;
        if (auto call = dyn_cast<func::CallOp>(instruction)) {
          if (auto e = check(symbols.lookup(call.getCallee())))
            return e;
          continue;
        }
        if (isa<data::FiniteFoldOp>(instruction)) {
          // Ordinary formation discharges callback bounds at each call edge.
          // Both callbacks belong to admission even for an empty domain.
          for (StringRef attribute : {"step", "predicate"}) {
            auto reference =
                instruction.getAttrOfType<FlatSymbolRefAttr>(attribute);
            if (reference)
              if (auto e = check(symbols.lookup(reference.getValue())))
                return e;
          }
          continue;
        }
        bool allowed = isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
                           algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
                           func::ReturnOp>(instruction);
        allowed |=
            isa<algebra::MultilinearRestrictPrefixOp, algebra::FieldEqualOp,
                algebra::GroupIdentityOp, algebra::GroupAddOp,
                algebra::GroupScaleOp, algebra::GroupEqualOp, data::IndexOp,
                data::EqualOp, data::LessOp, data::PowerOfTwoOp,
                data::IndexWrappingAddOp, data::IndexWrappingSubtractOp,
                data::IndexBitAndOp, data::IndexLogicalShiftRightOp,
                data::DimOp, data::MakeOp, data::GetOp, data::BoundedAtOp,
                arith::ConstantOp, arith::AndIOp, arith::OrIOp, arith::XOrIOp,
                arith::CmpIOp, arith::SelectOp>(instruction);
        bool selected = instruction.getName().getStringRef() == "data.branch";
        allowed |=
            selected || instruction.getName().getStringRef() == "data.yield";
        if (!allowed || (instruction.getNumRegions() && !selected))
          return error(code, instruction.getName().getStringRef());
      }
      computationChecked.insert(op);
      return Error::success();
    };
    for (auto *origin : view.execution.computations)
      if (auto call = dyn_cast<exec::ComputeOp>(origin)) {
        auto *root = symbols.lookup(call.getCallee().getRootReference());
        if (!root)
          return error("structured-source-realization",
                       "sibling helper required");
        if (auto premises =
                root->getAttrOfType<ArrayAttr>("data.preconditions");
            premises && !premises.empty())
          return error("structured-source-realization", "root preconditions");
        if (auto e = check(root))
          return e;
      }
    return Error::success();
  }

  Error closure() {
    // Height is the longest reference path in edges; a leaf has height zero.
    // Memoize heights, not only colors: a shared helper encountered first on a
    // short path must still count its whole suffix on a later, longer path.
    llvm::DenseMap<Operation *, unsigned> heights;
    llvm::DenseSet<Operation *> active;
    std::function<Expected<unsigned>(Operation *, unsigned)> visit =
        [&](Operation *op, unsigned depth) -> Expected<unsigned> {
      if (depth > 128 || !allowance.charge())
        return error("source-view-limit");
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
        if (height > 128)
          return error("source-view-limit");
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

  Error effectiveSites() {
    // Native verification already checks its conservative application/Math
    // expansion budget. Independently check final protocol-site collisions,
    // without cloning syntax or entering the separate closed helper namespace.
    llvm::StringSet<> effective;
    std::function<Error(Block &, StringRef, unsigned, unsigned)> visit =
        [&](Block &body, StringRef prefix, unsigned applicationDepth,
            unsigned repeatDepth) -> Error {
      if (applicationDepth > 128 || repeatDepth > 128)
        return error("source-view-limit");
      for (Operation &op : body) {
        if (!allowance.charge())
          return error("source-view-limit");
        auto site = op.getAttrOfType<StringAttr>("site");
        if (!site)
          continue;
        StringRef leaf = site.getValue();
        auto length = std::to_string(prefix.size());
        size_t overhead =
            prefix.empty() ? 0 : 8 + length.size() + prefix.size();
        if (!allowance.charge(1 + overhead + leaf.size()))
          return error("source-view-limit");
        std::string rendered =
            prefix.empty()
                ? leaf.str()
                : "apply_" + length + "_" + prefix.str() + "_" + leaf.str();
        if (auto call = dyn_cast<protocol_ir::ApplyOp>(op)) {
          // Headers disappear, but their rendered labels advance the context
          // and count toward metadata work. Revisit each static occurrence.
          if (auto e = visit(
                  symbols.lookup<protocol_ir::MathematicalOp>(call.getCallee())
                      .getBody()
                      .front(),
                  rendered, applicationDepth + 1, repeatDepth))
            return e;
        } else if (!effective.insert(rendered).second) {
          return error("structured-source-site", "expanded protocol collision");
        }
        if (op.getName().getStringRef() == "protocol.branch") {
          // Stored native sites already encode lexical arm identity. Only
          // application expansion adds an effective-site prefix.
          for (auto &nested : op.getRegions()) {
            if (auto e = visit(nested.front(), prefix, applicationDepth,
                               repeatDepth + 1))
              return e;
          }
        }
        if (auto repeat = dyn_cast<protocol_ir::RepeatOp>(op))
          // A repeat header survives expansion. Its body has the same static
          // prefix and is visited once, even when maximum is zero.
          if (auto e = visit(repeat.getBody().front(), prefix, applicationDepth,
                             repeatDepth + 1))
            return e;
      }
      return Error::success();
    };
    for (auto function :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      effective.clear();
      if (auto e = visit(function.getBody().front(), {}, 1, 0))
        return e;
    }
    return Error::success();
  }
  Error portRosters(ArrayAttr protocols) {
    for (Attribute value : protocols) {
      if (!allowance.charge())
        return error("source-view-limit");
      auto owner = cast<ArrayAttr>(value);
      auto function = symbols.lookup<protocol_ir::MathematicalOp>(
          cast<StringAttr>(owner[0]).getValue());
      if (!function)
        return error("component-declaration-role");
      std::map<StringRef, unsigned> roster;
      for (auto [index, role] : llvm::enumerate(function.getRoles()))
        roster.emplace(cast<StringAttr>(role).getValue(), index);
      std::function<Error(ArrayAttr)> inside = [&](ArrayAttr node) -> Error {
        if (!allowance.charge())
          return error("source-view-limit");
        auto known = [&](Attribute role) {
          return roster.count(cast<StringAttr>(role).getValue()) != 0;
        };
        auto all = [&](Attribute roles) {
          return llvm::all_of(cast<ArrayAttr>(roles), known);
        };
        auto tag = cast<StringAttr>(node[0]).getValue();
        if (tag == "data")
          return all(node[1]) ? Error::success()
                              : error("component-declaration-role");
        if (tag == "oracle")
          return known(node[1]) && all(node[2])
                     ? Error::success()
                     : error("component-declaration-role");
        if (!all(node[1]))
          return error("component-declaration-role");
        for (Attribute child : cast<ArrayAttr>(node[2]))
          if (auto e = inside(cast<ArrayAttr>(child)))
            return e;
        return Error::success();
      };
      for (unsigned side : {1u, 2u})
        for (Attribute port : cast<ArrayAttr>(owner[side])) {
          auto row = cast<ArrayAttr>(port);
          if (auto e = inside(cast<ArrayAttr>(row[5])))
            return e;
          std::optional<unsigned> previous;
          for (Attribute role : cast<ArrayAttr>(row[2])) {
            auto at = roster.at(cast<StringAttr>(role).getValue());
            if (previous && at <= *previous)
              return error("component-declaration-role");
            previous = at;
          }
        }
    }
    return Error::success();
  }

  Error domain(data::DomainOp domain) {
    if (domain.getSymVisibility() != "private")
      return error("structured-source-domain");
    if (auto e = attributes(*domain))
      return e;
    if (auto e = sorts(domain.getFunctionType().getInputs()))
      return e;
    for (auto &op : domain.getBody().front()) {
      if (!allowance.charge(1 + op.getNumOperands()))
        return error("source-view-limit");
      if (auto e = attributes(op))
        return e;
      if (isa<data::DomainYieldOp>(op))
        continue;
      if (!isa<data::DomainElementsOp, data::DomainIndicesOp,
               data::DomainRangeOp, data::DomainZipOp, data::DomainProductOp>(
              op))
        return error("structured-source-domain");
      if (isa<data::DomainElementsOp, data::DomainIndicesOp>(op) &&
          !isa<data::FieldVectorType, data::SequenceType>(
              op.getOperand(0).getType()))
        return error("structured-source-domain");
      if (auto indices = dyn_cast<data::DomainIndicesOp>(op);
          indices && indices.getAxis() != 0)
        return error("structured-source-domain");
      if (auto e = sorts(
              cast<data::DomainType>(op.getResult(0).getType()).getItemTypes()))
        return e;
    }
    return Error::success();
  }

public:
  Admission(SourceView &view, SourceAllowance &allowance)
      : view(view), allowance(allowance),
        unit(cast<protocol_ir::ProtocolModuleOp>(
            view.native->getBody()->front())),
        symbols(unit) {}
  Error run() {
    if (auto e = metadata())
      return e;
    if (auto e = attributes(*unit))
      return e;
    auto closureView = readSourceExecutionClosure(unit);
    if (!closureView)
      return closureView.takeError();
    view.execution = std::move(*closureView);
    llvm::StringSet<> names;
    for (auto &op : unit.getBody().front()) {
      if (!allowance.charge())
        return error("source-view-limit");
      auto name = op.getAttrOfType<StringAttr>("sym_name");
      if (!name || name.getValue().empty() ||
          !names.insert(name.getValue()).second)
        return error("structured-source-symbol");
      definition = &op;
      sites.clear();
      dependencies.try_emplace(&op);
      if (auto declaration = dyn_cast<data::DomainOp>(op)) {
        if (auto e = domain(declaration))
          return e;
      } else if (auto declaration = dyn_cast<runtime::BindingOp>(op)) {
        if (auto e = binding(declaration))
          return e;
      } else if (auto relation = dyn_cast<relation::DeclareOp>(op)) {
        if (auto e = attributes(op))
          return e;
        if (auto e = sorts(relation.getSignature().getInputs()))
          return e;
        if (auto e = sorts(relation.getSignature().getResults()))
          return e;
      } else if (auto outlined = dyn_cast<func::FuncOp>(op);
                 outlined && outlined->hasAttr("runtime.region")) {
        // The closure checked this actual CFG; its logical occurrences are
        // indexed at each use, retaining distinct formal argument identities.
      } else {
        auto kind = sourceKind(op);
        if (kind.empty())
          return error("structured-source-operation",
                       op.getName().getStringRef());
        if (auto e = function(op, kind))
          return e;
      }
    }
    if (auto e = closure())
      return e;
    if (auto e = preparationProfiles())
      return e;
    if (auto e = effectiveSites())
      return e;
    if (auto attr = unit->getAttr("source_declarations")) {
      if (auto e = language::checkComponentDeclarations(attr, allowance))
        return e;
      if (auto e = portRosters(cast<ArrayAttr>(cast<ArrayAttr>(attr)[1])))
        return e;
    }
    return Error::success();
  }
};
} // namespace
Error indexSource(SourceView &view, SourceAllowance &allowance) {
  return Admission(view, allowance).run();
}
} // namespace zkc::protocol

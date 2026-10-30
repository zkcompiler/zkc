#include "ClosureAdmission.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Exec/ResourceOrigins.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol::detail {
namespace {
// This profile deliberately bounds both expanded control occurrences and
// declaration work. Byte encodings impose their separate nesting/size limits.
constexpr unsigned maximumPorts = 1024, maximumDepth = 64;
constexpr uint64_t maximumInstructions = 65536;
bool occurrenceName(StringRef name) {
  return !name.empty() && name.size() <= 128 &&
         (isAlpha(name.front()) || name.front() == '_') &&
         all_of(name, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}
struct Summary {
  unsigned height = 1;
  bool history = false;
};
class Admission {
  Operation *owner;
  const SourceExecutionClosure &closure;
  bool physical;
  uint64_t &remaining;
  SymbolTableCollection symbols;
  mathematical::NativeTypePolicies types;
  llvm::DenseMap<Operation *, ArrayRef<SourceExecutionStep>> bodies;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> edges;
  llvm::DenseMap<Operation *, Summary> summaries;
  llvm::DenseSet<Operation *> active, directHistory;
  llvm::DenseMap<Type, LogicalTypePermissions> permissions;
  std::string code, detail;
  uint64_t instructions = 0;

  bool fail(StringRef reason, StringRef message) {
    if (code.empty()) {
      code = reason.str();
      detail = message.str();
    }
    return false;
  }
  bool charge(uint64_t amount = 1) {
    if (amount > remaining)
      return fail("execution-analysis-limit", "closure work limit exceeded");
    remaining -= amount;
    return true;
  }
  bool type(Type type) {
    if (!charge())
      return false;
    if (permissions.contains(type))
      return true;
    auto represented = dyn_cast<runtime::RepresentedType>(type);
    if (bool(represented) != physical)
      return fail("execution-cfg", "data value differs from closure stage");
    auto logical = logicalValueType(type);
    if (mathematical::isFormalType(logical) || !types.get(logical))
      return fail("execution-cfg", "data type has no executable use policy");
    LogicalTypePermissions facts;
    auto emit = [&] {
      auto diagnostic = owner->emitError();
      diagnostic.abandon();
      return diagnostic;
    };
    if (failed(verifyLogicalType(emit, logical, &facts)) ||
        (physical && failed(verifyValueType(emit, type))))
      return fail("execution-cfg", "data value type is not formed");
    permissions.try_emplace(type, facts);
    return true;
  }
  bool ports(TypeRange ports, bool boundary = false) {
    if (ports.size() > maximumPorts)
      return fail("execution-cfg", "too many data ports");
    for (Type port : ports) {
      if (!type(port))
        return false;
      auto represented = dyn_cast<runtime::RepresentedType>(port);
      if (boundary && represented &&
          isDiagonalRepresentation(represented.getRepresentation()))
        return fail("execution-cfg",
                    "diagonal storage cannot cross function ports");
    }
    return true;
  }
  bool addEdge(Operation *function, Operation *target) {
    if (!target || target->getParentOp() != owner || !bodies.contains(target))
      return fail("execution-cfg", "callee is outside the scoped closure");
    edges[function].push_back(target);
    return true;
  }
  bool index() {
    if (!owner || !owner->hasTrait<OpTrait::SymbolTable>())
      return fail("execution-cfg", "closure has no symbol owner");
    for (const auto &[name, body] : closure.bodies) {
      if (!charge())
        return false;
      auto function = symbols.lookupSymbolIn<func::FuncOp>(
          owner, StringAttr::get(owner->getContext(), name));
      if (!function || !occurrenceName(name) || function.isExternal() ||
          body.empty() || !function.getNumArguments() ||
          !isa<runtime::ScopeType>(function.getArgument(0).getType()))
        return fail("execution-cfg", "missing scoped body association");
      auto result = function.getResultTypes();
      auto outcome = result.size() == 1 ? dyn_cast<exec::OutcomeType>(result[0])
                                        : exec::OutcomeType();
      if (!outcome || !ports(function.getArgumentTypes().drop_front(), true) ||
          !ports(outcome.getPayload(), true))
        return fail("execution-cfg", "invalid scoped data signature");
      if (!function->hasAttr("runtime.region")) {
        auto origin = function->getAttrOfType<ArrayAttr>("runtime.origin");
        if (!origin || origin.size() != 2 || !isa<StringAttr>(origin[0]) ||
            !occurrenceName(cast<StringAttr>(origin[0]).getValue()) ||
            !isa<ArrayAttr>(origin[1]) ||
            cast<ArrayAttr>(origin[1]).size() > 128)
          return fail("execution-cfg", "invalid logical callable origin");
        llvm::StringSet<> parameters;
        for (Attribute item : cast<ArrayAttr>(origin[1])) {
          auto pair = dyn_cast<ArrayAttr>(item);
          if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
              !isa<StringAttr>(pair[1]))
            return fail("execution-cfg", "invalid origin argument");
          auto key = cast<StringAttr>(pair[0]).getValue();
          auto value = cast<StringAttr>(pair[1]).getValue();
          if (!occurrenceName(key) || !parameters.insert(key).second ||
              (installedIdentitySort(value).empty() &&
               !staticIdentityMatches("Nat", value) &&
               !staticIdentityMatches("Type", value)))
            return fail("execution-cfg", "invalid origin argument identity");
        }
      }
      bodies.try_emplace(function, body);
      edges.try_emplace(function);
    }
    for (const auto &[function, body] : bodies)
      for (const auto &step : body) {
        if (!charge(1 + step.regions.size()))
          return false;
        if (!step.operation ||
            step.operation->getParentOfType<func::FuncOp>() !=
                cast<func::FuncOp>(function))
          return fail("execution-cfg", "step does not belong to its function");
        for (auto region : step.regions)
          if (!addEdge(function, region))
            return false;
        if (auto call = dyn_cast<func::CallOp>(step.operation)) {
          if (!addEdge(function, symbols.lookupSymbolIn<func::FuncOp>(
                                     owner, call.getCalleeAttr())))
            return false;
        } else if (isa<exec::FoldOp, exec::CollectOp>(step.operation)) {
          finite::Computation computation;
          if (failed(finite::describe(step.operation, computation, owner,
                                      &symbols)) ||
              !computation.scoped)
            return fail("execution-cfg", "invalid finite callback closure");
          for (auto *callback : {computation.helper, computation.predicate})
            if (callback && !addEdge(function, callback))
              return false;
        } else if (auto call = dyn_cast<exec::ApplyOp>(step.operation)) {
          auto binding = symbols.lookupSymbolIn<runtime::BindingOp>(
              owner, call.getBindingAttr());
          if (!binding)
            return fail("execution-cfg", "missing actual operation binding");
          if (isHistoryTransition(binding.getContract()))
            directHistory.insert(function);
        }
      }
    return true;
  }
  const Summary *summary(Operation *function, unsigned depth = 1) {
    if (!charge())
      return nullptr;
    if (!depth || depth > maximumDepth) {
      fail("execution-call-depth", "scoped call/control nesting exceeded");
      return nullptr;
    }
    if (auto found = summaries.find(function); found != summaries.end()) {
      if (found->second.height > maximumDepth - depth + 1) {
        fail("execution-call-depth", "cached callee depth exceeds this path");
        return nullptr;
      }
      return &found->second;
    }
    if (!active.insert(function).second) {
      fail("execution-call-cycle", "scoped call or callback cycle");
      return nullptr;
    }
    auto release = llvm::scope_exit([&] { active.erase(function); });
    Summary result;
    result.history = directHistory.contains(function);
    for (auto *target : edges[function]) {
      const auto *child = summary(target, depth + 1);
      if (!child)
        return nullptr;
      result.height = std::max(result.height, child->height + 1);
      result.history |= child->history;
    }
    return &summaries.try_emplace(function, result).first->second;
  }
  bool uses(func::FuncOp function, ArrayRef<SourceExecutionStep> body) {
    llvm::DenseSet<Value> available, consumed, diagonalUses;
    for (Value argument : function.getArguments().drop_front())
      available.insert(argument);
    auto consume = [&](ValueRange values, bool release = false) {
      if (!charge(values.size()) || values.size() > maximumPorts)
        return fail("execution-cfg", "too many data operands");
      for (Value value : values) {
        if (!available.contains(value) || !type(value.getType()))
          return fail("execution-cfg", "data value is outside its body");
        auto facts = permissions.lookup(value.getType());
        if (consumed.contains(value) ||
            ((release || !facts.copy) && !consumed.insert(value).second))
          return fail("execution-resource-reuse",
                      "data value already consumed");
        if (release && !facts.drop)
          return fail("execution-cfg", "released value lacks Drop");
      }
      return true;
    };
    for (const auto &step : body) {
      if (!charge())
        return false;
      auto *op = step.operation;
      bool terminal = isa<exec::ReturnOp, exec::CompleteOp, exec::RejectOp>(op);
      if (terminal != (&step == &body.back()))
        return fail("execution-cfg", "body must have one final completion");
      if (isa<runtime::ReleaseBindingsOp>(op)) {
        if (!physical || step.inputs.empty() || !consume(step.inputs, true))
          return fail("execution-cfg",
                      "storage release requires physical data");
      } else if (isa<exec::RangeOp>(op)) {
        unsigned states = step.outputs.size();
        if (step.regions.size() != 1 || step.inputs.size() < 2 + states ||
            !consume(ValueRange(step.inputs).take_front(2 + states)))
          return fail("execution-cfg", "invalid iteration data ports");
        for (Value capture : ValueRange(step.inputs).drop_front(2 + states)) {
          if (!available.contains(capture) || consumed.contains(capture) ||
              !type(capture.getType()) ||
              !permissions.lookup(capture.getType()).copy)
            return fail("execution-cfg", "iteration invariants require Copy");
        }
        auto region = step.regions.front();
        auto signature = cast<exec::OutcomeType>(region.getResultTypes()[0]);
        auto results = signature.getPayload();
        TypeRange inputTypes = ValueRange(step.inputs).getTypes();
        SmallVector<Type> expected{step.inputs[0].getType()};
        append_range(expected, inputTypes.drop_front(2));
        if (TypeRange(region.getArgumentTypes().drop_front()) !=
                TypeRange(expected) ||
            results.size() != states + unsigned(step.conditional) ||
            TypeRange(results.drop_front(unsigned(step.conditional))) !=
                ValueRange(step.inputs)
                    .drop_front(2)
                    .take_front(states)
                    .getTypes() ||
            ValueRange(step.outputs).getTypes() !=
                results.drop_front(unsigned(step.conditional)))
          return fail("execution-cfg", "iteration state signature differs");
        if (step.conditional &&
            (!logicalValueType(results.front()).isInteger(1) ||
             !isa<exec::CompleteOp>(bodies.lookup(region).back().operation)))
          return fail("execution-cfg",
                      "conditional iteration requires a Boolean yield");
      } else if (!consume(step.inputs))
        return false;
      if (auto call = dyn_cast<exec::ApplyOp>(op)) {
        auto binding = symbols.lookupSymbolIn<runtime::BindingOp>(
            owner, call.getBindingAttr());
        for (auto [i, input] : enumerate(step.inputs)) {
          auto represented =
              dyn_cast<runtime::RepresentedType>(input.getType());
          if (!represented ||
              !isDiagonalRepresentation(represented.getRepresentation()))
            continue;
          if (!physical || i != 1 ||
              (binding.getContract() != "vector.dot" &&
               binding.getContract() != "curve.msm"))
            return fail("execution-cfg",
                        "diagonal storage requires its contraction slot");
          diagonalUses.insert(input);
        }
      }
      if (auto reject = dyn_cast<exec::RejectOp>(op)) {
        if (!is_contained(ArrayRef<StringRef>{"reject", "abort", "exhausted",
                                              "incomplete", "refused"},
                          reject.getReason()))
          return fail("execution-cfg", "unknown explicit stop reason");
      } else if (isa<exec::TestOp, exec::MatchOp>(op)) {
        bool yields = false;
        for (auto region : step.regions) {
          auto last = bodies.lookup(region).back().operation;
          yields |= isa<exec::CompleteOp>(last);
          if (isa<exec::MatchOp>(op) && summaries.lookup(region).history)
            return fail("execution-match-history",
                        "match arm changes ordered history");
        }
        if (!yields && !step.outputs.empty())
          return fail("execution-cfg", "stopped arms cannot produce data");
      }
      if (!ports(ValueRange(step.outputs).getTypes()))
        return false;
      for (Value output : step.outputs)
        if (!available.insert(output).second)
          return fail("execution-cfg", "data result is already available");
    }
    for (auto value : available) {
      auto represented = dyn_cast<runtime::RepresentedType>(value.getType());
      if (represented &&
          isDiagonalRepresentation(represented.getRepresentation()) &&
          !diagonalUses.contains(value))
        return fail("execution-cfg",
                    "diagonal storage has no contraction consumer");
    }
    return true;
  }
  bool occurrences(Operation *function, llvm::StringSet<> &sites,
                   unsigned depth = 1) {
    if (depth > maximumDepth)
      return fail("execution-call-depth", "outlined control nesting exceeded");
    for (const auto &step : bodies.lookup(function)) {
      if (!charge() || ++instructions > maximumInstructions)
        return fail("execution-analysis-limit",
                    "expanded control instruction limit");
      auto *op = step.operation;
      if (!isa<exec::ReturnOp, exec::CompleteOp, runtime::ReleaseBindingsOp>(
              op)) {
        auto site = op->getAttrOfType<StringAttr>(
            isa<func::CallOp>(op) ? "runtime.site" : "site");
        if (!site || !occurrenceName(site.getValue()) ||
            !sites.insert(site.getValue()).second)
          return fail("execution-cfg",
                      "missing, invalid or duplicate occurrence");
      }
      for (auto region : step.regions)
        if (!occurrences(region, sites, depth + 1))
          return false;
    }
    return true;
  }

public:
  Admission(Operation *owner, const SourceExecutionClosure &closure,
            bool physical, uint64_t &remaining)
      : owner(owner), closure(closure), physical(physical),
        remaining(remaining), types(owner) {}
  Error run() {
    bool valid = index();
    if (valid)
      for (const auto &[function, body] : bodies)
        if (!summary(function)) {
          valid = false;
          break;
        }
    if (valid)
      for (const auto &[function, body] : bodies) {
        if (!uses(cast<func::FuncOp>(function), body)) {
          valid = false;
          break;
        }
        if (!function->hasAttr("runtime.region")) {
          llvm::StringSet<> sites;
          if (!occurrences(function, sites)) {
            valid = false;
            break;
          }
        }
      }
    if (!valid)
      return error(code, detail);
    if (!physical) {
      // The root checker receives only actual body/value associations. Other
      // consumers' temporary export records grant no facts to native admission.
      SourceExecutionClosure view;
      view.bodies = closure.bodies;
      auto roots = exec::ResourceOriginAnalysis::create(
          owner, std::move(view), remaining, maximumDepth);
      if (!roots)
        return roots.takeError();
      if (auto failure = (*roots)->verifyFiniteState())
        return failure;
    }
    return Error::success();
  }
};
} // namespace
Error verifyClosureUses(Operation *owner, const SourceExecutionClosure &closure,
                        bool physical, uint64_t &remaining) {
  return Admission(owner, closure, physical, remaining).run();
}
} // namespace zkc::protocol::detail

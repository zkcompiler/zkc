//===- ConstructionGraph.h - internal typed construction routes -*- C++ -*-===//
#ifndef ZKC_LIB_SEMANTICS_CONSTRUCTIONGRAPH_H
#define ZKC_LIB_SEMANTICS_CONSTRUCTIONGRAPH_H

#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <string>

namespace zkc::semantics {

namespace detail {
class ConstructionGraphBuilder;
}

enum class RouteReferenceKind {
  Bind,
  Slot,
  Challenge,
  Constant,
  Witness,
  InstanceResult,
};

/// Parsed syntax for one construction-route edge. Instance names may contain
/// dotted namespace segments; only the final `.<decimal>` suffix denotes a
/// result index.
struct RouteReference {
  RouteReferenceKind kind = RouteReferenceKind::Bind;
  std::string name;
  uint64_t output = 0;
};

llvm::Expected<RouteReference> parseRouteReference(llvm::StringRef text);
std::string printRouteReference(const RouteReference &reference);
bool isRouteInstanceName(llvm::StringRef name);

/// A typed, non-persisted view of the route dictionary attached to one PIR
/// container. Building it IS the construction-route judgment: the builder is
/// the single owner of every zkc-E223 refusal (contract resolution, parameter
/// and operand shape, dependency acyclicity, slot-binding legality, temporal
/// availability), and a graph value exists only for a route dictionary that
/// passed it. The value itself carries facts, not verdicts — it owns strings,
/// copied contracts, and typed edges; slot operations remain tied to the
/// current IR epoch.
class ConstructionGraph {
public:
  struct Witness {
    std::string label;
    std::string handleClass;
  };

  struct Instance {
    std::string name;
    std::string contractId;
    registry::HoleContract contract;
    mlir::DictionaryAttr parameters;
    llvm::SmallVector<RouteReference> inputs;
    llvm::SmallVector<std::string> dependencies;
  };

  static mlir::FailureOr<ConstructionGraph>
  build(mlir::Operation *container,
        const registry::ProtocolEnvironment &environment);

  llvm::ArrayRef<Witness> witnesses() const { return witnesses_; }
  llvm::ArrayRef<Instance> instances() const { return instances_; }

  const RouteReference *slotBinding(pir::SlotOp slot) const;

  /// The exact HoleContract citation section to stamp into a sealed artifact.
  mlir::DictionaryAttr resolvedHoleContracts(mlir::MLIRContext *context) const;

private:
  friend class detail::ConstructionGraphBuilder;

  llvm::SmallVector<Witness> witnesses_;
  llvm::SmallVector<Instance, 0> instances_;
  llvm::DenseMap<mlir::Operation *, RouteReference> slotBindings_;
};

namespace detail {

/// Run the complete Open-PIR judgment and return its typed construction graph.
/// This is an implementation seam shared by sealing and static linking, not a
/// public acceptance capability.
mlir::FailureOr<ConstructionGraph>
judgeOpenProtocol(pir::ProtocolOp protocol,
                  const registry::ProtocolEnvironment &environment);

} // namespace detail

} // namespace zkc::semantics

#endif // ZKC_LIB_SEMANTICS_CONSTRUCTIONGRAPH_H

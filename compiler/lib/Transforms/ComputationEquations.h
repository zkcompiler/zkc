#ifndef ZKC_TRANSFORMS_COMPUTATIONEQUATIONS_H
#define ZKC_TRANSFORMS_COMPUTATIONEQUATIONS_H

#include "zkc/Analysis/Computation.h"
#include "zkc/Analysis/ComputationWork.h"

namespace zkc::mathematical {
/// Transient equations over borrowed admitted SSA. No recipes, targets, or
/// replacement permission are implied by a match.
struct EquationWitness {
  llvm::SmallVector<mlir::Operation *> occurrencePath;
  llvm::SmallVector<finite::AxisIdentity> freeAxes, reducedAxes;
  llvm::SmallVector<finite::Access> accesses;
  finite::InputReference seed;
  mlir::Value yielded;
  /// Admission remains attached to this occurrence; nested matching never
  /// grants permission to hoist it above the outer iteration's empty case.
  llvm::SmallVector<mlir::Operation *> admission;
  llvm::SmallVector<finite::ArgumentReference> environment;
};
struct Reduction {
  EquationWitness witness;
  MathematicalIdentity combine;
  std::optional<MathematicalIdentity> termIdentity;
  /// Inputs in scalar term operand order, before any native permutation.
  llvm::SmallVector<unsigned> inputs;
  std::optional<unsigned> selectedIndex;
  /// Position in inputs/accesses with the matrix role. Other inputs retain
  /// source order, including the group/scalar order of a module action.
  std::optional<unsigned> matrixOperand;
  std::optional<finite::AccessKind> matrixAccess;
  llvm::SmallVector<finite::Access> accesses;
  mlir::Value accumulator, term;
  mlir::Operation *combiner = nullptr;
};
struct Bilinear {
  EquationWitness witness;
  mlir::Value matrix, left, right;
};

struct Elementwise {
  /// Scalar indexed reads that the lane emitter replaces by their container.
  llvm::DenseMap<mlir::Value, mlir::Value> lookups;
};
/// Common lane classification for an existing scalar SSA block. Every
/// instruction is inspected, including unused instructions. indices maps an
/// enumerated index to the exact captured container it traverses. Other exact
/// field arguments are uniform; the returned view retains only emitter inputs.
std::optional<Elementwise>
matchLaneFormula(mlir::Block &body, mlir::Type field,
                 mlir::ValueRange laneArguments,
                 const llvm::DenseMap<mlir::Value, mlir::Value> &indices =
                     llvm::DenseMap<mlir::Value, mlir::Value>());

std::optional<std::pair<unsigned, unsigned>>
matchMapProduct(mlir::Block &formula, llvm::ArrayRef<bool> rowwise);

struct ComputationEquations {
  std::optional<Reduction> reduction;
  std::optional<Elementwise> elementwise;
  std::optional<Bilinear> bilinear;
};
ComputationEquations matchComputation(const finite::ComputationView &view);
ComputationEquations
matchComputation(const finite::ComputationView &view,
                 finite::ComputationWork &work,
                 finite::ComputationDiagnostic *diagnostic = nullptr);

struct ContractionSeed {
  std::optional<unsigned> input;
  std::string constant;
};
struct NestedContraction {
  EquationWitness witness;
  finite::Computation outer, inner;
  mlir::Operation *call = nullptr;
  unsigned matrix = 0, vector = 0, axis = 0;
  ContractionSeed seed;
};
/// Compose the outer collection environment with an inner seeded contraction.
/// Retains conditional admission; does not choose a matvec implementation.
std::optional<NestedContraction>
matchNestedContraction(const finite::ComputationView &view);
std::optional<NestedContraction>
matchNestedContraction(const finite::ComputationView &view,
                       finite::ComputationWork &work,
                       finite::ComputationDiagnostic *diagnostic = nullptr);
} // namespace zkc::mathematical
#endif

#ifndef ZKC_TRANSFORMS_SCOPEDCANDIDATE_H
#define ZKC_TRANSFORMS_SCOPEDCANDIDATE_H

#include "zkc/Dialect/Exec/Execution.h"
#include "llvm/ADT/DenseMap.h"
#include <memory>

namespace zkc::mathematical {
// Borrowed association for one immutable, admitted numerical candidate. Payload
// block arguments belong to their actual producing instruction; outlined bodies
// retain their own formal arguments. This index does not generate IR,
// equations, recipes or a replacement program. Any mutation invalidates the
// whole view.
class ScopedCandidate {
  protocol::SourceExecutionClosure closure;
  llvm::DenseMap<mlir::Operation *, const protocol::SourceExecutionStep *>
      steps;
  llvm::DenseMap<mlir::Operation *, mlir::Operation *> successors;
  llvm::DenseMap<mlir::Block *, mlir::Operation *> entries;
  llvm::DenseMap<mlir::Value, mlir::Operation *> producers;

  explicit ScopedCandidate(protocol::SourceExecutionClosure value)
      : closure(std::move(value)) {}

public:
  enum class Requests { Resolved, Retained };
  static llvm::Expected<std::unique_ptr<ScopedCandidate>>
  read(mlir::Operation *owner, Requests requests = Requests::Resolved) {
    auto value = protocol::readSourceExecutionClosure(owner);
    if (!value)
      return value.takeError();
    if (requests == Requests::Resolved && !value->computations.empty())
      return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                     "unresolved numerical candidate");
    auto result = std::unique_ptr<ScopedCandidate>(
        new ScopedCandidate(std::move(*value)));
    mlir::SymbolTable symbols(owner);
    for (const auto &[name, body] : result->closure.bodies) {
      auto function = symbols.lookup<mlir::func::FuncOp>(name);
      if (!function || function.empty() || body.empty())
        return llvm::createStringError(llvm::inconvertibleErrorCode(),
                                       "missing scoped candidate body");
      result->entries[&function.front()] = body.front().operation;
      for (auto [index, step] : llvm::enumerate(body)) {
        result->steps[step.operation] = &body[index];
        result->successors[step.operation] =
            index + 1 == body.size() ? nullptr : body[index + 1].operation;
        for (auto output : step.outputs)
          result->producers[output] = step.operation;
      }
    }
    return std::move(result);
  }

  const protocol::SourceExecutionStep *get(mlir::Operation *operation) const {
    return steps.lookup(operation);
  }
  mlir::Operation *first(mlir::Block *block) const {
    return entries.lookup(block);
  }
  mlir::Operation *next(mlir::Operation *operation) const {
    return successors.lookup(operation);
  }
  mlir::Operation *producer(mlir::Value value) const {
    return producers.lookup(value);
  }
  mlir::ValueRange arguments(mlir::Block *block) const {
    return entries.contains(block)
               ? mlir::ValueRange(block->getArguments().drop_front())
               : mlir::ValueRange{};
  }
  mlir::Block *body(mlir::Operation *operation, unsigned index) const {
    auto *step = get(operation);
    if (!step || index >= step->regions.size())
      return nullptr;
    auto function = step->regions[index];
    return &function.front();
  }
  unsigned size() const { return entries.size(); }
};

// The same mathematical reader can inspect a standard numerical schedule or
// actual scoped execution. No fallback to raw operands is permitted when an
// operation is missing from a supplied scoped view.
class CandidatePorts {
  const ScopedCandidate *scoped;

public:
  explicit CandidatePorts(const ScopedCandidate *scoped = nullptr)
      : scoped(scoped) {}
  bool isScoped() const { return scoped != nullptr; }
  bool contains(mlir::Operation *operation) const {
    return operation && (!scoped || scoped->get(operation));
  }
  mlir::ValueRange inputs(mlir::Operation *operation) const {
    if (!operation)
      return {};
    if (!scoped)
      return operation->getOperands();
    auto *step = scoped->get(operation);
    return step ? mlir::ValueRange(step->inputs) : mlir::ValueRange{};
  }
  mlir::ValueRange outputs(mlir::Operation *operation) const {
    if (!operation)
      return {};
    if (!scoped)
      return operation->getResults();
    auto *step = scoped->get(operation);
    return step ? mlir::ValueRange(step->outputs) : mlir::ValueRange{};
  }
  mlir::Operation *next(mlir::Operation *operation) const {
    return !operation ? nullptr
           : scoped   ? scoped->next(operation)
                      : operation->getNextNode();
  }
  mlir::Operation *first(mlir::Block *block) const {
    return !block           ? nullptr
           : scoped         ? scoped->first(block)
           : block->empty() ? nullptr
                            : &block->front();
  }
  mlir::ValueRange arguments(mlir::Block *block) const {
    return !block   ? mlir::ValueRange{}
           : scoped ? scoped->arguments(block)
                    : mlir::ValueRange(block->getArguments());
  }
  unsigned bodies(mlir::Operation *operation) const {
    if (!operation)
      return 0;
    if (!scoped)
      return operation->getNumRegions();
    auto *step = scoped->get(operation);
    return step ? step->regions.size() : 0;
  }
  mlir::Block *body(mlir::Operation *operation, unsigned index) const {
    if (!operation)
      return nullptr;
    if (scoped)
      return scoped->body(operation, index);
    return index < operation->getNumRegions() &&
                   operation->getRegion(index).hasOneBlock()
               ? &operation->getRegion(index).front()
               : nullptr;
  }
  mlir::Operation *producer(mlir::Value value) const {
    return scoped ? scoped->producer(value) : value.getDefiningOp();
  }
  mlir::WalkResult
  walk(mlir::Operation *operation,
       llvm::function_ref<mlir::WalkResult(mlir::Operation *)> callback,
       unsigned depth = 0) const {
    if (!contains(operation) || depth > 64)
      return mlir::WalkResult::interrupt();
    if (!scoped)
      return operation->walk(callback);
    if (callback(operation).wasInterrupted())
      return mlir::WalkResult::interrupt();
    for (unsigned index = 0; index != bodies(operation); ++index)
      for (auto *op = first(body(operation, index)); op; op = next(op))
        if (walk(op, callback, depth + 1).wasInterrupted())
          return mlir::WalkResult::interrupt();
    return mlir::WalkResult::advance();
  }
};
} // namespace zkc::mathematical
#endif

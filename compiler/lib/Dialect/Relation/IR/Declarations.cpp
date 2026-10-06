#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include <map>
#include <tuple>

using namespace mlir;
using namespace llvm;

namespace zkc::relation {
namespace {
bool sameInput(Type a, Type b) {
  // MLIR type storage is context-local. The existing logical carrier retains
  // domains, dimensions and complete nominal descriptors across contexts.
  auto lhs = protocol::encodeBoundType(a, false);
  if (!lhs) {
    consumeError(lhs.takeError());
    return false;
  }
  auto rhs = protocol::encodeBoundType(b, false);
  if (!rhs) {
    consumeError(rhs.takeError());
    return false;
  }
  return *lhs == *rhs;
}
bool sameSchema(DeclareOp a, DeclareOp b) {
  if (a.getSignature().getNumInputs() != b.getSignature().getNumInputs())
    return false;
  for (auto [lhs, rhs] :
       zip(a.getSignature().getInputs(), b.getSignature().getInputs()))
    if (!sameInput(lhs, rhs))
      return false;
  for (auto [lhs, rhs] : zip(a.getPurposes(), b.getPurposes()))
    if (cast<StringAttr>(lhs).getValue() != cast<StringAttr>(rhs).getValue())
      return false;
  return true;
}
bool logicalData(const protocol::BoundType &type, unsigned depth,
                 protocol::TypeParseBudget &budget) {
  if (depth > 64 || !budget.consume() || !type.representation.empty())
    return false;
  if (type.kind == "variant") {
    auto descriptor = protocol::decodeVariant(type.spelling(), depth, &budget);
    if (!descriptor)
      return false;
    for (const auto &arm : descriptor->alternatives)
      for (const auto &leaf : arm.payload) {
        auto child = protocol::parseBoundType(leaf, false, depth + 1, &budget);
        if (!child) {
          consumeError(child.takeError());
          return false;
        }
        if (!logicalData(*child, depth + 1, budget))
          return false;
      }
    return true;
  }
  if (type.kind == "sequence")
    return llvm::all_of(type.arguments, [&](const auto &argument) {
      return argument.kind != protocol::TypeArgument::Kind::Type ||
             logicalData(*argument.type, depth + 1, budget);
    });
  // Data permission is independent of copyability, total arithmetic and wire
  // support. In particular copyable keys and private resources are not data.
  return type.kind == "bool" || type.kind == "index" || type.kind == "field" ||
         type.kind == "group" || type.kind == "field_array" ||
         type.kind == "vector" || type.kind == "matrix" ||
         type.kind == "groups" || type.kind == "indices";
}
bool logicalInputs(TypeRange inputs) {
  protocol::TypeParseBudget budget;
  size_t remainingBytes = 1024 * 1024;
  if (inputs.size() > 100000)
    return false;
  for (Type input : inputs) {
    auto logical = protocol::encodeBoundType(input, false);
    if (!logical) {
      consumeError(logical.takeError());
      return false;
    }
    size_t bytes = logical->spelling().size();
    if (bytes > remainingBytes || !logicalData(*logical, 0, budget))
      return false;
    remainingBytes -= bytes;
  }
  return true;
}
} // namespace
LogicalResult DeclareOp::verify() {
  if (getKind().empty() || getKey().empty() || getRevision().empty())
    return diagnostics::emit(
        emitOpError(), "relation-declaration-identity",
        "external kind, key and revision must be explicit");
  auto signature = getSignature();
  if (signature.getNumResults() != 1 ||
      !signature.getResult(0).isSignlessInteger(1) ||
      getPurposes().size() != signature.getNumInputs() ||
      !logicalInputs(signature.getInputs()))
    return diagnostics::emit(emitOpError(), "relation-declaration-signature",
                             "expected supported immutable logical data inputs "
                             "within type limits and one bool result");
  for (auto purpose : getPurposes()) {
    auto value = cast<StringAttr>(purpose).getValue();
    if (value != "parameter" && value != "statement" && value != "witness")
      return diagnostics::emit(
          emitOpError(), "relation-declaration-purpose",
          "each input requires parameter, statement or witness purpose");
  }
  return success();
}
LogicalResult verifyDeclarationConsistency(ArrayRef<Operation *> units) {
  using Identity = std::tuple<std::string, std::string, std::string>;
  std::map<Identity, DeclareOp> declarations;
  for (auto *unit : units) {
    if (!unit)
      return failure();
    auto result = unit->walk([&](DeclareOp declaration) {
      if (failed(declaration->getName().verifyInvariants(declaration)))
        return WalkResult::interrupt();
      Identity identity{declaration.getKind().str(), declaration.getKey().str(),
                        declaration.getRevision().str()};
      auto [it, added] = declarations.emplace(std::move(identity), declaration);
      if (!added && !sameSchema(it->second, declaration)) {
        auto diagnostic = diagnostics::emit(
            declaration.emitOpError(), "relation-declaration-conflict",
            "the same external identity has inconsistent input types or "
            "purposes");
        diagnostic.attachNote(it->second.getLoc()) << "previous declaration";
        return WalkResult::interrupt();
      }
      return WalkResult::advance();
    });
    if (result.wasInterrupted())
      return failure();
  }
  return success();
}
} // namespace zkc::relation

#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Support/Refusal.h"
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
    if (bytes > remainingBytes ||
        protocol::logicalRelationData(*logical, budget) !=
            protocol::RelationData::Supported)
      return false;
    remainingBytes -= bytes;
  }
  return true;
}
} // namespace
Expected<json::Value> readStaticArguments(ArrayAttr arguments) {
  if (!arguments || arguments.size() > 128)
    return zkc::error("relation-static-arguments");
  auto *context = arguments.getContext();
  SmallVector<Attribute> bindings;
  for (auto [index, argument] : enumerate(arguments))
    bindings.push_back(ArrayAttr::get(
        context, {StringAttr::get(context, "argument" + std::to_string(index)),
                  argument}));
  auto origin = protocol_ir::readProtocolOrigin(
      ArrayAttr::get(context, {StringAttr::get(context, "opaque"),
                               ArrayAttr::get(context, bindings)}));
  if (!origin)
    return origin.takeError();
  json::Array result;
  for (auto &binding : *(*origin->getAsArray())[1].getAsArray())
    result.push_back(std::move((*binding.getAsArray())[1]));
  return result;
}
LogicalResult DeclareOp::verify() {
  if (getKind().empty() || getKey().empty() || getRevision().empty())
    return diagnostics::emit(
        emitOpError(), "relation-declaration-identity",
        "external kind, key and revision must be explicit");
  auto arguments = readStaticArguments(getStaticArguments());
  if (!arguments) {
    consumeError(arguments.takeError());
    return diagnostics::emit(emitOpError(), "relation-static-arguments",
                             "expected closed canonical typed static arguments "
                             "within origin limits");
  }
  if (getKind().starts_with("zkc.") && !getStaticArguments().empty())
    return diagnostics::emit(
        emitOpError(), "relation-static-arguments",
        "source formula and captured identities do not take opaque arguments");
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
LogicalResult DeclareOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto unit = (*this)->getParentOfType<protocol_ir::ProtocolModuleOp>();
  bool original = unit && unit.getProfile() == protocol_ir::Profile::Protocol;
  auto formula = getFormulaAttr();
  if (!formula) {
    if (original && getKind() == "zkc.language.formula/0")
      return diagnostics::emit(
          emitOpError(), "relation-formula",
          "formula declaration requires an exact helper reference");
    return success();
  }
  auto helper = tables.lookupNearestSymbolFrom<func::FuncOp>(*this, formula);
  if (!original || getKind() != "zkc.language.formula/0" || !helper ||
      helper->getParentOp() != (*this)->getParentOp() || helper.isExternal() ||
      helper.getFunctionType() != getSignature())
    return diagnostics::emit(emitOpError(), "relation-formula",
                             "formula must name a defined Math helper with the "
                             "complete relation ABI");
  return success();
}
LogicalResult verifyDeclarationConsistency(ArrayRef<Operation *> units) {
  using Identity =
      std::tuple<std::string, std::string, std::string, std::string>;
  std::map<Identity, DeclareOp> declarations;
  for (auto *unit : units) {
    if (!unit)
      return failure();
    auto result = unit->walk([&](DeclareOp declaration) {
      if (failed(declaration->getName().verifyInvariants(declaration)))
        return WalkResult::interrupt();
      auto arguments = readStaticArguments(declaration.getStaticArguments());
      if (!arguments) {
        consumeError(arguments.takeError());
        return WalkResult::interrupt();
      }
      std::string canonical;
      raw_string_ostream(canonical) << *arguments;
      Identity identity{declaration.getKind().str(), declaration.getKey().str(),
                        declaration.getRevision().str(), canonical};
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

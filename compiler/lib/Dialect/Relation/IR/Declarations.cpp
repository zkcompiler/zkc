#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Refusal.h"
#include <map>
#include <tuple>

using namespace mlir;
using namespace llvm;

namespace zkc::relation {
namespace {
// Both signatures have passed native formation before these comparisons.
// Compare their semantic structure, including all nominal metadata; native
// storage is context-local and a program-byte spelling is a separate profile.
bool sameIdentityTerm(Attribute a, Attribute b) {
  if (a == b)
    return true;
  if (auto text = dyn_cast<StringAttr>(a)) {
    auto other = dyn_cast<StringAttr>(b);
    return other && text.getValue() == other.getValue();
  }
  auto lhs = dyn_cast<ArrayAttr>(a), rhs = dyn_cast<ArrayAttr>(b);
  return lhs && rhs && lhs.size() == rhs.size() &&
         all_of(zip(lhs, rhs), [](auto pair) {
           return sameIdentityTerm(std::get<0>(pair), std::get<1>(pair));
         });
}
bool sameInput(Type a, Type b) {
  if (a == b)
    return true;
  auto lhsVariant = dyn_cast<data::VariantType>(a);
  auto rhsVariant = dyn_cast<data::VariantType>(b);
  if (lhsVariant || rhsVariant) {
    if (!lhsVariant || !rhsVariant ||
        !sameIdentityTerm(lhsVariant.getIdentity().getTerm(),
                          rhsVariant.getIdentity().getTerm()) ||
        lhsVariant.getAlternatives().size() !=
            rhsVariant.getAlternatives().size())
      return false;
    for (auto [lhs, rhs] :
         zip(lhsVariant.getAlternatives(), rhsVariant.getAlternatives())) {
      if (lhs.getLabel().getValue() != rhs.getLabel().getValue() ||
          lhs.getPayload().size() != rhs.getPayload().size())
        return false;
      for (auto [left, right] : zip(lhs.getPayload(), rhs.getPayload()))
        if (!sameInput(left, right))
          return false;
    }
    return true;
  }
  auto lhs = cast<CatalogTypeInterface>(a).getCatalogApplication();
  auto rhs = cast<CatalogTypeInterface>(b).getCatalogApplication();
  if (lhs->constructor != rhs->constructor ||
      lhs->arguments.size() != rhs->arguments.size())
    return false;
  for (auto [left, right] : zip(lhs->arguments, rhs->arguments)) {
    if (auto type = dyn_cast<TypeAttr>(left)) {
      auto other = dyn_cast<TypeAttr>(right);
      if (!other || !sameInput(type.getValue(), other.getValue()))
        return false;
    } else if (auto natural = dyn_cast<IntegerAttr>(left)) {
      auto other = dyn_cast<IntegerAttr>(right);
      if (!other || natural.getValue() != other.getValue())
        return false;
    } else if (!sameIdentityTerm(left, right))
      return false;
  }
  return true;
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
bool relationData(Type type) {
  if (auto variant = dyn_cast<data::VariantType>(type)) {
    for (auto arm : variant.getAlternatives())
      if (!all_of(arm.getPayload(), relationData))
        return false;
    return true;
  }
  auto application = cast<CatalogTypeInterface>(type).getCatalogApplication();
  if (application->constructor == "sequence")
    return relationData(cast<TypeAttr>(application->arguments[0]).getValue());
  return protocol::logicalRelationAtom(application->constructor);
}
bool logicalInputs(DeclareOp declaration) {
  auto inputs = declaration.getSignature().getInputs();
  if (inputs.size() > 100000 || failed(verifyLogicalTypes(
                                    [&] {
                                      auto diagnostic =
                                          declaration.emitOpError();
                                      diagnostic.abandon();
                                      return diagnostic;
                                    },
                                    inputs)))
    return false;
  return all_of(inputs, relationData);
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
      getPurposes().size() != signature.getNumInputs() || !logicalInputs(*this))
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

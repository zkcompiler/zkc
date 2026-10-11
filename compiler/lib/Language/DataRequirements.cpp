#include "DataRequirements.h"
#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<Type> collectionElement(const Type &type, bool matrix) {
  if (type.kind != Type::Kind::Builtin)
    return {};
  if (matrix)
    return type.domain == "matrix" && type.arguments.size() == 1
               ? std::optional<Type>(type.arguments.front())
               : std::nullopt;
  if (type.domain == "indices" && type.arguments.empty())
    return Type(Type::Kind::Index);
  if (((type.domain == "vector" || type.domain == "groups" ||
        type.domain == "sequence") &&
       type.arguments.size() == 1) ||
      (type.domain == "field_array" && type.arguments.size() == 2))
    return type.arguments.front();
  return {};
}
bool collectionAxis(const Type &type, unsigned axis) {
  return collectionElement(type, true) ? axis < 2
         : collectionElement(type)     ? axis == 0
                                       : false;
}
std::optional<std::vector<DataPrecondition>>
mapDataPreconditions(Semantics &types, ArrayRef<DataPrecondition> original,
                     ArrayRef<unsigned> inputAliases) {
  std::vector<DataPrecondition> result;
  for (const auto &condition : original) {
    if (!types.charge(condition.left.path.size() + condition.right.path.size() +
                          result.size() + 1,
                      condition.span))
      return {};
    if (condition.left.port >= inputAliases.size() ||
        condition.right.port >= inputAliases.size()) {
      types.fail("source.data-bound",
                 "precondition input alias is outside its signature",
                 condition.span);
      return {};
    }
    auto mapped = condition;
    mapped.left.port = inputAliases[condition.left.port];
    mapped.right.port = inputAliases[condition.right.port];
    if (!llvm::is_contained(result, mapped))
      result.push_back(std::move(mapped));
  }
  return result;
}
bool Checker::dataRequirements(Declaration &decl) {
  auto refuse = [&](Span span, StringRef message) {
    return types.fail("source.data-bound", message, span);
  };
  auto select = [&](const SyntaxInputSelector &source,
                    InputSelector &result) -> std::optional<Type> {
    auto found = llvm::find_if(decl.inputs, [&](const Port &port) {
      return port.name == source.port;
    });
    if (found == decl.inputs.end()) {
      refuse(source.span, "data precondition requires a named data input");
      return {};
    }
    result.port = found - decl.inputs.begin();
    result.span = source.span;
    auto type = found->type;
    for (const auto &field : source.path) {
      if (!types.charge(1, source.span))
        return {};
      auto index = types.fieldIndex(decl, type, field, source.span);
      if (!index)
        return {};
      auto nested = types.projectedType(decl, type, {*index}, source.span);
      if (!nested)
        return {};
      result.path.push_back(*index);
      type = std::move(*nested);
    }
    return type;
  };
  for (const auto &source : sources[decl.id.index]->requirements) {
    if (!source.data)
      continue;
    if (decl.kind != Declaration::Kind::Math)
      return refuse(source.span,
                    "only mathematical functions assume data preconditions");
    if (!types.charge(1, source.span))
      return false;
    DataPrecondition condition{
        *source.data, {}, {}, source.leftAxis, source.rightAxis, source.span};
    auto left = select(source.left, condition.left);
    auto right = select(source.right, condition.right);
    if (!left || !right)
      return false;
    if (!collectionAxis(*right, condition.rightAxis) ||
        (condition.kind == DataPrecondition::Kind::IndexBound
             ? left->kind != Type::Kind::Index
             : !collectionAxis(*left, condition.leftAxis)))
      return refuse(source.span,
                    "data precondition input type or axis differs");
    if (condition.kind == DataPrecondition::Kind::EqualExtent &&
        left->domain == "field_array" && right->domain == "field_array") {
      const auto &a = left->arguments[1].dimension;
      const auto &b = right->arguments[1].dimension;
      if (a.isClosed() && b.isClosed() && a != b)
        return refuse(source.span, "fixed extents differ");
    }
    if (!types.charge(decl.dataPreconditions.size(), source.span))
      return false;
    if (llvm::is_contained(decl.dataPreconditions, condition))
      return refuse(source.span, "duplicate data precondition");
    if (decl.dataPreconditions.size() >= 1024)
      return types.fail("source.limit",
                        "helper exceeds 1024 data preconditions", source.span);
    decl.dataPreconditions.push_back(std::move(condition));
  }
  return true;
}
} // namespace zkc::language::detail

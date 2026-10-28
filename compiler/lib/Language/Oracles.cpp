#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::oracle(const Expression &expr,
                                           unsigned depth) {
  using K = Expression::Kind;
  using T = Type::Kind;
  if (!protocol()) {
    fail("source.mode", "oracle actions require protocol mode", expr.span);
    return {};
  }
  auto resultType = inferredType(uint32_t(&expr - syntax.expressions.data()));
  if (!resultType)
    return {};
  if (expr.kind == K::OracleSend) {
    const auto &kind = resultType->arguments.front();
    auto family = checker.roles(decl, *expr.roles, expr.span);
    auto holder = checker.roles(decl, {expr.roles->front()}, expr.span);
    if (!family || !holder || !active(*family, expr.span))
      return {};
    if (family->size() < 2) {
      fail("source.oracle-role",
           "oracle send requires a distinct holder and receivers", expr.span);
      return {};
    }
    std::vector<unsigned> receivers;
    for (auto role : *family)
      if (role != holder->front())
        receivers.push_back(role);
    bool sized = kind.arguments.size() == 2;
    if ((sized && (expr.children.size() != 1 || expr.arguments.size() != 1)) ||
        (!sized && (expr.children.size() != 2 || expr.arguments.size() != 2))) {
      fail("source.oracle-shape",
           "sized sends infer rows; unsized sends require rows and max",
           expr.span);
      return {};
    }
    std::optional<Natural> maximum;
    if (!sized) {
      auto bound = checker.type(decl, expr.arguments[1]);
      if (!bound)
        return {};
      if (bound->kind != T::Natural) {
        fail("source.oracle-shape", "oracle maximum must be a static natural",
             expr.span);
        return {};
      }
      maximum = bound->dimension;
    }
    auto dataType = checker.types.associated(kind, "Data", expr.span);
    auto data = dataType ? expression(expr.children[0], *dataType, depth + 1)
                         : std::nullopt;
    if (!data || !demand(*data, *holder, expr.span) || !use(*data, expr.span))
      return {};
    auto rows = sized ? emit(MathValue{MathematicalIdentity::IndexConstant,
                                       {},
                                       "",
                                       {kind.arguments[1]}},
                             Type(T::Index), allRoles(), expr.span)
                      : expression(expr.children[1], Type(T::Index), depth + 1);
    if (!rows || !demand(*rows, *family, expr.span) || !use(*rows, expr.span))
      return {};
    return emit(OracleSend{*data, *rows, holder->front(), receivers, maximum},
                *resultType, *family, expr.span);
  }
  auto handle = expression(expr.children.front(), {}, depth + 1);
  if (!handle)
    return {};
  const auto value = body.values[handle->index];
  if (value.type.kind != T::Oracle || !value.oracleHolder) {
    fail("source.oracle-role",
         "oracle action requires a retained holder family", expr.span);
    return {};
  }
  if (!use(*handle, expr.span))
    return {};
  if (expr.kind == K::OracleContents) {
    if (!active({*value.oracleHolder}, expr.span) ||
        !demand(*handle, {*value.oracleHolder}, expr.span))
      return {};
    return emit(OracleContents{*handle, *value.oracleHolder}, *resultType,
                {*value.oracleHolder}, expr.span);
  }
  if (expr.kind == K::OracleRows)
    return emit(OracleRows{*handle}, *resultType, components(*handle),
                expr.span);
  if (expr.kind == K::OracleForgetRows)
    return emit(OracleForgetRows{*handle}, *resultType, components(*handle),
                expr.span);
  auto queryType = checker.types.associated(value.type.arguments.front(),
                                            "Query", expr.span);
  auto position = queryType
                      ? expression(expr.children[1], *queryType, depth + 1)
                      : std::nullopt;
  if (!position || !use(*position, expr.span))
    return {};
  auto available = components(*handle);
  llvm::erase(available.roles, *value.oracleHolder);
  auto selected = placement->owner(expr.span);
  if (!selected || !placement->together(*selected, available, expr.span) ||
      !placement->together(*selected, components(*position), expr.span))
    return {};
  auto answer = emit(OracleQuery{*handle, *position, 0}, *resultType, *selected,
                     expr.span);
  if (answer)
    placement->oracleQueries.emplace_back(body.operations.size() - 1,
                                          selected->owners.front());
  return answer;
}
} // namespace zkc::language::detail

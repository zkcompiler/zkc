#ifndef ZKC_FRONTEND_INSTANTIATION_WORK_H
#define ZKC_FRONTEND_INSTANTIATION_WORK_H
#include "../Syntax/Tree.h"
#include "zkc/Frontend/Work.h"

namespace zkc::frontend::instantiation {
// Preflight syntax snapshots and specializations before their deep copies.
// This counts nodes, type fields and call vector slots, not string storage.
inline bool chargeTypeCopy(WorkBudget &budget, const syntax::Type &type) {
  if (!budget.charge(WorkAccount::AuthoredStatic))
    return false;
  for (const auto &argument : type.arguments)
    if (!chargeTypeCopy(budget, argument))
      return false;
  return true;
}
inline bool chargeBodyCopy(WorkBudget &, const syntax::Body &);
inline bool chargeExpressionCopy(WorkBudget &budget,
                                 const syntax::Expression &e) {
  if (!budget.charge(WorkAccount::AuthoredStatic))
    return false;
  for (const auto &operand : e.operands)
    if (!chargeExpressionCopy(budget, operand))
      return false;
  return !e.traversal || chargeBodyCopy(budget, e.traversal->body);
}
inline bool chargeBodyCopy(WorkBudget &budget, const syntax::Body &body) {
  for (const auto &instruction : body) {
    if (!budget.charge(WorkAccount::AuthoredStatic))
      return false;
    bool good = std::visit(
        [&](const auto &v) {
          using T = std::decay_t<decltype(v)>;
          if constexpr (std::is_same_v<T, syntax::Binding> ||
                        std::is_same_v<T, syntax::Call>) {
            if (v.annotation)
              for (const auto &type : *v.annotation)
                if (!chargeTypeCopy(budget, type))
                  return false;
            if constexpr (std::is_same_v<T, syntax::Binding>)
              return chargeExpressionCopy(budget, v.expression);
            else {
              // Both decoded operands and retained lexical atoms are copied.
              // Charge each vector separately to avoid overflowing a sum.
              for (size_t slots :
                   {v.staticTerms.size(), v.attributeAtoms.size(),
                    v.inputAtoms.size(), v.attributes.size(), v.inputs.size(),
                    v.outputs.size(), v.argumentNames.size(),
                    v.staticArguments ? v.staticArguments->size() : size_t{0}})
                if (!budget.charge(WorkAccount::AuthoredStatic, slots))
                  return false;
              for (const auto &term : v.staticTerms)
                if (!budget.charge(WorkAccount::AuthoredStatic,
                                   term.members.size()))
                  return false;
            }
          } else if constexpr (std::is_same_v<T, syntax::Invocation>) {
            for (size_t slots :
                 {v.inputs.size(), v.outputs.size(), v.resultNames.size()})
              if (!budget.charge(WorkAccount::AuthoredStatic, slots))
                return false;
          } else if constexpr (std::is_same_v<T, syntax::Exit>) {
            return chargeExpressionCopy(budget, v.expression);
          } else if constexpr (std::is_same_v<T, syntax::Conditional>) {
            return chargeExpressionCopy(budget, v.condition) &&
                   chargeBodyCopy(budget, v.thenBody) &&
                   chargeBodyCopy(budget, v.elseBody);
          } else if constexpr (std::is_same_v<T, syntax::For>) {
            return chargeExpressionCopy(budget, v.lower) &&
                   chargeExpressionCopy(budget, v.upper) &&
                   chargeBodyCopy(budget, v.body);
          } else if constexpr (std::is_same_v<T, syntax::Loop> ||
                               std::is_same_v<T, syntax::ArrayTraversal>) {
            return chargeBodyCopy(budget, v.body);
          } else if constexpr (std::is_same_v<T, syntax::Placement>) {
            return (!v.annotation || chargeTypeCopy(budget, *v.annotation)) &&
                   chargeBodyCopy(budget, v.body);
          } else if constexpr (std::is_same_v<T, syntax::Match>) {
            for (const auto &arm : v.arms)
              if (!budget.charge(WorkAccount::AuthoredStatic) ||
                  !chargeBodyCopy(budget, arm.body))
                return false;
          }
          return true;
        },
        instruction.value);
    if (!good)
      return false;
  }
  return true;
}
template <typename Declaration>
bool chargeDeclarationCopy(WorkBudget &budget, const Declaration &d) {
  if (!budget.charge(WorkAccount::AuthoredStatic))
    return false;
  if constexpr (std::is_same_v<Declaration, syntax::Function> ||
                std::is_same_v<Declaration, syntax::Protocol>) {
    for (const auto &argument : d.arguments)
      if (!chargeTypeCopy(budget, argument.type))
        return false;
    for (const auto &result : d.results) {
      if constexpr (std::is_same_v<Declaration, syntax::Function>) {
        if (!chargeTypeCopy(budget, result))
          return false;
      } else if (!chargeTypeCopy(budget, result.type))
        return false;
    }
    if (d.body && !chargeBodyCopy(budget, *d.body))
      return false;
  } else if constexpr (std::is_same_v<Declaration, syntax::Struct>) {
    for (const auto &field : d.fields)
      if (!chargeTypeCopy(budget, field.type))
        return false;
  } else if constexpr (std::is_same_v<Declaration, syntax::Constant>) {
    return chargeExpressionCopy(budget, d.expression);
  }
  return true;
}
} // namespace zkc::frontend::instantiation
#endif

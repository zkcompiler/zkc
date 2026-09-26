#ifndef ZKC_FRONTEND_LOWERING_OUTPUT_WORK_H
#define ZKC_FRONTEND_LOWERING_OUTPUT_WORK_H
#include "../Model/Body.h"
#include "../Work.h"

namespace zkc::frontend::lowering {
// Both typed and common bodies have the same structural region schedule. These
// are output slots, not encoded byte counts. Strings and descriptors are not
// measured by this account.
template <typename Body>
llvm::Error chargeBody(WorkBudget &budget, WorkAccount account,
                       const Body &body) {
  for (const auto &instruction : body) {
    if (auto error = work::charge(budget, account))
      return error;
    auto error = std::visit(
        [&](const auto &value) -> llvm::Error {
          using T = std::decay_t<decltype(value)>;
          auto slots =
              [&](std::initializer_list<size_t> counts) -> llvm::Error {
            for (auto count : counts)
              if (auto error = work::charge(budget, account, count))
                return error;
            return llvm::Error::success();
          };
          if constexpr (std::is_same_v<T, model::Call> ||
                        std::is_same_v<T, source::Operation>) {
            return slots({value.inputs.size(), value.outputs.size(),
                          value.staticArguments.size(),
                          value.attributes.size()});
          } else if constexpr (std::is_same_v<T, source::AlgorithmCall>) {
            return slots({value.inputs.size(), value.outputs.size(),
                          value.staticArguments.size()});
          } else if constexpr (std::is_same_v<T, source::LocalCall> ||
                               std::is_same_v<T, source::ProtocolCall>) {
            return slots({value.inputs.size(), value.outputs.size()});
          } else if constexpr (std::is_same_v<T, source::Return> ||
                               std::is_same_v<T, source::Yield> ||
                               std::is_same_v<T, source::Release>) {
            return slots({value.values.size()});
          } else if constexpr (std::is_same_v<T, source::VariantConstruct>) {
            return slots({value.payload.size()});
          } else if constexpr (std::is_same_v<T, model::Loop> ||
                               std::is_same_v<T, model::For> ||
                               std::is_same_v<T, source::Loop> ||
                               std::is_same_v<T, source::For>) {
            if (auto error = slots({value.carried.size(), value.captures.size(),
                                    value.outputs.size()}))
              return error;
            return chargeBody(budget, account, value.body);
          } else if constexpr (std::is_same_v<T, model::Conditional> ||
                               std::is_same_v<T, source::Conditional>) {
            if (auto error =
                    slots({value.captures.size(), value.outputs.size()}))
              return error;
            if (auto error = chargeBody(budget, account, value.thenBody))
              return error;
            return chargeBody(budget, account, value.elseBody);
          } else if constexpr (std::is_same_v<T, model::Match> ||
                               std::is_same_v<T, source::Match>) {
            if (auto error = slots({value.captures.size(), value.outputs.size(),
                                    value.arms.size()}))
              return error;
            for (const auto &arm : value.arms) {
              if (auto error = slots({arm.payload.size()}))
                return error;
              if (auto error = chargeBody(budget, account, arm.body))
                return error;
            }
          }
          return llvm::Error::success();
        },
        instruction.value);
    if (error)
      return error;
  }
  return llvm::Error::success();
}
inline llvm::Error chargeFunction(WorkBudget &budget, WorkAccount account,
                                  const source::Function &function) {
  for (auto count :
       {size_t(1), function.arguments.size(), function.results.size()})
    if (auto error = work::charge(budget, account, count))
      return error;
  return function.body ? chargeBody(budget, account, *function.body)
                       : llvm::Error::success();
}
} // namespace zkc::frontend::lowering
#endif

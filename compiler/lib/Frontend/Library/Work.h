#ifndef ZKC_FRONTEND_LIBRARY_WORK_H
#define ZKC_FRONTEND_LIBRARY_WORK_H
#include "../Work.h"
#include "zkc/Frontend/Library.h"

namespace zkc::frontend::library::detail {
// Visit the written type even when its eventual payload is empty. Multiplicity
// preflights copies made by children(); no product is evaluated before
// checking.
inline llvm::Error chargeType(WorkBudget &budget, const Type &type,
                              uint64_t copies = 1) {
  if (auto error = work::charge(budget, WorkAccount::LibraryFormation, copies))
    return error;
  if (!budget.chargeProduct(WorkAccount::LibraryFormation, copies,
                            type.fields.size()))
    return work::exhausted(WorkAccount::LibraryFormation);
  for (const auto &element : type.elements)
    if (auto error = chargeType(budget, element, copies))
      return error;
  return llvm::Error::success();
}
inline llvm::Error
chargeInstructions(WorkBudget &budget,
                   const std::vector<Instruction> &instructions) {
  for (const auto &instruction : instructions) {
    if (auto error = work::charge(budget, WorkAccount::LibraryFormation))
      return error;
    if (const auto *join = branches(instruction)) {
      for (const auto &arm : join->arms) {
        if (auto error = work::charge(budget, WorkAccount::LibraryFormation))
          return error;
        if (auto error = chargeInstructions(budget, arm.body->instructions))
          return error;
      }
    } else if (const auto *traversal =
                   std::get_if<ArrayTraversal>(&instruction)) {
      if (auto error =
              chargeInstructions(budget, traversal->body->instructions))
        return error;
    }
  }
  return llvm::Error::success();
}
inline llvm::Error chargeBody(WorkBudget &budget, const Body &body) {
  if (auto error = work::charge(budget, WorkAccount::LibraryFormation))
    return error;
  for (const auto *ports : {&body.signature.inputs, &body.signature.outputs})
    for (const auto &port : *ports)
      if (auto error = chargeType(budget, port.type))
        return error;
  return chargeInstructions(budget, body.instructions);
}
} // namespace zkc::frontend::library::detail
#endif

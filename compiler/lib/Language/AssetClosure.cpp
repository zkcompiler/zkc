#include "State.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/RingExpression.h"
#include <functional>

using namespace llvm;
namespace zkc::language::detail {
Error closeAssets(const CheckedProject &project, ClosedStorage &closed,
                  Work &work) {
  std::map<std::string, const Asset *> available, retained;
  for (const auto &asset : project.assets()) {
    if (auto error = work.charge(1))
      return error;
    available.emplace(asset.identity().str(), &asset);
  }
  std::set<std::pair<std::string, std::string>> checked;
  std::function<Error(const Body &)> visit = [&](const Body &body) -> Error {
    for (const auto &operation : body.operations) {
      if (auto error = work.charge(1, operation.span))
        return error;
      if (const auto *primitive =
              std::get_if<LocalPrimitive>(&operation.action)) {
        if (!StringRef(primitive->contract).starts_with("ring."))
          continue;
        if (primitive->parameters.size() != 1 || !primitive->bindingArguments ||
            primitive->bindingArguments->size() != 1)
          return failure("source.asset-reference", "invalid evaluator binding",
                         operation.span);
        const auto &identity = primitive->parameters.front();
        auto found = available.find(identity);
        if (found == available.end() || !found->second->ring())
          return failure("source.asset-reference",
                         "required captured ring expression is absent",
                         operation.span);
        const auto &carrier = primitive->bindingArguments->front();
        if (carrier.kind != Type::Kind::Field || carrier.symbolic)
          return failure("source.asset-carrier",
                         "evaluator field is not closed", operation.span);
        if (checked.emplace(identity, carrier.domain).second) {
          const auto &arena = *found->second->ring();
          if (auto error =
                  work.charge(arena.inputs().size() + arena.facts().size() + 1,
                              operation.span))
            return error;
          auto accepts = [&](StringRef field) {
            return field == carrier.domain ||
                   field == protocol::installedDomains().associatedIdentity(
                                carrier.domain, "BaseField");
          };
          for (const auto &input : arena.inputs())
            if (!accepts(input.field))
              return failure("source.asset-carrier",
                             "expression input field differs from carrier",
                             operation.span);
          for (const auto &fact : arena.facts())
            if (!accepts(fact.field))
              return failure("source.asset-carrier",
                             "expression node field differs from carrier",
                             operation.span);
        }
        retained.emplace(identity, found->second);
      } else if (const auto *control =
                     std::get_if<LocalControl>(&operation.action)) {
        for (const auto &region : control->regions)
          if (auto error = visit(*region))
            return error;
      } else if (const auto *repeat =
                     std::get_if<ProtocolRepeat>(&operation.action)) {
        if (auto error = visit(*repeat->region))
          return error;
      }
    }
    return Error::success();
  };
  for (const auto &declaration : closed.declarations)
    if (declaration.body)
      if (auto error = visit(*declaration.body))
        return error;
  for (const auto &entry : retained)
    closed.assets.push_back(*entry.second);
  return Error::success();
}
} // namespace zkc::language::detail

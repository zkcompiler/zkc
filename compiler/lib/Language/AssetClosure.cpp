#include "State.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Support/Refusal.h"
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
        for (const auto &reference : primitive->assetReferences) {
          if (auto error = work.charge(1, operation.span))
            return error;
          const auto &identity = reference.term.domain;
          auto found = available.find(identity);
          if (reference.term.kind != Type::Kind::Asset ||
              reference.term.symbolic || found == available.end() ||
              reference.position >= primitive->parameters.size() ||
              primitive->parameters[reference.position] != identity)
            return failure("source.asset-reference",
                           "closed kernel parameter does not name a captured "
                           "asset",
                           operation.span);
          if (const auto *arena = found->second->ring()) {
            // Every ring kernel substitutes the arena in one carrier field;
            // the arena's fields must be that carrier or embed into it.
            if (!primitive->bindingArguments ||
                primitive->bindingArguments->size() != 1)
              return failure("source.asset-reference",
                             "invalid evaluator binding", operation.span);
            const auto &carrier = primitive->bindingArguments->front();
            if (carrier.kind != Type::Kind::Field || carrier.symbolic)
              return failure("source.asset-carrier",
                             "evaluator field is not closed", operation.span);
            if (checked.emplace(identity, carrier.domain).second) {
              if (auto error = work.charge(arena->inputs().size() +
                                               arena->facts().size() + 1,
                                           operation.span))
                return error;
              auto accepts = [&](StringRef field) {
                return field == carrier.domain ||
                       field == protocol::installedDomains().associatedIdentity(
                                    carrier.domain, "BaseField");
              };
              for (const auto &input : arena->inputs())
                if (!accepts(input.field))
                  return failure("source.asset-carrier",
                                 "expression input field differs from carrier",
                                 operation.span);
              for (const auto &fact : arena->facts())
                if (!accepts(fact.field))
                  return failure("source.asset-carrier",
                                 "expression node field differs from carrier",
                                 operation.span);
            }
          } else if (const auto *bundle = found->second->bundle()) {
            if (!primitive->bindingArguments ||
                primitive->bindingArguments->size() != 2)
              return failure("source.asset-reference", "invalid table binding",
                             operation.span);
            const auto &carrier = (*primitive->bindingArguments)[0];
            const auto &table = (*primitive->bindingArguments)[1];
            if (carrier.kind != Type::Kind::Field || carrier.symbolic ||
                table.kind != Type::Kind::Natural ||
                !table.dimension.isClosed())
              return failure("source.asset-reference",
                             "table binding is not closed", operation.span);
            const auto index = table.dimension.closedValue();
            if (index >= bundle->tables().size())
              return failure("source.asset-table",
                             "table index is out of range", operation.span);
            const auto key = primitive->contract + ":" + carrier.domain + ":" +
                             std::to_string(index);
            if (checked.emplace(identity, key).second) {
              const auto &definition = bundle->tables()[index];
              if (auto error = work.charge(definition.arena.nodes().size() +
                                               definition.groups.size() +
                                               bundle->publics().size() + 1,
                                           operation.span))
                return error;
              // The Relation owner states each kernel's reference rule.
              StringRef code = "source.asset-carrier";
              std::string message;
              handleAllErrors(
                  relation::checkBundleTableReference(
                      *bundle, primitive->contract, index, carrier.domain),
                  [&](const zkc::Refusal &refusal) {
                    if (refusal.code != "relation-table-carrier")
                      code = "source.asset-table";
                    message = refusal.message();
                  },
                  [&](const ErrorInfoBase &other) {
                    message = other.message();
                  });
              if (!message.empty())
                return failure(code, message, operation.span);
            }
          }
          retained.emplace(identity, found->second);
        }
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
  for (const auto &declaration : closed.declarations) {
    if (auto error = work.charge(1, declaration.span))
      return error;
    if (declaration.relation &&
        declaration.relation->kind == RelationDefinition::Kind::Bundle) {
      const auto index = declaration.relation->asset;
      if (!index || *index >= project.assets().size() ||
          !project.assets()[*index].bundle())
        return failure("source.asset-reference", "captured relation is absent",
                       declaration.span);
      const auto &asset = project.assets()[*index];
      retained.emplace(asset.identity().str(), &asset);
    }
    if (declaration.body)
      if (auto error = visit(*declaration.body))
        return error;
  }
  for (const auto &entry : retained)
    closed.assets.push_back(*entry.second);
  return Error::success();
}
} // namespace zkc::language::detail

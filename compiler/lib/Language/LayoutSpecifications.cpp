#include "Checker.h"
#include "FormalSource.h"
#include "zkc/Language/Companions.h"

using namespace llvm;
namespace zkc::language::detail {

bool Checker::layoutSpecifications() {
  std::map<unsigned, Span> owners;
  std::set<std::pair<unsigned, std::string>> names;
  for (const auto &module : output.declarations) {
    auto moduleId = module.id;
    for (const auto &formal : sources[moduleId.index]->formalSyntax) {
      if (!formal.subject)
        continue;
      const auto &tree = formal.tree;
      auto span = tree.span(formal.node);
      if (!types.charge(1, span))
        return false;
      auto target = resolve(module, formal.subject->name, formal.subject->span);
      if (!target)
        return false;
      const auto &protocol = output.declarations[target->index];
      if (protocol.kind != Declaration::Kind::Protocol)
        return types.fail("source.spec.subject",
                          "spec subject is not a protocol", span);
      bool owner = formal.name.empty() && protocol.parent &&
                   protocol.parent->index == moduleId.index &&
                   !StringRef(formal.subject->name).contains("::") &&
                   formal.subject->arguments.empty();
      if (owner && !owners.emplace(target->index, span).second)
        return types.fail("source.spec.owner",
                          "protocol has more than one owner spec", span);
      if (!formal.name.empty() &&
          !names.emplace(moduleId.index, formal.name).second)
        return types.fail("source.spec.name",
                          "duplicate named spec in this module", span);
      if (!formal.authored) {
        if (recoveryDiagnostics && !recoveryDiagnostics->empty())
          continue;
        return types.fail("source.formal-syntax",
                          "spec source was not projected", span);
      }
      const auto &authored = *formal.authored;
      const auto &declaration = std::get<FormalDeclaration>(
          authored.nodes[authored.root.index].value);
      if (!declaration.body)
        return types.fail("source.formal-syntax", "spec has no body", span);
      const auto &body = std::get<FormalSequence>(
          authored.nodes[declaration.body->index].value);
      std::set<std::pair<unsigned, std::string>> labels;
      std::vector<PendingObligation> obligations;
      unsigned postconditions = 0, requests = 0;
      for (auto clauseId : body.elements) {
        const auto &node = authored.nodes[clauseId.index];
        const auto *clause = std::get_if<FormalClause>(&node.value);
        if (!clause)
          continue;
        using C = FormalClause::Kind;
        bool contract = clause->kind == C::Requires ||
                        clause->kind == C::Ensures ||
                        clause->kind == C::Target || clause->kind == C::Reduces;
        if (contract && !owner)
          return types.fail("source.spec.audit",
                            "consumer specs may request goals but cannot "
                            "change a protocol contract",
                            node.span);
        if (clause->label) {
          const auto &labelNode = authored.nodes[clause->label->index];
          const auto *label = std::get_if<FormalReference>(&labelNode.value);
          if (!label)
            return types.fail("source.spec.label", "spec label must be a name",
                              labelNode.span);
          unsigned space = contract ? 0 : clause->kind == C::Request ? 1 : 2;
          if (!labels.emplace(space, label->name).second)
            return types.fail("source.spec.label",
                              "duplicate explicit label in this spec namespace",
                              labelNode.span);
        }
        if (clause->kind == C::Ensures || clause->kind == C::Request) {
          if (!types.charge(1, node.span))
            return false;
          bool postcondition = clause->kind == C::Ensures;
          PendingObligation obligation{
              postcondition ? PendingObligation::Kind::Postcondition
                            : PendingObligation::Kind::Request,
              {},
              postcondition ? postconditions++ : requests++,
              node.span,
              {}};
          if (clause->label)
            obligation.label = std::get<FormalReference>(
                                   authored.nodes[clause->label->index].value)
                                   .name;
          if (owner || !formal.name.empty()) {
            auto identityOwner =
                owner ? protocol.qualifiedName
                      : module.qualifiedName + "::" + formal.name;
            auto identity = companionIdentity(
                identityOwner, {},
                postcondition ? ObligationRole::Postcondition
                              : ObligationRole::Request,
                obligation.label ? std::optional<StringRef>(*obligation.label)
                                 : std::nullopt,
                obligation.ordinal, work.limits);
            if (!identity)
              return types.accept(identity.takeError());
            obligation.companion = std::move(*identity);
          }
          obligations.push_back(std::move(obligation));
        }
      }
      output.pendingSpecifications.push_back({moduleId, *target, formal.name,
                                              owner, formal.isPublic, span,
                                              std::move(obligations)});
    }
  }
  return true;
}

} // namespace zkc::language::detail

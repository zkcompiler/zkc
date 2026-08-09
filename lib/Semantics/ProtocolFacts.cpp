//===- ProtocolFacts.cpp - judgment-free protocol body facts ------------===//

#include "zkc/Semantics/ProtocolFacts.h"

#include <algorithm>

using namespace mlir;
using namespace zkc;

semantics::ProtocolFacts semantics::ProtocolFacts::compute(Block &body) {
  ProtocolFacts facts;
  int64_t position = 0;
  for (Operation &operation : body) {
    if (auto member = dyn_cast<pir::ProtocolMemberOpInterface>(&operation))
      if (auto membership = member.getMembership()) {
        facts
            .memberships_[membership->instance][membership->role]
                         [membership->idx]
            .push_back(&operation);
        auto [span, inserted] = facts.bodySpans_.try_emplace(
            membership->instance, std::make_pair(position, position));
        if (!inserted) {
          span->second.first = std::min(span->second.first, position);
          span->second.second = std::max(span->second.second, position);
        }
      }

    if (auto reduce = dyn_cast<pir::ReduceOp>(operation))
      facts.reductions_.push_back(reduce);
    ++position;
  }
  return facts;
}

ArrayRef<Operation *> semantics::ProtocolFacts::membershipOccurrences(
    StringRef instance, StringRef role, int64_t occurrence) const {
  auto instanceIt = memberships_.find(instance);
  if (instanceIt == memberships_.end())
    return {};
  auto roleIt = instanceIt->second.find(role);
  if (roleIt == instanceIt->second.end())
    return {};
  auto occurrenceIt = roleIt->second.find(occurrence);
  if (occurrenceIt == roleIt->second.end())
    return {};
  return occurrenceIt->second;
}

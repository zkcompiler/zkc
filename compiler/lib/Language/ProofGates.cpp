#include "Semantics.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Source/Names.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>

using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<unsigned>>
Semantics::proofGateOrder(const Declaration &protocol,
                          const ProofEntry &proof) {
  if (proof.gates.empty())
    return std::vector<unsigned>{};
  auto refuse = [&](const Twine &message, Span span) {
    fail("source.gate", message, span);
    return std::nullopt;
  };
  if (proof.gates.size() > 64 ||
      proof.construction != ProofEntry::Construction::FiatShamir ||
      proof.selectedConstruction || proof.services.size() != 1 ||
      proof.services.front() >= protocol.services.size() ||
      protocol.services[proof.services.front()].owner != proof.verifier ||
      !protocol::installedDomains().hasFact("IndexBlockTranscript",
                                            {proof.suite}))
    return refuse("gates require a direct native block construction",
                  proof.span);

  std::set<std::vector<std::string>> unique;
  std::vector<std::vector<unsigned>> coordinates;
  for (const auto &gate : proof.gates) {
    if (gate.bits > 64 || gate.path.empty() || gate.path.size() > 64 ||
        !unique.insert(gate.path).second)
      return refuse("invalid or duplicate gate selector", gate.span);
    uint64_t bytes = 0;
    for (const auto &part : gate.path) {
      if (!charge(part.size() + 1, gate.span))
        return {};
      bytes += part.size() + 1;
      if (!source::isSourceIdentifier(part) || bytes > work.limits.symbolBytes)
        return refuse("invalid gate path", gate.span);
    }
    unsigned matches = 0;
    std::vector<unsigned> selected, coordinate;
    // Repeats retain lexical site identity. Calls consume authored path
    // components; generated names never participate in source resolution.
    auto walk = [&](auto &&self, const Body &body, unsigned component,
                    ArrayRef<unsigned> services, unsigned depth) -> bool {
      if (depth > work.limits.callDepth)
        return fail("source.limit", "gate occurrence depth exceeded",
                    gate.span);
      for (auto [index, operation] : enumerate(body.operations)) {
        if (!charge(services.size() + 1, operation.span))
          return false;
        coordinate.push_back(index);
        if (auto *repeat = std::get_if<ProtocolRepeat>(&operation.action)) {
          std::vector<unsigned> captures;
          for (auto service : repeat->services)
            captures.push_back(services[service.index]);
          if (!self(self, *repeat->region, component, captures, depth + 1))
            return false;
        } else if (operation.site && *operation.site == gate.path[component]) {
          if (component + 1 == gate.path.size()) {
            auto *query = std::get_if<ServiceQuery>(&operation.action);
            if (!query || !query->count ||
                services[query->service.index] != proof.services.front())
              return fail("source.gate",
                          "gate must select an indices query of the selected "
                          "verifier service",
                          gate.span);
            ++matches;
            selected = coordinate;
          } else {
            auto *call = std::get_if<ProtocolApplication>(&operation.action);
            if (!call)
              return fail(
                  "source.gate",
                  "gate path must traverse labelled protocol applications",
                  gate.span);
            std::vector<unsigned> captures;
            for (auto service : call->services)
              captures.push_back(services[service.index]);
            const auto &callee = declarations[call->callee.index];
            if (!callee.body ||
                !self(self, *callee.body, component + 1, captures, depth + 1))
              return false;
          }
        }
        coordinate.pop_back();
      }
      return true;
    };
    std::vector<unsigned> services(protocol.services.size());
    std::iota(services.begin(), services.end(), 0);
    if (!protocol.body || !walk(walk, *protocol.body, 0, services, 1))
      return {};
    if (matches != 1)
      return refuse(
          matches
              ? "ambiguous gate selector"
              : "gate selector is absent or crosses an unlabelled application",
          gate.span);
    coordinates.push_back(std::move(selected));
  }
  std::vector<unsigned> order(proof.gates.size());
  std::iota(order.begin(), order.end(), 0);
  llvm::sort(order, [&](unsigned a, unsigned b) {
    return coordinates[a] < coordinates[b];
  });
  return order;
}
} // namespace zkc::language::detail

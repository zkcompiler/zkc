#include "zkc/Analysis/OracleAccess.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringMap.h"
#include <limits>
#include <set>

using namespace llvm;
namespace zkc {
namespace {
using Operation = source::ExecutionOperation;
using Draws = std::set<std::string>;

class Analysis {
  const source::Execution &execution;
  OraclePolicy policy;
  OracleAccessReport report;
  std::map<std::string, const Operation *> producers;
  std::map<const Operation *, std::string> paths;
  std::map<std::string, Draws> dependencies, receivedDependencies;
  std::map<std::string, Draws> providerHistory, unknownDependencies;
  // Index zero is the empty chain. Each observation adds one immutable node;
  // provider successors and draws retain only an index, never copy a prefix.
  struct Observation {
    size_t parent;
    std::string payload, role;
  };
  std::vector<Observation> observations{{0, {}, {}}};
  std::map<std::string, size_t> absorptions, drawAbsorptions;
  std::set<std::string> authenticatedResponses;
  std::map<std::string, uint64_t> constants;
  std::map<std::string, size_t> coordinateTerms;
  std::map<source::Names, size_t> internedTerms;
  std::map<std::string, std::string> aliases;
  std::map<std::string, source::Names> guards;
  std::vector<const Operation *> indexDraws, responses;
  size_t steps = 0;
  size_t workLimit;
  bool exhausted = false;

  void finding(StringRef code, StringRef path) {
    report.findings.push_back({code.str(), path.str()});
  }
  bool charge(size_t amount = 1) {
    if (exhausted)
      return false;
    if (amount > workLimit - steps) {
      exhausted = true;
      finding("oracle-analysis-limit", "$");
      return false;
    }
    steps += amount;
    return true;
  }
  bool copyCost(const Draws &draws, const Draws &receptions,
                const Draws &history, const Draws &unknowns) {
    return charge(draws.size()) && charge(receptions.size()) &&
           charge(history.size()) && charge(unknowns.size());
  }
  bool validate() {
    if (execution.order.size() != execution.operations.size()) {
      finding("oracle-execution-invalid", "$");
      return false;
    }
    static const auto kernels = [] {
      StringMap<const protocol::Kernel *> result;
      for (const auto &k : protocol::kernels())
        result.try_emplace(k.key, &k);
      return result;
    }();
    for (size_t i = 0; i < execution.order.size(); ++i) {
      if (!charge())
        return false;
      const auto &path = execution.order[i];
      auto found = execution.operations.find(path);
      if (found == execution.operations.end() || found->second.ordinal != i ||
          !paths.emplace(&found->second, path).second) {
        finding("oracle-execution-invalid", path);
        return false;
      }
      const auto &op = found->second;
      if (op.role.empty() ||
          (op.callee == "message" &&
           (op.inputs.size() != 1 || op.outputs.size() != 1 ||
            op.receiver.empty() || op.receiver == op.role))) {
        finding("oracle-execution-invalid", path);
        return false;
      }
      auto k = kernels.find(op.callee);
      if (k != kernels.end() &&
          (op.inputs.size() != k->second->inputs.size() ||
           op.outputs.size() != k->second->outputs.size())) {
        const auto &c = k->second->contracts;
        finding(c.sampling                    ? "oracle-sampler-signature"
                : c.observation               ? "oracle-observation-signature"
                : op.callee == "oracle.check" ? "oracle-check-signature"
                                              : "oracle-execution-invalid",
                path);
        return false;
      }
      for (const auto &output : op.outputs) {
        if (!charge())
          return false;
        if (output.empty() || !producers.emplace(output, &op).second) {
          finding("oracle-execution-invalid", path);
          return false;
        }
      }
    }
    return true;
  }
  const Operation *producer(StringRef value) const {
    auto it = producers.find(value.str());
    return it == producers.end() ? nullptr : it->second;
  }
  // Exact local aliases only. Two receptions remain different even when the
  // authored sender supplies the same root to both.
  std::string localValue(std::string value) {
    while (charge()) {
      auto found = aliases.find(value);
      if (found == aliases.end())
        break;
      value = found->second;
    }
    return value;
  }
  // Only provenance aliases, not semantic equalities: messages remain distinct
  // values in the report, even though their authored sender is inspectable.
  std::optional<std::string> origin(std::string value) {
    while (charge()) {
      auto alias = aliases.find(value);
      if (alias != aliases.end()) {
        value = alias->second;
        continue;
      }
      const auto *op = producer(value);
      if (op && op->callee == "message") {
        value = op->inputs[0];
        continue;
      }
      return value;
    }
    return {};
  }
  const Operation *reception(std::string value, StringRef role) {
    while (charge()) {
      auto alias = aliases.find(value);
      if (alias != aliases.end()) {
        value = alias->second;
        continue;
      }
      const auto *op = producer(value);
      return op && op->callee == "message" && op->receiver == role ? op
                                                                   : nullptr;
    }
    return nullptr;
  }
  void constant(const Operation &op) {
    if (op.outputs.size() != 1)
      return;
    std::optional<uint64_t> result;
    if (op.callee == "index.constant" && op.attributes.size() == 1) {
      uint64_t n;
      if (!StringRef(op.attributes[0]).getAsInteger(10, n))
        result = n;
    } else if (op.inputs.size() == 2 && constants.count(op.inputs[0]) &&
               constants.count(op.inputs[1])) {
      auto a = constants.at(op.inputs[0]), b = constants.at(op.inputs[1]);
      if (op.callee == "index.add" && a <= UINT64_MAX - b)
        result = a + b;
      else if (op.callee == "index.sub" && a >= b)
        result = a - b;
      else if (op.callee == "index.mul" && (!b || a <= UINT64_MAX / b))
        result = a * b;
      else if (op.callee == "index.div" && b)
        result = a / b;
      else if (op.callee == "index.mod" && b)
        result = a % b;
    }
    if (result)
      constants.emplace(op.outputs[0], *result);
  }
  size_t intern(source::Names term) {
    auto [it, inserted] =
        internedTerms.emplace(std::move(term), internedTerms.size());
    return it->second;
  }
  size_t coordinateTerm(const std::string &value) {
    auto [it, inserted] = coordinateTerms.emplace(value, 0);
    if (inserted)
      it->second = intern({"value", value});
    return it->second;
  }
  void coordinate(const Operation &op) {
    if (op.outputs.size() != 1)
      return;
    const auto &out = op.outputs[0];
    if (op.callee == "message" && op.inputs.size() == 1) {
      // Authored transport provenance only. This does not equate a malicious
      // peer's supplied bytes with the value in an honest local execution.
      coordinateTerms[out] = coordinateTerm(op.inputs[0]);
    } else if (auto it = constants.find(out); it != constants.end()) {
      coordinateTerms[out] = intern({"constant", std::to_string(it->second)});
    } else if (op.callee == "indices.empty" && op.inputs.empty() &&
               op.attributes.empty()) {
      coordinateTerms[out] = intern({"indices.empty"});
    } else if (op.inputs.size() == 2 && op.attributes.empty() &&
               (op.callee == "index.add" || op.callee == "index.sub" ||
                op.callee == "index.mul" || op.callee == "index.div" ||
                op.callee == "index.mod" || op.callee == "indices.append" ||
                op.callee == "indices.at")) {
      // Congruence of exact checked-index expressions on successful execution.
      // No algebraic rewriting, range inference or elimination of failures.
      coordinateTerms[out] =
          intern({op.callee, std::to_string(coordinateTerm(op.inputs[0])),
                  std::to_string(coordinateTerm(op.inputs[1]))});
    }
  }
  void selected(const Operation &op) {
    if ((op.callee != "commitments.at" && op.callee != "opening_states.at") ||
        !constants.count(op.inputs[1]))
      return;
    // Follow only locally constructed persistent lists. A received list may
    // have different elements from its authored sender, even after a round
    // trip.
    std::vector<std::string> reversed;
    std::string value = op.inputs[0];
    while (charge()) {
      if (auto alias = aliases.find(value); alias != aliases.end()) {
        value = alias->second;
        continue;
      }
      const auto *p = producer(value);
      if (!p)
        return;
      if (p->callee == "commitments.empty" ||
          p->callee == "opening_states.empty") {
        auto index = constants.at(op.inputs[1]);
        if (index < reversed.size())
          aliases.emplace(op.outputs[0], reversed[reversed.size() - 1 - index]);
        return;
      }
      if (p->callee != "commitments.append" &&
          p->callee != "opening_states.append")
        return;
      reversed.push_back(p->inputs[1]);
      value = p->inputs[0];
    }
  }
  void guard(const std::string &value, const std::string &path,
             const Operation &guardOp) {
    std::vector<std::string> pending{value};
    std::set<std::string> visited;
    while (!pending.empty() && charge()) {
      auto v = pending.back();
      pending.pop_back();
      if (!visited.insert(v).second)
        continue;
      const auto *p = producer(v);
      if (!p || p->role != guardOp.role || p->ordinal >= guardOp.ordinal)
        continue;
      guards[v].push_back(path);
      if (protocol::isConjunction(p->callee) && charge(p->inputs.size()))
        pending.insert(pending.end(), p->inputs.begin(), p->inputs.end());
    }
  }

public:
  Analysis(const source::Execution &execution, OraclePolicy policy,
           size_t workLimit)
      : execution(execution), policy(policy), workLimit(workLimit) {}
  OracleAccessReport run() {
    report.acceptanceResult = policy.acceptanceResult;
    if (!validate())
      return std::move(report);
    for (const auto &path : execution.order) {
      if (!charge())
        return std::move(report);
      const auto &op = execution.operations.at(path);
      Draws draws, receptions, history, unknowns;
      for (const auto &input : op.inputs) {
        if (!charge())
          return std::move(report);
        if (const auto *p = producer(input); p && p->ordinal >= op.ordinal) {
          finding("oracle-execution-invalid", path);
          return std::move(report);
        }
        const auto &deps = dependencies[input];
        const auto &received = receivedDependencies[input];
        const auto &absorbed = providerHistory[input];
        const auto &unknown = unknownDependencies[input];
        if (!copyCost(deps, received, absorbed, unknown))
          return std::move(report);
        draws.insert(deps.begin(), deps.end());
        receptions.insert(received.begin(), received.end());
        history.insert(absorbed.begin(), absorbed.end());
        unknowns.insert(unknown.begin(), unknown.end());
      }
      const bool message = op.callee == "message";
      const auto *contracts = protocol::operationContracts(op.callee);
      const auto *sample = protocol::samplingContract(op.callee);
      const auto *observation = contracts && contracts->observation
                                    ? &*contracts->observation
                                    : nullptr;
      if (!message && protocol::hasUnclassifiedProviderEffect(op.callee)) {
        unknowns.insert(path);
        if (policy.publicationBeforeQueries || policy.queriesBeforeResponses ||
            policy.sampledQueries)
          finding("oracle-unsupported-provenance", path);
      }
      if (sample &&
          (sample->stateInput >= op.inputs.size() ||
           sample->valueOutput >= op.outputs.size() ||
           sample->stateOutput >= op.outputs.size() ||
           (sample->boundInput && *sample->boundInput >= op.inputs.size()))) {
        finding("oracle-sampler-signature", path);
        return std::move(report);
      }
      if (observation && (observation->stateInput >= op.inputs.size() ||
                          observation->payloadInput >= op.inputs.size() ||
                          observation->stateOutput >= op.outputs.size())) {
        finding("oracle-observation-signature", path);
        return std::move(report);
      }
      if (sample) {
        const auto before = absorptions[op.inputs[sample->stateInput]];
        drawAbsorptions[path] = before;
        absorptions[op.outputs[sample->stateOutput]] = before;
      } else if (observation) {
        const auto before = absorptions[op.inputs[observation->stateInput]];
        auto payload = localValue(op.inputs[observation->payloadInput]);
        if (exhausted)
          return std::move(report);
        observations.push_back({before, std::move(payload), op.role});
        absorptions[op.outputs[observation->stateOutput]] =
            observations.size() - 1;
      }
      for (size_t i = 0; i < op.outputs.size(); ++i) {
        if (!charge() || !copyCost(draws, receptions, history, unknowns))
          return std::move(report);
        auto &outDraws = dependencies[op.outputs[i]];
        auto &outReceived = receivedDependencies[op.outputs[i]];
        auto &outHistory = providerHistory[op.outputs[i]];
        auto &outUnknown = unknownDependencies[op.outputs[i]];
        outDraws = draws;
        outReceived = receptions;
        outHistory = history;
        outUnknown = unknowns;
        if (message) {
          // An adversarial receive starts a new dependency; the sender's
          // sampling history is not authority for the received value.
          outDraws.clear();
          outReceived = {path};
          outHistory.clear();
          outUnknown.clear();
        } else if (sample) {
          outDraws.clear();
          outReceived.clear();
          if (!charge(receptions.size()))
            return std::move(report);
          outHistory.insert(receptions.begin(), receptions.end());
          if (i == sample->valueOutput) {
            // Provider dependence is historical, but direct data arguments
            // (notably the bound) can still be peer-selected or sampled.
            for (size_t j = 0; j < op.inputs.size(); ++j) {
              if (!charge())
                return std::move(report);
              if (j == sample->stateInput)
                continue;
              const auto &d = dependencies[op.inputs[j]];
              const auto &r = receivedDependencies[op.inputs[j]];
              if (!charge(d.size()) || !charge(r.size()))
                return std::move(report);
              outDraws.insert(d.begin(), d.end());
              outReceived.insert(r.begin(), r.end());
            }
            outDraws.insert(path);
          }
        } else if (observation && i == observation->stateOutput) {
          outDraws.clear();
          outReceived.clear();
          if (!charge(receptions.size()))
            return std::move(report);
          outHistory.insert(receptions.begin(), receptions.end());
        }
      }
      if (sample && sample->domain == protocol::SampleDomain::BoundedIndex)
        indexDraws.push_back(&op);
      constant(op);
      coordinate(op);
      selected(op);
      if (exhausted)
        return std::move(report);
      if (protocol::isAcceptanceGuard(op.callee))
        guard(op.inputs[0], path, op);
      if (op.callee == "message") {
        auto input = origin(op.inputs[0]);
        const auto *p = input ? producer(*input) : nullptr;
        if (p && p->callee == "oracle.open")
          responses.push_back(&op);
      }
      if (exhausted)
        return std::move(report);
    }
    if (policy.acceptanceResult) {
      const auto index = *policy.acceptanceResult;
      const auto value = index < execution.results.size()
                             ? execution.values.find(execution.results[index])
                             : execution.values.end();
      if (value != execution.values.end() && !value->second.role.empty())
        report.acceptanceRole = value->second.role;
      if (value == execution.values.end() || value->second.type != "bool" ||
          value->second.role.empty()) {
        finding("oracle-acceptance-result", "$");
      } else {
        Operation sink;
        sink.role = value->second.role;
        sink.ordinal = std::numeric_limits<size_t>::max();
        guard(value->first, "$accept[" + std::to_string(index) + "]", sink);
      }
      if (exhausted)
        return std::move(report);
    }
    for (const auto &path : execution.order) {
      if (!charge())
        return std::move(report);
      const auto &op = execution.operations.at(path);
      if (op.callee != "oracle.check")
        continue;
      if (op.inputs.size() != 6 || op.outputs.size() != 1) {
        finding("oracle-check-signature", path);
        continue;
      }
      OracleAccess access;
      access.path = path;
      access.role = op.role;
      access.ordinal = op.ordinal;
      access.root = op.inputs[0];
      access.width = op.inputs[1];
      access.height = op.inputs[2];
      access.coordinate = op.inputs[3];
      access.row = op.inputs[4];
      access.proof = op.inputs[5];
      access.accepted = op.outputs[0];
      const auto *received = reception(access.root, access.role);
      if (received)
        access.rootReception = paths.at(received);
      if (!charge(guards[access.accepted].size()))
        return std::move(report);
      access.guards = guards[access.accepted];
      if (access.guards.empty())
        finding("oracle-check-unguarded", path);
      const auto &draws = dependencies[access.coordinate];
      const auto &receptions = receivedDependencies[access.coordinate];
      const auto &history = providerHistory[access.coordinate];
      const auto &unknowns = unknownDependencies[access.coordinate];
      if (!copyCost(draws, receptions, history, unknowns))
        return std::move(report);
      access.coordinateDraws.assign(draws.begin(), draws.end());
      access.coordinateReceptions.assign(receptions.begin(), receptions.end());
      access.coordinateProviderHistory.assign(history.begin(), history.end());
      access.coordinateUnknowns.assign(unknowns.begin(), unknowns.end());
      const auto localCoordinate = localValue(access.coordinate);
      if (const auto *p = producer(localCoordinate)) {
        if (const auto *sample = protocol::samplingContract(p->callee);
            sample && localCoordinate == p->outputs[sample->valueOutput]) {
          access.coordinateSample = paths.at(p);
          if (sample->domain == protocol::SampleDomain::BoundedIndex &&
              sample->boundInput)
            access.sampleBoundMatchesHeight =
                localValue(p->inputs[*sample->boundInput]) ==
                localValue(access.height);
        }
      }
      const auto localRoot = localValue(access.root);
      if (exhausted)
        return std::move(report);
      if (policy.sampledQueries) {
        if (!access.coordinateSample)
          finding("oracle-query-not-exact-sample", path);
        else if (!access.sampleBoundMatchesHeight)
          finding("oracle-query-bound-unresolved", path);
      }
      for (const auto &draw : draws) {
        if (!charge())
          return std::move(report);
        const auto *sample =
            protocol::samplingContract(execution.operations.at(draw).callee);
        if (sample->provider != protocol::RandomnessProvider::Transcript)
          continue;
        bool bindsRoot = false;
        for (size_t node = drawAbsorptions[draw]; node;
             node = observations[node].parent) {
          if (!charge())
            return std::move(report);
          const auto &observe = observations[node];
          if (observe.role == access.role && observe.payload == localRoot) {
            bindsRoot = true;
            break;
          }
        }
        if (bindsRoot)
          access.publicationBoundDraws.push_back(draw);
        else if (policy.publicationBeforeQueries)
          finding("oracle-query-publication-unabsorbed", path);
      }
      if (policy.publicationBeforeQueries && !receptions.empty())
        finding("oracle-query-coordinate-received", path);
      if (!access.guards.empty())
        for (const auto &value : {access.row, access.proof})
          if (const auto *response = reception(value, access.role))
            authenticatedResponses.insert(paths.at(response));
      auto row = origin(access.row), proof = origin(access.proof);
      const auto *opening = row ? producer(*row) : nullptr;
      if (opening && opening->callee == "oracle.open" && proof &&
          producer(*proof) == opening && opening->outputs.size() == 2 &&
          *row == opening->outputs[0] && *proof == opening->outputs[1]) {
        access.opening = paths.at(opening);
        access.openingCoordinateLinked = coordinateTerm(opening->inputs[1]) ==
                                         coordinateTerm(access.coordinate);
        if (!access.openingCoordinateLinked)
          finding("oracle-opening-coordinate-unresolved", path);
        auto state = origin(opening->inputs[0]);
        auto root = origin(access.root);
        const auto *publication = state ? producer(*state) : nullptr;
        if (publication && publication->callee == "oracle.commit" && root &&
            producer(*root) == publication &&
            publication->outputs.size() == 2 &&
            *root == publication->outputs[0] &&
            *state == publication->outputs[1]) {
          access.publication = paths.at(publication);
          if (policy.publicationBeforeQueries && received)
            for (const auto &draw : draws) {
              if (!charge())
                return std::move(report);
              if (execution.operations.at(draw).ordinal <= received->ordinal)
                finding("oracle-query-before-publication", path);
            }
        }
      }
      if (policy.publicationBeforeQueries &&
          (!access.publication || !access.rootReception))
        finding("oracle-publication-unresolved", path);
      if (exhausted)
        return std::move(report);
      report.accesses.push_back(std::move(access));
    }
    std::optional<size_t> firstResponse;
    for (const auto *response : responses) {
      if (!charge())
        return std::move(report);
      if (!firstResponse || response->ordinal < *firstResponse)
        firstResponse = response->ordinal;
      if (!authenticatedResponses.count(paths.at(response)))
        finding("oracle-response-unauthenticated", paths.at(response));
    }
    if (policy.queriesBeforeResponses)
      for (const auto *draw : indexDraws) {
        if (!charge())
          return std::move(report);
        if (firstResponse && *firstResponse < draw->ordinal)
          finding("oracle-query-after-response", paths.at(draw));
      }
    return std::move(report);
  }
};
} // namespace

OracleAccessReport analyzeOracleAccess(const source::Execution &execution,
                                       OraclePolicy policy, size_t workLimit) {
  return Analysis(execution, policy, workLimit).run();
}
Expected<OracleAccessReport> inspectOracleAccess(const source::Module &module,
                                                 StringRef entry,
                                                 OraclePolicy policy) {
  auto execution = source::inspectExecution(module, entry);
  if (!execution)
    return execution.takeError();
  return analyzeOracleAccess(*execution, policy);
}
json::Value encodeOracleAccess(const OracleAccessReport &report) {
  auto names = [](const source::Names &values) {
    json::Array out;
    for (const auto &v : values)
      out.push_back(v);
    return out;
  };
  json::Array accesses, findings;
  for (const auto &a : report.accesses) {
    json::Object entry{
        {"path", a.path},
        {"role", a.role},
        {"root", a.root},
        {"width", a.width},
        {"height", a.height},
        {"coordinate", a.coordinate},
        {"row", a.row},
        {"proof", a.proof},
        {"accepted", a.accepted},
        {"ordinal", uint64_t(a.ordinal)},
        {"guards", names(a.guards)},
        {"coordinate_draws", names(a.coordinateDraws)},
        {"coordinate_receptions", names(a.coordinateReceptions)},
        {"coordinate_provider_history", names(a.coordinateProviderHistory)},
        {"coordinate_unknowns", names(a.coordinateUnknowns)},
        {"publication_bound_draws", names(a.publicationBoundDraws)},
        {"sample_bound_matches_height", a.sampleBoundMatchesHeight}};
    if (a.coordinateSample)
      entry["coordinate_sample"] = *a.coordinateSample;
    if (a.opening)
      entry["opening"] = *a.opening;
    if (a.publication)
      entry["publication"] = *a.publication;
    if (a.rootReception)
      entry["root_reception"] = *a.rootReception;
    entry["opening_coordinate_linked"] = a.openingCoordinateLinked;
    accesses.push_back(std::move(entry));
  }
  for (const auto &f : report.findings)
    findings.push_back(json::Object{{"code", f.code}, {"path", f.path}});
  json::Object result{{"format", "zkc.oracle-access/2"},
                      {"accesses", std::move(accesses)},
                      {"findings", std::move(findings)}};
  if (report.acceptanceResult)
    result["acceptance_result"] = *report.acceptanceResult;
  if (report.acceptanceRole)
    result["acceptance_role"] = *report.acceptanceRole;
  return result;
}
} // namespace zkc

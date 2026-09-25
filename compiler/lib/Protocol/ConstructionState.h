#ifndef ZKC_PROTOCOL_CONSTRUCTION_STATE_H
#define ZKC_PROTOCOL_CONSTRUCTION_STATE_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Protocol/Construction.h"
#include "llvm/ADT/BitVector.h"
#include <functional>
#include <iterator>
#include <map>
#include <optional>
#include <set>

namespace zkc::protocol::construction {
using llvm::Expected;
using llvm::StringRef;
namespace json = llvm::json;
using Names = std::map<std::string, std::string>;
inline Names pairsOf(const source::Assignments &pairs) {
  return Names(pairs.begin(), pairs.end());
}
template <typename T>
source::Instruction instruction(std::string site, T value,
                                const source::Node *origin = nullptr) {
  source::Instruction result;
  result.site = std::move(site);
  result.value = std::move(value);
  if (origin)
    result.location = origin->location;
  return result;
}
inline bool hasLocalControl(const source::Function &fn) {
  bool found = false;
  if (fn.body)
    source::walk(*fn.body, [&](const source::Instruction &i) {
      found |= i.get<source::Conditional>() || i.get<source::For>() ||
               i.get<source::Match>() || i.get<source::VariantConstruct>();
    });
  return found;
}
inline bool randomDraw(StringRef op) { return isConstructionDraw(op); }
inline bool recipe(StringRef op) { return isPublicReplay(op); }
// Invocation-local interning keeps long source paths out of every SSA fact.
// IDs are never emitted: iteration recovers the exact original token strings.
struct DependencyTokens {
  std::map<std::string, unsigned> ids;
  std::vector<std::string> names;
  std::function<bool(size_t)> charge;
};
class TokenSet {
  DependencyTokens *pool = nullptr;
  llvm::BitVector bits;
  size_t words() const { return (bits.size() + 63) / 64; }
  bool charge(size_t cost) const { return !pool || pool->charge(cost); }

public:
  TokenSet() = default;
  TokenSet(const TokenSet &other) : pool(other.pool) {
    if (charge(1 + other.words()))
      bits = other.bits;
  }
  TokenSet &operator=(const TokenSet &other) {
    if (this != &other) {
      pool = other.pool;
      if (charge(1 + other.words()))
        bits = other.bits;
    }
    return *this;
  }
  TokenSet(TokenSet &&) = default;
  TokenSet &operator=(TokenSet &&) = default;
  void attach(DependencyTokens &tokens) {
    assert(!pool || pool == &tokens);
    pool = &tokens;
  }
  void insert(const std::string &token) {
    assert(pool);
    // Charge string lookup/storage and possible bitmap reallocation before it
    // happens. The source grammar separately bounds individual token lengths.
    if (!charge(1 + token.size() / 16 + (pool->names.size() + 64) / 64))
      return;
    auto [it, added] = pool->ids.try_emplace(token, pool->names.size());
    if (added)
      pool->names.push_back(token);
    if (it->second >= bits.size())
      bits.resize(it->second + 1);
    bits.set(it->second);
  }
  void join(const TokenSet &other) {
    assert(!pool || !other.pool || pool == other.pool);
    if (!pool)
      pool = other.pool;
    // Bound both the union traversal and a possible copy on growth.
    if (charge(1 + words() + other.words()))
      bits |= other.bits;
  }
  bool operator==(const TokenSet &other) const {
    assert(!pool || !other.pool || pool == other.pool);
    if (!(pool ? charge(1 + words() + other.words())
               : other.charge(1 + other.words())))
      return false;
    return bits == other.bits;
  }
  class Iterator {
    const TokenSet *set;
    int index;

  public:
    using iterator_category = std::input_iterator_tag;
    using value_type = std::string;
    using difference_type = std::ptrdiff_t;
    using pointer = const std::string *;
    using reference = const std::string &;
    Iterator(const TokenSet *set, int index) : set(set), index(index) {}
    reference operator*() const { return set->pool->names[index]; }
    Iterator &operator++() {
      index = set->bits.find_next(index);
      return *this;
    }
    Iterator operator++(int) {
      auto old = *this;
      ++*this;
      return old;
    }
    bool operator==(const Iterator &other) const {
      return set == other.set && index == other.index;
    }
    bool operator!=(const Iterator &other) const { return !(*this == other); }
  };
  Iterator begin() const {
    // Enumeration is used only when exporting final demand. Include both the
    // word scan and an upper bound on emitted token/string-set insertions.
    if (!charge(1 + words() + bits.size()))
      return end();
    return Iterator(this, bits.find_first());
  }
  Iterator end() const { return Iterator(this, -1); }
};
struct ValueDependencies {
  std::set<unsigned> values, draws;
  // Provider origins consumed by samplers with no construction counterpart.
  // Keep these effects even if their values are dead; substitute them through
  // protocol calls before deciding whether the selected RNG was touched.
  std::map<std::string, std::set<unsigned>> unconvertedSamplers;
  TokenSet tokens;
  std::set<std::string> blockers;
  void join(const ValueDependencies &d) {
    values.insert(d.values.begin(), d.values.end());
    draws.insert(d.draws.begin(), d.draws.end());
    for (const auto &[key, origins] : d.unconvertedSamplers)
      unconvertedSamplers[key].insert(origins.begin(), origins.end());
    tokens.join(d.tokens);
    blockers.insert(d.blockers.begin(), d.blockers.end());
  }
  bool operator==(const ValueDependencies &d) const {
    return values == d.values && draws == d.draws &&
           unconvertedSamplers == d.unconvertedSamplers && tokens == d.tokens &&
           blockers == d.blockers;
  }
  ValueDependencies challenge() const {
    ValueDependencies d = *this;
    d.draws.insert(d.values.begin(), d.values.end());
    d.values.clear();
    return d;
  }
  ValueDependencies
  substitute(const std::vector<ValueDependencies> &args) const {
    ValueDependencies d;
    d.tokens = tokens;
    d.blockers = blockers;
    for (auto i : values)
      d.join(args.at(i));
    for (auto i : draws)
      d.join(args.at(i).challenge());
    for (const auto &[key, origins] : unconvertedSamplers)
      for (auto i : origins) {
        const auto &actual = args.at(i).values;
        d.unconvertedSamplers[key].insert(actual.begin(), actual.end());
      }
    return d;
  }
};
struct ValueInfo {
  std::string role, type;
  ValueDependencies dep;
};
using Env = std::map<std::string, ValueInfo>;
struct DependencySummary {
  std::vector<ValueInfo> outputs;
  ValueDependencies roots;
};
struct Instance {
  const source::Instance *record = nullptr;
  const source::Protocol *def = nullptr;
  Names roles, parameters, dependencies;
  DependencySummary summary;
  std::string generated;
  bool analyzed = false;
};
struct Binding {
  std::string label, type;
  std::vector<std::string> ports;
  std::string producerPort;
};
// One construction owns the source snapshots and the shared work budget.
// Availability and exact resource origins have separate summaries; emission
// consumes both without changing the admitted source or its identity.
class Construction {
  const source::Module &source, &sourceIdentity;
  const source::Construction &descriptor;
  mlir::MLIRContext &ctx;
  std::string suite, entry, producer, validator, root, selectedRng;
  DependencyTokens dependencyTokens{
      {}, {}, [this](size_t cost) { return budget(cost); }};
  struct Signature {
    std::vector<std::string> inputs, outputs;
  };
  std::map<std::string, source::OperationBinding> operations;
  std::map<std::string, Signature> signatures;
  Names generatedBindings;
  std::vector<source::OperationBinding> outBindings;
  std::map<std::string, const source::Function *> functions;
  std::map<std::string, const source::Protocol *> definitions;
  std::map<std::string, Instance> instances;
  std::set<std::pair<std::string, std::string>> draws;
  std::vector<Binding> bindings;
  Names publicPorts;
  std::set<std::string> demanded, used;
  std::string problem, sourcePrefix;
  unsigned next = 0;
  size_t work = 0;
  std::vector<source::Function> outFunctions;
  std::vector<source::Protocol> outProtocols;
  std::vector<source::Instance> outInstances;
  json::Array inputMap, origins, resultMap;
  std::set<std::string> emitted;
  Names inactiveNames, inactiveDefinitions;
  using Origin = std::optional<unsigned>;
  using Flow = std::vector<Origin>;
  std::map<std::string, Flow> resourceSummaries;
  std::set<size_t> inertEntryResults;
  bool fail(StringRef why);
  bool budget(size_t cost = 1);
  bool account(const ValueDependencies &dep);
  std::string fresh();
  std::string contract(const std::string &key);
  const Signature *signature(const std::string &key);
  std::string transcriptType() const;
  std::string transcriptBinding(const std::string &operation,
                                const std::string &payload = {});
  std::string seedBinding(const std::string &operation,
                          const std::string &payload);
  std::string token(const std::string &instance, const std::string &path,
                    const std::string &name);
  bool needs(const std::string &instance, const std::string &path,
             const std::string &name);
  void mark(ValueInfo &v, const std::string &id, const std::string &path,
            const std::string &name);
  std::vector<ValueInfo> operands(const source::Names &v, const Env &env);
  ValueDependencies join(const std::vector<ValueInfo> &vs);
  uint64_t count(const source::Loop &loop, const Instance &i);
  DependencySummary local(const std::string &id, const std::string &path,
                          const source::Instruction &ins, const Env &outer);
  DependencySummary block(const std::string &id, const std::string &path,
                          const source::Body &body, Env env);
  void analyze(const std::string &id);
  bool descriptorAdmission();

  // Exact source RNG result origins are a separate question from conservative
  // recipe availability. Every RNG successor in this finite language is a
  // projection of an input resource. Counted-loop projections compose by binary
  // exponentiation, including arbitrary permutations; no iteration is unrolled.
  Flow resourceBlock(const std::string &id, const source::Body &body,
                     std::map<std::string, Origin> env);
  const Flow &resourceInstance(const std::string &id);
  bool omitResult(const std::string &id, size_t k);

  struct EmissionState {
    Names original, mirror, types, roles;
    std::string producerTranscript, validatorTranscript;
  };
  std::string lookup(const Names &env, const std::string &name);
  std::string value(EmissionState &st, const std::string &name,
                    bool replay = false);
  std::string helper(source::Body &body, const std::string &role,
                     const std::string &key, const source::Names &attrs,
                     const std::vector<std::string> &operands,
                     const std::string &protocol, const std::string &callsite,
                     const std::string &function, const std::string &opsite,
                     const std::string &sourceRole, const std::string &kind,
                     std::vector<std::string> &results,
                     const source::Node *origin = nullptr);
  void emitLocal(const std::string &id, const std::string &path,
                 const source::Instruction &ins, EmissionState &state,
                 source::Body &body, bool active);
  bool preserveLocal(const std::string &id, const std::string &path,
                     const source::Function &fn, const std::string &role,
                     bool active);
  std::string outputType(const std::string &key, size_t index);
  void observe(const std::string &id, const source::Instruction &ins,
               EmissionState &st, source::Body &body);
  bool inputMirror(const std::string &id, size_t k);
  bool outputMirror(const std::string &id, size_t k);
  // Preserve unreachable source bodies, including effects, without creating
  // availability obligations for an exact zero loop. Their calls use separate
  // unreachable source instances; no live logical path uses these names.
  std::string inactiveInstance(const std::string &id);

  std::vector<std::string>
  emitBlock(const std::string &id, const std::string &path,
            const source::Body &instructions, EmissionState &st,
            source::Body &body, std::vector<source::Dependency> &depDecls,
            source::Assignments &depBindings, bool active,
            std::vector<std::string> *returnedMirrors = nullptr);
  void emitInstance(const std::string &id);

  void reserve(const source::Module &module);

public:
  Construction(const source::Module &source,
               const source::Module &sourceIdentity,
               const source::Construction &descriptor, mlir::MLIRContext &ctx)
      : source(source), sourceIdentity(sourceIdentity), descriptor(descriptor),
        ctx(ctx) {}
  Expected<ConstructionResult> run();
};

} // namespace zkc::protocol::construction
#endif

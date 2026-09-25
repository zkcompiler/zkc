#include "zkc/Protocol/Construction.h"
#include "ConstructionState.h"
#include "zkc/Compiler/Instantiation.h"
#include "zkc/Protocol/Admission.h"
#include "zkc/Protocol/Algorithms.h"
#include "zkc/Protocol/Domains.h"
#include "zkc/Protocol/Kernels.h"
#include "zkc/Protocol/Module.h"
#include "zkc/Source/Codec.h"
#include "zkc/Source/Resolution.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <functional>
#include <optional>
#include <type_traits>

using namespace llvm;
namespace zkc::protocol::construction {
bool Construction::fail(StringRef why) {
  if (problem.empty())
    problem = why.str();
  return false;
}

bool Construction::budget(size_t cost) {
  if (!problem.empty())
    return false;
  // Account for dependency-set copying as well as visits. Work is independent
  // of the public trip count and has a separate host resource ceiling.
  if (cost > 1000000 || work > 1000000 - cost)
    return fail("construction-analysis-limit");
  work += cost;
  return true;
}

std::string Construction::fresh() {
  std::string n;
  do {
    n = "constructed_" + sourcePrefix + std::to_string(next++);
  } while (used.count(n));
  used.insert(n);
  return n;
}

std::string Construction::contract(const std::string &key) {
  auto found = operations.find(key);
  if (found == operations.end()) {
    fail("construction-binding:" + key);
    return {};
  }
  return found->second.contract;
}

const Construction::Signature *Construction::signature(const std::string &key) {
  auto found = signatures.find(key);
  if (found != signatures.end())
    return &found->second;
  Signature result;
  auto binding = operations.find(key);
  if (binding == operations.end()) {
    fail("construction-binding:" + key);
    return nullptr;
  }
  auto selected = resolveBinding(binding->second, false);
  if (!selected) {
    fail("construction-binding:" + key + ":" + toString(selected.takeError()));
    return nullptr;
  }
  for (const auto &ty : selected->inputs)
    result.inputs.push_back(ty.spelling());
  for (const auto &ty : selected->outputs)
    result.outputs.push_back(ty.spelling());
  return &signatures.emplace(key, std::move(result)).first->second;
}

std::string Construction::token(const std::string &instance,
                                const std::string &path,
                                const std::string &name) {
  return instance + "/" + path + "/" + name;
}

bool Construction::needs(const std::string &instance, const std::string &path,
                         const std::string &name) {
  return demanded.count(token(instance, path, name));
}

// Admission has already required a parameter count to name a protocol
// parameter, every instance to bind each parameter, and every binding and
// constant count to be a bounded natural
// (docs/spec/profiles/source/common-protocols.md).
uint64_t Construction::count(const source::Loop &loop, const Instance &i) {
  const auto &n = loop.count;
  StringRef value = n.value;
  if (n.kind == source::LoopCount::Kind::Parameter) {
    auto found = i.parameters.find(n.value);
    if (found == i.parameters.end())
      report_fatal_error("construction reached a loop count its instance does "
                         "not bind; admission must refuse it first");
    value = found->second;
  }
  uint64_t result = 0;
  if (value.getAsInteger(10, result))
    report_fatal_error("construction reached a loop count that is not a "
                       "natural; admission must refuse it first");
  return result;
}

bool Construction::descriptorAdmission() {
  entry = descriptor.entry;
  producer = descriptor.producer;
  validator = descriptor.validator;
  // Installation supplies the nominal association, not constructor support.
  const auto &domains = installedDomains();
  bool supported =
      descriptor.suite == "merlin3.bls12-381.fr64be/1" ||
      (descriptor.suite == "merlin3.ristretto255.scalar64le/1" ||
       descriptor.suite ==
           "merlin3.koala-bear.ext8-binomial3.rejection31le/1" ||
       descriptor.suite == "spongefish0.7.4.keccak.bls12-381.fr64be/1");
  if (producer == validator || !supported ||
      domains.identitySort(descriptor.suite) != "Transcript" ||
      domains.associatedIdentity(descriptor.suite, "ChallengeField").empty())
    return fail("construction-suite-or-roles");
  suite = descriptor.suite;
  for (const auto &e : source.entries)
    if (e.name == entry)
      root = e.instance;
  if (root.empty())
    return fail("construction-entry");
  const auto &i = instances.at(root);
  const auto &ports = i.def->arguments;
  if (descriptor.publicBindings.size() > 1024)
    return fail("construction-descriptor");
  selectedRng = descriptor.randomness;
  bool rngFound = false;
  for (const auto &p : ports)
    if (p.name == selectedRng && i.roles.at(p.role) == validator &&
        p.type == "rng:" + associatedIdentity(suite, "ChallengeField").str())
      rngFound = true;
  if (!rngFound)
    return fail("construction-rng-port");
  if (descriptor.draws.size() > 32768)
    return fail("construction-descriptor-limit");
  for (const auto &selector : descriptor.draws) {
    auto f = functions.find(selector.first);
    bool found = false;
    if (f != functions.end() && f->second->body)
      for (const auto &ins : *f->second->body)
        if (const auto *op = ins.get<source::Operation>())
          if (ins.site == selector.second && randomDraw(contract(op->callee))) {
            {
              const auto *sig = signature(op->callee);
              if (!sig)
                return false;
              const auto *sample = samplingContract(contract(op->callee));
              if (sample->domain == SampleDomain::Field &&
                  sig->outputs[sample->valueOutput] !=
                      "field:" +
                          associatedIdentity(suite, "ChallengeField").str())
                return fail("construction-challenge-field");
            }
            found = true;
          }
    if (!found || !draws.insert(selector).second)
      return fail("construction-draw-selector");
  }
  std::set<std::string> labels, seenPorts;
  for (const auto &binding : descriptor.publicBindings) {
    Binding b;
    b.label = binding.name;
    if (b.label.empty() || b.label.size() > 128 ||
        !labels.insert(b.label).second || binding.ports.empty())
      return fail("construction-public-binding");
    for (const auto &[role, name] : binding.ports) {
      bool found = false;
      for (const auto &port : ports) {
        if (port.name != name || i.roles.at(port.role) != role)
          continue;
        if (!serializable(port.type) ||
            (!b.type.empty() && b.type != port.type) ||
            !seenPorts.insert(port.name).second)
          return fail("construction-public-binding");
        b.type = port.type;
        b.ports.push_back(port.name);
        publicPorts[port.name] = b.label;
        if (role == producer && b.producerPort.empty())
          b.producerPort = port.name;
        found = true;
      }
      if (!found)
        return fail("construction-public-port");
    }
    bindings.push_back(std::move(b));
  }
  const std::string &n = descriptor.acceptance;
  uint64_t index = 0;
  if (n.empty() || (n.size() > 1 && n.front() == '0') ||
      !all_of(n, [](char c) { return c >= '0' && c <= '9'; }) ||
      StringRef(n).getAsInteger(10, index))
    return fail("construction-acceptance-index");
  unsigned k = 0;
  bool found = false;
  for (const auto &result : i.def->results)
    if (i.roles.at(result.role) == validator)
      if (k++ == index)
        found = result.type == "bool";
  return found || fail("construction-acceptance-index");
}

void Construction::reserve(const source::Module &module) {
  auto names = [&](const source::Names &values) {
    used.insert(values.begin(), values.end());
  };
  auto pairs = [&](const source::Assignments &values) {
    for (const auto &[key, value] : values) {
      used.insert(key);
      used.insert(value);
    }
  };
  auto body = [&](const source::Body &body) {
    source::walk(body, [&](const source::Instruction &ins) {
      used.insert(ins.site);
      std::visit(
          [&](const auto &op) {
            using T = std::decay_t<decltype(op)>;
            if constexpr (std::is_same_v<T, source::Operation>) {
              used.insert(op.callee);
              names(op.staticArguments);
              names(op.attributes);
              names(op.inputs);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::LocalCall>) {
              used.insert(op.role);
              used.insert(op.callee);
              names(op.inputs);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::ProtocolCall>) {
              used.insert(op.callee);
              names(op.inputs);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::Message>) {
              used.insert(op.schema);
              used.insert(op.sender);
              used.insert(op.receiver);
              used.insert(op.input);
              used.insert(op.output);
            } else if constexpr (std::is_same_v<T, source::Send>) {
              used.insert(op.schema);
              used.insert(op.peer);
              used.insert(op.input);
            } else if constexpr (std::is_same_v<T, source::Receive>) {
              used.insert(op.schema);
              used.insert(op.peer);
              used.insert(op.output);
              used.insert(op.type);
            } else if constexpr (std::is_same_v<T, source::Return> ||
                                 std::is_same_v<T, source::Yield>) {
              names(op.values);
            } else if constexpr (std::is_same_v<T, source::Stop>) {
              used.insert(op.role);
              used.insert(op.reason);
            } else if constexpr (std::is_same_v<T, source::Conditional>) {
              used.insert(op.condition);
              names(op.captures);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::For>) {
              used.insert(op.induction);
              used.insert(op.lower);
              used.insert(op.upper);
              pairs(op.carried);
              names(op.captures);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::AlgorithmCall>) {
              used.insert(op.callee);
              names(op.staticArguments);
              names(op.inputs);
              names(op.outputs);
            } else if constexpr (std::is_same_v<T, source::Loop>) {
              used.insert(op.count.value);
              pairs(op.carried);
              names(op.captures);
              names(op.outputs);
            }
          },
          ins.value);
    });
  };
  for (const auto &binding : module.bindings) {
    used.insert(binding.name);
    used.insert(binding.contract);
    names(binding.arguments);
    used.insert(binding.implementation);
  }
  for (const auto &fn : module.functions) {
    used.insert(fn.name);
    for (const auto &arg : fn.arguments) {
      used.insert(arg.name);
      used.insert(arg.type);
    }
    names(fn.results);
    if (fn.body)
      body(*fn.body);
    if (fn.origin) {
      used.insert(fn.origin->definition);
      pairs(fn.origin->arguments);
    }
  }
  for (const auto &protocol : module.protocols) {
    used.insert(protocol.name);
    names(protocol.roles);
    names(protocol.parameters);
    for (const auto &arg : protocol.arguments) {
      used.insert(arg.name);
      used.insert(arg.role);
      used.insert(arg.type);
    }
    for (const auto &result : protocol.results) {
      used.insert(result.role);
      used.insert(result.type);
    }
    for (const auto &dep : protocol.dependencies) {
      used.insert(dep.name);
      used.insert(dep.protocol);
      pairs(dep.agreements);
    }
    if (protocol.body)
      body(*protocol.body);
  }
  for (const auto &instance : module.instances) {
    used.insert(instance.name);
    used.insert(instance.protocol);
    for (const auto &[key, binding] : instance.parameters) {
      used.insert(key);
      if (const auto *constant = std::get_if<std::string>(&binding))
        used.insert(*constant);
      else {
        const auto &ingress = std::get<source::FamilyIngress>(binding);
        used.insert(ingress.bound);
        for (const auto &selector : ingress.selectors) {
          used.insert(selector.role);
          used.insert(selector.function);
          names(selector.arguments);
        }
      }
    }
    pairs(instance.dependencies);
    pairs(instance.roles);
  }
  for (const auto &entry : module.entries) {
    used.insert(entry.name);
    used.insert(entry.instance);
  }
  for (const auto &definition : module.definitions) {
    used.insert(definition.name);
    for (const auto &parameter : definition.parameters) {
      used.insert(parameter.name);
      used.insert(parameter.sort);
    }
    for (const auto &requirement : definition.requirements) {
      used.insert(requirement.predicate);
      names(requirement.arguments);
    }
    for (const auto &arg : definition.arguments) {
      used.insert(arg.name);
      used.insert(arg.type);
    }
    names(definition.results);
    body(definition.body);
  }
  for (const auto &configuration : module.configurations) {
    used.insert(configuration.name);
    used.insert(configuration.base);
    pairs(configuration.arguments);
    pairs(configuration.implementations);
  }
}

Expected<ConstructionResult> Construction::run() {
  for (const auto &instance : source.instances)
    for (const auto &[name, binding] : instance.parameters)
      if (std::holds_alternative<source::FamilyIngress>(binding))
        return error("construction-family-input-required");
  if (auto e = admit(source, true))
    return e;
  if (source.isLibrary())
    return error("construction-common-source");
  for (const auto &binding : source.bindings) {
    auto selected = binding;
    outBindings.push_back(selected);
    operations.emplace(binding.name, std::move(selected));
  }
  // Dynamic provider/resource paths have no unconditional construction
  // manifest. Preserve only complete local bodies over non-affine ports and
  // primitives.
  for (const auto &fn : source.functions) {
    if (!hasLocalControl(fn))
      continue;
    for (const auto &selector : descriptor.draws)
      if (selector.first == fn.name)
        return error("construction-local-control-draw");
    bool safe = true;
    for (const auto &arg : fn.arguments)
      safe &= duplicable(arg.type);
    for (const auto &type : fn.results)
      safe &= duplicable(type);
    source::walk(*fn.body, [&](const source::Instruction &i) {
      if (const auto *op = i.get<source::Operation>()) {
        const auto *sig = signature(op->callee);
        if (!sig) {
          safe = false;
          return;
        }
        for (const auto &type : sig->inputs)
          safe &= duplicable(type);
        for (const auto &type : sig->outputs)
          safe &= duplicable(type);
      }
    });
    if (!problem.empty())
      return error(problem);
    if (!safe)
      return error("construction-local-control-resource");
  }
  // Check the actual admitted source IR before analysis. Encoding here only
  // measures the established portable source byte limit.
  if (printJson(source::encode(source)).size() > 1024 * 1024)
    return error("construction-byte-limit");
  auto original = importModule(source, ctx);
  if (!original)
    return original.takeError();
  for (const auto &fn : source.functions)
    functions[fn.name] = &fn;
  for (const auto &protocol : source.protocols)
    definitions[protocol.name] = &protocol;
  // Include SSA names, unused declarations and open library selections so a
  // generated name cannot shadow a name from either source snapshot.
  reserve(source);
  reserve(sourceIdentity);
  // Canonical binary-tree source identity, including unused declarations,
  // selected instances, parameters and all entries. Generated names are never
  // transcript origins; this prefix only makes the prescribed checker bind
  // the exact source instead of accidentally accepting an unchanged
  // projection.
  SHA256 hash;
  size_t treeNodes = 0, treeBytes = 0;
  std::function<void(const json::Value &)> hashTree =
      [&](const json::Value &v) {
        auto str = v.getAsString();
        uint64_t length = str ? str->size() : v.getAsArray()->size();
        size_t bytes = 9 + (str ? str->size() : 0);
        if (++treeNodes > 200000 || bytes > 16 * 1024 * 1024 ||
            treeBytes > 16 * 1024 * 1024 - bytes) {
          fail("construction-canonical-tree-limit");
          return;
        }
        treeBytes += bytes;
        uint8_t header[9];
        header[0] = str ? 0 : 1;
        for (unsigned k = 0; k < 8; ++k)
          header[k + 1] = uint8_t(length >> (8 * k));
        hash.update(ArrayRef<uint8_t>(header));
        if (str)
          hash.update(*str);
        else
          for (const auto &child : *v.getAsArray()) {
            if (!problem.empty())
              return;
            hashTree(child);
          }
      };
  hashTree(source::encode(sourceIdentity));
  if (!problem.empty())
    return error(problem);
  sourcePrefix = toHex(hash.final(), true) + "_";
  for (const auto &record : source.instances) {
    Instance i;
    i.record = &record;
    i.def = definitions.at(record.protocol);
    i.roles = pairsOf(record.roles);
    for (const auto &[name, binding] : record.parameters) {
      const auto *value = std::get_if<std::string>(&binding);
      if (!value)
        return error("construction-family-input-required");
      i.parameters.emplace(name, *value);
    }
    i.dependencies = pairsOf(record.dependencies);
    i.generated = fresh();
    instances[record.name] = std::move(i);
  }
  if (!descriptorAdmission())
    return error(problem);
  // Close per-instance output demand across all actual call contexts. A
  // shared child is specialized once, so a result demanded by one caller also
  // imposes its input recipe on other callers. Every such requirement is
  // substituted back to the real root before admission succeeds.
  ValueDependencies demand;
  for (;;) {
    for (auto &[id, inst] : instances) {
      inst.analyzed = false;
      inst.summary = {};
    }
    analyze(root);
    if (!problem.empty())
      return error(problem);
    demand = instances.at(root).summary.roots;
    for (auto &out : instances.at(root).summary.outputs)
      if (out.role == producer)
        demand.join(out.dep);
    if (!demand.blockers.empty())
      return error(*demand.blockers.begin());
    const auto &ports = instances.at(root).def->arguments;
    for (const auto &[sampler, origins] : demand.unconvertedSamplers)
      for (unsigned k : origins)
        if (ports[k].name == selectedRng)
          return error("construction-selected-rng-sampler:" + sampler);
    for (unsigned k : demand.values) {
      const auto &p = ports[k];
      if (instances.at(root).roles.at(p.role) != producer &&
          !publicPorts.count(p.name))
        return error("construction-private-demand:" + p.name);
    }
    for (unsigned k : demand.draws)
      if (ports[k].name != selectedRng)
        return error("construction-private-rng:" + ports[k].name);
    size_t old = demanded.size();
    demanded.insert(demand.tokens.begin(), demand.tokens.end());
    if (old == demanded.size())
      break;
  }
  const auto &resourceOutputs = resourceInstance(root);
  if (!problem.empty())
    return error(problem);
  const auto &rootDef = *instances.at(root).def;
  for (size_t k = 0; k < resourceOutputs.size(); ++k) {
    if (typeKind(rootDef.results[k].type) == "rng" && resourceOutputs[k] &&
        rootDef.arguments[*resourceOutputs[k]].name == selectedRng)
      inertEntryResults.insert(k);
  }
  // Original definitions are retained solely for unreachable zero-loop calls.
  // They are ordinary inspectable source, with no executable entry of their
  // own.
  outFunctions = source.functions;
  outProtocols = source.protocols;
  emitInstance(root);
  if (!problem.empty())
    return error(problem);
  source::Module common;
  common.location = source.location;
  common.bindings = source.bindings;
  common.bindings.insert(common.bindings.end(),
                         outBindings.begin() + source.bindings.size(),
                         outBindings.end());
  common.functions = std::move(outFunctions);
  common.protocols = std::move(outProtocols);
  common.instances = std::move(outInstances);
  source::Entry outputEntry;
  for (const auto &e : source.entries)
    if (e.name == entry)
      outputEntry = e;
  outputEntry.name = entry;
  outputEntry.instance = root;
  common.entries.push_back(std::move(outputEntry));
  const source::Node *failedRecord = nullptr;
  if (auto e = admit(common, true, &failedRecord)) {
    std::string context = "module";
    auto record = [&](const source::Node &node, const std::string &name) {
      if (&node == failedRecord && !name.empty())
        context = name;
    };
    auto body = [&](const source::Body &body) {
      source::walk(
          body, [&](const source::Instruction &ins) { record(ins, ins.site); });
    };
    for (const auto &binding : common.bindings)
      record(binding, binding.name);
    for (const auto &fn : common.functions) {
      record(fn, fn.name);
      if (fn.body)
        body(*fn.body);
    }
    for (const auto &protocol : common.protocols) {
      record(protocol, protocol.name);
      for (const auto &dep : protocol.dependencies)
        record(dep, dep.name);
      if (protocol.body)
        body(*protocol.body);
    }
    for (const auto &instance : common.instances)
      record(instance, instance.name);
    for (const auto &entry : common.entries)
      record(entry, entry.name);
    return error("construction-output:" + toString(std::move(e)) + ":" +
                 context);
  }

  auto constructed = importModule(common, ctx);
  if (!constructed)
    return constructed.takeError();
  json::Value result =
      json::Array{"zkc.construction-result/1", source::encode(descriptor),
                  source::encode(common),      std::move(inputMap),
                  std::move(origins),          std::move(resultMap)};
  if (printJson(result).size() > 1024 * 1024)
    return error("construction-byte-limit");
  return ConstructionResult{std::move(*constructed), std::move(result)};
}

} // namespace zkc::protocol::construction

namespace zkc::protocol {
using construction::Construction;
namespace {
Expected<ConstructionResult> constructAlgorithms(
    const source::Module &prepared, const source::Module &original,
    const source::Construction &descriptor, mlir::MLIRContext &ctx) {
  if (descriptor.draws.size() > 32768)
    return error("construction-descriptor-limit");
  bool calls = false;
  for (const auto &fn : prepared.functions)
    if (fn.body)
      source::walk(*fn.body, [&](const source::Instruction &ins) {
        calls |= ins.get<source::AlgorithmCall>() != nullptr;
      });
  // A selector (definition, site) selects every expanded copy of that
  // definition's primitive, and a function's own name its direct site
  // (docs/spec/profiles/compiler/local-algorithms.md). A materialized
  // top-level configuration is such a copy: its origin is the definition.
  // Concrete names and logical origins may overlap in valid source; closed
  // selectors take their union. Normalized resolution checks that numbering
  // preserves each selected alias's occurrence membership before this step.
  using Selector = std::pair<std::string, std::string>;
  std::map<Selector, std::vector<Selector>> occurrences;
  std::optional<ExpandedAlgorithms> expanded;
  if (calls) {
    auto result = expandAlgorithms(prepared, ctx);
    if (!result)
      return result.takeError();
    expanded = std::move(*result);
    if (expanded->origins.size() > 1000000)
      return error("construction-analysis-limit");
    for (const auto &origin : expanded->origins)
      occurrences[{origin.definition, origin.originalSite}].emplace_back(
          origin.function, origin.site);
  } else {
    // Expansion keeps every site of a call-free module: record its
    // occurrences as expansion does, without re-serializing the module.
    size_t work = 0;
    for (const auto &fn : prepared.functions)
      if (fn.body)
        source::walk(*fn.body, [&](const source::Instruction &ins) {
          if (ins.get<source::Return>() || ins.get<source::Yield>() ||
              ++work > 1000000)
            return;
          occurrences[{fn.name, ins.site}].emplace_back(fn.name, ins.site);
          if (fn.origin && fn.origin->definition != fn.name)
            occurrences[{fn.origin->definition, ins.site}].emplace_back(
                fn.name, ins.site);
        });
    if (work > 1000000)
      return error("construction-analysis-limit");
  }
  // The descriptor selects the union of its selectors' occurrence sets, and
  // naming one selector twice is malformed
  // (docs/spec/profiles/compiler/local-algorithms.md).
  auto selected = descriptor;
  selected.draws.clear();
  std::set<Selector> selectors, chosen;
  for (const auto &selector : descriptor.draws) {
    if (!selectors.insert(selector).second)
      return error("construction-draw-selector");
    auto found = occurrences.find(selector);
    if (calls && found == occurrences.end())
      return error("construction-draw-selector");
    // A call-free module keeps its sites, so construction refuses a selector
    // without an occurrence where it checks every selector.
    const std::vector<Selector> direct{selector};
    for (const auto &copy :
         found == occurrences.end() ? direct : found->second) {
      if (!chosen.insert(copy).second)
        continue;
      if (selected.draws.size() == 32768)
        return error("construction-descriptor-limit");
      selected.draws.push_back(copy);
    }
  }
  auto result = Construction(expanded ? expanded->source : prepared, original,
                             selected, ctx)
                    .run();
  if (!result)
    return result.takeError();
  // The certificate keeps the caller's selectors, which may be longer than
  // the occurrences they select.
  (*result->certificate.getAsArray())[1] = source::encode(descriptor);
  if (printJson(result->certificate).size() > 1024 * 1024)
    return error("construction-byte-limit");
  return result;
}
} // namespace
Expected<ConstructionResult> construct(const source::Module &module,
                                       const source::Construction &descriptor,
                                       mlir::MLIRContext &ctx) {
  // Programmatic records establish structure only. Validate both original
  // snapshots before resolution, preparation, or analysis can dereference them.
  if (auto e = source::checkStructure(module))
    return e;
  if (auto e = source::checkStructure(descriptor))
    return e;
  if (descriptor.identity == source::Construction::Identity::Normalized) {
    auto resolved = source::resolveProtocolSites(module);
    if (!resolved)
      return resolved.takeError();
    auto selected = resolved->descriptor(descriptor);
    if (!selected)
      return selected.takeError();
    Expected<source::Module> prepared = std::move(resolved->source);
    if (prepared->isLibrary())
      prepared = generic::prepareLibrary(*prepared);
    if (!prepared)
      return prepared.takeError();
    auto result = constructAlgorithms(*prepared, module, *selected, ctx);
    if (!result)
      return result.takeError();
    // The certificate retains the caller's original descriptor. Only the
    // executable copy uses derived occurrence coordinates.
    (*result->certificate.getAsArray())[1] = source::encode(descriptor);
    if (printJson(result->certificate).size() > 1024 * 1024)
      return error("construction-byte-limit");
    return result;
  }
  if (module.isLibrary()) {
    auto prepared = generic::prepareLibrary(module);
    if (!prepared)
      return prepared.takeError();
    return constructAlgorithms(*prepared, module, descriptor, ctx);
  }
  return constructAlgorithms(module, module, descriptor, ctx);
}
Error checkConstruction(const source::Module &source,
                        const source::Construction &descriptor,
                        const json::Value &candidate, mlir::MLIRContext &ctx) {
  auto expected = construct(source, descriptor, ctx);
  if (!expected)
    return expected.takeError();
  if (expected->certificate != candidate)
    return error("construction-candidate-mismatch");
  return Error::success();
}
} // namespace zkc::protocol

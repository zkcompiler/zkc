#include "Library.h"
#include "zkc/Protocol/Bindings.h"
#include "zkc/Protocol/Variant.h"
#include "zkc/Source/Codec.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::frontend::library {
namespace {
Error fail(StringRef detail) { return zkc::error("library-lowering", detail); }

class Lowerer {
  ArrayRef<LinkedProgram> programs;
  OriginResolver resolveOrigin;
  const Environment *environment = nullptr;
  source::Module result;
  std::map<std::string, std::string> resourceSlots;
  std::map<std::pair<std::string, source::Names>, std::string> bindings;
  std::map<std::string, std::string> originDeclarations;

  Expected<std::string> domain(const StaticTerm &term) const {
    if (!environment)
      return fail("linked program has no captured domain environment");
    return resolvedDomain(term, *environment);
  }

  Expected<std::string> type(const LayoutLeaf &leaf) const {
    if (leaf.kind == LayoutLeaf::Kind::Variant) {
      auto nominal = parseJson(leaf.variantIdentity);
      if (!nominal)
        return nominal.takeError();
      protocol::VariantDescriptor descriptor{std::move(*nominal), {}};
      for (size_t i = 0; i < leaf.alternatives.size(); ++i) {
        protocol::VariantAlternative alternative;
        alternative.label = leaf.type.fields[i];
        for (const auto &payload : leaf.alternatives[i]) {
          auto spelling = type(payload);
          if (!spelling)
            return spelling.takeError();
          alternative.payload.push_back(*spelling);
        }
        descriptor.alternatives.push_back(std::move(alternative));
      }
      auto encoded = protocol::encodeVariant(descriptor);
      if (!encoded)
        return fail("variant descriptor exceeds carrier limits or has an "
                    "invalid logical payload");
      return *encoded;
    }
    if (leaf.kind == LayoutLeaf::Kind::ResourceUnit) {
      auto found = resourceSlots.find(leaf.resourceIdentity);
      if (found == resourceSlots.end() || leaf.permissions.copy)
        return fail("missing or duplicable resource-unit slot");
      return "resource_unit:" + found->second;
    }
    if (leaf.type.kind != Type::Kind::Logical || leaf.type.arguments.size() > 1)
      return fail("a layout leaf is not a closed installed logical type");
    std::string spelling = leaf.type.name;
    if (!leaf.type.arguments.empty()) {
      auto actual = domain(leaf.type.arguments.front());
      if (!actual)
        return actual.takeError();
      spelling += ":" + *actual;
    }
    auto checked = protocol::parseBoundType(spelling, false);
    if (!checked)
      return checked.takeError();
    return spelling;
  }

  Expected<std::string> binding(StringRef operation, source::Names actuals) {
    auto key = std::make_pair(operation.str(), actuals);
    if (auto found = bindings.find(key); found != bindings.end())
      return found->second;
    source::OperationBinding out;
    out.name = "__library_operation_" + std::to_string(bindings.size());
    out.contract = operation.str();
    out.arguments = std::move(actuals);
    if (auto e = protocol::checkBindingDeclaration(out, false))
      return std::move(e);
    auto name = out.name;
    result.bindings.push_back(std::move(out));
    bindings.emplace(std::move(key), name);
    return name;
  }

  struct ValueLeaves {
    const Layout *layout;
    source::Names names;
  };
  using Values = std::map<uint32_t, ValueLeaves>;

  Expected<source::Names> project(const Place &place, const Values &values) {
    auto found = values.find(place.value.index);
    if (found == values.end())
      return fail("unavailable typed value");
    const auto &value = found->second;
    if (value.names.size() != value.layout->leaves.size())
      return fail("value layout does not match emitted names");
    source::Names names;
    for (size_t i = 0; i < value.names.size(); ++i) {
      const auto &path = value.layout->leaves[i].path;
      if (place.path.size() <= path.size() &&
          std::equal(place.path.begin(), place.path.end(), path.begin()))
        names.push_back(value.names[i]);
    }
    return names;
  }

  Expected<source::Names> operands(ArrayRef<Place> places,
                                   const Values &values) {
    source::Names result;
    for (const auto &place : places) {
      auto leaves = project(place, values);
      if (!leaves)
        return leaves.takeError();
      result.insert(result.end(), leaves->begin(), leaves->end());
    }
    return result;
  }

  // Every carrier block needs a terminator. A region that ends in an
  // exhaustive match of terminal arms has already stopped on every path, so
  // its own terminator is unreachable: emit a halt, never a return or yield,
  // which would name a value that no execution can produce.
  static void halt(source::Body &block, std::string site) {
    if (!block.empty() && block.back().isTerminator())
      return;
    source::Instruction unreachable;
    unreachable.site = std::move(site);
    unreachable.value = source::Stop{"", "abort"};
    block.push_back(std::move(unreachable));
  }

  Expected<source::Function> function(const LinkedFunction &linked) {
    // This carrier is a role-free local algorithm. Fixed roles need a located
    // function carrier; assigning it to an arbitrary caller would erase a
    // checked obligation rather than implement participant projection.
    auto located = [](const Port &port) { return !port.role.empty(); };
    if (any_of(linked.body.signature.inputs, located) ||
        any_of(linked.body.signature.outputs, located))
      return fail("fixed-role ports need a located function carrier");
    for (const auto &instruction : linked.body.instructions) {
      bool hasRole = std::visit(
          [&](const auto &node) {
            using T = std::decay_t<decltype(node)>;
            if constexpr (std::is_same_v<T, Call>)
              return !node.role.empty() ||
                     any_of(node.outputs,
                            [&](const auto &v) { return located(v.port); });
            else if constexpr (std::is_same_v<T, Construct> ||
                               std::is_same_v<T, Project> ||
                               std::is_same_v<T, VariantConstruct>)
              return located(node.output.port);
            else
              return false;
          },
          instruction);
      if (hasRole)
        return fail("fixed-role body needs a located function carrier");
    }
    source::Function out;
    out.name = linked.symbol;
    std::string definition;
    for (const auto &scope : linked.body.id.module)
      definition += scope + ".";
    definition += linked.body.id.name;
    if (resolveOrigin)
      definition = resolveOrigin(linked.body.id);
    auto [origin, fresh] =
        originDeclarations.emplace(definition, identity(linked.body.id));
    if (!fresh && origin->second != identity(linked.body.id))
      return zkc::error("library-origin-ambiguity",
                        "distinct declarations share " + definition);
    out.origin = source::LogicalOrigin{std::move(definition), {}};
    out.body.emplace();
    source::Body *body = &*out.body;
    Values values;
    std::map<std::string, std::string> resourceNames;
    std::set<std::string> consumedUnits;
    auto bind = [&](const Value &value,
                    std::optional<source::Names> aliases = {})
        -> Expected<source::Names> {
      auto layout = linked.values.find(value.id.index);
      if (layout == linked.values.end())
        return fail("typed value has no linked representation");
      source::Names names;
      if (aliases) {
        names = std::move(*aliases);
        if (names.size() != layout->second.leaves.size())
          return fail("aggregate projection changed representation arity");
      } else {
        for (size_t i = 0; i < layout->second.leaves.size(); ++i) {
          auto name =
              "v" + std::to_string(value.id.index) + "_" + std::to_string(i);
          while (llvm::is_contained(linked.body.signature.inputLabels, name))
            name += "_";
          names.push_back(std::move(name));
        }
      }
      if (!values.emplace(value.id.index, ValueLeaves{&layout->second, names})
               .second)
        return fail("duplicate typed value definition");
      for (size_t i = 0; i < names.size(); ++i)
        if (layout->second.leaves[i].kind == LayoutLeaf::Kind::ResourceUnit) {
          const auto &slot =
              resourceSlots.at(layout->second.leaves[i].resourceIdentity);
          auto [entry, added] = resourceNames.emplace(names[i], slot);
          if (!added && entry->second != slot)
            return fail("one value aliases two nominal resource slots");
        }
      return names;
    };
    size_t nextDiscard = 0;
    auto consume = [&](const std::string &name) -> Error {
      auto resource = resourceNames.find(name);
      if (resource == resourceNames.end())
        return Error::success();
      if (!consumedUnits.insert(name).second)
        return fail("logical resource is consumed twice");
      auto operation = binding("resource_unit.consume", {resource->second});
      if (!operation)
        return operation.takeError();
      source::Instruction discard;
      discard.site = "discard_" + std::to_string(nextDiscard++);
      discard.value = source::Operation{*operation, {}, {}, {name}, {}};
      body->push_back(std::move(discard));
      return Error::success();
    };
    for (size_t port = 0; port < linked.body.inputs.size(); ++port) {
      const auto &input = linked.body.inputs[port];
      std::optional<source::Names> publicName;
      const auto &inputLayout = linked.values.at(input.id.index);
      if (!linked.body.signature.inputLabels.empty()) {
        publicName.emplace();
        for (const auto &leaf : inputLayout.leaves) {
          auto name = linked.body.signature.inputLabels[port];
          for (auto index : leaf.path)
            name += "." + std::to_string(index);
          publicName->push_back(std::move(name));
        }
      }
      auto names = bind(input, std::move(publicName));
      if (!names)
        return names.takeError();
      const auto &layout = *values.at(input.id.index).layout;
      for (size_t i = 0; i < names->size(); ++i) {
        auto spelling = type(layout.leaves[i]);
        if (!spelling)
          return spelling.takeError();
        out.arguments.push_back({(*names)[i], *spelling});
      }
    }
    std::function<Error(const std::vector<Instruction> &, std::vector<size_t>)>
        emit;
    emit = [&](const std::vector<Instruction> &instructions,
               std::vector<size_t> prefix) -> Error {
      for (size_t index = 0; index < instructions.size(); ++index) {
        const auto &instruction = instructions[index];
        auto path = prefix;
        path.push_back(index);
        std::string site;
        for (size_t part : path)
          site += "_" + std::to_string(part);
        if (const auto *call = std::get_if<Call>(&instruction)) {
          auto target = linked.calls.find(path);
          if (target == linked.calls.end())
            return fail("unresolved typed call");
          auto inputs = operands(call->inputs, values);
          if (!inputs)
            return inputs.takeError();
          for (const auto &input : *inputs)
            if (resourceNames.count(input) &&
                !consumedUnits.insert(input).second)
              return fail("logical resource is consumed twice");
          source::Names outputs;
          for (const auto &output : call->outputs) {
            auto names = bind(output);
            if (!names)
              return names.takeError();
            outputs.insert(outputs.end(), names->begin(), names->end());
          }
          source::Instruction emitted;
          emitted.site = "call" + site;
          if (target->second.logical) {
            const auto *logical = std::get_if<LogicalCall>(&call->target);
            if (!logical)
              return fail("linked logical target disagrees with typed call");
            source::Names actuals;
            for (const auto &argument : logical->arguments) {
              auto actual = domain(argument);
              if (!actual)
                return actual.takeError();
              actuals.push_back(*actual);
            }
            auto name = binding(target->second.target, std::move(actuals));
            if (!name)
              return name.takeError();
            emitted.value = source::Operation{
                *name, {}, call->attributes, std::move(*inputs), outputs};
          } else {
            emitted.value = source::AlgorithmCall{target->second.target,
                                                  std::move(*inputs), outputs};
          }
          // In particular, retain a guard whose result layout has zero leaves.
          body->push_back(std::move(emitted));
        } else if (const auto *construct =
                       std::get_if<Construct>(&instruction)) {
          auto inputs = operands(construct->elements, values);
          if (!inputs)
            return inputs.takeError();
          const auto layout = linked.values.find(construct->output.id.index);
          if (layout == linked.values.end())
            return fail("constructed value has no linked representation");
          if (inputs->empty() && !layout->second.leaves.empty() &&
              all_of(layout->second.leaves, [](const auto &leaf) {
                return leaf.kind == LayoutLeaf::Kind::ResourceUnit;
              })) {
            // A private unit constructor creates a logical permission token.
            // This asserts no cryptographic fact; preceding guards remain
            // calls.
            auto names = bind(construct->output);
            if (!names)
              return names.takeError();
            for (size_t i = 0; i < names->size(); ++i) {
              auto slot =
                  resourceSlots.at(layout->second.leaves[i].resourceIdentity);
              auto operation = binding("resource_unit.create", {slot});
              if (!operation)
                return operation.takeError();
              source::Instruction create;
              create.site = "unit" + site + "_" + std::to_string(i);
              create.value =
                  source::Operation{*operation, {}, {}, {}, {(*names)[i]}};
              body->push_back(std::move(create));
            }
            continue;
          }
          auto names = bind(construct->output, std::move(*inputs));
          if (!names)
            return names.takeError();
        } else if (const auto *projection =
                       std::get_if<Project>(&instruction)) {
          auto selected = project(projection->input, values);
          if (!selected)
            return selected.takeError();
          auto names = bind(projection->output, std::move(*selected));
          if (!names)
            return names.takeError();
        } else if (const auto *drop = std::get_if<Drop>(&instruction)) {
          auto selected = project(drop->input, values);
          if (!selected)
            return selected.takeError();
          for (const auto &name : *selected)
            if (auto error = consume(name))
              return error;
        } else if (const auto *c =
                       std::get_if<VariantConstruct>(&instruction)) {
          auto payload = project(c->payload, values);
          if (!payload)
            return payload.takeError();
          auto names = bind(c->output);
          if (!names)
            return names.takeError();
          const auto &layout = linked.values.at(c->output.id.index);
          if (names->size() != 1 || layout.leaves.size() != 1)
            return fail("variant constructor has no single logical carrier");
          auto spelling = type(layout.leaves.front());
          if (!spelling)
            return spelling.takeError();
          for (const auto &name : *payload)
            if (resourceNames.count(name) && !consumedUnits.insert(name).second)
              return fail("variant payload consumes a resource twice");
          source::Instruction pack;
          pack.site = "variant" + site;
          pack.value = source::VariantConstruct{
              *spelling, c->alternative, std::move(*payload), names->front()};
          body->push_back(std::move(pack));
        } else if (const auto *m = branches(instruction)) {
          bool conditional = std::holds_alternative<Conditional>(instruction);
          if (!m->role.empty())
            return fail("fixed-role match needs a located function carrier");
          auto input = project(m->input, values);
          if (!input)
            return input.takeError();
          if (input->size() != 1)
            return fail("match requires one logical variant");
          auto captures = operands(m->captures, values);
          if (!captures)
            return captures.takeError();
          std::vector<source::Names> captureGroups;
          for (const auto &p : m->captures) {
            auto names = project(p, values);
            if (!names)
              return names.takeError();
            captureGroups.push_back(std::move(*names));
          }
          for (const auto &name : *captures)
            if (resourceNames.count(name) && !consumedUnits.insert(name).second)
              return fail("match capture consumes a resource twice");
          source::Match matched;
          matched.input = input->front();
          // Products and projections alias their flattened carrier names. A
          // copyable leaf may occur in several checked source captures, but
          // the carrier region imports each name only once. Keep captureGroups
          // unchanged so every arm parameter still aliases the proper leaves.
          // Source/link ownership and the unit-use check above precede this
          // deduplication; it must never authorize a second affine use.
          std::set<std::string> capturedNames;
          for (const auto &name : *captures)
            if (capturedNames.insert(name).second)
              matched.captures.push_back(name);
          for (const auto &v : m->outputs) {
            auto names = bind(v);
            if (!names)
              return names.takeError();
            matched.outputs.insert(matched.outputs.end(), names->begin(),
                                   names->end());
          }
          const auto savedValues = values;
          const auto savedResources = resourceNames;
          const auto savedConsumed = consumedUnits;
          auto *savedBody = body;
          // Emit in declaration order even when builders list arms differently.
          const auto &variant = linked.values.at(m->input.value.index);
          const LayoutLeaf *schema = nullptr;
          for (const auto &leaf : variant.leaves)
            if (leaf.path == m->input.path)
              schema = &leaf;
          if (!conditional &&
              (!schema || schema->kind != LayoutLeaf::Kind::Variant))
            return fail("match input has no variant schema");
          for (const auto &label :
               conditional ? std::vector<std::string>{"then", "else"}
                           : schema->type.fields) {
            auto arm = std::find_if(
                m->arms.begin(), m->arms.end(),
                [&](const auto &a) { return a.alternative == label; });
            if (arm == m->arms.end())
              return fail("match arm missing after checking");
            values.clear();
            resourceNames.clear();
            consumedUnits.clear();
            source::MatchArm emittedArm;
            emittedArm.alternative = label;
            body = &emittedArm.body;
            if (!conditional) {
              auto payload = bind(arm->body->inputs.front());
              if (!payload)
                return payload.takeError();
              emittedArm.payload = *payload;
            }
            for (size_t i = 0; i < captureGroups.size(); ++i) {
              auto names = bind(arm->body->inputs[i + (conditional ? 0 : 1)],
                                captureGroups[i]);
              if (!names)
                return names.takeError();
            }
            auto nested = path;
            nested.push_back(arm - m->arms.begin());
            if (auto error = emit(arm->body->instructions, nested))
              return error;
            // A terminal arm yields nothing and releases nothing: cleanup after
            // a stop belongs to the runtime, and a fabricated discard here
            // would claim work that never happens. Its block still needs a
            // terminator when its own final join, not an explicit stop, ended
            // it.
            if (terminal(arm->body->instructions))
              halt(*body,
                   "halt" + site + "_" + std::to_string(arm - m->arms.begin()));
            else {
              auto yields = operands(arm->body->returns, values);
              if (!yields)
                return yields.takeError();
              for (const auto &[name, slot] : resourceNames)
                if (!consumedUnits.count(name) && !is_contained(*yields, name))
                  if (auto error = consume(name))
                    return error;
              source::Instruction yield;
              yield.value = source::Yield{std::move(*yields)};
              body->push_back(std::move(yield));
            }
            matched.arms.push_back(std::move(emittedArm));
          }
          values = savedValues;
          resourceNames = savedResources;
          consumedUnits = savedConsumed;
          body = savedBody;
          source::Instruction match;
          match.site = (conditional ? "if" : "match") + site;
          if (conditional)
            match.value = source::Conditional{
                matched.input, std::move(matched.captures),
                std::move(matched.arms[0].body),
                std::move(matched.arms[1].body), std::move(matched.outputs)};
          else
            match.value = std::move(matched);
          body->push_back(std::move(match));
        } else if (const auto *stop = std::get_if<Stop>(&instruction)) {
          // The terminal stop of the common model, with no participant: a
          // checked library body is a role-free local algorithm.
          source::Instruction emitted;
          emitted.site = "stop" + site;
          emitted.value = source::Stop{"", stop->reason};
          body->push_back(std::move(emitted));
        } else {
          return fail("unexpanded typed traversal");
        }
      }
      return Error::success();
    };
    if (auto error = emit(linked.body.instructions, {}))
      return std::move(error);
    // A body that cannot continue keeps its promised result signature. It never
    // returns, so no Return is invented for it and no value is named for a
    // caller that can never observe one.
    if (terminal(linked.body.instructions)) {
      halt(*out.body, "halt");
      for (const auto &declared : linked.results)
        for (const auto &leaf : declared.leaves) {
          auto spelling = type(leaf);
          if (!spelling)
            return spelling.takeError();
          out.results.push_back(*spelling);
        }
      return out;
    }
    auto returns = operands(linked.body.returns, values);
    if (!returns)
      return returns.takeError();
    for (const auto &[name, slot] : resourceNames)
      if (!consumedUnits.count(name) && !is_contained(*returns, name))
        if (auto error = consume(name))
          return std::move(error);
    for (const auto &place : linked.body.returns) {
      const auto &layout = *values.at(place.value.index).layout;
      for (const auto &leaf : layout.leaves) {
        if (place.path.size() > leaf.path.size() ||
            !std::equal(place.path.begin(), place.path.end(),
                        leaf.path.begin()))
          continue;
        auto spelling = type(leaf);
        if (!spelling)
          return spelling.takeError();
        out.results.push_back(*spelling);
      }
    }
    source::Instruction ret;
    ret.value = source::Return{std::move(*returns)};
    body->push_back(std::move(ret));
    return out;
  }

public:
  explicit Lowerer(ArrayRef<LinkedProgram> programs, OriginResolver origin = {})
      : programs(programs), resolveOrigin(std::move(origin)) {}
  Expected<source::Module> run() {
    std::set<std::string> slots;
    std::map<std::string, const DependencyRecord *> world;
    std::map<std::string, std::pair<std::string, std::string>> captures;
    for (const auto &program : programs) {
      for (const auto &dependency : program.dependencies()) {
        const std::string path =
            dependency.paths.empty() ? "<entry>" : dependency.paths.front();
        auto [capture, fresh] =
            captures.emplace(dependency.normalizedSelection,
                             std::make_pair(dependency.captureIdentity, path));
        if (!fresh && capture->second.first != dependency.captureIdentity)
          return zkc::error("library-selection-capture",
                            "conflicting captures through " +
                                capture->second.second + " and " + path);
        auto [found, added] = world.emplace(dependency.selection, &dependency);
        if (!added && found->second->implementationIdentity !=
                          dependency.implementationIdentity)
          return fail("incoherent implementations across linked clients");
      }
      std::function<Error(const std::vector<LayoutLeaf> &)> collect =
          [&](const auto &leaves) -> Error {
        for (const auto &leaf : leaves) {
          if (leaf.kind == LayoutLeaf::Kind::ResourceUnit) {
            if (leaf.resourceIdentity.empty())
              return fail("resource unit has no nominal identity");
            slots.insert(leaf.resourceIdentity);
          }
          for (const auto &alternative : leaf.alternatives)
            if (auto error = collect(alternative))
              return error;
        }
        return Error::success();
      };
      for (const auto &function : program.functions()) {
        for (const auto &[id, layout] : function.values)
          if (auto error = collect(layout.leaves))
            return std::move(error);
        // A body that always stops holds no value of its promised results, and
        // its declared boundary still needs their slots.
        for (const auto &declared : function.results)
          if (auto error = collect(declared.leaves))
            return std::move(error);
      }
    }
    // The table is closed over this linked program. Exact keys decide sharing;
    // no collision-prone digest or unchecked source spelling decides equality.
    for (const auto &slot : slots)
      resourceSlots.emplace(slot, "library_slot_" +
                                      std::to_string(resourceSlots.size()));
    std::map<std::string, json::Value> emittedFunctions;
    std::map<std::string, std::string> exactSymbols;
    for (const auto &program : programs) {
      environment = &program.environment();
      for (const auto &linked : program.functions()) {
        auto [symbol, fresh] =
            exactSymbols.emplace(linked.symbol, linked.exactSubject);
        // Linking sets every exact subject, and unequal subjects under one
        // symbol would be a SHA-256 collision.
        if (linked.exactSubject.empty() ||
            (!fresh && symbol->second != linked.exactSubject))
          report_fatal_error("unequal exact linked subjects share a symbol");
        auto emitted = function(linked);
        if (!emitted)
          return emitted.takeError();
        source::Module snapshot;
        snapshot.functions.push_back(*emitted);
        if (auto error = source::checkStructure(snapshot))
          return std::move(error);
        auto bytes = source::encode(snapshot);
        auto found = emittedFunctions.find(emitted->name);
        if (found != emittedFunctions.end()) {
          if (found->second != bytes)
            return fail("conflicting linked function symbols");
        } else {
          emittedFunctions.emplace(emitted->name, std::move(bytes));
          result.functions.push_back(std::move(*emitted));
        }
      }
    }
    return std::move(result);
  }
};
} // namespace
Expected<source::Module> lower(const LinkedProgram &program) {
  return Lowerer(program).run();
}
Expected<source::Module> lower(ArrayRef<LinkedProgram> programs) {
  return Lowerer(programs).run();
}
Expected<source::Module> lower(ArrayRef<LinkedProgram> programs,
                               OriginResolver origin) {
  return Lowerer(programs, std::move(origin)).run();
}
} // namespace zkc::frontend::library

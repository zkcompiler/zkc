#include "LanguageInterface.h"
#include "zkc/Analysis/CommonControl.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Refusal.h"
#include <algorithm>
#include <map>
#include <numeric>
#include <set>
#include <tuple>

using namespace llvm;
namespace zkc::language::detail {
namespace {
constexpr unsigned MaxGroups = 1024, MaxComponents = 32768, MaxPath = 32;
using Observation = std::pair<unsigned, unsigned>;
Observation observation(const CommonControlRequirement &r) {
  return {r.extentAxis ? 2 : r.tagOnly ? 1 : 0, r.extentAxis.value_or(0)};
}
Observation observation(const InterfaceCommonRequirement &r) {
  const auto *extent = std::get_if<InterfaceCommonExtent>(&r.observation);
  return {unsigned(r.observation.index()), extent ? extent->axis : 0};
}
InterfaceCommonObservation observed(Observation o) {
  if (o.first == 2)
    return InterfaceCommonExtent{o.second};
  if (o.first == 1)
    return InterfaceCommonTag{};
  return InterfaceCommonValue{};
}
Error invalid(StringRef message) { return error("source.interface", message); }
Error capacity() {
  return error("source.limit", "common inventory limit exceeded");
}
bool charge(uint64_t &remaining, uint64_t amount) {
  if (amount > remaining)
    return false;
  remaining -= amount;
  return true;
}
struct SourceLess {
  bool operator()(const CommonControlComponent &a,
                  const CommonControlComponent &b) const {
    if (a.input != b.input)
      return a.input < b.input;
    auto stepLess = [](const CommonControlStep &a, const CommonControlStep &b) {
      return std::tie(a.kind, a.index) < std::tie(b.kind, b.index);
    };
    if (a.path != b.path)
      return std::lexicographical_compare(
          a.path.begin(), a.path.end(), b.path.begin(), b.path.end(), stepLess);
    return a.role < b.role;
  }
};
struct NativeComponent {
  unsigned input, role;
  std::vector<unsigned> path;
  bool operator<(const NativeComponent &b) const {
    return std::tie(input, path, role) < std::tie(b.input, b.path, b.role);
  }
  bool operator==(const NativeComponent &b) const {
    return input == b.input && role == b.role && path == b.path;
  }
};
template <typename C> struct Class {
  std::vector<C> components;
  std::string type;
  Observation observation;
};
template <typename C, typename Less>
bool classLess(const Class<C> &a, const Class<C> &b, Less less) {
  if (a.components != b.components)
    return std::lexicographical_compare(
        a.components.begin(), a.components.end(), b.components.begin(),
        b.components.end(), less);
  return a.observation < b.observation;
}
// A complete connected class is invariant under edge direction and spanning
// tree choice. Indexing is bounded before any comparison or sorting occurs.
template <typename C, typename Less>
Expected<std::vector<Class<C>>> normalize(std::vector<Class<C>> edges,
                                          uint64_t &remaining, Less less) {
  uint64_t count = 0;
  for (const auto &edge : edges) {
    count += edge.components.size();
    if (count > MaxComponents ||
        !charge(remaining, (edge.type.size() + 1) * 16))
      return capacity();
    for (const auto &c : edge.components)
      if (c.path.size() > MaxPath)
        return capacity();
  }
  // Conservative bound for balanced-map and sort comparisons of bounded paths.
  if (!charge(remaining, (count + edges.size() + 1) * (MaxPath + 1) * 16))
    return capacity();
  using Key = std::pair<std::string, Observation>;
  std::map<Key, std::vector<const Class<C> *>> groups;
  for (const auto &edge : edges)
    groups[{edge.type, edge.observation}].push_back(&edge);
  std::vector<Class<C>> result;
  for (const auto &[key, group] : groups) {
    std::map<C, unsigned, Less> indices(less);
    std::vector<unsigned> parents;
    auto root = [&](unsigned i) {
      while (parents[i] != i) {
        parents[i] = parents[parents[i]];
        i = parents[i];
      }
      return i;
    };
    for (const auto *edge : group) {
      std::optional<unsigned> first;
      for (const auto &c : edge->components) {
        auto [it, inserted] = indices.try_emplace(c, parents.size());
        if (inserted)
          parents.push_back(parents.size());
        auto at = root(it->second);
        if (first)
          parents[at] = root(*first);
        else
          first = at;
      }
    }
    std::map<unsigned, std::vector<C>> classes;
    for (const auto &[c, index] : indices)
      classes[root(index)].push_back(c);
    for (auto &[_, components] : classes) {
      std::set<unsigned> roles;
      for (const auto &c : components)
        roles.insert(c.role);
      if (roles.size() < 2)
        return invalid("common class needs at least two distinct roles");
      result.push_back({std::move(components), key.first, key.second});
      if (result.size() > MaxGroups)
        return capacity();
    }
  }
  std::sort(result.begin(), result.end(), [&](const auto &a, const auto &b) {
    return classLess(a, b, less);
  });
  return result;
}
using ComponentKey = std::tuple<unsigned, std::vector<unsigned>, unsigned>;
struct Mapping {
  std::map<ComponentKey, const InterfaceComponent *> components;
  Error index(const InterfaceProtocol &p, uint64_t &remaining) {
    if (!charge(remaining, p.inputs.size() + 1))
      return capacity();
    for (unsigned i = 0; i < p.inputs.size(); ++i)
      for (const auto &c : p.inputs[i].components) {
        if (!charge(remaining, (c.path.size() + 1) * 16))
          return capacity();
        if (c.facet == InterfaceComponentFacet::Data && c.leaf == 0 &&
            !components.emplace(ComponentKey{i, c.path, c.role}, &c).second)
          return invalid("ambiguous ordinary common component");
      }
    return Error::success();
  }
  struct Resolved {
    const InterfaceSchema *schema;
    NativeComponent native;
  };
  Expected<Resolved> resolve(const InterfaceProtocol &p,
                             const CommonControlComponent &c,
                             uint64_t &remaining, const Limits &limits) const {
    if (c.path.size() > MaxPath || c.path.size() > limits.typeDepth ||
        !charge(remaining, (c.path.size() + 1) * 16))
      return capacity();
    if (c.input >= p.inputs.size() || c.role >= p.roles.size() ||
        !p.inputs[c.input].schema)
      return invalid("common input or role is outside its Protocol");
    auto *schema = p.inputs[c.input].schema.get();
    std::vector<unsigned> fields, path;
    for (unsigned i = 0; i < c.path.size(); ++i) {
      if (schema->oracle)
        return invalid("common path traverses a handle");
      const auto &step = c.path[i];
      if (step.kind == CommonControlStep::Kind::Field) {
        if (schema->kind == Type::Kind::Variant ||
            schema->kind == Type::Kind::Associated ||
            step.index >= schema->fields.size())
          return invalid("common field differs from its declared schema");
        const auto &field = schema->fields[step.index];
        if (path.empty())
          fields.push_back(step.index);
        else {
          if (uint64_t(path.back()) + field.offset > UINT32_MAX)
            return capacity();
          path.back() += field.offset;
        }
        schema = field.schema.get();
      } else if (step.kind == CommonControlStep::Kind::Alternative) {
        if (schema->kind != Type::Kind::Variant || schema->leaves.size() != 1 ||
            step.index >= schema->alternatives.size() ||
            i + 1 >= c.path.size() ||
            c.path[i + 1].kind != CommonControlStep::Kind::Payload)
          return invalid("common alternative must select its exact payload");
        const auto &payloads = schema->alternatives[step.index].fields;
        unsigned payload = c.path[++i].index;
        if (payload >= payloads.size())
          return invalid("common payload is outside its alternative");
        path.push_back(step.index);
        path.push_back(payloads[payload].offset);
        schema = payloads[payload].schema.get();
      } else
        return invalid("common payload has no preceding alternative");
      if (!schema)
        return invalid("common path has no schema");
    }
    if (schema->custody || !schema->fields.empty() ||
        schema->leaves.size() != 1 || logicalSchema(*schema))
      return invalid("common path must resolve to one ordinary component");
    auto found = components.find({c.input, fields, c.role});
    if (found == components.end())
      return invalid("common component is absent at its named role");
    return Resolved{schema, {found->second->native, c.role, std::move(path)}};
  }
};
Error checkObservation(const InterfaceSchema &schema,
                       const InterfaceCommonRequirement &r,
                       uint64_t &remaining) {
  if (!charge(remaining, schema.leaves.front().size() + 1))
    return capacity();
  if (std::holds_alternative<InterfaceCommonTag>(r.observation))
    return schema.kind == Type::Kind::Variant
               ? Error::success()
               : invalid("tag observation requires a variant");
  if (!schema.permissions.copy)
    return invalid("common value or extent requires Copy data");
  if (const auto *extent = std::get_if<InterfaceCommonExtent>(&r.observation)) {
    auto type = protocol::parseBoundType(schema.leaves.front(), false);
    if (!type)
      return type.takeError();
    // The collection rank is the constructor's catalog row.
    const auto *declared = protocol::typeDeclaration(type->kind);
    unsigned rank =
        declared && declared->collection ? declared->collection->rank : 0;
    if (extent->axis >= rank)
      return invalid("common extent axis is outside its collection");
  }
  return Error::success();
}
Expected<std::vector<Class<NativeComponent>>>
mapRequirements(const InterfaceProtocol &p, uint64_t &remaining,
                const Limits &limits) {
  Mapping mapping;
  if (auto e = mapping.index(p, remaining))
    return e;
  if (p.commonInputRequirements.size() > MaxGroups)
    return capacity();
  std::vector<Class<CommonControlComponent>> source;
  std::vector<Class<NativeComponent>> mapped;
  unsigned count = 0;
  for (const auto &r : p.commonInputRequirements) {
    if (r.components.size() > MaxComponents - count)
      return capacity();
    count += r.components.size();
    Class<CommonControlComponent> s{r.components, {}, observation(r)};
    Class<NativeComponent> n{{}, {}, observation(r)};
    std::set<unsigned> roles;
    for (const auto &c : r.components) {
      auto resolved = mapping.resolve(p, c, remaining, limits);
      if (!resolved)
        return resolved.takeError();
      if (auto e = checkObservation(*resolved->schema, r, remaining))
        return e;
      const auto &schema = *resolved->schema;
      if (!s.type.empty() &&
          (s.type != schema.identity || n.type != schema.leaves[0]))
        return invalid("common class contains distinct logical types");
      s.type = schema.identity;
      n.type = schema.leaves[0];
      roles.insert(c.role);
      n.components.push_back(std::move(resolved->native));
    }
    if (roles.size() < 2)
      return invalid("common class needs at least two distinct roles");
    source.push_back(std::move(s));
    mapped.push_back(std::move(n));
  }
  auto canonical = normalize(source, remaining, SourceLess{});
  if (!canonical)
    return canonical.takeError();
  if (canonical->size() != source.size())
    return invalid("common classes are repeated or not maximal");
  for (unsigned i = 0; i < source.size(); ++i)
    if ((*canonical)[i].components != source[i].components ||
        (*canonical)[i].observation != source[i].observation)
      return invalid("common inventory is duplicated or noncanonical");
  // Source identities are checked above. Physical coincidence cannot repair a
  // malformed source inventory: each serialized class remains a distinct class.
  if (!charge(remaining, (count + 1) * (MaxPath + 1) * 16))
    return capacity();
  for (auto &r : mapped) {
    std::sort(r.components.begin(), r.components.end());
    if (std::adjacent_find(r.components.begin(), r.components.end()) !=
        r.components.end())
      return invalid("distinct common coordinates alias one native component");
  }
  std::sort(mapped.begin(), mapped.end(), [](const auto &a, const auto &b) {
    return classLess(a, b, std::less<NativeComponent>{});
  });
  return mapped;
}
} // namespace

Expected<std::vector<InterfaceCommonRequirement>>
sourceCommonRequirements(const ClosedEntry &entry, const Declaration &decl,
                         uint64_t &remaining, const Limits &limits) {
  auto derived =
      deriveCommonControlRequirements(entry, decl.id, limits, remaining);
  if (!derived)
    return derived.takeError();
  if (derived->size() > MaxComponents)
    return capacity();
  Layouts layouts(entry, limits, remaining);
  std::map<const Layout *, std::string> identities;
  std::vector<Class<CommonControlComponent>> edges;
  unsigned count = 0;
  for (const auto &r : *derived) {
    if (r.components.size() > MaxComponents - count)
      return capacity();
    count += r.components.size();
    for (const auto &c : r.components) {
      if (c.path.size() > MaxPath || !charge(remaining, c.path.size() + 1))
        return capacity();
      if (c.input >= decl.inputs.size() || c.role >= decl.roles.size())
        return invalid("derived common coordinate is outside its Protocol");
    }
    if (r.tagOnly && r.extentAxis)
      return invalid("contradictory derived common observation");
    auto layout = layouts.get(r.type);
    if (!layout)
      return layout.takeError();
    auto [identity, inserted] = identities.try_emplace(layout->get());
    if (inserted)
      identity->second = typeIdentity((*layout)->type);
    if (!charge(remaining, identity->second.size() + 1))
      return capacity();
    edges.push_back({r.components, identity->second, observation(r)});
  }
  auto canonical = normalize(std::move(edges), remaining, SourceLess{});
  if (!canonical)
    return canonical.takeError();
  std::vector<InterfaceCommonRequirement> result;
  for (auto &r : *canonical)
    result.push_back({std::move(r.components), observed(r.observation)});
  return result;
}
json::Value encodeCommonRequirements(ArrayRef<InterfaceCommonRequirement> rs,
                                     ArrayRef<std::string> roles) {
  json::Array result;
  for (const auto &r : rs) {
    json::Array components;
    for (const auto &c : r.components) {
      json::Array path;
      for (const auto &step : c.path)
        path.push_back(json::Object{
            {"kind", step.kind == CommonControlStep::Kind::Field ? "field"
                     : step.kind == CommonControlStep::Kind::Alternative
                         ? "alternative"
                         : "payload"},
            {"index", step.index}});
      components.push_back(json::Object{{"input", c.input},
                                        {"role", roles[c.role]},
                                        {"path", std::move(path)}});
    }
    auto o = observation(r);
    json::Object obs{{"kind", o.first == 2   ? "extent"
                              : o.first == 1 ? "tag"
                                             : "value"}};
    if (o.first == 2)
      obs["axis"] = o.second;
    result.push_back(json::Object{{"components", std::move(components)},
                                  {"observation", std::move(obs)}});
  }
  return result;
}
Expected<std::vector<InterfaceCommonRequirement>>
decodeCommonRequirements(const json::Value &value, const InterfaceProtocol &p,
                         uint64_t &remaining, const Limits &limits) {
  const auto *groups = value.getAsArray();
  if (!groups)
    return invalid("common inventory must be an array");
  if (groups->size() > MaxGroups || !charge(remaining, groups->size() + 1))
    return capacity();
  std::map<std::string, unsigned> roles;
  for (unsigned i = 0; i < p.roles.size(); ++i)
    roles.emplace(p.roles[i], i);
  auto exact = [](const json::Object *o,
                  std::initializer_list<StringRef> keys) {
    return o && o->size() == keys.size() &&
           all_of(keys, [&](auto key) { return o->get(key); });
  };
  auto natural = [](const json::Object &o,
                    StringRef key) -> std::optional<unsigned> {
    auto v = o.getInteger(key);
    if (!v || *v < 0 || uint64_t(*v) > UINT32_MAX)
      return {};
    return unsigned(*v);
  };
  std::vector<InterfaceCommonRequirement> result;
  unsigned count = 0;
  for (const auto &group : *groups) {
    auto *o = group.getAsObject();
    if (!exact(o, {"components", "observation"}))
      return invalid("common requirement members differ");
    auto *cs = o->getArray("components");
    auto *obs = o->getObject("observation");
    if (!cs || !obs)
      return invalid("common requirement shape differs");
    if (cs->size() > MaxComponents - count ||
        !charge(remaining, cs->size() + 1))
      return capacity();
    count += cs->size();
    auto kind = obs->getString("kind");
    InterfaceCommonRequirement r;
    if (kind == "value" || kind == "tag") {
      if (!exact(obs, {"kind"}))
        return invalid("common observation members differ");
      r.observation = kind == "tag"
                          ? InterfaceCommonObservation(InterfaceCommonTag{})
                          : InterfaceCommonObservation(InterfaceCommonValue{});
    } else if (kind == "extent") {
      if (!exact(obs, {"kind", "axis"}) || !natural(*obs, "axis"))
        return invalid("common extent requires a bounded axis");
      r.observation = InterfaceCommonExtent{*natural(*obs, "axis")};
    } else
      return invalid("unknown common observation");
    for (const auto &component : *cs) {
      auto *c = component.getAsObject();
      if (!exact(c, {"input", "role", "path"}))
        return invalid("common component members differ");
      auto input = natural(*c, "input");
      auto role = c->getString("role");
      auto *path = c->getArray("path");
      if (!input || !role || !path)
        return invalid("invalid common component coordinate");
      if (path->size() > MaxPath || path->size() > limits.typeDepth ||
          role->size() > limits.identifierBytes ||
          !charge(remaining, path->size() + role->size() + 1))
        return capacity();
      if (!roles.count(role->str()))
        return invalid("unknown common component role");
      CommonControlComponent parsed{*input, roles.at(role->str()), {}};
      for (const auto &step : *path) {
        auto *s = step.getAsObject();
        if (!exact(s, {"kind", "index"}) || !natural(*s, "index"))
          return invalid("invalid common path step");
        auto k = s->getString("kind");
        CommonControlStep::Kind kind;
        if (k == "field")
          kind = CommonControlStep::Kind::Field;
        else if (k == "alternative")
          kind = CommonControlStep::Kind::Alternative;
        else if (k == "payload")
          kind = CommonControlStep::Kind::Payload;
        else
          return invalid("unknown common path step");
        parsed.path.push_back({kind, *natural(*s, "index")});
      }
      r.components.push_back(std::move(parsed));
    }
    result.push_back(std::move(r));
  }
  return result;
}
bool sameCommonRequirements(ArrayRef<InterfaceCommonRequirement> a,
                            ArrayRef<InterfaceCommonRequirement> b) {
  if (a.size() != b.size())
    return false;
  for (unsigned i = 0; i < a.size(); ++i)
    if (a[i].components != b[i].components ||
        observation(a[i]) != observation(b[i]))
      return false;
  return true;
}
Error checkNativeCommonRequirements(mlir::Operation *operation,
                                    const InterfaceProtocol &p,
                                    uint64_t &remaining, const Limits &limits) {
  auto mapped = mapRequirements(p, remaining, limits);
  if (!mapped)
    return mapped.takeError();
  facts::Work work(remaining);
  auto native = zkc::deriveCommonControlRequirements(
      mlir::cast<protocol_ir::MathematicalOp>(operation), work);
  if (!native) {
    if (work.exhausted()) {
      consumeError(native.takeError());
      return capacity();
    }
    return native.takeError();
  }
  if (native->size() > MaxComponents || !charge(remaining, p.roles.size() * 16))
    return capacity();
  std::map<std::string, unsigned> roles;
  for (unsigned i = 0; i < p.roles.size(); ++i)
    roles.emplace(nativeRoleName(i), i);
  std::vector<Class<NativeComponent>> edges;
  std::map<const void *, std::string> types;
  unsigned count = 0;
  for (const auto &r : *native) {
    if (r.components.size() > MaxComponents - count ||
        !charge(remaining, r.components.size() + 1))
      return capacity();
    count += r.components.size();
    auto [type, inserted] = types.try_emplace(r.type.getAsOpaquePointer());
    if (inserted) {
      auto encoded = protocol::encodeBoundType(r.type, false);
      if (!encoded)
        return encoded.takeError();
      type->second = encoded->spelling();
    }
    if (!charge(remaining, type->second.size() + 1))
      return capacity();
    Class<NativeComponent> edge{{},
                                type->second,
                                {r.extentAxis ? 2u
                                 : r.tagOnly  ? 1u
                                              : 0u,
                                 r.extentAxis.value_or(0)}};
    for (const auto &c : r.components) {
      if (c.path.size() > MaxPath || !charge(remaining, c.path.size() + 16))
        return capacity();
      auto role = roles.find(c.role.getValue().str());
      if (role == roles.end())
        return invalid("native common role is outside its Protocol");
      edge.components.push_back(
          {c.input, role->second,
           std::vector<unsigned>(c.path.begin(), c.path.end())});
    }
    edges.push_back(std::move(edge));
  }
  auto canonical =
      normalize(std::move(edges), remaining, std::less<NativeComponent>{});
  if (!canonical)
    return canonical.takeError();
  if (canonical->size() != mapped->size())
    return error("source.interface",
                 Twine("common inventory differs for ") + p.symbol +
                     ": original classes=" + Twine(canonical->size()) +
                     ", interface classes=" + Twine(mapped->size()));
  for (unsigned i = 0; i < canonical->size(); ++i)
    if ((*canonical)[i].components != (*mapped)[i].components ||
        (*canonical)[i].type != (*mapped)[i].type ||
        (*canonical)[i].observation != (*mapped)[i].observation)
      return error("source.interface", Twine("common inventory differs for ") +
                                           p.symbol + " at class " + Twine(i));
  return Error::success();
}
} // namespace zkc::language::detail

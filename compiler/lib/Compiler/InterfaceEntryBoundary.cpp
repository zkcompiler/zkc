#include "LanguageInterface.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/EntryBoundary.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/STLExtras.h"
#include <set>
using namespace llvm;
namespace zkc::language::detail {
namespace {
class Boundary {
  uint64_t &remaining;
  const Limits &limits;

public:
  Error failure = Error::success();
  Boundary(uint64_t &remaining, const Limits &limits)
      : remaining(remaining), limits(limits) {}
  bool fail(StringRef message) {
    if (!failure)
      failure = error("source.interface", message);
    return false;
  }
  bool charge(uint64_t n, unsigned depth = 0) {
    if (failure)
      return false;
    if (n > remaining || depth > limits.typeDepth) {
      failure =
          error("source.limit", "Entry boundary work or depth limit exceeded");
      return false;
    }
    remaining -= n;
    return true;
  }
  const ValuePlacement *child(const InterfaceSchema &schema,
                              const ValuePlacement &p, unsigned i) {
    if (auto *product = std::get_if<ProductPlacement>(&p.value)) {
      unsigned index = schema.kind == Type::Kind::Array ? 0 : i;
      if (index >= product->fields.size()) {
        fail("Entry child placement is absent");
        return nullptr;
      }
      return &product->fields[index];
    }
    return &p;
  }
  std::optional<std::vector<unsigned>> ordinary(const InterfaceSchema &s,
                                                const ValuePlacement &p,
                                                unsigned depth = 0) {
    if (!charge(1, depth) || logicalSchema(s))
      return {};
    if (auto *data = std::get_if<DataPlacement>(&p.value)) {
      if (!charge(data->roles.size()))
        return {};
      return data->roles;
    }
    const auto *product = std::get_if<ProductPlacement>(&p.value);
    if (!product)
      return {};
    std::optional<std::vector<unsigned>> roles;
    for (unsigned i = 0; i < product->fields.size(); ++i) {
      auto schema = s.kind == Type::Kind::Array ? s.element
                    : i < s.fields.size()       ? s.fields[i].schema
                                                : nullptr;
      if (!schema) {
        fail("ordinary product schema differs");
        return {};
      }
      auto next = ordinary(*schema, product->fields[i], depth + 1);
      if (!next)
        return {};
      if (!roles)
        roles = std::move(next);
      else {
        if (!charge(uint64_t(roles->size()) * next->size()))
          return {};
        llvm::erase_if(
            *roles, [&](unsigned role) { return !is_contained(*next, role); });
      }
    }
    return roles;
  }
  bool key(const InterfaceSchema &s) {
    return s.kind == Type::Kind::Builtin && s.leaves.size() == 1 &&
           protocol::setupKey(protocol::typeKind(s.leaves[0])).has_value();
  }
  bool setup(const InterfaceSchema &s, unsigned depth = 0) {
    if (!charge(1, depth))
      return false;
    for (const auto &leaf : s.leaves) {
      if (!charge(leaf.size() + 1))
        return false;
      protocol::TypeParseBudget budget;
      budget.remaining = std::min(budget.remaining, remaining);
      auto before = budget.remaining;
      auto type = protocol::parseBoundType(leaf, false, 0, &budget);
      if (!charge(before - budget.remaining)) {
        if (!type)
          consumeError(type.takeError());
        return false;
      }
      if (!type) {
        consumeError(type.takeError());
        return fail("invalid setup leaf");
      }
      if (protocol::nativeSetupType(*type))
        return true;
    }
    for (const auto &field : s.fields)
      if (setup(*field.schema, depth + 1))
        return true;
    return false;
  }
  bool publicSchema(const InterfaceSchema &s, unsigned depth = 0) {
    if (!charge(1, depth))
      return false;
    if (logicalSchema(s) || s.sealed || s.custody)
      return fail("public selection requires accessible ordinary data");
    if (s.element && !publicSchema(*s.element, depth + 1))
      return false;
    auto fields = [&](ArrayRef<InterfaceField> fields) {
      for (const auto &field : fields)
        if (!field.isPublic || !publicSchema(*field.schema, depth + 1))
          return fail("public selection hides a required field");
      return true;
    };
    if (!fields(s.fields))
      return false;
    for (const auto &alternative : s.alternatives)
      if (!fields(alternative.fields))
        return false;
    return true;
  }
  enum class Supply { TypedValue, ExternalData };
  bool construct(const InterfaceSchema &s, Supply supply, bool keyAllowed,
                 unsigned depth = 0) {
    if (!charge(1, depth))
      return false;
    bool external = supply == Supply::ExternalData;
    if (logicalSchema(s) || s.custody || (external && s.sealed))
      return fail(
          "ordinary selection has unprovided logical or assembly authority");
    if (external && !s.constructible && !(keyAllowed && key(s)))
      return fail("ordinary selection lacks construction authority");
    if (!s.permissions.copy || !s.permissions.drop)
      return fail("ordinary Entry selection requires Copy and Drop data");
    if (s.element && !construct(*s.element, supply, false, depth + 1))
      return false;
    for (const auto &field : s.fields) {
      if (external && !field.isPublic)
        return fail("ordinary selection hides a private field");
      if (!construct(*field.schema, supply, false, depth + 1))
        return false;
    }
    for (const auto &alternative : s.alternatives)
      for (const auto &field : alternative.fields)
        if (!construct(*field.schema, supply, false, depth + 1))
          return false;
    return true;
  }
  bool templateAuthority(const InterfaceSchema &s, unsigned depth = 0) {
    if (!charge(1, depth))
      return false;
    if (s.sealed || s.custody)
      return fail("zero-array element requires assembly authority");
    if (!logicalSchema(s) &&
        !construct(s, Supply::ExternalData, false, depth + 1))
      return false;
    if (s.element && !templateAuthority(*s.element, depth + 1))
      return false;
    for (const auto &field : s.fields)
      if (!field.isPublic || !templateAuthority(*field.schema, depth + 1))
        return fail("zero-array element hides a required field");
    return true;
  }
  bool atoms(const InterfaceSchema &s, const ValuePlacement &p,
             EntryInputSelection &coordinate,
             std::set<EntryInputSelection> &out, unsigned depth = 0) {
    if (!charge(coordinate.path.size() + 1, depth))
      return false;
    if (s.oracle)
      return true;
    if (s.fields.empty()) {
      auto roles = ordinary(s, p, depth);
      if (roles && is_contained(*roles, coordinate.role))
        out.insert(coordinate);
      return !failure;
    }
    for (unsigned i = 0; i < s.fields.size(); ++i) {
      auto *where = child(s, p, i);
      if (!where)
        return false;
      coordinate.path.push_back(i);
      if (!atoms(*s.fields[i].schema, *where, coordinate, out, depth + 1))
        return false;
      coordinate.path.pop_back();
    }
    return true;
  }
  bool native(const InterfacePort &port, InterfaceEntryField &field) {
    for (const auto &component : port.components) {
      if (!charge(component.path.size() + 1))
        return false;
      if (component.role != field.selection.role ||
          !entryPathContains(field.selection.port, field.selection.path,
                             field.selection.port, component.path))
        continue;
      if (component.facet != InterfaceComponentFacet::Data)
        return fail("ordinary selection contains an authority component");
      field.native.push_back(component.native);
    }
    llvm::sort(field.native);
    field.native.erase(std::unique(field.native.begin(), field.native.end()),
                       field.native.end());
    return field.native.size() == field.schema->leaves.size() ||
           fail("ordinary selection does not cover every native leaf at its "
                "role");
  }
  bool select(const InterfacePort &port, const EntryInputSelection &coordinate,
              InterfaceEntryField &result, bool publicSelection) {
    if (!port.schema || !port.placement)
      return fail("Entry port schema or placement is absent");
    result.selection = coordinate;
    result.schema = port.schema;
    result.name = port.name;
    const auto *where = &*port.placement;
    for (auto step : coordinate.path) {
      if (!charge(1) || step >= result.schema->fields.size())
        return fail("ordinary selection path is absent");
      const auto &schema = *result.schema;
      // Splitting an ancestor needs its constructor; a logical record is
      // never constructed whole.
      if (schema.custody || schema.sealed ||
          (!logicalSchema(schema) && !schema.constructible) ||
          schema.kind == Type::Kind::Associated ||
          schema.kind == Type::Kind::Variant || !schema.fields[step].isPublic)
        return fail(
            "ordinary selection crosses an assembly or privacy barrier");
      where = child(schema, *where, step);
      if (!where)
        return false;
      result.name += "_" + schema.fields[step].name;
      result.schema = schema.fields[step].schema;
    }
    auto roles = ordinary(*result.schema, *where);
    if (!roles || !is_contained(*roles, coordinate.role))
      return fail("ordinary selection is unavailable at its role");
    return (!publicSelection || publicSchema(*result.schema)) &&
           native(port, result);
  }
};
} // namespace
Expected<std::vector<unsigned>> interfacePublicNative(
    const InterfaceProtocol &protocol, ArrayRef<EntryInputSelection> selections,
    unsigned verifier, uint64_t &remaining, const Limits &limits) {
  Boundary work(remaining, limits);
  std::set<EntryInputSelection> required, covered;
  for (unsigned i = 0; i < protocol.inputs.size(); ++i) {
    const auto &port = protocol.inputs[i];
    EntryInputSelection coordinate{i, {}, verifier, {}};
    if (!port.schema || !port.placement ||
        !work.atoms(*port.schema, *port.placement, coordinate, required)) {
      if (!work.failure)
        work.fail("Entry public schema or placement is absent");
      return std::move(work.failure);
    }
  }
  std::vector<unsigned> native;
  const EntryInputSelection *previous = nullptr;
  for (const auto &selection : selections) {
    if (!work.charge(selection.path.size() + 1))
      return std::move(work.failure);
    if (selection.role != verifier ||
        selection.port >= protocol.inputs.size() ||
        (previous && (!(*previous < selection) ||
                      entryPathContains(previous->port, previous->path,
                                        selection.port, selection.path)))) {
      work.fail("public selections are unordered, overlapping or at the wrong "
                "participant");
      return std::move(work.failure);
    }
    previous = &selection;
    InterfaceEntryField field;
    if (!work.select(protocol.inputs[selection.port], selection, field, true))
      return std::move(work.failure);
    bool nonempty = false;
    for (const auto &atom : required) {
      if (!work.charge(atom.path.size() + 1))
        return std::move(work.failure);
      if (entryPathContains(selection.port, selection.path, atom.port,
                            atom.path)) {
        nonempty = true;
        if (!covered.insert(atom).second) {
          work.fail("public selections overlap semantically");
          return std::move(work.failure);
        }
      }
    }
    if (!nonempty) {
      work.fail("public selection has no ordinary coverage");
      return std::move(work.failure);
    }
    llvm::append_range(native, field.native);
  }
  if (required != covered) {
    work.fail("public selections do not cover verifier ordinary fields");
    return std::move(work.failure);
  }
  llvm::sort(native);
  native.erase(std::unique(native.begin(), native.end()), native.end());
  return native;
}
Expected<std::vector<InterfaceEntryField>>
interfaceEntryFields(const LanguageInterface &view, bool inputs,
                     std::optional<unsigned> role, bool publicOnly,
                     bool witness, uint64_t &remaining, const Limits &limits) {
  Boundary work(remaining, limits);
  const auto &protocol = view.selectedProtocol();
  const auto &ports = inputs ? protocol.inputs : protocol.outputs;
  std::vector<InterfaceEntryField> result;
  for (unsigned ordinal = 0; ordinal < ports.size(); ++ordinal) {
    const auto &port = ports[ordinal];
    if (!port.schema || !port.placement)
      return error("source.interface", "Entry schema or placement is absent");
    for (unsigned participant = 0; participant < protocol.roles.size();
         ++participant) {
      if (role && participant != *role)
        continue;
      EntryInputSelection coordinate{ordinal, {}, participant, {}};
      std::function<bool(std::shared_ptr<const InterfaceSchema>,
                         const ValuePlacement &, std::string, unsigned)>
          walk;
      walk = [&](std::shared_ptr<const InterfaceSchema> s,
                 const ValuePlacement &p, std::string name, unsigned depth) {
        if (!work.charge(name.size() + coordinate.path.size() + 1, depth))
          return false;
        if (!is_contained(placementRoles(p), participant))
          return true;
        auto roles = work.ordinary(*s, p, depth);
        bool ordinary = roles && is_contained(*roles, participant);
        bool splitPublic = false, isPublic = false, associated = false;
        if (inputs && view.proof)
          for (const auto &selection : view.proof->publicInputs) {
            if (!work.charge(selection.path.size() + 1))
              return false;
            isPublic |= entryPathContains(selection.port, selection.path,
                                          ordinal, coordinate.path);
            splitPublic |= coordinate.path.size() < selection.path.size() &&
                           entryPathContains(ordinal, coordinate.path,
                                             selection.port, selection.path);
          }
        if (inputs)
          for (const auto &slot : view.setups)
            for (const auto &selection : slot.inputs) {
              if (!work.charge(selection.path.size() + 1))
                return false;
              associated |= entryPathContains(selection.port, selection.path,
                                              ordinal, coordinate.path) ||
                            entryPathContains(ordinal, coordinate.path,
                                              selection.port, selection.path);
            }
        bool setup = associated && work.setup(*s);
        if (work.failure)
          return false;
        bool splitSetup = setup && !s->fields.empty();
        if (ordinary && !splitPublic && !splitSetup) {
          // Generated signatures transport whole typed ordinary values. Only
          // setup context is externally reconstructed; splitting ancestors
          // below still requires assembly authority.
          if (inputs && !setup &&
              ((publicOnly && (!isPublic || !view.proof ||
                               participant != view.proof->verifier)) ||
               (witness && isPublic)))
            return true;
          if (!work.construct(*s,
                              setup ? Boundary::Supply::ExternalData
                                    : Boundary::Supply::TypedValue,
                              setup && work.key(*s), depth + 1))
            return false;
          if (inputs && setup)
            return true;
          InterfaceEntryField field{coordinate, s, {}, name};
          if (!work.native(port, field))
            return false;
          result.push_back(std::move(field));
          return true;
        }
        if (s->sealed || s->custody || s->oracle)
          return work.fail(
              "generated Entry family has residual assembly authority");
        if (!logicalSchema(*s) && !s->constructible && !s->fields.empty())
          return work.fail("generated Entry family requires an unavailable "
                           "product constructor");
        if (s->kind == Type::Kind::Array && s->fields.empty()) {
          if (!s->element)
            return work.fail("array element template is absent");
          return work.templateAuthority(*s->element, depth + 1);
        }
        for (unsigned i = 0; i < s->fields.size(); ++i) {
          const auto &field = s->fields[i];
          auto *where = work.child(*s, p, i);
          if (!where)
            return false;
          if (!is_contained(placementRoles(*where), participant))
            continue;
          if (!field.isPublic)
            return work.fail("generated Entry family requires a hidden field");
          coordinate.path.push_back(i);
          if (!walk(field.schema, *where, name + "_" + field.name, depth + 1))
            return false;
          coordinate.path.pop_back();
        }
        return true;
      };
      if (!walk(port.schema, *port.placement, port.name, 1))
        return std::move(work.failure);
    }
  }
  llvm::sort(result, [](const auto &a, const auto &b) {
    return a.selection < b.selection;
  });
  std::vector<EntryInputSelection> coordinates;
  std::vector<std::string> names;
  for (const auto &field : result) {
    coordinates.push_back(field.selection);
    names.push_back(field.name);
  }
  auto aliases = entrySelectionAliases(coordinates, names, remaining);
  if (!aliases)
    return aliases.takeError();
  for (unsigned i = 0; i < result.size(); ++i)
    result[i].name = (*aliases)[i];
  return result;
}
} // namespace zkc::language::detail

#include "zkc/Language/EntryBoundary.h"
#include "Semantics.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include <numeric>
#include <set>
using namespace llvm;
namespace zkc::language {
bool entryPathContains(unsigned port, ArrayRef<unsigned> path,
                       unsigned selectedPort, ArrayRef<unsigned> selected) {
  return port == selectedPort && path.size() <= selected.size() &&
         std::equal(path.begin(), path.end(), selected.begin());
}
Expected<std::vector<std::string>>
entrySelectionAliases(ArrayRef<EntryInputSelection> selections,
                      ArrayRef<std::string> candidates, uint64_t &remaining) {
  if (selections.size() != candidates.size())
    return detail::failure("source.entry", "selection alias roster differs");
  std::set<std::string> used;
  std::vector<std::string> result(selections.size());
  auto charge = [&](uint64_t n) -> Error {
    if (n > remaining)
      return detail::failure("source.limit", "selection alias limit exceeded");
    remaining -= n;
    return Error::success();
  };
  auto allocate = [&](unsigned i) -> Error {
    if (auto e = charge(candidates[i].size() + selections[i].path.size() + 1))
      return e;
    auto name = candidates[i];
    if (name.size() > 120) {
      std::string coordinate = std::to_string(selections[i].port);
      for (auto step : selections[i].path)
        detail::frame(coordinate, std::to_string(step));
      unsigned end = 48;
      while (end && (static_cast<unsigned char>(name[end]) & 0xc0) == 0x80)
        --end;
      name = name.substr(0, end) + "_" + detail::digest(coordinate);
    }
    auto candidate = name;
    for (unsigned suffix = 2; !used.insert(candidate).second; ++suffix) {
      if (auto e = charge(name.size() + 1))
        return e;
      candidate = name + "_" + std::to_string(suffix);
    }
    result[i] = std::move(candidate);
    return Error::success();
  };
  for (unsigned i = 0; i < selections.size(); ++i)
    if (selections[i].path.empty())
      if (auto e = allocate(i))
        return std::move(e);
  for (unsigned i = 0; i < selections.size(); ++i)
    if (!selections[i].path.empty())
      if (auto e = allocate(i))
        return std::move(e);
  return result;
}
} // namespace zkc::language
namespace zkc::language::detail {
namespace {
std::optional<std::vector<unsigned>> ordinaryRoles(const Type &type,
                                                   const ValuePlacement &where,
                                                   Semantics &types, Span span,
                                                   unsigned depth = 0) {
  if (depth > types.work.limits.typeDepth) {
    types.fail("source.limit", "ordinary component role depth exceeded", span);
    return {};
  }
  if (!types.charge(1, span) || isLogicalValue(type))
    return {};
  if (const auto *data = std::get_if<DataPlacement>(&where.value)) {
    if (!types.charge(data->roles.size(), span))
      return {};
    return data->roles;
  }
  const auto *product = std::get_if<ProductPlacement>(&where.value);
  if (!product ||
      (type.kind != Type::Kind::Tuple && type.kind != Type::Kind::Array))
    return {};
  std::optional<std::vector<unsigned>> result;
  for (unsigned i = 0; i < product->fields.size(); ++i) {
    if (!types.charge(1, span))
      return {};
    unsigned child = type.kind == Type::Kind::Array ? 0 : i;
    if (child >= type.arguments.size())
      return {};
    auto roles = ordinaryRoles(type.arguments[child], product->fields[i], types,
                               span, depth + 1);
    if (!roles)
      return {};
    if (!result)
      result = std::move(roles);
    else {
      if (!types.charge(uint64_t(result->size()) * roles->size(), span))
        return {};
      llvm::erase_if(*result, [&](unsigned role) {
        return !llvm::is_contained(*roles, role);
      });
    }
  }
  return result;
}
} // namespace
std::optional<std::vector<Semantics::EntryField>>
Semantics::entryFields(const Declaration &protocol, const Declaration *entry,
                       bool inputs, bool atoms) {
  std::vector<EntryField> result;
  auto bindings = entry && entry->kind == Declaration::Kind::Entry
                      ? substitution(protocol, entry->staticArguments)
                      : Substitution{};
  const auto &ports = inputs ? protocol.inputs : protocol.outputs;
  for (unsigned ordinal = 0; ordinal < ports.size(); ++ordinal) {
    const auto &port = ports[ordinal];
    auto type = substitute(port.type, bindings, port.span);
    if (!type)
      return {};
    auto placed = port.placement;
    if (placed) {
      placed = placement(*type, *placed, protocol.roles.size(), port.span);
      if (!placed)
        return {};
    } else
      placed = DataPlacement{port.roles};
    std::vector<unsigned> path;
    std::function<bool(const Type &, const ValuePlacement &, std::string,
                       unsigned, unsigned)>
        visit;
    visit = [&](const Type &current, const ValuePlacement &where,
                std::string name, unsigned depth, unsigned role) {
      if (depth > work.limits.typeDepth ||
          !charge(path.size() + name.size() + 1, port.span))
        return diagnostic ? false
                          : fail("source.limit",
                                 "Entry selection depth exceeded", port.span);
      const auto *data = std::get_if<DataPlacement>(&where.value);
      const auto *product = std::get_if<ProductPlacement>(&where.value);
      if (!llvm::is_contained(placementRoles(where), role) ||
          (!data && !product))
        return true; // Handles require an origin supplier.
      auto available = ordinaryRoles(current, where, *this, port.span);
      if (diagnostic)
        return false;
      bool ordinary = available && llvm::is_contained(*available, role);
      bool split = !ordinary || atoms;
      if (inputs && entry) {
        if (entry->proof())
          for (const auto &selection : entry->proof()->publicInputs) {
            if (!charge(selection.path.size() + 1, port.span))
              return false;
            split |= path.size() < selection.path.size() &&
                     entryPathContains(ordinal, path, selection.port,
                                       selection.path);
          }
        bool associated = false;
        for (const auto &slot : entry->setups)
          for (const auto &selection : slot.inputs) {
            if (!charge(selection.path.size() + 1, port.span))
              return false;
            associated |= entryPathContains(ordinal, path, selection.port,
                                            selection.path) ||
                          entryPathContains(selection.port, selection.path,
                                            ordinal, path);
          }
        if (associated) {
          auto authority = setupAuthority(current, port.span);
          if (!authority)
            return false;
          split |= *authority;
        }
      }
      bool fieldsAvailable =
          current.kind == Type::Kind::Record ||
          current.kind == Type::Kind::LogicalRecord ||
          current.kind == Type::Kind::Tuple ||
          (current.kind == Type::Kind::Array && current.dimension.isClosed());
      const auto *definition = typeDeclaration(current);
      if (product && !atoms && definition &&
          (definition->sealed || definition->resource))
        return true;
      if (split && fieldsAvailable) {
        auto children = fields(current, port.span, depth + 1);
        if (!children)
          return false;
        if (!children->empty()) {
          for (auto [index, field] : enumerate(*children)) {
            if (!atoms && !field.isPublic)
              continue;
            // A field of a distributed record placed only at other roles
            // supplies nothing here; it is visited at each of its own roles.
            if (product && index < product->fields.size() &&
                !llvm::is_contained(placementRoles(product->fields[index]),
                                    role))
              continue;
            auto childPlacement = projectedPlacement(
                current, where, {unsigned(index)}, port.span);
            if (!childPlacement)
              return false;
            path.push_back(index);
            if (!visit(field.type, *childPlacement, name + "_" + field.name,
                       depth + 1, role))
              return false;
            path.pop_back();
          }
          return true;
        }
      }
      // Empty logical products have no ordinary carrier. Their assembly policy
      // is still checked by the closed boundary walk.
      if (!ordinary)
        return true;
      {
        if (!charge(path.size() + name.size() + 1, port.span) ||
            !chargeType(current, port.span))
          return false;
        bool initialized = false;
        if (inputs && entry && current.kind == Type::Kind::Builtin &&
            protocol::setupKey(current.domain) == protocol::SetupKey::Verifier)
          for (const auto &slot : entry->setups)
            for (const auto &selection : slot.inputs) {
              if (!charge(selection.path.size() + 1, port.span))
                return false;
              initialized |= entryPathContains(selection.port, selection.path,
                                               ordinal, path);
            }
        result.push_back(
            {{ordinal, path, role, port.span}, current, name, initialized});
      }
      return true;
    };
    // Only the roles a port is placed at can supply its fields.
    auto placedRoles = placementRoles(*placed);
    llvm::sort(placedRoles);
    placedRoles.erase(std::unique(placedRoles.begin(), placedRoles.end()),
                      placedRoles.end());
    if (!charge(placedRoles.size(), port.span))
      return {};
    for (auto role : placedRoles)
      if (role < protocol.roles.size() &&
          !visit(*type, *placed, port.name, 1, role))
        return {};
  }
  llvm::sort(result, [](const auto &a, const auto &b) {
    return a.selection < b.selection;
  });
  return result;
}
std::optional<std::vector<Semantics::EntryField>>
Semantics::entryFamilyFields(const Declaration &generated,
                             ArrayRef<Type> arguments, Span span) {
  if (!generated.generated ||
      generated.generated->target.index >= declarations.size()) {
    fail("source.host-api", "generated Entry owner is absent", span);
    return {};
  }
  const auto target = generated.generated->target;
  const auto &declared = declarations[target.index];
  bool proof = declared.kind == Declaration::Kind::Entry;
  if (proof &&
      (!declared.target || declared.target->index >= declarations.size())) {
    fail("source.host-api", "generated Entry owner is absent", span);
    return {};
  }
  const auto walked = proof ? *declared.target : target;
  StringRef member = generated.generated->member;
  bool inputs = member.starts_with("Inputs:") || member == "Public" ||
                member == "Witness";
  // One family walk serves every member: the roster depends only on these.
  // The memo belongs to this view, so lookup keys of the substitution suffice.
  std::string key;
  frame(key, std::to_string(target.index));
  frame(key, std::to_string(walked.index));
  frame(key, inputs ? "inputs" : "outputs");
  // Preserve the map's atom order without copying argument Types on a hit.
  std::map<StringRef, const Type *> staticBindings;
  for (unsigned i = 0; i < arguments.size() && i < generated.parameters.size();
       ++i) {
    if (!charge(1, span))
      return {};
    staticBindings.emplace(generated.parameters[i].atom, &arguments[i]);
  }
  for (const auto &[atom, type] : staticBindings) {
    if (!chargeIdentity(*type, span) || !charge(atom.size(), span))
      return {};
    frame(key, atom);
    frameTypeIdentity(key, *type);
  }
  if (!charge(key.size(), span))
    return {};
  auto cached = familyRosters.find(key);
  if (cached == familyRosters.end()) {
    for (const auto &[atom, type] : staticBindings)
      if (!chargeType(*type, span) || !charge(atom.size() + 1, span))
        return {};
    auto bindings = substitution(generated, arguments);
    auto owner = declared;
    auto protocol = declarations[walked.index];
    if (proof) {
      for (auto &argument : owner.staticArguments) {
        auto actual = substitute(argument, bindings, span);
        if (!actual)
          return {};
        argument = std::move(*actual);
      }
    } else {
      for (auto *ports : {&protocol.inputs, &protocol.outputs})
        for (auto &port : *ports) {
          auto actual = substitutePlaced({port.type, port.placement}, bindings,
                                         protocol.roles.size(), span);
          if (!actual)
            return {};
          port.type = std::move(actual->type);
          port.placement = std::move(actual->placement);
        }
    }
    auto fields = entryFields(protocol, proof ? &owner : &protocol, inputs);
    if (!fields)
      return {};
    FamilyRoster roster;
    roster.byRole.resize(protocol.roles.size());
    for (unsigned role = 0; role < protocol.roles.size(); ++role)
      if (!roster.roles.emplace(protocol.roles[role], role).second) {
        fail("source.host-api", "generated participant is repeated", span);
        return {};
      }
    for (auto &field : *fields) {
      bool isPublic =
          proof &&
          llvm::any_of(
              owner.proof()->publicInputs, [&](const EntryInputSelection &p) {
                return entryPathContains(p.port, p.path, field.selection.port,
                                         field.selection.path);
              });
      auto authority = setupAuthority(field.type, span);
      if (!authority)
        return {};
      if (field.selection.role >= roster.byRole.size()) {
        fail("source.host-api", "generated participant is absent", span);
        return {};
      }
      roster.byRole[field.selection.role].push_back(roster.fields.size());
      roster.facts.emplace_back(isPublic, *authority);
      roster.fields.push_back(std::move(field));
    }
    cached = familyRosters.emplace(std::move(key), std::move(roster)).first;
  }
  const auto &roster = cached->second;
  std::optional<unsigned> role;
  if (member.contains(':')) {
    auto found = roster.roles.find(member.split(':').second.str());
    if (found == roster.roles.end()) {
      fail("source.host-api", "generated participant is absent", span);
      return {};
    }
    role = found->second;
  } else if (proof)
    role = member == "Public" || member == "VerifierOutputs"
               ? declared.proof()->verifier
               : declared.proof()->prover;
  std::vector<unsigned> all;
  if (!role) {
    all.resize(roster.fields.size());
    std::iota(all.begin(), all.end(), 0u);
  } else if (*role >= roster.byRole.size()) {
    fail("source.host-api", "generated participant is absent", span);
    return {};
  }
  const auto &selected = role ? roster.byRole[*role] : all;
  if (!charge(selected.size() + 1, span))
    return {};
  std::vector<EntryField> result;
  std::vector<EntryInputSelection> coordinates;
  std::vector<std::string> names;
  for (auto index : selected) {
    const auto &field = roster.fields[index];
    auto [isPublic, authority] = roster.facts[index];
    if (inputs && (field.initialized || (member == "Public" && !isPublic) ||
                   (member == "Witness" && isPublic)))
      continue;
    if (inputs && authority)
      continue;
    coordinates.push_back(field.selection);
    names.push_back(field.name);
    result.push_back(field);
  }
  const auto before = work.remaining();
  auto remaining = before;
  auto aliases = entrySelectionAliases(coordinates, names, remaining);
  const bool charged = charge(before - remaining, span);
  if (!aliases) {
    accept(aliases.takeError(), span);
    return {};
  }
  if (!charged)
    return {};
  for (auto [index, field] : enumerate(result))
    field.name = (*aliases)[index];
  return result;
}
bool Semantics::checkEntryPublic(const Declaration &entry,
                                 const Declaration &protocol) {
  const auto &proof = *entry.proof();
  auto atoms = entryFields(protocol, &entry, true, true);
  if (!atoms)
    return false;
  for (const auto &selection : proof.publicInputs) {
    if (!charge(selection.path.size() + 1, selection.span))
      return false;
    if (selection.role != proof.verifier ||
        selection.port >= protocol.inputs.size())
      return fail("source.entry", "public selection requires the verifier",
                  selection.span);
    const auto &port = protocol.inputs[selection.port];
    auto placed =
        substitutePlaced({port.type, port.placement},
                         substitution(protocol, entry.staticArguments),
                         protocol.roles.size(), selection.span);
    if (!placed)
      return false;
    auto type =
        projectedType(entry, placed->type, selection.path, selection.span);
    if (!type)
      return false;
    auto where = placed->placement
                     ? projectedPlacement(placed->type, *placed->placement,
                                          selection.path, selection.span)
                     : std::optional<ValuePlacement>(DataPlacement{port.roles});
    if (!where)
      return false;
    auto available = ordinaryRoles(*type, *where, *this, selection.span);
    if (diagnostic)
      return false;
    if (!available || !is_contained(*available, proof.verifier))
      return fail("source.entry",
                  "public selection requires ordinary verifier data",
                  selection.span);
    bool found = false;
    for (const auto &atom : *atoms) {
      if (!charge(atom.selection.path.size() + 1, selection.span))
        return false;
      found |= atom.selection.role == proof.verifier &&
               entryPathContains(selection.port, selection.path,
                                 atom.selection.port, atom.selection.path);
    }
    if (!found)
      return fail("source.entry", "public selection has no ordinary coverage",
                  selection.span);
  }
  for (const auto &atom : *atoms) {
    if (atom.selection.role != proof.verifier)
      continue;
    unsigned suppliers = 0;
    for (const auto &selection : proof.publicInputs) {
      if (!charge(selection.path.size() + 1, selection.span))
        return false;
      suppliers += entryPathContains(selection.port, selection.path,
                                     atom.selection.port, atom.selection.path);
    }
    if (suppliers != 1)
      return fail(
          "source.entry",
          "public selections must exactly cover verifier ordinary fields",
          proof.span);
  }
  return true;
}
} // namespace zkc::language::detail

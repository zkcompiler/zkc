#include "Checker.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/Support/JSON.h"
#include <algorithm>
#include <tuple>

using namespace llvm;
namespace zkc::language::detail {
namespace {
using Site = std::tuple<uint32_t, uint32_t, uint32_t>;
Site site(Span span) { return {span.module.index, span.begin, span.end}; }
} // namespace

bool Checker::retainNotations() {
  auto &records = output.notations;
  // Every loop charges before allocating its retained records or lookup tables.
  // Temporary indexes only connect already-checked evidence, never select a
  // callable or recreate the inference candidate search.
  if (!types.charge(syntax.size() + sources.size(), Span{{0}, 0, 0}))
    return false;
  std::vector<uint32_t> moduleScopes(syntax.size());
  std::map<OperatorSite, uint32_t> moduleBindings;
  std::map<Site, uint32_t> bindingSites;
  std::vector<std::map<std::string, uint32_t>> descriptorsByScope;
  auto addScope = [&](NotationScopeRecord scope) {
    auto id = uint32_t(records.scopes.size());
    records.scopes.push_back(std::move(scope));
    descriptorsByScope.emplace_back();
    return id;
  };
  auto addDescriptor = [&](const NotationDescriptor &descriptor, Span span,
                           bool isPublic, bool fixed,
                           bool explicitSyntax) -> std::optional<uint32_t> {
    if (!types.charge(descriptor.symbol.size() + descriptor.closing.size() + 1,
                      span))
      return {};
    auto id = uint32_t(records.descriptors.size());
    records.descriptors.push_back(
        {descriptor, span, isPublic, fixed, explicitSyntax});
    return id;
  };
  auto printType = [&](const Type &type,
                       Span span) -> std::optional<std::string> {
    if (!types.chargeType(type, span))
      return {};
    auto text = formatType(type);
    if (!types.charge(text.size(), span))
      return {};
    return text;
  };
  auto addBinding = [&](const SyntaxOperator &source,
                        const OperatorBinding &binding, uint32_t scope,
                        bool local) -> std::optional<uint32_t> {
    if (!source.notation) {
      types.fail("source.binding-witness", "binding has no descriptor",
                 source.span);
      return {};
    }
    if (!types.charge(binding.arguments.size() +
                          source.target.arguments.size() + source.holes.size() +
                          1,
                      source.span))
      return {};
    auto descriptor =
        addDescriptor(*source.notation, source.span, source.isPublic && !local,
                      false, source.explicitNotation);
    if (!descriptor)
      return {};
    NotationBindingRecord record;
    record.descriptor = *descriptor;
    record.scope = scope;
    record.target = binding.target.declaration;
    record.span = source.span;
    record.targetSpan = source.target.span;
    record.isPublic = source.isPublic && !local;
    record.local = local;
    if (binding.target.component) {
      record.component = printType(*binding.target.component, source.span);
      if (!record.component)
        return {};
    }
    for (const auto &argument : binding.arguments) {
      std::optional<std::string> printed;
      if (argument) {
        printed = printType(*argument, source.span);
        if (!printed)
          return {};
      }
      record.arguments.push_back(std::move(printed));
    }
    for (const auto &argument : source.target.arguments)
      record.authoredArguments.push_back(argument.span);
    for (const auto &hole : source.holes) {
      if (!types.charge(hole.size() + 1, source.span))
        return {};
      record.holes.push_back(hole);
    }
    // The canonical key is retained solely to relate Operation.binding.family
    // evidence to original declarations, including identical reexports.
    if (!types.charge(output.declarations[binding.target.declaration.index]
                              .qualifiedName.size() +
                          1,
                      source.span))
      return {};
    if (binding.target.component &&
        !types.chargeType(*binding.target.component, source.span))
      return {};
    for (const auto &argument : binding.arguments)
      if (argument && !types.chargeType(*argument, source.span))
        return {};
    record.identity = operatorBindingKey(binding, output.declarations);
    if (!types.charge(record.identity.size(), source.span))
      return {};
    auto id = uint32_t(records.bindings.size());
    records.bindings.push_back(std::move(record));
    bindingSites.emplace(site(source.span), id);
    records.scopes[scope].bindings.push_back(id);
    return id;
  };
  for (const auto &module : syntax) {
    Span span{module.id, 0,
              uint32_t((*output.sources)[module.id.index].text.size())};
    if (!types.charge(1, span))
      return false;
    NotationScopeRecord scope;
    scope.span = span;
    moduleScopes[module.id.index] = addScope(std::move(scope));
  }
  for (const auto &module : syntax) {
    auto scope = moduleScopes[module.id.index];
    for (unsigned i = 0; i < module.operators.size(); ++i) {
      auto binding =
          addBinding(module.operators[i],
                     moduleOperators.at({module.id.index, i}), scope, false);
      if (!binding)
        return false;
      moduleBindings.emplace(OperatorSite{module.id.index, i}, *binding);
    }
  }
  for (const auto &module : syntax) {
    auto scope = moduleScopes[module.id.index];
    auto &record = records.scopes[scope];
    for (const auto &import : module.imports) {
      if (!types.charge(import.names.size() + import.operators.size() +
                            import.notations.size() +
                            (import.alias ? import.alias->size() : 0) + 1,
                        import.span))
        return false;
      for (const auto *names :
           {&import.names, &import.operators, &import.notations})
        for (const auto &name : *names)
          if (!types.charge(name.size(), import.span))
            return false;
      record.imports.push_back({modules.at(import.module), import.span,
                                import.alias, import.names, import.operators,
                                import.notations, import.isPublic});
    }
    for (auto original : visibleOperators[module.id.index]) {
      if (!types.charge(1, record.span))
        return false;
      record.visible.push_back(moduleBindings.at(original));
    }
    for (auto original : exportedOperators[module.id.index]) {
      if (!types.charge(1, record.span))
        return false;
      record.exported.push_back(moduleBindings.at(original));
    }
    for (const auto &[key, syntax] : *notationEnvironments[module.id.index]) {
      if (!types.charge(key.size() + 1, syntax.span))
        return false;
      std::optional<uint32_t> descriptor;
      auto original = bindingSites.find(site(syntax.span));
      if (original != bindingSites.end())
        descriptor = records.bindings[original->second].descriptor;
      else
        descriptor =
            addDescriptor(*syntax.descriptor, syntax.span, true, true, false);
      if (!descriptor)
        return false;
      record.descriptors.push_back(*descriptor);
      descriptorsByScope[scope].emplace(key, *descriptor);
    }
  }
  for (unsigned owner = 0; owner < sources.size(); ++owner) {
    const auto occurrenceBegin = records.occurrences.size();
    const auto &source = *sources[owner];
    const auto &declaration = output.declarations[owner];
    if (!types.charge(source.bodies.size() + source.expressions.size() + 1,
                      source.span))
      return false;
    bool publicOwner = true;
    for (auto id = std::optional(declaration.id); id;
         id = output.declarations[id->index].parent) {
      if (!types.charge(1, source.span))
        return false;
      publicOwner &= output.declarations[id->index].isPublic;
    }
    std::vector<uint32_t> scopes(source.bodies.size());
    for (unsigned i = 0; i < source.bodies.size(); ++i) {
      NotationScopeRecord scope;
      scope.span = source.bodies[i].span;
      scope.owner = declaration.id;
      scope.body = i;
      scope.isPublic = publicOwner;
      scopes[i] = addScope(std::move(scope));
    }
    for (unsigned i = 0; i < source.bodies.size(); ++i) {
      const auto &body = source.bodies[i];
      auto scope = scopes[i];
      auto &record = records.scopes[scope];
      record.parent = body.parent ? scopes[*body.parent]
                                  : moduleScopes[declaration.module.index];
      // Public callable bodies may still contain private lexical declarations.
      // Exclude their complete subtree from the default occurrence inventory.
      for (auto parent = std::optional<uint32_t>(i); parent;
           parent = source.bodies[*parent].parent) {
        if (!types.charge(1, body.span))
          return false;
        record.isPublic &= source.bodies[*parent].operators.empty();
      }
      if (body.operators.size() != body.resolvedOperators.size())
        return types.fail("source.binding-witness",
                          "local notation declarations were not checked",
                          body.span);
      for (unsigned j = 0; j < body.operators.size(); ++j) {
        auto binding = addBinding(body.operators[j], body.resolvedOperators[j],
                                  scope, true);
        if (!binding)
          return false;
        auto descriptor = records.bindings[*binding].descriptor;
        const auto &shape = records.descriptors[descriptor].descriptor;
        if (!types.charge(shape.symbol.size() + 1, body.span))
          return false;
        // Multiple overload sites remain in bindings, but share the scope's
        // active descriptor. Lookup follows parent links for inherited shapes.
        if (descriptorsByScope[scope].emplace(shape.key(), descriptor).second)
          record.descriptors.push_back(descriptor);
      }
    }
    std::map<Site, uint32_t> occurrences;
    for (unsigned i = 0; i < source.expressions.size(); ++i) {
      const auto &expression = source.expressions[i];
      if (expression.kind != Expression::Kind::NotationCall)
        continue;
      if (!expression.notation || !expression.scope)
        return types.fail("source.binding-witness",
                          "notation occurrence has no checked scope",
                          expression.span);
      auto scope = scopes[*expression.scope];
      if (!types.charge(expression.children.size() +
                            expression.notation->symbol.size() + 1,
                        expression.span))
        return false;
      auto key = expression.notation->key();
      std::optional<uint32_t> descriptor;
      for (auto parent = std::optional(scope); parent;
           parent = records.scopes[*parent].parent) {
        if (!types.charge(1, expression.span))
          return false;
        auto found = descriptorsByScope[*parent].find(key);
        if (found != descriptorsByScope[*parent].end()) {
          descriptor = found->second;
          break;
        }
      }
      if (!descriptor ||
          records.descriptors[*descriptor].descriptor != *expression.notation)
        return types.fail("source.binding-witness",
                          "notation descriptor differs from its scope",
                          expression.span);
      NotationOccurrenceRecord record{*descriptor,     scope, i, declaration.id,
                                      expression.span, {},    {}};
      for (auto child : expression.children)
        record.operands.push_back({child, source.expressions[child].span});
      auto id = uint32_t(records.occurrences.size());
      records.occurrences.push_back(std::move(record));
      if (!occurrences.emplace(site(expression.span), id).second)
        return types.fail("source.binding-witness",
                          "notation occurrences share a source interval",
                          expression.span);
    }
    uint32_t nextRegion = 0;
    std::function<bool(const Body &, unsigned)> emitted;
    emitted = [&](const Body &body, unsigned depth) {
      if (depth > work.limits.expressionDepth)
        return types.fail("source.limit", "notation region depth exceeded",
                          declaration.span);
      if (!types.charge(body.operations.size() + 1, declaration.span))
        return false;
      auto region = nextRegion++;
      for (unsigned index = 0; index < body.operations.size(); ++index) {
        const auto &operation = body.operations[index];
        if (operation.binding && !operation.binding->symbol.empty()) {
          const auto &binding = *operation.binding;
          auto occurrence = occurrences.find(site(operation.span));
          // Calls.cpp emits the checked expression's span (which may include
          // grouping/specialization), not the operator token's interval. A
          // mismatch must not silently manufacture a not-emitted occurrence.
          if (occurrence == occurrences.end() || !binding.origin ||
              !binding.notation)
            return types.fail("source.binding-witness",
                              "emitted notation has no source occurrence",
                              operation.span);
          auto original = bindingSites.find(site(*binding.origin));
          if (original == bindingSites.end())
            return types.fail("source.binding-witness",
                              "emitted notation has no original binding",
                              operation.span);
          auto &record = records.occurrences[occurrence->second];
          if (record.selection ||
              *binding.notation !=
                  records.descriptors[record.descriptor].descriptor ||
              binding.operands.size() != record.operands.size())
            return types.fail("source.binding-witness",
                              "emitted notation evidence differs",
                              operation.span);
          if (!types.charge(binding.arguments.size() + binding.family.size() +
                                binding.operands.size() + 1,
                            operation.span))
            return false;
          NotationEmissionRecord selection{
              original->second, region, index, &operation, {}, {}, {}};
          for (const auto &argument : binding.arguments) {
            auto text = printType(argument, operation.span);
            if (!text)
              return false;
            selection.arguments.push_back(std::move(*text));
          }
          if (binding.target.component) {
            selection.component =
                printType(*binding.target.component, operation.span);
            if (!selection.component)
              return false;
          }
          // Map the retained family evidence to sites in the first defining
          // scope. This is a scope walk, not a fresh overload search.
          bool defined = false;
          if (!types.charge(binding.family.size(), operation.span))
            return false;
          std::vector<bool> matched(binding.family.size());
          for (auto parent = std::optional(record.scope); parent && !defined;
               parent = records.scopes[*parent].parent) {
            const auto &scope = records.scopes[*parent];
            const auto &entries = scope.owner ? scope.bindings : scope.visible;
            if (!types.charge(entries.size() + 1, operation.span))
              return false;
            for (auto entry : entries) {
              const auto &candidate = records.bindings[entry];
              if (records.descriptors[candidate.descriptor].descriptor !=
                  *binding.notation)
                continue;
              defined = true;
              for (unsigned member = 0; member < binding.family.size();
                   ++member) {
                const auto &identity = binding.family[member];
                if (!types.charge(identity.size() + 1, operation.span))
                  return false;
                if (identity == candidate.identity) {
                  selection.family.push_back(entry);
                  matched[member] = true;
                }
              }
            }
          }
          if (std::find(matched.begin(), matched.end(), false) != matched.end())
            return types.fail("source.binding-witness",
                              "emitted family has no original binding site",
                              operation.span);
          record.selection = std::move(selection);
          // A public short binding carries its descriptor even when the
          // environment originally obtained that shape from a private site.
          const auto &selected = records.bindings[original->second];
          if (!records.descriptors[record.descriptor].isPublic &&
              selected.isPublic)
            record.descriptor = selected.descriptor;
        }
        if (auto control = std::get_if<LocalControl>(&operation.action)) {
          for (const auto &nested : control->regions)
            if (!emitted(*nested, depth + 1))
              return false;
        } else if (auto repeat =
                       std::get_if<ProtocolRepeat>(&operation.action)) {
          if (!emitted(*repeat->region, depth + 1))
            return false;
        }
      }
      return true;
    };
    if (declaration.body && !emitted(*declaration.body, 1))
      return false;
    // Authored operand text can contain an entire nested block. Excluding just
    // the inner occurrence would still expose its private declaration through
    // the outer one's text. Merge hidden byte intervals before marking records.
    if (!types.charge(scopes.size() + records.occurrences.size() -
                          occurrenceBegin,
                      source.span))
      return false;
    std::vector<std::pair<uint32_t, uint32_t>> hidden;
    for (auto scope : scopes)
      if (!records.scopes[scope].isPublic) {
        const auto span = records.scopes[scope].span;
        hidden.emplace_back(span.begin, span.end);
      }
    for (size_t i = occurrenceBegin; i < records.occurrences.size(); ++i) {
      const auto &occurrence = records.occurrences[i];
      if (!records.descriptors[occurrence.descriptor].isPublic ||
          (occurrence.selection &&
           !records.bindings[occurrence.selection->binding].isPublic))
        hidden.emplace_back(occurrence.span.begin, occurrence.span.end);
    }
    unsigned levels = 1;
    for (auto count = hidden.size(); count > 1; count /= 2)
      ++levels;
    if (!types.charge(hidden.size() * levels +
                          (records.occurrences.size() - occurrenceBegin) *
                              levels,
                      source.span))
      return false;
    std::sort(hidden.begin(), hidden.end());
    size_t merged = 0;
    for (const auto &interval : hidden) {
      if (merged && interval.first <= hidden[merged - 1].second)
        hidden[merged - 1].second =
            std::max(hidden[merged - 1].second, interval.second);
      else
        hidden[merged++] = interval;
    }
    hidden.resize(merged);
    for (size_t i = occurrenceBegin; i < records.occurrences.size(); ++i) {
      auto &occurrence = records.occurrences[i];
      auto overlap =
          std::lower_bound(hidden.begin(), hidden.end(), occurrence.span.begin,
                           [](const auto &interval, uint32_t begin) {
                             return interval.second <= begin;
                           });
      occurrence.isPublic =
          publicOwner &&
          (overlap == hidden.end() || overlap->first >= occurrence.span.end);
    }
  }
  return true;
}
} // namespace zkc::language::detail

namespace zkc::language {
namespace {
StringRef position(NotationDescriptor::Position position) {
  switch (position) {
  case NotationDescriptor::Position::Prefix:
    return "prefix";
  case NotationDescriptor::Position::Infix:
    return "infix";
  case NotationDescriptor::Position::Postfix:
    return "postfix";
  case NotationDescriptor::Position::Delimited:
    return "delimited";
  }
  llvm_unreachable("unknown notation position");
}
StringRef association(NotationDescriptor::Association association) {
  switch (association) {
  case NotationDescriptor::Association::None:
    return "none";
  case NotationDescriptor::Association::Left:
    return "left";
  case NotationDescriptor::Association::Right:
    return "right";
  }
  llvm_unreachable("unknown notation association");
}
} // namespace

Expected<std::string> inspectNotations(const CheckedProject &project,
                                       const NotationInspectionOptions &options,
                                       const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedOperations() > limits.operations ||
      project.checkedNotationDescriptors() > limits.notationDescriptors ||
      project.checkedNotationHoles() > limits.notationHoles)
    return detail::failure(
        "source.limit", "checked project exceeds notation inspection limits");
  const auto &records = project.storage->notations;
  detail::Work work{limits};
  if (auto error =
          work.charge(records.descriptors.size() + records.bindings.size() +
                      records.scopes.size() + records.occurrences.size()))
    return std::move(error);
  std::vector<bool> descriptors(records.descriptors.size());
  std::vector<bool> bindings(records.bindings.size());
  std::vector<bool> scopes(records.scopes.size());
  auto originAllowed = [&](Span span) {
    return options.includeInstallation ||
           project.sources()[span.module.index].origin ==
               SourceOrigin::Captured;
  };
  for (unsigned i = 0; i < scopes.size(); ++i) {
    const auto &scope = records.scopes[i];
    scopes[i] =
        originAllowed(scope.span) && (options.includePrivate || scope.isPublic);
    // Count even filtered traversal before allocating or emitting any arrays.
    if (auto error =
            work.charge(scope.descriptors.size() + scope.bindings.size() +
                            scope.visible.size() + scope.exported.size() +
                            scope.imports.size(),
                        scope.span))
      return std::move(error);
    for (const auto &import : scope.imports)
      if (auto error =
              work.charge(import.names.size() + import.operators.size() +
                              import.notations.size(),
                          import.span))
        return std::move(error);
  }
  for (unsigned i = 0; i < bindings.size(); ++i) {
    const auto &binding = records.bindings[i];
    bindings[i] = scopes[binding.scope] && originAllowed(binding.span) &&
                  (options.includePrivate || binding.isPublic);
    if (bindings[i])
      descriptors[binding.descriptor] = true;
    if (auto error = work.charge(binding.arguments.size() +
                                     binding.authoredArguments.size() +
                                     binding.holes.size(),
                                 binding.span))
      return std::move(error);
  }
  for (unsigned i = 0; i < descriptors.size(); ++i) {
    const auto &descriptor = records.descriptors[i];
    descriptors[i] =
        descriptors[i] || (originAllowed(descriptor.span) &&
                           (options.includePrivate || descriptor.isPublic));
  }
  for (const auto &occurrence : records.occurrences) {
    uint64_t count = occurrence.operands.size();
    if (occurrence.selection)
      count += occurrence.selection->arguments.size() +
               occurrence.selection->family.size();
    if (auto error = work.charge(count, occurrence.span))
      return std::move(error);
  }

  std::string bytes;
  BoundedStream out(bytes, limits.notationInspectionBytes);
  json::OStream json(out);
  auto span = [&](Span value) {
    json.object([&] {
      json.attribute("module", value.module.index);
      json.attribute("begin", value.begin);
      json.attribute("end", value.end);
    });
  };
  auto location = [&](Span value) {
    const auto &source = project.sources()[value.module.index];
    json.attribute("module", source.module);
    json.attribute("origin", source.origin == SourceOrigin::Captured
                                 ? "captured"
                                 : "installation");
    json.attributeBegin("span");
    span(value);
    json.attributeEnd();
  };
  auto text = [&](Span value) {
    return StringRef(project.sources()[value.module.index].text)
        .slice(value.begin, value.end);
  };
  auto strings = [&](StringRef name, const std::vector<std::string> &values) {
    json.attributeArray(name, [&] {
      for (const auto &value : values) {
        if (out.overflow())
          break;
        json.value(value);
      }
    });
  };
  auto references = [&](StringRef name, const std::vector<uint32_t> &values,
                        const std::vector<bool> &included) {
    json.attributeArray(name, [&] {
      for (auto id : values) {
        if (out.overflow())
          break;
        if (included[id])
          json.value(id);
      }
    });
  };
  auto authored = [&](StringRef name, const std::vector<Span> &values) {
    json.attributeArray(name, [&] {
      for (auto value : values) {
        if (out.overflow())
          break;
        json.object([&] {
          json.attributeBegin("span");
          span(value);
          json.attributeEnd();
          json.attribute("text", text(value));
        });
      }
    });
  };
  // Write fragments of one JSON string directly into the bounded stream. In
  // particular, never concatenate potentially large authored operands first.
  auto quotedPart = [&](StringRef value) {
    static constexpr char hex[] = "0123456789abcdef";
    for (unsigned char byte : value.bytes()) {
      if (out.overflow())
        break;
      if (byte == '"' || byte == '\\')
        out << '\\' << char(byte);
      else if (byte < 0x20)
        out << "\\u00" << hex[byte >> 4] << hex[byte & 15];
      else
        out << char(byte);
    }
  };
  json.object([&] {
    json.attribute("format", "zkc.notations/0");
    json.attribute("include_private", options.includePrivate);
    json.attribute("include_installation", options.includeInstallation);
    json.attributeArray("descriptors", [&] {
      for (unsigned i = 0; i < descriptors.size() && !out.overflow(); ++i) {
        if (!descriptors[i])
          continue;
        const auto &record = records.descriptors[i];
        const auto &descriptor = record.descriptor;
        json.object([&] {
          json.attribute("id", i);
          location(record.span);
          json.attribute("symbol", descriptor.symbol);
          json.attribute("position", position(descriptor.position));
          json.attribute("precedence", descriptor.precedence);
          json.attribute("association", association(descriptor.association));
          json.attribute("closing", descriptor.closing);
          json.attribute("arity", descriptor.arity);
          json.attribute("fixed", record.fixed);
          json.attribute("explicit", record.explicitSyntax);
        });
      }
    });
    json.attributeArray("bindings", [&] {
      for (unsigned i = 0; i < bindings.size() && !out.overflow(); ++i) {
        if (!bindings[i])
          continue;
        const auto &binding = records.bindings[i];
        json.object([&] {
          json.attribute("id", i);
          location(binding.span);
          json.attribute("descriptor", binding.descriptor);
          json.attribute("scope", binding.scope);
          json.attribute("visibility", binding.local      ? "local"
                                       : binding.isPublic ? "public"
                                                          : "private");
          json.attribute(
              "target",
              project.declarations()[binding.target.index].qualifiedName);
          json.attribute("target_declaration", binding.target.index);
          json.attributeBegin("target_definition_span");
          span(project.declarations()[binding.target.index].span);
          json.attributeEnd();
          json.attribute("component", binding.component
                                          ? json::Value(*binding.component)
                                          : json::Value(nullptr));
          json.attributeBegin("target_span");
          span(binding.targetSpan);
          json.attributeEnd();
          json.attributeArray("static_arguments", [&] {
            for (const auto &argument : binding.arguments) {
              if (out.overflow())
                break;
              json.value(argument ? json::Value(*argument)
                                  : json::Value(nullptr));
            }
          });
          authored("authored_static_arguments", binding.authoredArguments);
          strings("holes", binding.holes);
        });
      }
    });
    json.attributeArray("scopes", [&] {
      for (unsigned i = 0; i < scopes.size() && !out.overflow(); ++i) {
        if (!scopes[i])
          continue;
        const auto &scope = records.scopes[i];
        json.object([&] {
          json.attribute("id", i);
          location(scope.span);
          json.attribute("kind", scope.owner ? "lexical" : "module");
          json.attribute("parent", scope.parent && scopes[*scope.parent]
                                       ? json::Value(*scope.parent)
                                       : json::Value(nullptr));
          if (scope.owner) {
            json.attribute(
                "owner",
                project.declarations()[scope.owner->index].qualifiedName);
            json.attribute("owner_declaration", scope.owner->index);
            json.attribute("body", *scope.body);
          }
          json.attribute("binding_policy", scope.owner
                                               ? "replace-matching-descriptor"
                                               : "module-visibility");
          references("descriptors", scope.descriptors, descriptors);
          references("bindings", scope.bindings, bindings);
          references("visible_bindings", scope.visible, bindings);
          references("exported_bindings", scope.exported, bindings);
          json.attributeArray("imports", [&] {
            for (const auto &import : scope.imports) {
              if (out.overflow())
                break;
              if ((!options.includePrivate && !import.isPublic) ||
                  (!options.includeInstallation &&
                   project.sources()[import.module.index].origin ==
                       SourceOrigin::Installation))
                continue;
              json.object([&] {
                json.attribute("module",
                               project.sources()[import.module.index].module);
                json.attributeBegin("span");
                span(import.span);
                json.attributeEnd();
                json.attribute("reexport", import.isPublic);
                json.attribute("alias", import.alias
                                            ? json::Value(*import.alias)
                                            : json::Value(nullptr));
                strings("names", import.names);
                strings("operators", import.operators);
                strings("notations", import.notations);
              });
            }
          });
        });
      }
    });
    json.attributeArray("occurrences", [&] {
      for (unsigned i = 0; i < records.occurrences.size() && !out.overflow();
           ++i) {
        const auto &occurrence = records.occurrences[i];
        if (!scopes[occurrence.scope] || !descriptors[occurrence.descriptor] ||
            !originAllowed(occurrence.span) ||
            (!options.includePrivate && !occurrence.isPublic))
          continue;
        const auto *selection =
            occurrence.selection ? &*occurrence.selection : nullptr;
        if (!options.includePrivate && selection &&
            !records.bindings[selection->binding].isPublic)
          continue;
        bool showSelection = selection && bindings[selection->binding];
        json.object([&] {
          json.attribute("id", i);
          location(occurrence.span);
          json.attribute("descriptor", occurrence.descriptor);
          json.attribute("scope", occurrence.scope);
          json.attribute("expression", occurrence.expression);
          json.attribute(
              "owner",
              project.declarations()[occurrence.owner.index].qualifiedName);
          json.attribute("owner_declaration", occurrence.owner.index);
          json.attribute("state", selection ? "emitted" : "not-emitted");
          json.attribute("selection_visibility", !selection ? "not-emitted"
                                                 : showSelection
                                                     ? "included"
                                                     : "installation-excluded");
          json.attribute("selected_binding",
                         showSelection ? json::Value(selection->binding)
                                       : json::Value(nullptr));
          json.attributeArray("operands", [&] {
            for (unsigned operand = 0; operand < occurrence.operands.size();
                 ++operand) {
              if (out.overflow())
                break;
              const auto &value = occurrence.operands[operand];
              json.object([&] {
                json.attribute("position", operand);
                json.attribute("expression", value.expression);
                json.attributeBegin("span");
                span(value.span);
                json.attributeEnd();
                json.attribute("text", text(value.span));
                if (selection)
                  json.attribute(
                      "runtime_value",
                      selection->emitted->binding->operands[operand].index);
              });
            }
          });
          if (selection) {
            json.attribute("region", selection->region);
            json.attribute("operation", selection->operation);
            json.attributeBegin("operation_span");
            span(selection->emitted->span);
            json.attributeEnd();
          }
          json.attributeBegin("named_call");
          if (!showSelection)
            json.value(nullptr);
          else {
            const auto &evidence = *selection->emitted->binding;
            json.object([&] {
              json.attribute("kind", "target-qualified-call");
              json.attribute(
                  "target",
                  project.declarations()[evidence.target.declaration.index]
                      .qualifiedName);
              json.attribute("component",
                             selection->component
                                 ? json::Value(*selection->component)
                                 : json::Value(nullptr));
              strings("static_arguments", selection->arguments);
              json.attributeBegin("rendering");
              json.rawValueBegin();
              out << '"';
              quotedPart(
                  project.declarations()[evidence.target.declaration.index]
                      .qualifiedName);
              if (!selection->arguments.empty()) {
                out << '<';
                for (unsigned argument = 0;
                     argument < selection->arguments.size() && !out.overflow();
                     ++argument) {
                  if (argument)
                    out << ", ";
                  quotedPart(selection->arguments[argument]);
                }
                out << '>';
              }
              out << '(';
              for (unsigned operand = 0;
                   operand < occurrence.operands.size() && !out.overflow();
                   ++operand) {
                if (operand)
                  out << ", ";
                quotedPart(text(occurrence.operands[operand].span));
              }
              out << ")\"";
              json.rawValueEnd();
              json.attributeEnd();
              json.attributeArray("operand_order", [&] {
                for (unsigned operand = 0; operand < occurrence.operands.size();
                     ++operand) {
                  if (out.overflow())
                    break;
                  json.value(operand);
                }
              });
              json.attribute("symbol", evidence.symbol);
              references("family", selection->family, bindings);
              bool complete = true;
              for (auto member : selection->family)
                complete &= bindings[member];
              json.attribute("family_complete", complete);
            });
          }
          json.attributeEnd();
        });
      }
    });
  });
  if (out.overflow())
    return detail::failure("source.limit",
                           "notation inspection byte limit exceeded");
  return bytes;
}
} // namespace zkc::language

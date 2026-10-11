#include "State.h"
#include "zkc/Language/Diagnostics.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "llvm/Support/JSON.h"

using namespace llvm;

namespace zkc::language {
namespace {
StringRef position(NotationDescriptor::Position position) {
  switch (position) {
  case NotationDescriptor::Position::Index:
    return "index";
  case NotationDescriptor::Position::Reduction:
    return "reduction";
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
           project.sources()[span.source.index].origin ==
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
      if (auto error = work.charge(
              import.names.size() + import.operators.size() +
                  import.notations.size() + import.reductions.size(),
              import.span))
        return std::move(error);
  }
  for (unsigned i = 0; i < bindings.size(); ++i) {
    const auto &binding = records.bindings[i];
    bindings[i] = scopes[binding.scope] && originAllowed(binding.span) &&
                  (options.includePrivate || binding.isPublic);
    if (bindings[i])
      descriptors[binding.descriptor] = true;
    if (binding.filtered)
      if (auto error =
              work.charge(binding.filtered->arguments.size() +
                              binding.filtered->authoredArguments.size() + 1,
                          binding.span))
        return std::move(error);
    if (auto error = work.charge(binding.arguments.size() +
                                     binding.authoredArguments.size() +
                                     binding.holes.size(),
                                 binding.span))
      return std::move(error);
  }
  // A descriptor's public flag is relative to its defining module. Retain
  // unbound syntax only when it is visible in an included scope; a public
  // operator inside a private module must not leak through this table.
  for (unsigned i = 0; i < scopes.size(); ++i)
    if (scopes[i])
      for (auto id : records.scopes[i].descriptors) {
        const auto &descriptor = records.descriptors[id];
        if (originAllowed(descriptor.span) &&
            (options.includePrivate || descriptor.isPublic))
          descriptors[id] = true;
      }
  for (const auto &occurrence : records.occurrences) {
    uint64_t count = occurrence.operands.size();
    for (const auto &operand : occurrence.operands)
      count += operand.rendering.size();
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
      json.attribute("source", value.source.index);
      json.attribute("begin", value.begin);
      json.attribute("end", value.end);
    });
  };
  auto location = [&](Span value) {
    const auto &source = project.sources()[value.source.index];
    json.attribute("module", source.module);
    json.attribute("origin", source.origin == SourceOrigin::Captured
                                 ? "captured"
                                 : "installation");
    json.attributeBegin("span");
    span(value);
    json.attributeEnd();
  };
  auto text = [&](Span value) {
    return StringRef(project.sources()[value.source.index].text)
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
          json.attribute("receiver", binding.module
                                         ? json::Value(*binding.module)
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
          json.attributeBegin("filtered_target");
          if (!binding.filtered)
            json.value(nullptr);
          else {
            const auto &target = *binding.filtered;
            json.object([&] {
              json.attribute(
                  "target",
                  project.declarations()[target.target.index].qualifiedName);
              json.attribute("target_declaration", target.target.index);
              json.attribute("receiver", target.module
                                             ? json::Value(*target.module)
                                             : json::Value(nullptr));
              json.attributeBegin("target_span");
              span(target.span);
              json.attributeEnd();
              json.attributeArray("static_arguments", [&] {
                for (const auto &argument : target.arguments) {
                  if (out.overflow())
                    break;
                  json.value(argument ? json::Value(*argument)
                                      : json::Value(nullptr));
                }
              });
              authored("authored_static_arguments", target.authoredArguments);
            });
          }
          json.attributeEnd();
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
          json.attribute("kind", scope.body ? "lexical" : "module");
          json.attribute("parent", scope.parent && scopes[*scope.parent]
                                       ? json::Value(*scope.parent)
                                       : json::Value(nullptr));
          if (scope.owner) {
            json.attribute(
                "owner",
                project.declarations()[scope.owner->index].qualifiedName);
            json.attribute("owner_declaration", scope.owner->index);
            if (scope.body)
              json.attribute("body", *scope.body);
          }
          json.attribute("binding_policy", scope.body
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
                   project.sources()[project.declarations()[import.module.index]
                                         .span.source.index]
                           .origin == SourceOrigin::Installation))
                continue;
              json.object([&] {
                json.attribute(
                    "module",
                    project.declarations()[import.module.index].qualifiedName);
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
                strings("reductions", import.reductions);
                json.attribute("indexing", import.indexing);
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
                if (selection) {
                  const auto &evidence = *selection->emitted->binding;
                  if (evidence.notation->position ==
                      NotationDescriptor::Position::Reduction) {
                    const auto &target =
                        project
                            .declarations()[evidence.target.declaration.index];
                    const auto &slot =
                        target.inputOrder[evidence.argumentOrder[operand]];
                    bool domain =
                        slot.kind == Declaration::InputSlot::Kind::Domain;
                    json.attribute("kind", domain ? "domain" : "scoped");
                    json.attribute("binding",
                                   domain
                                       ? evidence.domainArguments[slot.index]
                                       : evidence.scopedArguments[slot.index]);
                  } else {
                    json.attribute("kind", "data");
                    json.attribute("runtime_value",
                                   evidence.operands[operand].index);
                  }
                }
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
              json.attribute("receiver", selection->module
                                             ? json::Value(*selection->module)
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
                const auto &value = occurrence.operands[operand];
                if (value.rendering.empty())
                  quotedPart(text(value.span));
                else
                  for (const auto &part : value.rendering) {
                    if (out.overflow())
                      break;
                    if (auto source = std::get_if<Span>(&part))
                      quotedPart(text(*source));
                    else
                      quotedPart(std::get<std::string>(part));
                  }
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
              json.attribute("filtered", evidence.filteredReduction);
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

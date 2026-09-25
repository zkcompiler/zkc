#include "zkc/Frontend/Inspection.h"
#include "../Resolution/Project.h"
#include "../Semantics/Libraries.h"
#include "../Syntax/Tree.h"
#include "Access.h"
#include "Libraries.h"
#include "Lints.h"

using namespace llvm;
namespace zkc::frontend {
namespace {
template <typename Tag> json::Value id(ModelId<Tag> value) {
  return value.valid() ? json::Value(int64_t(value.index))
                       : json::Value(nullptr);
}
json::Value span(const std::optional<source::Span> &value) {
  if (!value)
    return nullptr;
  return json::Object{{"offset", int64_t(value->offset)},
                      {"length", int64_t(value->length)},
                      {"file", int64_t(value->file)}};
}
StringRef kind(Declaration::Kind value) {
  switch (value) {
  case Declaration::Kind::Function:
    return "function";
  case Declaration::Kind::Protocol:
    return "protocol";
  case Declaration::Kind::Record:
    return "record";
  case Declaration::Kind::Parameter:
    return "parameter";
  case Declaration::Kind::Binding:
    return "binding";
  case Declaration::Kind::Configuration:
    return "configuration";
  case Declaration::Kind::Dependency:
    return "dependency";
  case Declaration::Kind::Instance:
    return "instance";
  case Declaration::Kind::Entry:
    return "entry";
  case Declaration::Kind::Relation:
    return "relation";
  case Declaration::Kind::RelationView:
    return "relation_view";
  case Declaration::Kind::Bundle:
    return "bundle";
  case Declaration::Kind::Operation:
    return "operation";
  case Declaration::Kind::Constant:
    return "constant";
  }
  llvm_unreachable("unknown declaration kind");
}
StringRef causeKind(DiagnosticCause::Kind kind) {
  switch (kind) {
  case DiagnosticCause::Kind::Declaration:
    return "declaration";
  case DiagnosticCause::Kind::ImportedInterface:
    return "imported_interface";
  case DiagnosticCause::Kind::SelectedComponent:
    return "selected_component";
  case DiagnosticCause::Kind::UnsatisfiedObligation:
    return "unsatisfied_obligation";
  case DiagnosticCause::Kind::CapturedSubject:
    return "captured_subject";
  case DiagnosticCause::Kind::Checker:
    return "checker";
  case DiagnosticCause::Kind::Premise:
    return "premise";
  }
  llvm_unreachable("unknown diagnostic cause kind");
}
StringRef dependencyKind(SemanticDependency::Kind kind) {
  switch (kind) {
  case SemanticDependency::Kind::Interface:
    return "interface";
  case SemanticDependency::Kind::Body:
    return "body";
  case SemanticDependency::Kind::LinkLayout:
    return "link_layout";
  case SemanticDependency::Kind::Evidence:
    return "evidence";
  case SemanticDependency::Kind::DiagnosticProvenance:
    return "diagnostic_provenance";
  }
  llvm_unreachable("unknown dependency kind");
}
json::Value qualifiedDeclaration(const library::QualifiedDecl &d) {
  json::Array module;
  for (const auto &part : d.module)
    module.push_back(part);
  return json::Object{
      {"namespace", d.library.nameSpace}, {"library", d.library.name},
      {"version", d.library.version},     {"resolution", d.library.resolution},
      {"module", std::move(module)},      {"name", d.name}};
}
json::Array ports(ArrayRef<Port> values, const Analysis &analysis) {
  json::Array result;
  for (const auto &port : values)
    result.push_back(json::Object{{"name", port.name},
                                  {"role", port.role},
                                  {"type", id(port.type)},
                                  {"display", analysis.display(port.type)},
                                  {"span", span(port.location)}});
  return result;
}
json::Array bindings(ArrayRef<ParameterBinding> values) {
  json::Array result;
  for (const auto &binding : values)
    result.push_back(json::Object{{"parameter", id(binding.parameter)},
                                  {"argument", id(binding.argument)}});
  return result;
}
json::Array requirements(ArrayRef<Requirement> values) {
  json::Array result;
  for (const auto &requirement : values) {
    json::Array arguments;
    for (auto argument : requirement.arguments)
      arguments.push_back(id(argument));
    result.push_back(json::Object{{"predicate", requirement.predicate},
                                  {"arguments", std::move(arguments)},
                                  {"span", span(requirement.location)}});
  }
  return result;
}
} // namespace

json::Value inspectAnalysis(const Analysis &analysis) {
  json::Array scopes, declarations, types, domains, uses, instances,
      diagnostics, localBindings, valueUses;
  for (const auto &scope : analysis.scopes())
    scopes.push_back(json::Object{{"id", id(scope.id)},
                                  {"parent", id(scope.parent)},
                                  {"owner", id(scope.owner)}});
  for (const auto &declaration : analysis.declarations()) {
    json::Array parameters, constructors, roles, naturalParameters;
    for (const auto &role : declaration.roles)
      roles.push_back(role);
    for (const auto &parameter : declaration.naturalParameters)
      naturalParameters.push_back(parameter);
    for (auto parameter : declaration.parameters)
      parameters.push_back(id(parameter));
    for (auto constructor : declaration.constructors)
      constructors.push_back(id(constructor));
    declarations.push_back(json::Object{
        {"id", id(declaration.id)},
        {"scope", id(declaration.scope)},
        {"members", id(declaration.members)},
        {"kind", kind(declaration.kind)},
        {"name", declaration.name},
        {"lowered_name", declaration.loweredName
                             ? json::Value(*declaration.loweredName)
                             : json::Value(nullptr)},
        {"display_name", declaration.displayName.empty()
                             ? declaration.name
                             : declaration.displayName},
        {"identity", declaration.identity.empty()
                         ? json::Value(nullptr)
                         : json::Value(declaration.identity)},
        {"sort", declaration.sort},
        {"span", span(declaration.location)},
        {"generic", declaration.generic},
        {"checked_constructor_authority", declaration.checked},
        {"has_body", declaration.hasBody},
        {"signature_checked", declaration.signatureChecked},
        {"constant_value",
         declaration.constantValue
             ? json::Value(int64_t(*declaration.constantValue))
             : json::Value(nullptr)},
        {"body_state",
         declaration.bodyState == Declaration::BodyState::Checked
             ? "source_checked"
         : declaration.bodyState == Declaration::BodyState::Deferred
             ? "deferred"
             : "external"},
        {"roles", std::move(roles)},
        {"natural_parameters", std::move(naturalParameters)},
        {"parameters", std::move(parameters)},
        {"constructors", std::move(constructors)},
        {"inputs", ports(declaration.inputs, analysis)},
        {"outputs", ports(declaration.outputs, analysis)},
        {"fields", ports(declaration.fields, analysis)},
        {"requirements", requirements(declaration.requirements)},
        {"target", id(declaration.target)}});
  }
  for (const auto &type : analysis.types()) {
    json::Array arguments, elements;
    for (auto element : type.elements)
      elements.push_back(id(element));
    for (auto argument : type.arguments)
      arguments.push_back(id(argument));
    types.push_back(
        json::Object{{"kind", type.kind == Type::Kind::Record    ? "record"
                              : type.kind == Type::Kind::Product ? "product"
                              : type.kind == Type::Kind::Array   ? "array"
                                                                 : "logical"},
                     {"count", type.count},
                     {"constructor", type.constructor},
                     {"declaration", id(type.declaration)},
                     {"arguments", std::move(arguments)},
                     {"elements", std::move(elements)}});
  }
  for (const auto &domain : analysis.domains())
    domains.push_back(json::Object{
        {"kind", domain.kind == Domain::Kind::Identity    ? "identity"
                 : domain.kind == Domain::Kind::Parameter ? "parameter"
                                                          : "projection"},
        {"name", domain.name},
        {"sort", domain.sort},
        {"parameter", id(domain.parameter)},
        {"parent", id(domain.parent)}});
  for (const auto &use : analysis.uses())
    uses.push_back(json::Object{
        {"kind", use.kind == ResolvedUse::Kind::Call        ? "call"
                 : use.kind == ResolvedUse::Kind::Construct ? "construct"
                                                            : "invoke"},
        {"owner", id(use.owner)},
        {"target", id(use.target)},
        {"scope", id(use.scope)},
        {"span", span(use.location)},
        {"site", use.site},
        {"role", use.role},
        {"written_arguments", use.writtenArguments},
        {"bindings", bindings(use.bindings)},
        {"results", ports(use.results, analysis)},
        {"requirements", requirements(use.requirements)}});
  for (const auto &instance : analysis.instantiations())
    instances.push_back(
        json::Object{{"definition", id(instance.definition)},
                     {"emitted", id(instance.emitted)},
                     {"span", span(instance.location)},
                     {"bindings", bindings(instance.bindings)}});
  for (const auto &binding : analysis.bindings()) {
    json::Array leaves;
    for (const auto &leaf : binding.leaves)
      leaves.push_back(leaf);
    localBindings.push_back(
        json::Object{{"id", id(binding.id)},
                     {"scope", id(binding.scope)},
                     {"name", binding.name},
                     {"type", id(binding.type)},
                     {"display", analysis.display(binding.type)},
                     {"leaves", std::move(leaves)},
                     {"mutable", binding.mutableBinding},
                     {"span", span(binding.location)}});
  }
  for (const auto &use : analysis.valueUses())
    valueUses.push_back(json::Object{{"binding", id(use.binding)},
                                     {"scope", id(use.scope)},
                                     {"span", span(use.location)}});
  auto renderDiagnostic = [](const Diagnostic &diagnostic, StringRef category) {
    json::Array related, causes;
    for (const auto &r : diagnostic.related)
      related.push_back(
          json::Object{{"message", r.message}, {"span", span(r.location)}});
    for (const auto &c : diagnostic.causes)
      causes.push_back(json::Object{{"kind", causeKind(c.kind)},
                                    {"subject", c.subject},
                                    {"explanation", c.explanation},
                                    {"span", span(c.location)}});
    return json::Object{{"code", diagnostic.code},
                        {"message", diagnostic.message},
                        {"category", category},
                        {"span", span(diagnostic.location)},
                        {"primary", span(diagnostic.location)},
                        {"related", std::move(related)},
                        {"causes", std::move(causes)}};
  };
  for (const auto &diagnostic : analysis.diagnostics())
    diagnostics.push_back(
        renderDiagnostic(diagnostic, isResourceLimitDiagnostic(diagnostic.code)
                                         ? "resource_limit"
                                         : "error"));
  json::Array warnings;
  for (const auto &warning : tooling::unusedBindingWarnings(analysis))
    warnings.push_back(renderDiagnostic(warning, "warning"));
  json::Value libraries = nullptr;
  if (auto retained = semantics::AnalysisAccess::libraries(analysis))
    libraries = tooling::inspectLibraries(
        *retained, semantics::AnalysisAccess::get(analysis).resolution.get());
  if (!analysis.complete())
    if (auto *report = libraries.getAsObject()) {
      (*report)["query_state"] = "retained_partial_checked_capabilities";
      (*report)["unselected_component_conformance"] =
          "only_reported_components_checked";
    }
  if (libraries.kind() == json::Value::Null) {
    json::Array syntaxFiles;
    bool checkedSyntax = false;
    auto inspectFile = [&](StringRef text, StringRef filename, uint32_t file) {
      auto parsed = syntax::parseRecoverable(text, filename);
      if (!parsed.content)
        return;
      if (const auto *module = std::get_if<syntax::Module>(&*parsed.content))
        checkedSyntax |= semantics::hasLibraries(*module);
      syntaxFiles.push_back(
          json::Object{{"file", int64_t(file)},
                       {"syntax", syntax::inspect(*parsed.content)}});
    };
    if (const auto *project = analysis.project()) {
      uint32_t file = 0;
      for (const auto &library : project->libraries())
        for (const auto &source : library.sources)
          inspectFile(source.input.text(), source.input.filename(), file++);
    } else
      inspectFile(analysis.sourceText(), analysis.filename(), 0);
    if (checkedSyntax)
      libraries =
          json::Object{{"query_state", "typed_library_queries_unavailable"},
                       {"syntax_files", std::move(syntaxFiles)},
                       {"checking", "unavailable"},
                       {"unselected_component_conformance", "not_claimed"},
                       {"pir_admission", "not_requested"}};
  }
  json::Array files;
  if (const auto *project = analysis.project()) {
    uint32_t file = 0;
    uint32_t owner = 0;
    for (const auto &library : project->libraries()) {
      for (const auto &source : library.sources) {
        json::Array module;
        for (const auto &part : source.module)
          module.push_back(part);
        files.push_back(
            json::Object{{"id", int64_t(file++)},
                         {"owner", int64_t(owner)},
                         {"module", std::move(module)},
                         {"filename", source.input.filename()},
                         {"bytes", int64_t(source.input.text().size())}});
      }
      ++owner;
    }
  } else
    files.push_back(
        json::Object{{"id", 0},
                     {"filename", analysis.filename()},
                     {"bytes", int64_t(analysis.sourceText().size())}});
  json::Array dependencies, resolvedDeclarations;
  for (const auto &d : analysis.dependencies())
    dependencies.push_back(json::Object{{"category", dependencyKind(d.kind)},
                                        {"source", d.source},
                                        {"target", d.target},
                                        {"span", span(d.location)}});
  const auto &model = semantics::AnalysisAccess::get(analysis);
  if (model.resolution)
    for (const auto &d : model.resolution->declarations) {
      std::string display;
      for (const auto &part : d.identity.module)
        display += part + "::";
      display += d.identity.name;
      resolvedDeclarations.push_back(json::Object{
          {"symbol", d.symbol},
          {"origin", model.resolution->origin(d.identity)},
          {"display_name", display},
          {"identity", qualifiedDeclaration(d.identity)},
          {"identity_key", library::identity(d.identity)},
          {"resolution", model.resolution->unavailable.count(d.symbol)
                             ? "unavailable"
                         : analysis.resolutionComplete() ? "resolved"
                                                         : "collected"},
          {"exported", d.exported},
          {"span", span(d.location)}});
    }
  auto retained = semantics::AnalysisAccess::libraries(analysis);
  size_t checkedBodies = 0;
  for (const auto &d : analysis.declarations())
    checkedBodies +=
        d.generic && d.bodyState == Declaration::BodyState::Checked;
  if (retained)
    checkedBodies +=
        retained->clients.size() + retained->componentBodies.size();
  auto availability = [](size_t count) -> json::Value {
    return json::Object{{"state", count ? "available" : "unavailable"},
                        {"count", int64_t(count)}};
  };
  json::Object phases{
      {"resolution", analysis.resolutionComplete() ? "complete" : "incomplete"},
      {"formed_interface",
       availability(retained ? retained->interfaces.size() : 0)},
      {"checked_generic_body", availability(checkedBodies)},
      {"linked_selection", availability(retained ? retained->links.size() : 0)},
      {"source_check", analysis.complete() ? "complete" : "incomplete"},
      {"pir_admission", "not_requested"},
      {"runtime_readiness", "not_requested"}};
  return json::Object{
      {"files", std::move(files)},
      {"resolved_declarations", std::move(resolvedDeclarations)},
      {"dependencies", std::move(dependencies)},
      {"dependency_tracking", "retained_references_not_minimal_invalidation"},
      {"cache", "not_implemented"},
      {"phases", std::move(phases)},
      {"unused_binding_warnings", "checked_retained_bodies"},
      {"decision_result_usage", "unavailable_no_decision_metadata"},
      {"acceptance_dependence", "not_analyzed"},
      {"cryptographic_soundness", "not_claimed"},
      {"checked_libraries", std::move(libraries)},
      {"format", "zkc.frontend-analysis/1"},
      {"state", analysis.complete() ? "source_checked" : "incomplete"},
      {"phase",
       analysis.state() == AnalysisState::SyntaxPartial   ? "syntax_partial"
       : analysis.state() == AnalysisState::SemanticError ? "semantic_error"
       : analysis.state() == AnalysisState::ResourceLimit ? "resource_limit"
                                                          : "source_checked"},
      {"admission", "not_requested"},
      {"scopes", std::move(scopes)},
      {"declarations", std::move(declarations)},
      {"types", std::move(types)},
      {"domains", std::move(domains)},
      {"uses", std::move(uses)},
      {"local_bindings", std::move(localBindings)},
      {"value_uses", std::move(valueUses)},
      {"instantiations", std::move(instances)},
      {"warnings", std::move(warnings)},
      {"diagnostics", std::move(diagnostics)}};
}
} // namespace zkc::frontend

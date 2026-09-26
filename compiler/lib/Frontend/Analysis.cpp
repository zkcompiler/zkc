#include "zkc/Frontend/Analysis.h"
#include "Instantiation/Select.h"
#include "Library/Diagnostic.h"
#include "Lowering/LibrarySource.h"
#include "Lowering/PIR.h"
#include "Model/Access.h"
#include "Resolution/Declarations.h"
#include "Resolution/Project.h"
#include "Semantics/Analysis.h"
#include "Semantics/Libraries.h"
#include "Semantics/Provenance.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::frontend {
Analysis model::AnalysisAccess::finish(model::EmittedSource emitted,
                                       WorkUsage usage) {
  auto model = std::move(emitted.model);
  model->workUsage = usage;
  semantics::retainQueryMetadata(*model);
  return Analysis(std::shared_ptr<const CompletedAnalysis>(
      new CompletedAnalysis(std::move(*model), std::move(emitted.content))));
}
Analysis analyzeProtocol(const Input &input) {
  return analyzeProtocol(input, {});
}
Analysis analyzeProtocol(const Input &input, WorkLimits limits) {
  return analyzeProject(ProjectInput::single(input), limits);
}
Analysis analyzeProject(const ProjectInput &input) {
  return analyzeProject(input, {});
}
Analysis analyzeProject(const ProjectInput &input, WorkLimits limits) {
  WorkBudget budget(limits);
  auto resolved = resolution::resolve(input);
  const auto *root = input.file(
      resolved.context->owners.empty() ? 0 : resolved.context->owners[0].root);
  StringRef text = root ? root->text() : StringRef();
  StringRef filename = root ? root->filename() : StringRef("<project>");
  const bool resolutionComplete = resolved.diagnostics.empty();
  std::shared_ptr<const model::LibraryReport> retainedLibraries;
  auto failure = [&](std::unique_ptr<model::Module> model = nullptr) {
    if (!model)
      model = std::make_unique<model::Module>();
    model->workUsage = budget.usage();
    model->resolution = resolved.context;
    model->resolutionComplete = resolutionComplete;
    model->text = text.str();
    model->filename = filename.str();
    model->diagnostics.insert(model->diagnostics.begin(),
                              resolved.diagnostics.begin(),
                              resolved.diagnostics.end());
    model->syntaxPartial = resolved.syntaxPartial;
    for (auto &d : model->declarations)
      d.loweredName.reset();
    if (!model->libraries)
      model->libraries = retainedLibraries;
    if (const auto *m = std::get_if<syntax::Module>(&resolved.content))
      resolution::declarations(*m, [&](const auto &d, auto kind) {
        using K = resolution::Declaration::Kind;
        auto semanticKind =
            kind == K::Protocol                    ? Declaration::Kind::Protocol
            : kind == K::Record || kind == K::Enum ? Declaration::Kind::Record
            : kind == K::Constant                  ? Declaration::Kind::Constant
            : kind == K::Relation                  ? Declaration::Kind::Relation
            : kind == K::View          ? Declaration::Kind::RelationView
            : kind == K::Instance      ? Declaration::Kind::Instance
            : kind == K::Entry         ? Declaration::Kind::Entry
            : kind == K::Configuration ? Declaration::Kind::Configuration
            : kind == K::Binding       ? Declaration::Kind::Binding
            : kind == K::Bundle        ? Declaration::Kind::Bundle
                                       : Declaration::Kind::Function;
        if (!model->lookup({0}, d.name).valid()) {
          auto id = model->add(semanticKind, {0}, d.name, d.location);
          if constexpr (std::is_same_v<std::decay_t<decltype(d)>,
                                       syntax::Function> ||
                        std::is_same_v<std::decay_t<decltype(d)>,
                                       syntax::Protocol>) {
            auto &stub = model->declarations[id.index];
            stub.generic = d.generic;
            stub.hasBody = bool(d.body);
            stub.bodyState = d.body ? Declaration::BodyState::Deferred
                                    : Declaration::BodyState::External;
          }
        }
      });
    semantics::retainQueryMetadata(*model);
    return model::AnalysisAccess::freeze(std::move(model));
  };
  if (!resolutionComplete && !resolved.recoverable)
    return failure();
  // Only resolution may select a safe subset: checking the original content
  // after a visibility failure could otherwise manufacture an invalid result.
  const auto &content =
      resolutionComplete ? resolved.content : *resolved.recoverable;
  auto recordFailure = [&](Error error) {
    handleAllErrors(
        std::move(error),
        [&](const SourceDiagnostic &d) {
          resolved.diagnostics.push_back(
              {d.code, d.message, d.location, d.related, d.causes});
        },
        [&](const Refusal &e) {
          resolved.diagnostics.push_back({e.code, e.detail, {}});
        },
        [&](const library::Diagnostic &e) {
          resolved.diagnostics.push_back({e.code, e.message, {}});
        },
        [&](const ErrorInfoBase &e) {
          std::string message;
          raw_string_ostream out(message);
          e.log(out);
          report_fatal_error(Twine("unexpected frontend phase error: ") +
                             message);
        });
  };
  // Library formation/linking is explicit and precedes static specialization.
  // A failed phase retains its partial judgments without a mutable out
  // parameter.
  std::optional<syntax::Content> elaborated;
  LibraryEmission linked;
  source::Names linkedNames;
  if (const auto *module = std::get_if<syntax::Module>(&content)) {
    auto libraries = semantics::elaborateLibraries(*module, *resolved.context,
                                                   text, filename, budget);
    retainedLibraries = std::move(libraries.report);
    if (!libraries.content) {
      recordFailure(libraries.content.takeError());
      return failure();
    }
    auto &formed = *libraries.content;
    auto prepared = lowering::emitLibrarySource(
        std::move(formed.ordinary), formed.environment, formed.programs,
        formed.entryAliases, formed.reservedNames, *resolved.context, budget);
    if (!prepared) {
      recordFailure(prepared.takeError());
      return failure();
    }
    elaborated = std::move(prepared->ordinary);
    linked = std::move(prepared->generated);
    // Every authored alias reserves its name, regardless of whether its
    // layout needs a generated aggregate entry adapter.
    for (const auto &[entry, aliases] : formed.entryAliases)
      llvm::append_range(linkedNames, aliases);
  }
  auto staged = instantiation::select(elaborated ? *elaborated : content,
                                      *resolved.context, text, filename,
                                      linkedNames, budget);
  if (!staged) {
    recordFailure(staged.takeError());
    return failure();
  }
  auto checked = semantics::checkStaged(content, *staged, linked,
                                        retainedLibraries, resolved.context,
                                        text, filename, resolutionComplete);
  if (auto *partial = std::get_if<std::unique_ptr<model::Module>>(&checked))
    return failure(std::move(*partial));
  auto source = std::get<model::CheckedSource>(std::move(checked));
  if (!resolutionComplete || resolved.syntaxPartial)
    return failure(std::move(source).takeModel());
  auto emitted = lowering::lower(std::move(source), budget);
  if (!emitted) {
    recordFailure(emitted.takeError());
    return failure(std::move(source).takeModel());
  }
  return model::AnalysisAccess::finish(std::move(*emitted), budget.usage());
}
Analysis analyzeProtocol(StringRef text, StringRef filename) {
  return analyzeProtocol(text, filename, {});
}
Analysis analyzeProtocol(StringRef text, StringRef filename,
                         WorkLimits limits) {
  return analyzeProtocol(Input(text.str(), filename.str()), limits);
}

} // namespace zkc::frontend

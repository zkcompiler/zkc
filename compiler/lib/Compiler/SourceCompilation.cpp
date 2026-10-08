#include "CompilationState.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Compiler/SourceLocations.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
using detail::Diagnostics;
namespace {
Error sourceCompilationError(Error error,
                             const frontend::ProjectInput *project = nullptr) {
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::vector<InvocationPrecondition> preconditions;
  detail::collectError(error, refusals, locations, preconditions);
  visitErrors(error, [&](const ErrorInfoBase &info) {
    if (info.isA<frontend::SourceDiagnostic>()) {
      const auto &source =
          static_cast<const frontend::SourceDiagnostic &>(info);
      refusals.push_back({source.code, source.message});
      auto locate = [&](source::Span span) {
        const auto *input = project ? project->file(span.file) : nullptr;
        if (!input)
          return;
        auto prefix = input->text().take_front(span.offset);
        auto newline = prefix.rfind('\n');
        locations.push_back(
            {input->filename().str(), unsigned(prefix.count('\n') + 1),
             unsigned(newline == StringRef::npos ? prefix.size() + 1
                                                 : prefix.size() - newline)});
      };
      locate(source.location);
      for (const auto &related : source.related)
        if (related.location)
          locate(*related.location);
    }
  });
  return make_error<CompilationError>(toString(std::move(error)),
                                      std::move(refusals), std::move(locations),
                                      std::move(preconditions));
}
} // namespace
Expected<Compilation> compileProtocol(source::Document document,
                                      const ProtocolOptions &options,
                                      const DialectRegistry &registry) {
  if (auto e = protocol::checkImplementationSelection(
          options.physical.implementations, document.root()))
    return sourceCompilationError(std::move(e));
  auto result = std::make_unique<Compilation::Storage>(registry);
  result->source = std::move(document);
  const auto &source = *result->source;
  Diagnostics diagnostics(result->context);
  result->context.loadAllAvailableDialects();
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  std::optional<source::Content> specialized;
  const source::Content *closed = &source.root();
  if (source.module() && source.module()->isLibrary()) {
    const source::Node *failure = nullptr;
    auto elaborated = generic::elaborateLibrary(*source.module(), &failure);
    if (!elaborated)
      return sourceDiagnostic(source, elaborated.takeError(), failure);
    specialized = std::move(*elaborated);
    closed = &*specialized;
  }
  const source::Node *failure = nullptr;
  SourceLocations locations(source, result->context);
  auto imported = protocol::importModule(
      *closed, result->context,
      [&](const source::Node &node) { return locations(node); }, &failure);
  if (!imported)
    return diagnostics.failure(
        sourceDiagnostic(source, imported.takeError(), failure));
  result->module = std::move(*imported);
  if (options.action == ProtocolAction::Expand) {
    if (failed(protocol::expandAlgorithms(*result->module, &result->origins)))
      return diagnostics.failure(error("algorithm-expansion-failed"));
  } else if (options.action != ProtocolAction::Import) {
    PassManager pipeline(&result->context);
    buildParticipantPipeline(pipeline, options.physical,
                             options.action == ProtocolAction::Project,
                             &result->statistics);
    diagnostics.atRoot(result->module->getLoc());
    if (failed(pipeline.run(*result->module)))
      return diagnostics.failure();
  }
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  return Compilation(std::move(result));
}
Expected<Compilation> compileTable(const json::Value &source,
                                   const TableOptions &options,
                                   const DialectRegistry &registry) {
  const bool physical = options.action == TableAction::Lazy ||
                        options.action == TableAction::Materialized;
  if (options.simplify && !physical)
    return sourceCompilationError(error("simplification-requires-physical"));
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
  result->context.loadAllAvailableDialects();
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  auto imported = importSource(source, result->context);
  if (!imported)
    return diagnostics.failure(imported.takeError());
  result->module = std::move(*imported);
  if (options.action != TableAction::Import) {
    PassManager pipeline(&result->context);
    buildTablePipeline(pipeline, options.simplify,
                       options.action == TableAction::Lazy ? "lazy"
                       : options.action == TableAction::Materialized
                           ? "materialized"
                           : "");
    if (failed(pipeline.run(*result->module)))
      return diagnostics.failure();
  }
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  return Compilation(std::move(result));
}
Expected<ConstructedProtocol>
constructProtocol(const frontend::Analysis &analysis,
                  source::Construction descriptor,
                  const DialectRegistry &registry) {
  auto checked = analysis.checkedModule();
  if (!checked)
    return sourceCompilationError(checked.takeError(), analysis.project());
  auto bound = frontend::bindConstruction(*checked, std::move(descriptor));
  if (!bound)
    return sourceCompilationError(bound.takeError(), analysis.project());
  auto document = lowerSource(analysis);
  if (!document)
    return sourceCompilationError(document.takeError(), analysis.project());
  if (!document->module())
    return sourceCompilationError(error("construction-input-kind"));
  auto result = std::make_unique<Compilation::Storage>(registry);
  result->source = std::move(*document);
  Diagnostics diagnostics(result->context);
  result->context.loadAllAvailableDialects();
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  auto constructed =
      protocol::construct(*result->source->module(), *bound, result->context);
  if (!constructed)
    return diagnostics.failure(constructed.takeError());
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  result->module = std::move(constructed->module);
  return ConstructedProtocol{Compilation(std::move(result)),
                             std::move(constructed->certificate)};
}
} // namespace zkc

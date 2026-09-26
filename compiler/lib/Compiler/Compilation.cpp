#include "zkc/Compiler/Compilation.h"
#include "mlir/IR/Location.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Compiler/SourceLocations.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
char CompilationError::ID;
struct Compilation::Storage {
  MLIRContext context;
  std::optional<source::Document> source;
  OwningOpRef<ModuleOp> module;
  std::vector<protocol::AlgorithmOrigin> origins;
  LinearContractionStats statistics;
  explicit Storage(const DialectRegistry &registry) : context(registry) {
    DialectRegistry builtins;
    registerDialects(builtins);
    context.appendDialectRegistry(builtins);
    context.printOpOnDiagnostic(false);
  }
};
Compilation::Compilation(std::unique_ptr<Storage> value)
    : storage(std::move(value)) {}
Compilation::Compilation(Compilation &&) noexcept = default;
Compilation &Compilation::operator=(Compilation &&) noexcept = default;
Compilation::~Compilation() = default;
ModuleOp Compilation::module() const { return *storage->module; }
const source::Document *Compilation::source() const {
  return storage->source ? &*storage->source : nullptr;
}
ArrayRef<protocol::AlgorithmOrigin> Compilation::origins() const {
  return storage->origins;
}
const LinearContractionStats &Compilation::statistics() const {
  return storage->statistics;
}
namespace {
void collectError(const Error &error,
                  std::vector<diagnostics::RefusalInfo> &refusals,
                  std::vector<DiagnosticLocation> &locations,
                  const frontend::ProjectInput *project = nullptr) {
  visitErrors(error, [&](const ErrorInfoBase &info) {
    if (info.isA<Refusal>()) {
      const auto &refusal = static_cast<const Refusal &>(info);
      refusals.push_back({refusal.code, refusal.detail});
    } else if (info.isA<CompilationError>()) {
      const auto &compilation = static_cast<const CompilationError &>(info);
      llvm::append_range(refusals, compilation.refusals);
      llvm::append_range(locations, compilation.locations);
    } else if (info.isA<frontend::SourceDiagnostic>()) {
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
}
Error compilationError(Error error,
                       const frontend::ProjectInput *project = nullptr) {
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  collectError(error, refusals, locations, project);
  return make_error<CompilationError>(
      toString(std::move(error)), std::move(refusals), std::move(locations));
}
/// Collect diagnostics while their context lives. Do not recover codes from
/// prose. A module-level pass refusal keeps the CLI's unlocated rendering.
class Diagnostics {
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::optional<Location> root;
  bool sawError = false;
  ScopedDiagnosticHandler handler;

public:
  explicit Diagnostics(MLIRContext &context)
      : handler(&context, [&](Diagnostic &diagnostic) {
          // Match the default MLIR handler: warnings and remarks do not turn
          // a successful invocation into an error or leak to process stderr.
          if (diagnostic.getSeverity() != DiagnosticSeverity::Error)
            return success();
          sawError = true;
          if (!message.empty())
            message += '\n';
          raw_string_ostream out(message);
          if (!root || diagnostic.getLocation() != *root) {
            if (!isa<UnknownLoc>(diagnostic.getLocation())) {
              diagnostic.getLocation().print(out);
              out << ": ";
            }
            out << "error: ";
          }
          if (auto location =
                  diagnostic.getLocation()->findInstanceOf<FileLineColLoc>())
            locations.push_back({location.getFilename().str(),
                                 location.getLine(), location.getColumn()});
          diagnostic.print(out);
          for (auto &note : diagnostic.getNotes()) {
            out << '\n';
            if (!isa<UnknownLoc>(note.getLocation())) {
              note.getLocation().print(out);
              out << ": ";
            }
            out << "note: ";
            note.print(out);
            if (auto location =
                    note.getLocation()->findInstanceOf<FileLineColLoc>())
              locations.push_back({location.getFilename().str(),
                                   location.getLine(), location.getColumn()});
          }
          auto metadata = diagnostics::refusals(diagnostic);
          llvm::append_range(refusals, metadata);
          return success();
        }) {}
  void atRoot(Location location) { root = location; }
  bool hasErrors() const { return sawError; }
  Error failure(Error fallback = Error::success()) {
    if (fallback) {
      collectError(fallback, refusals, locations);
      if (!message.empty())
        message += '\n';
      message += toString(std::move(fallback));
    }
    if (message.empty())
      message = "pass pipeline failed without an error diagnostic";
    return make_error<CompilationError>(std::move(message), std::move(refusals),
                                        std::move(locations));
  }
};
} // namespace
Expected<Compilation> compileProtocol(source::Document document,
                                      const ProtocolOptions &options,
                                      const DialectRegistry &registry) {
  if (auto e = protocol::checkImplementationSelection(
          options.physical.implementations, document.root()))
    return compilationError(std::move(e));
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
    return compilationError(error("simplification-requires-physical"));
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
    return compilationError(checked.takeError(), analysis.project());
  auto bound = frontend::bindConstruction(*checked, std::move(descriptor));
  if (!bound)
    return compilationError(bound.takeError(), analysis.project());
  auto document = lowerSource(analysis);
  if (!document)
    return compilationError(document.takeError(), analysis.project());
  if (!document->module())
    return compilationError(error("construction-input-kind"));
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

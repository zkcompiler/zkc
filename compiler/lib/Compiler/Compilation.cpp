#include "zkc/Compiler/Compilation.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Compiler/SourceLocations.h"
#include "zkc/Dialect/Registry.h"
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
    context.loadAllAvailableDialects();
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
/// Collect diagnostics while their context lives. Do not recover codes from
/// prose. A module-level pass refusal keeps the CLI's unlocated rendering.
class Diagnostics {
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  std::optional<Location> root;
  ScopedDiagnosticHandler handler;

public:
  explicit Diagnostics(MLIRContext &context)
      : handler(&context, [&](Diagnostic &diagnostic) {
          // Match the default MLIR handler: warnings and remarks do not turn
          // a successful invocation into an error or leak to process stderr.
          if (diagnostic.getSeverity() != DiagnosticSeverity::Error)
            return success();
          if (!message.empty())
            message += '\n';
          raw_string_ostream out(message);
          if ((!root || diagnostic.getLocation() != *root) &&
              !isa<UnknownLoc>(diagnostic.getLocation())) {
            diagnostic.getLocation().print(out);
            out << ": ";
            switch (diagnostic.getSeverity()) {
            case DiagnosticSeverity::Error:
              out << "error: ";
              break;
            case DiagnosticSeverity::Warning:
              out << "warning: ";
              break;
            case DiagnosticSeverity::Remark:
              out << "remark: ";
              break;
            case DiagnosticSeverity::Note:
              out << "note: ";
              break;
            }
          }
          diagnostic.print(out);
          auto metadata = diagnostics::refusals(diagnostic);
          llvm::append_range(refusals, metadata);
          return success();
        }) {}
  void atRoot(Location location) { root = location; }
  Error failure(Error fallback = Error::success()) {
    if (message.empty())
      return fallback ? std::move(fallback)
                      : createStringError(
                            "pass pipeline failed without an error diagnostic");
    return joinErrors(
        make_error<CompilationError>(std::move(message), std::move(refusals)),
        std::move(fallback));
  }
};
} // namespace
Expected<Compilation> compileProtocol(source::Document document,
                                      const ProtocolOptions &options,
                                      const DialectRegistry &registry) {
  if (auto e = protocol::checkImplementationSelection(
          options.physical.implementations, document.root()))
    return e;
  auto result = std::make_unique<Compilation::Storage>(registry);
  result->source = std::move(document);
  const auto &source = *result->source;
  Diagnostics diagnostics(result->context);
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
  return Compilation(std::move(result));
}
Expected<Compilation> compileTable(const json::Value &source,
                                   const TableOptions &options,
                                   const DialectRegistry &registry) {
  const bool physical = options.action == TableAction::Lazy ||
                        options.action == TableAction::Materialized;
  if (options.simplify && !physical)
    return error("simplification-requires-physical");
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
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
  return Compilation(std::move(result));
}
} // namespace zkc

#include "zkc/Compiler/Compilation.h"
#include "NativeDeployment.h"
#include "Run.h"
#include "mlir/IR/Location.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Construction.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Compiler/Inspection.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Compiler/PolynomialReduction.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Compiler/SourceLocations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Compile.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Protocol.h"
#include "zkc/Translation/Table.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"

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
                  std::vector<InvocationPrecondition> &preconditions,
                  const frontend::ProjectInput *project = nullptr) {
  visitErrors(error, [&](const ErrorInfoBase &info) {
    if (info.isA<Refusal>()) {
      const auto &refusal = static_cast<const Refusal &>(info);
      refusals.push_back({refusal.code, refusal.detail});
    } else if (info.isA<CompilationError>()) {
      const auto &compilation = static_cast<const CompilationError &>(info);
      llvm::append_range(refusals, compilation.refusals);
      llvm::append_range(locations, compilation.locations);
      llvm::append_range(preconditions, compilation.invocationPreconditions);
    } else if (info.isA<DialectRegistrationError>()) {
      preconditions.push_back(
          static_cast<const DialectRegistrationError &>(info).precondition);
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
  std::vector<InvocationPrecondition> preconditions;
  collectError(error, refusals, locations, preconditions, project);
  return make_error<CompilationError>(toString(std::move(error)),
                                      std::move(refusals), std::move(locations),
                                      std::move(preconditions));
}
/// Collect diagnostics while their context lives. Do not recover codes from
/// prose. A module-level pass refusal keeps the CLI's unlocated rendering.
class Diagnostics {
  std::string message;
  std::vector<diagnostics::RefusalInfo> refusals;
  std::vector<DiagnosticLocation> locations;
  std::vector<InvocationPrecondition> preconditions;
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
      collectError(fallback, refusals, locations, preconditions);
      if (!message.empty())
        message += '\n';
      message += toString(std::move(fallback));
    }
    if (message.empty())
      message = "pass pipeline failed without an error diagnostic";
    return make_error<CompilationError>(std::move(message), std::move(refusals),
                                        std::move(locations),
                                        std::move(preconditions));
  }
};
Expected<OwningOpRef<ModuleOp>> parseNativeSource(StringRef text,
                                                  StringRef filename,
                                                  MLIRContext &context,
                                                  Diagnostics &diagnostics) {
  if (text.size() > 16 * 1024 * 1024 || filename.size() > 4096 ||
      !mlirNestingWithinLimit(text))
    return diagnostics.failure(error("run-input-limit"));
  context.loadAllAvailableDialects();
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  SourceMgr source;
  source.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(text, filename),
                            SMLoc());
  auto module = parseSourceFile<ModuleOp>(source, &context);
  if (!module || diagnostics.hasErrors())
    return diagnostics.failure();
  auto roots = module->getOps<protocol_ir::ProtocolModuleOp>();
  if (!llvm::hasSingleElement(roots) ||
      (*roots.begin()).getProfile() != protocol_ir::Profile::Protocol)
    return diagnostics.failure(error("run-source-profile"));
  diagnostics.atRoot(module->getLoc());
  return module;
}
LogicalResult lowerProgram(ModuleOp module, bool simplify, bool fixPolynomials,
                           bool releaseStorage,
                           LinearContractionStats &statistics) {
  PassManager pipeline(module.getContext());
  if (simplify)
    pipeline.addPass(protocol::createSimplifyParticipantPass());
  if (fixPolynomials)
    pipeline.addPass(protocol::createFixPolynomialFactorsPass());
  pipeline.addPass(protocol::createEliminatePolynomialsPass());
  pipeline.addPass(protocol::createLowerMathPass());
  pipeline.addPass(protocol::createSelectPhysicalPass({}, false, releaseStorage,
                                                      &statistics));
  return pipeline.run(module);
}
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
Expected<CompiledRun> compileRun(StringRef text, StringRef filename,
                                 const RunOptions &options,
                                 const DialectRegistry &registry) {
  if (text.size() > 16 * 1024 * 1024 || options.entry.empty() ||
      options.entry.size() > 4096 || filename.size() > 4096 ||
      !mlirNestingWithinLimit(text))
    return compilationError(error("run-input-limit"));
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
  auto parsed = parseNativeSource(text, filename, result->context, diagnostics);
  if (!parsed)
    return parsed.takeError();
  result->module = std::move(*parsed);
  std::optional<json::Value> publicCoin;
  if (options.publicCoinRequirement) {
    auto checked =
        analyzePublicCoin(*result->module, *options.publicCoinRequirement);
    if (!checked)
      return diagnostics.failure(checked.takeError());
    if (checked->getAsObject()->getString("entry") != options.entry)
      return diagnostics.failure(error("public-coin-interface"));
    publicCoin = std::move(*checked);
  }
  PassManager pipeline(&result->context);
  // Freeze the source before helper expansion. Checked candidates are projected
  // without folding, checked once, and then lowered in this same invocation.
  std::optional<json::Value> correspondence;
  OwningOpRef<ModuleOp> original;
  if (options.polynomialRequirements)
    original = cast<ModuleOp>(result->module->getOperation()->clone());
  pipeline.addPass(protocol::createPrepareProtocolPass(false));
  if (failed(pipeline.run(*result->module)) || diagnostics.hasErrors())
    return diagnostics.failure();
  auto prepared = OwningOpRef<ModuleOp>(
      cast<ModuleOp>(result->module->getOperation()->clone()));
  pipeline.clear();
  pipeline.addPass(protocol::createProjectProtocolPass(
      !options.polynomialRequirements && options.simplify));
  if (failed(pipeline.run(*result->module)) || diagnostics.hasErrors())
    return diagnostics.failure();
  pipeline.clear();
  if (options.polynomialRequirements) {
    auto checked = checkPolynomialReductions(*original, *result->module,
                                             *options.polynomialRequirements);
    if (!checked)
      return diagnostics.failure(checked.takeError());
    bool covered = false;
    for (auto &item : *checked->getAsObject()->getArray("requirements")) {
      auto &record = *item.getAsObject();
      covered |= record.getString("reduction") == options.entry ||
                 record.getString("terminal") == options.entry;
      if (auto *composition = record.getObject("composition"))
        covered |= composition->getString("entry") == options.entry;
    }
    if (!covered)
      return diagnostics.failure(error("polynomial-correspondence-entry"));
    correspondence = std::move(*checked);
  }
  if (failed(lowerProgram(*result->module, options.simplify,
                          options.fixPolynomialFactors, options.releaseStorage,
                          result->statistics)) ||
      diagnostics.hasErrors())
    return diagnostics.failure();
  auto bundle =
      detail::buildRunBundle(*prepared, *result->module, options.entry);
  if (!bundle)
    return diagnostics.failure(bundle.takeError());
  if (diagnostics.hasErrors())
    return diagnostics.failure();
  std::optional<std::string> report;
  if (correspondence) {
    auto digest = [](StringRef value) {
      return llvm::toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
    };
    auto &object = *correspondence->getAsObject();
    object["source_sha256"] = digest(text);
    object["requirements_input_sha256"] =
        digest(*options.polynomialRequirements);
    object["bundle_sha256"] = digest(*bundle);
    object["entry"] = options.entry;
    object["simplify"] = options.simplify;
    object["release_storage"] = options.releaseStorage;
    object["fix_polynomial_factors"] = options.fixPolynomialFactors;
    json::Array passes;
    if (options.simplify) {
      passes.push_back("zkc-simplify-participant");
    }
    if (options.fixPolynomialFactors)
      passes.push_back("zkc-fix-polynomial-factors");
    passes.push_back("zkc-eliminate-polynomials");
    passes.push_back("zkc-lower-math");
    passes.push_back("zkc-select-physical");
    object["post_check_passes"] = std::move(passes);
    // Bind every checked entry from the same final module, including a
    // composed caller when a standalone component is the selected output.
    json::Object hashes;
    hashes[options.entry] = digest(*bundle);
    for (auto &item : *object.getArray("requirements")) {
      auto &record = *item.getAsObject();
      SmallVector<StringRef> entries{*record.getString("reduction"),
                                     *record.getString("terminal")};
      if (auto *composition = record.getObject("composition"))
        entries.push_back(*composition->getString("entry"));
      for (StringRef entry : entries) {
        if (hashes.get(entry))
          continue;
        auto companion =
            detail::buildRunBundle(*prepared, *result->module, entry);
        if (!companion)
          return diagnostics.failure(companion.takeError());
        hashes[entry.str()] = digest(*companion);
      }
    }
    object["bundles_sha256"] = std::move(hashes);
    report.emplace();
    raw_string_ostream(*report) << *correspondence;
  }
  std::optional<std::string> viewReport;
  if (publicCoin) {
    auto digest = [](StringRef value) {
      return llvm::toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
    };
    json::Value record(
        json::Object{{"format", "zkc.compiled-public-coin/1"},
                     {"view", std::move(*publicCoin)},
                     {"source_sha256", digest(text)},
                     {"bundle_sha256", digest(*bundle)},
                     {"simplify", options.simplify},
                     {"release_storage", options.releaseStorage},
                     {"fix_polynomial_factors", options.fixPolynomialFactors}});
    json::Array passes;
    passes.push_back("zkc-project-protocol");
    if (options.simplify)
      passes.push_back("zkc-simplify-participant");
    if (options.fixPolynomialFactors)
      passes.push_back("zkc-fix-polynomial-factors");
    passes.push_back("zkc-eliminate-polynomials");
    passes.push_back("zkc-lower-math");
    passes.push_back("zkc-select-physical");
    (*record.getAsObject())["post_analysis_passes"] = std::move(passes);
    (*record.getAsObject())["projection_simplify"] =
        !options.polynomialRequirements && options.simplify;
    viewReport.emplace();
    raw_string_ostream(*viewReport) << record;
  }
  return CompiledRun{Compilation(std::move(result)), std::move(*bundle),
                     std::move(report), std::move(viewReport)};
}
Expected<CompiledNativeProof>
compileNativeProof(StringRef text, StringRef filename,
                   const NativeProofOptions &options,
                   const DialectRegistry &registry) {
  auto result = std::make_unique<Compilation::Storage>(registry);
  Diagnostics diagnostics(result->context);
  auto policy = parseNativeProofPolicy(options.policy);
  if (!policy)
    return diagnostics.failure(policy.takeError());
  auto parsed = parseNativeSource(text, filename, result->context, diagnostics);
  if (!parsed)
    return parsed.takeError();
  auto original = std::move(*parsed);
  auto constructed = constructNativeProof(*original, *policy);
  if (!constructed)
    return diagnostics.failure(constructed.takeError());
  result->module = std::move(constructed->module);
  if (failed(lowerProgram(*result->module, options.simplify, false,
                          options.releaseStorage, result->statistics)) ||
      diagnostics.hasErrors())
    return diagnostics.failure();
  auto exported = protocol::exportModule(*result->module);
  if (!exported)
    return diagnostics.failure(exported.takeError());
  auto candidate = printJson(*exported);
  if (candidate.size() > 1024 * 1024)
    return diagnostics.failure(error("native-proof-candidate-limit"));
  auto root = *result->module->getOps<protocol_ir::ProtocolModuleOp>().begin();
  auto projection =
      *root.getBody().front().getOps<protocol_ir::ProjectionOp>().begin();
  auto interface = cast<DictionaryAttr>(projection.getInterfaces()[0]);
  auto type =
      cast<FunctionType>(interface.getAs<TypeAttr>("original_type").getValue());
  json::Array maps;
  for (auto item : interface.getAs<ArrayAttr>("participants")) {
    auto port = cast<DictionaryAttr>(item);
    json::Array inputs, outputs, services;
    auto data = [&](ArrayAttr ports, bool input, json::Array &out) -> Error {
      for (auto value : ports) {
        auto index = cast<IntegerAttr>(value).getInt();
        auto logical = protocol::encodeBoundType(
            input ? type.getInput(index) : type.getResult(index), false);
        if (!logical)
          return logical.takeError();
        out.push_back(json::Array{std::to_string(index), logical->spelling()});
      }
      return Error::success();
    };
    if (auto e = data(port.getAs<ArrayAttr>("inputs"), true, inputs))
      return diagnostics.failure(std::move(e));
    if (auto e = data(port.getAs<ArrayAttr>("outputs"), false, outputs))
      return diagnostics.failure(std::move(e));
    auto role = port.getAs<StringAttr>("role").str();
    auto participant =
        cast<protocol_ir::ParticipantOp>(SymbolTable::lookupSymbolIn(
            root, port.getAs<FlatSymbolRefAttr>("participant")));
    auto installed = participant->getAttrOfType<ArrayAttr>("service_ports");
    unsigned serviceIndex = 0;
    for (auto input : port.getAs<ArrayAttr>("service_inputs")) {
      auto originalInput = cast<IntegerAttr>(input).getInt();
      if (policy->service == originalInput)
        continue;
      // Projection verification owns the service map. Serialize its installed
      // names and ingress indices instead of reconstructing generated names.
      auto service = cast<ArrayAttr>(installed[serviceIndex++]);
      services.push_back(json::Array{
          std::to_string(originalInput), cast<StringAttr>(service[0]).str(),
          cast<StringAttr>(service[1]).str(),
          std::to_string(cast<IntegerAttr>(service[2]).getInt())});
    }
    std::string acceptance;
    if (role == policy->validator)
      for (auto [i, originalOutput] :
           llvm::enumerate(port.getAs<ArrayAttr>("outputs")))
        if (cast<IntegerAttr>(originalOutput).getInt() == policy->acceptance)
          acceptance = std::to_string(i);
    maps.push_back(json::Array{
        role, port.getAs<FlatSymbolRefAttr>("participant").getValue().str(),
        std::move(inputs), std::move(outputs), std::move(services),
        std::move(acceptance)});
  }
  auto descriptorBytes = encodeLogicalTree(constructed->descriptor);
  if (!descriptorBytes)
    return diagnostics.failure(descriptorBytes.takeError());
  auto digest = [](StringRef bytes) {
    return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  };
  json::Value deployment(json::Array{
      "zkc.native-proof/" + std::to_string(policy->version), digest(text),
      constructed->descriptor, digest(*descriptorBytes), candidate,
      digest(candidate), std::move(maps),
      json::Array{options.simplify ? "true" : "false",
                  options.releaseStorage ? "true" : "false"},
      json::Array(constructed->wireSites)});
  auto encoded = printJson(deployment);
  if (encoded.size() > 16 * 1024 * 1024)
    return diagnostics.failure(error("native-proof-deployment-limit"));
  if (auto e = detail::verifyNativeDeployment(
          *original, *result->module, text, *policy, options,
          constructed->descriptor, constructed->wireSites, encoded))
    return diagnostics.failure(std::move(e));
  return CompiledNativeProof{Compilation(std::move(result)),
                             std::move(encoded)};
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

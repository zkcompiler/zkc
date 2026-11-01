#include "zkc/Compiler/Language.h"
#include "LanguageDiagnostics.h"
#include "LanguageInterface.h"
#include "SourceView.h"
#include "mlir/AsmParser/AsmParser.h"
#include "mlir/AsmParser/AsmParserState.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/VCSRevision.h"
#include <algorithm>
#include <map>
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
constexpr StringLiteral filename = "zkc-language-original.mlir";
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
void frame(std::string &out, StringRef value) {
  uint64_t size = value.size();
  for (unsigned i = 0; i < 8; ++i)
    out.push_back(static_cast<char>(size >> (8 * i)));
  out.append(value.data(), value.size());
}
class SourceCoordinates {
  const ClosedEntry &entry;
  std::vector<std::vector<unsigned>> lines;

public:
  explicit SourceCoordinates(const ClosedEntry &entry) : entry(entry) {
    for (const auto &source : entry.project().sources()) {
      std::vector<unsigned> offsets{0};
      for (unsigned i = 0; i < source.text.size(); ++i)
        if (source.text[i] == '\n')
          offsets.push_back(i + 1);
      lines.push_back(std::move(offsets));
    }
  }
  DiagnosticLocation location(Span span) const {
    const auto &source = entry.project().sources()[span.source.index];
    const auto &offsets = lines[span.source.index];
    auto line = std::upper_bound(offsets.begin(), offsets.end(), span.begin);
    unsigned number = line - offsets.begin();
    return {source.diagnosticPath.empty() ? source.module
                                          : source.diagnosticPath,
            number, unsigned(span.begin - *(line - 1) + 1)};
  }
};
void attachDeclaration(const ClosedEntry &entry, mlir::ModuleOp module,
                       std::vector<DiagnosticLocation> &locations,
                       std::string &diagnostics) {
  std::set<std::string> declarations;
  std::set<std::pair<unsigned, unsigned>> coordinates;
  for (const auto &location : locations)
    if (location.filename == filename)
      coordinates.emplace(location.line, location.column);
  SourceCoordinates source(entry);
  module.walk([&](mlir::Operation *op) {
    auto loc = mlir::dyn_cast<mlir::FileLineColLoc>(op->getLoc());
    if (!loc || !coordinates.count({loc.getLine(), loc.getColumn()}))
      return;
    for (auto *parent = op; parent; parent = parent->getParentOp()) {
      auto symbol = parent->getAttrOfType<mlir::StringAttr>("sym_name");
      if (symbol) {
        declarations.insert(symbol.getValue().str());
        break;
      }
    }
  });
  for (const auto &decl : entry.declarations())
    if (declarations.erase(decl.relation ? formulaSymbol(decl) : decl.symbol) ||
        declarations.erase(decl.symbol)) {
      diagnostics += "related source declaration: " + decl.qualifiedName + "\n";
      locations.push_back(source.location(decl.span));
    }
}

} // namespace
struct CheckedOriginal::Storage {
  explicit Storage(ClosedEntry entry) : selected(std::move(entry)) {}
  ClosedEntry selected;
  std::unique_ptr<mlir::MLIRContext> context;
  std::unique_ptr<SourceMgr> sourceManager;
  std::unique_ptr<mlir::AsmParserState> parser;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  std::string identity, interface, toolchain, locationsIdentity;
  Correspondence report;
  LanguageInterface interfaceView;
  Limits limits;
};
const Limits &CheckedOriginal::admissionLimits() const {
  return storage->limits;
}
std::string compilerToolchainIdentity() {
  static const std::string identity = [] {
    std::string material;
    frame(material, "zkc.language-toolchain");
    frame(material, installedCatalogIdentity());
    frame(material, ZKC_BUILD_ID);
    frame(material, ZKC_LLVM_VERSION);
#ifdef LLVM_REVISION
    frame(material, LLVM_REVISION);
#else
    frame(material, "revision-unavailable");
#endif
    return digest(material);
  }();
  return identity;
}
Expected<NativeProofPolicy> proofPolicy(const CheckedOriginal &original) {
  const auto &view = original.interface();
  if (!view.proof || view.host)
    return error("source.entry", "expected a checked proof Entry");
  const auto &protocol = view.selectedProtocol();
  const auto &proof = *view.proof;
  NativeProofPolicy policy;
  policy.entry = protocol.symbol;
  policy.producer = nativeRoleName(proof.prover);
  policy.validator = nativeRoleName(proof.verifier);
  policy.acceptance = proof.acceptance.native.front();
  policy.suite = proof.suite;
  policy.construction = proof.selectedConstruction;
  policy.format = proof.format;
  for (const auto &gate : proof.gates) {
    std::string site;
    for (const auto &part : gate.path) {
      auto label = nativeSiteName(part, 0);
      site = site.empty() ? label
                          : mathematical::expandedApplicationSite(site, label);
    }
    policy.gates.emplace_back(std::move(site), gate.bits);
  }
  for (auto service : proof.services)
    policy.services.push_back(protocol.services[service].native);
  for (auto index : proof.publicInputs)
    append_range(policy.publicInputs, protocol.inputs[index].native);
  return policy;
}
Expected<CheckedOriginal> prepareOriginal(const ClosedEntry &entry,
                                          const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  context.printOpOnDiagnostic(false);
  auto emitted = emitOriginal(entry, context, limits);
  if (!emitted)
    return emitted.takeError();
  auto encoded = detail::emitInterface(entry, digest(*emitted),
                                       compilerToolchainIdentity(), limits);
  if (!encoded)
    return encoded.takeError();
  return CheckedOriginal::admit(entry, *emitted, *encoded, limits, false);
}
Expected<CheckedOriginal> admitOriginal(const ClosedEntry &entry,
                                        StringRef original, StringRef interface,
                                        const Limits &limits) {
  return CheckedOriginal::admit(entry, original, interface, limits, true);
}
Expected<CheckedOriginal> CheckedOriginal::admit(const ClosedEntry &entry,
                                                 StringRef original,
                                                 StringRef interface,
                                                 const Limits &limits,
                                                 bool requireCanonical) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (original.size() > limits.irBytes ||
      interface.size() > limits.interfaceBytes ||
      !mlirNestingWithinLimit(original))
    return error("source.limit", "original or interface limit exceeded");
  if (!json::isUTF8(original))
    return error("target.admission", "original is not UTF-8");
  auto parsedInterface = detail::parseInterface(interface, limits);
  if (!parsedInterface)
    return parsedInterface.takeError();
  mlir::DialectRegistry registry;
  registerDialects(registry);
  auto ownedContext = std::make_unique<mlir::MLIRContext>(
      registry, mlir::MLIRContext::Threading::DISABLED);
  auto &context = *ownedContext;
  context.loadAllAvailableDialects();
  context.printOpOnDiagnostic(false);
  std::string diagnostics;
  std::vector<DiagnosticLocation> locations;
  mlir::ScopedDiagnosticHandler handler(
      &context, [&](mlir::Diagnostic &diagnostic) {
        raw_string_ostream stream(diagnostics);
        diagnostic.print(stream);
        stream << '\n';
        diagnostic.getLocation()->walk([&](mlir::Location location) {
          if (auto loc = mlir::dyn_cast<mlir::FileLineColLoc>(location))
            locations.push_back(
                {loc.getFilename().str(), loc.getLine(), loc.getColumn()});
          return mlir::WalkResult::advance();
        });
        return mlir::success();
      });
  auto ownedManager = std::make_unique<SourceMgr>();
  auto &manager = *ownedManager;
  manager.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(original, filename),
                             SMLoc());
  // Parsing verifies syntax only; whole-module admission runs once below.
  mlir::ParserConfig config(&context, false);
  auto parser = std::make_unique<mlir::AsmParserState>();
  mlir::Block parsed;
  mlir::OwningOpRef<mlir::ModuleOp> module;
  if (mlir::succeeded(
          mlir::parseAsmSourceFile(manager, &parsed, config, parser.get())))
    module =
        mlir::detail::constructContainerOpForParserIfNecessary<mlir::ModuleOp>(
            &parsed, &context,
            mlir::FileLineColLoc::get(&context, filename, 1, 1));
  if (!module)
    return make_error<CompilationError>(
        diagnostics,
        std::vector<diagnostics::RefusalInfo>{
            {"target.parse", "original failed target parsing"}},
        std::move(locations));
  // Admission refusals and refusals reported as diagnostics on the original
  // gain its locations and related source declarations.
  auto located = [&](Error failure, bool diagnosed = false) -> Error {
    return handleErrors(
        std::move(failure), [&](const Refusal &refusal) -> Error {
          if (!diagnosed && refusal.code != "target.admission" &&
              refusal.code != "source.limit")
            return error(refusal.code, refusal.detail);
          attachDeclaration(entry, *module, locations, diagnostics);
          diagnostics += refusal.code + ": " + refusal.detail + "\n";
          return make_error<CompilationError>(
              diagnostics,
              std::vector<diagnostics::RefusalInfo>{
                  {refusal.code, refusal.detail}},
              std::move(locations));
        });
  };
  auto compared = compareOriginal(entry, *module, limits);
  if (!compared)
    return located(compared.takeError());
  uint64_t remaining = limits.work;
  auto checkMathematics = [&](mlir::ModuleOp subject) -> Error {
    return mathematical::checkFormulaDefinitions(subject, remaining);
  };
  if (entry.entry().kind == Declaration::Kind::EntryFunction) {
    for (auto numeric : module->getOps<mlir::ModuleOp>()) {
      auto copy = mlir::OwningOpRef<mlir::ModuleOp>(
          mlir::cast<mlir::ModuleOp>(numeric->clone()));
      copy->getOperation()->removeAttr("entry.calculation");
      if (auto e = checkMathematics(*copy))
        return located(std::move(e), true);
    }
  } else if (auto e = checkMathematics(*module))
    return located(std::move(e), true);
  auto storage = std::make_shared<CheckedOriginal::Storage>(entry);
  storage->limits = limits;
  storage->report = std::move(*compared);
  storage->identity = digest(original);
  storage->toolchain = compilerToolchainIdentity();
  storage->interface = interface.str();
  std::string mapIdentity;
  frame(mapIdentity, "zkc.language-locations");
  frame(mapIdentity, entry.project().capture().identity());
  frame(mapIdentity, storage->identity);
  for (const auto &location : storage->report.locations) {
    for (uint64_t value :
         {uint64_t(location.line), uint64_t(location.column),
          uint64_t(location.source.source.index),
          uint64_t(location.source.begin), uint64_t(location.source.end)}) {
      for (unsigned i = 0; i < 8; ++i)
        mapIdentity.push_back(static_cast<char>(value >> (i * 8)));
    }
  }
  storage->locationsIdentity = digest(mapIdentity);
  auto interfaceView =
      detail::decodeInterface(*module, storage->identity, *parsedInterface,
                              limits, entry.project().assets());
  if (!interfaceView)
    return interfaceView.takeError();
  if (auto error = compareInterface(entry, *interfaceView, limits))
    return std::move(error);
  if (requireCanonical) {
    // Independent formation and correspondence above establish meaning. This
    // final filter fixes binding names, declaration order and source locations
    // as well as spelling; reprinting the candidate alone would not do so.
    auto canonical = emitOriginal(entry, context, limits);
    if (!canonical)
      return canonical.takeError();
    if (original != *canonical)
      return error("source.correspondence",
                   "original encoding is not canonical");
    auto encoded = detail::emitInterface(entry, storage->identity,
                                         storage->toolchain, limits);
    if (!encoded)
      return encoded.takeError();
    if (interface != *encoded)
      return error("source.interface", "interface encoding is not canonical");
  }
  storage->interfaceView = std::move(*interfaceView);
  // Retained immutable originals may be read concurrently. Clones still share
  // MLIR's uniqued types/attributes, so their context must support those
  // readers.
  context.enableMultithreading();
  storage->context = std::move(ownedContext);
  storage->sourceManager = std::move(ownedManager);
  storage->parser = std::move(parser);
  storage->module = std::move(module);
  return CheckedOriginal(std::move(storage));
}
mlir::OwningOpRef<mlir::ModuleOp>
detail::OriginalAccess::clone(const CheckedOriginal &original,
                              mlir::IRMapping *mapping) {
  auto source = original.storage->module.get();
  return mlir::OwningOpRef<mlir::ModuleOp>(mlir::cast<mlir::ModuleOp>(
      mapping ? source->clone(*mapping) : source->clone()));
}
Expected<protocol::SourceView>
detail::OriginalAccess::read(const CheckedOriginal &original) {
  if (!original.entry().protocolOrNull())
    return error("source.entry", "structured source requires a protocol");
  const auto &storage = *original.storage;
  mlir::IRMapping mapping;
  auto copy = clone(original, &mapping);
  llvm::DenseMap<mlir::Operation *, mlir::Operation *> written;
  storage.module.get()->walk([&](mlir::Operation *op) {
    if (auto *copy = mapping.lookupOrNull(op))
      written[copy] = op;
  });
  auto result = protocol::readSourceView(
      std::move(copy), original.bytes(), original.entry().protocol().symbol,
      storage.parser.get(), storage.sourceManager.get(), &written);
  if (!result)
    return result.takeError();
  result->originalOwner = original;
  return std::move(*result);
}
const ClosedEntry &CheckedOriginal::entry() const { return storage->selected; }
StringRef CheckedOriginal::bytes() const {
  const auto &manager = *storage->sourceManager;
  return manager.getMemoryBuffer(manager.getMainFileID())->getBuffer();
}
StringRef CheckedOriginal::identity() const { return storage->identity; }
StringRef CheckedOriginal::interfaceJson() const { return storage->interface; }
const LanguageInterface &CheckedOriginal::interface() const {
  return storage->interfaceView;
}
StringRef CheckedOriginal::toolchain() const { return storage->toolchain; }
StringRef CheckedOriginal::locationsIdentity() const {
  return storage->locationsIdentity;
}
ArrayRef<SourceLocation> CheckedOriginal::locations() const {
  return storage->report.locations;
}
const Correspondence &CheckedOriginal::correspondence() const {
  return storage->report;
}
Error locateCompilationFailure(const CheckedOriginal &original, Error error) {
  return handleErrors(
      std::move(error),
      [&](const CompilationError &failure) -> Error {
        auto locations = failure.locations;
        SourceCoordinates source(original.entry());
        std::map<std::pair<unsigned, unsigned>, Span> mapping;
        for (const auto &record : original.locations())
          mapping.emplace(std::make_pair(record.line, record.column),
                          record.source);
        bool mapped = false;
        for (auto &location : locations)
          if (location.filename == filename) {
            auto found = mapping.find({location.line, location.column});
            if (found != mapping.end()) {
              location = source.location(found->second);
              mapped = true;
            }
          }
        if (!mapped)
          locations.push_back(source.location(original.entry().entry().span));
        return make_error<CompilationError>(failure.message, failure.refusals,
                                            std::move(locations),
                                            failure.invocationPreconditions);
      },
      [&](const Refusal &failure) -> Error {
        return make_error<DiagnosticError>(Diagnostic{
            failure.code, failure.detail, original.entry().entry().span, {}});
      });
}
} // namespace zkc::language

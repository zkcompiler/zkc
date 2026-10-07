#include "zkc/Compiler/Language.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Diagnostics.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/VCSRevision.h"
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
DiagnosticLocation sourceSpan(const ClosedEntry &entry, Span span) {
  const auto &source = entry.project().capture().sources()[span.module.index];
  unsigned line = 1, column = 1;
  for (unsigned i = 0; i < span.begin; ++i) {
    if (source.text[i] == '\n') {
      ++line;
      column = 1;
    } else
      ++column;
  }
  return {source.diagnosticPath.empty() ? source.module : source.diagnosticPath,
          line, column};
}
std::optional<DiagnosticLocation>
sourceLocation(const ClosedEntry &entry, ArrayRef<SourceLocation> locations,
               unsigned line, unsigned column) {
  auto found = llvm::find_if(locations, [&](const auto &position) {
    return position.line == line && position.column == column;
  });
  if (found == locations.end())
    return {};
  return sourceSpan(entry, found->source);
}
void attachDeclaration(const ClosedEntry &entry, mlir::ModuleOp module,
                       std::vector<DiagnosticLocation> &locations,
                       std::string &diagnostics) {
  std::set<std::string> declarations;
  module.walk([&](mlir::Operation *op) {
    auto loc = mlir::dyn_cast<mlir::FileLineColLoc>(op->getLoc());
    if (!loc || !llvm::any_of(locations, [&](const auto &position) {
          return position.filename == filename &&
                 position.line == loc.getLine() &&
                 position.column == loc.getColumn();
        }))
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
    if (declarations.count(decl.symbol)) {
      diagnostics += "related source declaration: " + decl.qualifiedName + "\n";
      locations.push_back(sourceSpan(entry, decl.span));
    }
}
Error writeInterface(json::OStream &out, BoundedStream &stream,
                     const ClosedEntry &entry, StringRef original,
                     StringRef toolchain, const Limits &limits) {
  const auto &protocol = entry.protocol();
  Layouts layouts(entry, limits);
  std::vector<std::shared_ptr<const Layout>> inputs, outputs;
  for (bool input : {true, false})
    for (auto &port : input ? protocol.inputs : protocol.outputs) {
      auto layout = layouts.get(port.type);
      if (!layout)
        return layout.takeError();
      (input ? inputs : outputs).push_back(*layout);
    }
  uint64_t remaining = limits.work;
  bool limited = false;
  auto charge = [&](uint64_t work) {
    if (limited || stream.overflow() || work > remaining) {
      limited = true;
      return false;
    }
    remaining -= work;
    return true;
  };
  std::function<void(const Layout &)> schema;
  schema = [&](const Layout &layout) {
    if (!charge(1)) {
      out.value(nullptr);
      return;
    }
    out.object([&] {
      out.attribute("type", spelling(layout.type));
      out.attribute("custody", layout.custody);
      out.attributeArray("permissions", [&] {
        if (layout.permissions.copy)
          out.value("Copy");
        if (layout.permissions.drop)
          out.value("Drop");
        if (layout.permissions.share)
          out.value("Share");
        if (layout.permissions.wire)
          out.value("Wire");
      });
      auto fields = [&](ArrayRef<LayoutField> fields) {
        for (auto &field : fields) {
          if (!charge(field.name.size() + 1))
            break;
          out.object([&] {
            out.attribute("name", field.name);
            out.attribute("offset", field.offset);
            out.attributeBegin("schema");
            schema(*field.layout);
            out.attributeEnd();
          });
        }
      };
      out.attributeArray("fields", [&] { fields(layout.fields); });
      out.attributeArray("alternatives", [&] {
        for (auto &alternative : layout.alternatives) {
          if (!charge(alternative.name.size() + 1))
            break;
          out.object([&] {
            out.attribute("name", alternative.name);
            out.attributeArray("fields", [&] { fields(alternative.fields); });
          });
        }
      });
      out.attributeArray("leaves", [&] {
        for (auto &leaf : layout.leaves) {
          if (!charge(leaf.size() + 1))
            break;
          out.value(leaf);
        }
      });
    });
  };
  auto ports = [&](StringRef name, ArrayRef<Port> source,
                   ArrayRef<std::shared_ptr<const Layout>> layouts) {
    unsigned flat = 0;
    out.attributeArray(name, [&] {
      for (unsigned i = 0; i < source.size(); ++i) {
        if (!charge(source[i].name.size() + 1))
          break;
        out.object([&] {
          out.attribute("name", source[i].name);
          out.attribute("type", spelling(source[i].type));
          out.attributeArray("roles", [&] {
            for (unsigned role : source[i].roles)
              out.value(protocol.roles[role]);
          });
          out.attribute("index", i);
          out.attributeArray("native", [&] {
            for (unsigned j = 0; j < layouts[i]->leaves.size(); ++j)
              out.value(flat++);
          });
          out.attributeBegin("schema");
          schema(*layouts[i]);
          out.attributeEnd();
        });
      }
    });
  };
  out.object([&] {
    out.attribute("format", "zkc.language-interface/2");
    out.attribute("capture", entry.project().capture().identity());
    out.attribute("original", original);
    out.attribute("toolchain", toolchain);
    out.attribute("entry", entry.entry().qualifiedName);
    out.attribute("protocol", protocol.symbol);
    out.attributeArray("roles", [&] {
      for (const auto &role : protocol.roles)
        out.value(role);
    });
    ports("inputs", protocol.inputs, inputs);
    ports("outputs", protocol.outputs, outputs);
  });
  if (limited || stream.overflow())
    return error("source.limit", "interface traversal or byte limit exceeded");
  return Error::success();
}
} // namespace
struct CheckedOriginal::Storage {
  explicit Storage(ClosedEntry entry) : selected(std::move(entry)) {}
  ClosedEntry selected;
  std::string original;
  std::string identity, interface, toolchain, locationsIdentity;
  Correspondence report;
};
std::string compilerToolchainIdentity() {
  std::string material;
  frame(material, "zkc.language-toolchain/1");
  frame(material, installedCatalogIdentity());
  frame(material, ZKC_BUILD_ID);
  frame(material, ZKC_LLVM_VERSION);
#ifdef LLVM_REVISION
  frame(material, LLVM_REVISION);
#else
  frame(material, "revision-unavailable");
#endif
  return digest(material);
}
Expected<CheckedOriginal> prepareOriginal(const ClosedEntry &entry,
                                          const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  mlir::DialectRegistry registry;
  registerNativeDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  context.printOpOnDiagnostic(false);
  auto emitted = emitOriginal(entry, context, limits);
  if (!emitted)
    return emitted.takeError();
  if (!mlirNestingWithinLimit(*emitted))
    return error("source.limit", "original exceeds MLIR nesting limit");
  std::string diagnostics;
  std::vector<DiagnosticLocation> locations;
  mlir::ScopedDiagnosticHandler handler(
      &context, [&](mlir::Diagnostic &diagnostic) {
        raw_string_ostream stream(diagnostics);
        diagnostic.print(stream);
        stream << '\n';
        if (auto loc = mlir::dyn_cast<mlir::FileLineColLoc>(
                diagnostic.getLocation())) {
          locations.push_back({filename.str(), loc.getLine(), loc.getColumn()});
        }
        return mlir::success();
      });
  SourceMgr manager;
  manager.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(*emitted, filename),
                             SMLoc());
  // Parsing verifies syntax only; whole-module admission runs once below.
  mlir::ParserConfig config(&context, false);
  auto module = mlir::parseSourceFile<mlir::ModuleOp>(manager, config);
  if (!module)
    return make_error<CompilationError>(
        diagnostics,
        std::vector<diagnostics::RefusalInfo>{
            {"target.parse", "emitted original failed target parsing"}},
        std::move(locations));
  auto compared = compareOriginal(entry, *module, limits);
  if (!compared) {
    auto failure = compared.takeError();
    return handleErrors(
        std::move(failure), [&](const Refusal &refusal) -> Error {
          if (refusal.code != "target.admission")
            return error(refusal.code, refusal.detail);
          attachDeclaration(entry, *module, locations, diagnostics);
          return make_error<CompilationError>(
              diagnostics,
              std::vector<diagnostics::RefusalInfo>{
                  {refusal.code, refusal.detail}},
              std::move(locations));
        });
  }
  auto storage = std::make_shared<CheckedOriginal::Storage>(entry);
  storage->original = std::move(*emitted);
  storage->report = std::move(*compared);
  storage->identity = digest(storage->original);
  storage->toolchain = compilerToolchainIdentity();
  BoundedStream stream(storage->interface, limits.interfaceBytes);
  json::OStream interface(stream);
  if (auto error = writeInterface(interface, stream, entry, storage->identity,
                                  storage->toolchain, limits))
    return std::move(error);
  if (stream.overflow())
    return error("source.limit", "source interface byte limit exceeded");
  std::string mapIdentity;
  frame(mapIdentity, "zkc.language-locations/1");
  frame(mapIdentity, entry.project().capture().identity());
  frame(mapIdentity, storage->identity);
  for (const auto &location : storage->report.locations) {
    for (uint64_t value :
         {uint64_t(location.line), uint64_t(location.column),
          uint64_t(location.source.module.index),
          uint64_t(location.source.begin), uint64_t(location.source.end)}) {
      for (unsigned i = 0; i < 8; ++i)
        mapIdentity.push_back(static_cast<char>(value >> (i * 8)));
    }
  }
  storage->locationsIdentity = digest(mapIdentity);
  CheckedOriginal original(std::move(storage));
  if (auto failure = checkInterface(original, original.interfaceJson(), limits))
    return std::move(failure);
  return original;
}
const ClosedEntry &CheckedOriginal::entry() const { return storage->selected; }
StringRef CheckedOriginal::bytes() const { return storage->original; }
StringRef CheckedOriginal::identity() const { return storage->identity; }
StringRef CheckedOriginal::interfaceJson() const { return storage->interface; }
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
Expected<CompiledEntry> compileEntry(const CheckedOriginal &original,
                                     const EntryRunOptions &options) {
  RunOptions run;
  run.entry = original.entry().protocol().symbol;
  run.simplify = options.simplify;
  run.releaseStorage = options.releaseStorage;
  auto compiled =
      compileRun(original.bytes(), filename, run, mlir::DialectRegistry());
  if (!compiled) {
    auto error = compiled.takeError();
    return handleErrors(
        std::move(error), [&](const CompilationError &failure) -> Error {
          auto locations = failure.locations;
          for (auto &location : locations)
            if (location.filename == filename) {
              auto source =
                  sourceLocation(original.entry(), original.locations(),
                                 location.line, location.column);
              if (source)
                location = std::move(*source);
            }
          return make_error<CompilationError>(failure.message, failure.refusals,
                                              std::move(locations),
                                              failure.invocationPreconditions);
        });
  }
  auto bundle = json::parse(compiled->bundle);
  if (!bundle)
    return bundle.takeError();
  auto *object = bundle->getAsObject();
  if (!object ||
      object->getString("entry") != original.entry().protocol().symbol)
    return error("source.entry", "compiled bundle selected another protocol");
  return CompiledEntry(original, std::move(*compiled));
}
} // namespace zkc::language

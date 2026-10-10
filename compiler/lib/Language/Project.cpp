#include "Checker.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Relation.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ConvertUTF.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language {
#include "Prelude.inc"
char DiagnosticError::ID;
DiagnosticError::DiagnosticError(Diagnostic diagnostic)
    : value(std::move(diagnostic)) {}
void DiagnosticError::log(raw_ostream &out) const {
  out << value.code << ": " << value.message;
}
std::error_code DiagnosticError::convertToErrorCode() const {
  return inconvertibleErrorCode();
}

namespace {
std::optional<StringRef> exceededLimit(const Limits &limits,
                                       const Limits &ceiling) {
#define CHECK_LIMIT(name)                                                      \
  if (limits.name > ceiling.name)                                              \
  return StringRef(#name)
  CHECK_LIMIT(files);
  CHECK_LIMIT(fileBytes);
  CHECK_LIMIT(captureBytes);
  CHECK_LIMIT(assetBytes);
  CHECK_LIMIT(assetTotalBytes);
  CHECK_LIMIT(tokens);
  CHECK_LIMIT(tokenBytes);
  CHECK_LIMIT(identifierBytes);
  CHECK_LIMIT(moduleBytes);
  CHECK_LIMIT(parseDepth);
  CHECK_LIMIT(expressionDepth);
  CHECK_LIMIT(importDepth);
  CHECK_LIMIT(callDepth);
  CHECK_LIMIT(declarations);
  CHECK_LIMIT(operations);
  CHECK_LIMIT(work);
  CHECK_LIMIT(irBytes);
  CHECK_LIMIT(symbolBytes);
  CHECK_LIMIT(notationDescriptors);
  CHECK_LIMIT(notationHoles);
  CHECK_LIMIT(notationInspectionBytes);
  CHECK_LIMIT(interfaceBytes);
  CHECK_LIMIT(locationBytes);
  CHECK_LIMIT(typeDepth);
  CHECK_LIMIT(typeNodes);
  CHECK_LIMIT(instances);
  CHECK_LIMIT(aggregateLeaves);
  CHECK_LIMIT(naturalTerms);
  CHECK_LIMIT(naturalFactors);
#undef CHECK_LIMIT
  return {};
}
} // namespace
bool Limits::covers(const Limits &other) const {
  return !exceededLimit(other, *this);
}
Error checkLimits(const Limits &limits) {
  if (auto name = exceededLimit(limits, Limits{}))
    return detail::failure("source.limit",
                           "cannot raise " + *name + " ceiling");
  return Error::success();
}
namespace detail {
Error failure(StringRef code, const Twine &message, std::optional<Span> span,
              std::vector<Span> related) {
  return make_error<DiagnosticError>(
      Diagnostic{code.str(), message.str(), span, std::move(related)});
}
std::optional<Diagnostic> diagnose(Error error, std::optional<Span> fallback) {
  std::optional<Diagnostic> result;
  handleAllErrors(
      std::move(error),
      [&](const DiagnosticError &e) {
        if (!result) {
          result = e.diagnostic();
          if (!result->primary)
            result->primary = fallback;
        }
      },
      [&](const Refusal &e) {
        if (!result)
          result = Diagnostic{e.code, e.detail, fallback, {}};
      },
      [&](const ErrorInfoBase &e) {
        if (!result)
          result = Diagnostic{"source.internal", e.message(), fallback, {}};
      });
  return result;
}
bool isUnsupported(StringRef name) {
  static const std::set<StringRef> words = {
      "service", "predicate", "requires", "construct", "while", "extern"};
  return words.count(name);
}
bool isReserved(StringRef name) {
  static const std::set<StringRef> words = {
      "module", "use",       "pub",       "domain",    "field",        "group",
      "math",   "fn",        "protocol",  "roles",     "let",          "return",
      "send",   "bool",      "true",      "false",     "index",        "type",
      "struct", "enum",      "interface", "component", "where",        "nat",
      "mut",    "if",        "else",      "max",       "match",        "for",
      "in",     "drop",      "consume",   "require",   "stop",         "opaque",
      "Type",   "Field",     "Group",     "Copy",      "Drop",         "Share",
      "Wire",   "completes", "finish_if", "builtin",   "kernel",       "pow2",
      "formal", "intrinsic", "relation",  "spec",      "construction", "map",
      "each"};
  return words.count(name) || isUnsupported(name);
}
bool isIdentifier(StringRef name) { return isSourceIdentifier(name); }

bool isPath(StringRef path, const Limits &limits) {
  if (path.empty() || path.size() > limits.moduleBytes)
    return false;
  SmallVector<StringRef> parts;
  path.split(parts, "::");
  return llvm::all_of(parts, [&](StringRef part) {
    return part.size() <= limits.identifierBytes && isIdentifier(part) &&
           !isReserved(part);
  });
}
std::string digest(StringRef value) {
  return toHex(SHA256::hash(arrayRefFromStringRef(value)), true);
}
void frame(std::string &out, StringRef value) {
  uint64_t size = value.size();
  for (unsigned i = 0; i != 8; ++i)
    out.push_back(static_cast<char>(size >> (i * 8)));
  out.append(value.data(), value.size());
}
Error Work::charge(uint64_t amount, std::optional<Span> span) {
  if (amount > limits.work - used)
    return failure("source.limit", "checked work limit exceeded", span);
  used += amount;
  return Error::success();
}
Error Work::count(uint64_t &counter, uint64_t limit, StringRef what,
                  std::optional<Span> span) {
  if (counter >= limit)
    return failure("source.limit", what + " limit exceeded", span);
  ++counter;
  return Error::success();
}
static Error checkSources(ArrayRef<SourceBuffer> sources,
                          ArrayRef<AssetBuffer> assets, const Limits &limits) {
  if (sources.empty())
    return failure("source.capture",
                   "capture must contain at least one module");
  if (sources.size() > limits.files ||
      assets.size() > limits.files - sources.size())
    return failure("source.limit", "file count limit exceeded");
  uint64_t total = 0;
  std::set<StringRef> names;
  for (const auto &source : sources) {
    if (source.origin != SourceOrigin::Captured ||
        source.module == "zkc::prelude")
      return failure("source.module",
                     "zkc::prelude is reserved for installation sources");
    if (source.diagnosticPath.size() > 4096)
      return failure("source.limit", "diagnostic path byte limit exceeded");
    if (source.text.size() > limits.fileBytes ||
        source.text.size() > limits.captureBytes - total)
      return failure("source.limit", "source byte limit exceeded");
    total += source.text.size();
    if (!isPath(source.module, limits))
      return failure("source.module",
                     "invalid logical module path: " + source.module);
    if (!names.insert(source.module).second)
      return failure("source.module",
                     "duplicate logical module: " + source.module);
    const auto *begin = reinterpret_cast<const UTF8 *>(source.text.data());
    if (!isLegalUTF8String(&begin, begin + source.text.size()))
      return failure("source.encoding",
                     "source is not valid UTF-8: " + source.module);
  }
  names.clear();
  total = 0;
  for (const auto &asset : assets) {
    if (asset.diagnosticPath.size() > 4096 ||
        asset.bytes.size() > limits.assetBytes ||
        asset.bytes.size() > limits.assetTotalBytes - total)
      return failure("source.limit", "captured asset byte limit exceeded");
    total += asset.bytes.size();
    if (!llvm::all_of(asset.name,
                      [](unsigned char byte) { return byte < 128; }) ||
        !isPath(asset.name, limits) || !names.insert(asset.name).second)
      return failure("source.asset",
                     "invalid or duplicate captured asset name");
    if (asset.format != "r1cs-json" && asset.format != "r1cs-binary" &&
        asset.format != "air-json" && asset.format != "ring-json" &&
        asset.format != "relation-bundle-json")
      return failure("source.asset", "unknown captured asset format");
  }
  return Error::success();
}
} // namespace detail

Expected<CapturedProject> capture(std::vector<SourceBuffer> sources,
                                  const CaptureOptions &options) {
  return capture(std::move(sources), {}, options);
}
Expected<CapturedProject> capture(std::vector<SourceBuffer> sources,
                                  std::vector<AssetBuffer> assets,
                                  const CaptureOptions &options) {
  if (auto error = checkLimits(options.limits))
    return std::move(error);
  if (options.format != "zkc")
    return detail::failure("source.format",
                           "expected explicit source format 'zkc'");
  if (auto error = detail::checkSources(sources, assets, options.limits))
    return std::move(error);
  std::sort(sources.begin(), sources.end(),
            [](const auto &a, const auto &b) { return a.module < b.module; });
  std::sort(assets.begin(), assets.end(),
            [](const auto &a, const auto &b) { return a.name < b.name; });
  auto storage = std::make_shared<detail::CaptureStorage>();
  storage->assets = std::move(assets);
  storage->sources = std::move(sources);
  storage->format = options.format;
  std::string identity;
  detail::frame(identity, "zkc.capture");
  detail::frame(identity, options.format);
  detail::frame(identity, std::to_string(storage->sources.size()));
  for (const auto &source : storage->sources) {
    detail::frame(identity, source.module);
    detail::frame(identity, source.text);
  }
  detail::frame(identity, std::to_string(storage->assets.size()));
  for (const auto &asset : storage->assets) {
    detail::frame(identity, asset.name);
    detail::frame(identity, asset.format);
    detail::frame(identity, asset.bytes);
  }
  storage->identity = detail::digest(identity);
  return CapturedProject(std::move(storage));
}
CapturedProject::CapturedProject(
    std::shared_ptr<const detail::CaptureStorage> storage)
    : storage(std::move(storage)) {}
ArrayRef<SourceBuffer> CapturedProject::sources() const {
  return storage->sources;
}
ArrayRef<AssetBuffer> CapturedProject::assets() const {
  return storage->assets;
}
StringRef CapturedProject::identity() const { return storage->identity; }
StringRef CapturedProject::format() const { return storage->format; }
CheckedProject::CheckedProject(
    std::shared_ptr<const detail::CheckedStorage> storage)
    : storage(std::move(storage)) {}
const CapturedProject &CheckedProject::capture() const {
  return storage->capture;
}
ArrayRef<SourceBuffer> CheckedProject::sources() const {
  return *storage->sources;
}
ArrayRef<SourceBuffer> Analysis::sources() const { return *storage->sources; }
ArrayRef<Asset> CheckedProject::assets() const { return storage->assets; }
ArrayRef<Declaration> CheckedProject::declarations() const {
  return storage->declarations;
}
ArrayRef<Token> CheckedProject::tokens(ModuleId id) const {
  return id.index < storage->tokens.size()
             ? ArrayRef<Token>(storage->tokens[id.index])
             : ArrayRef<Token>();
}
StringRef CheckedProject::installationIdentity() const {
  return storage->installation;
}
uint64_t CheckedProject::checkedNotationDescriptors() const {
  return storage->notationDescriptors;
}
uint64_t CheckedProject::checkedNotationHoles() const {
  return storage->notationHoles;
}
uint64_t CheckedProject::checkedWork() const { return storage->work; }
uint64_t CheckedProject::checkedDeclarations() const {
  return storage->declarationCount;
}
uint64_t CheckedProject::checkedOperations() const {
  return storage->operationCount;
}
Analysis::Analysis(std::shared_ptr<const detail::AnalysisStorage> storage)
    : storage(std::move(storage)) {}
ArrayRef<Diagnostic> Analysis::diagnostics() const {
  return storage->diagnostics;
}
ArrayRef<Token> Analysis::tokens(ModuleId id) const {
  return id.index < storage->tokens.size()
             ? ArrayRef<Token>(storage->tokens[id.index])
             : ArrayRef<Token>();
}
Expected<CheckedProject> Analysis::checkedProject() const {
  if (storage->checked)
    return *storage->checked;
  if (!storage->diagnostics.empty())
    return make_error<DiagnosticError>(storage->diagnostics.front());
  return detail::failure("source.unchecked",
                         "analysis did not produce a checked project");
}
Analysis analyze(const CapturedProject &capture, const Limits &limits) {
  auto output = std::make_shared<detail::AnalysisStorage>();
  auto checked = std::make_shared<detail::CheckedStorage>(capture);
  auto sources = std::make_shared<std::vector<SourceBuffer>>(
      capture.sources().begin(), capture.sources().end());
  sources->push_back({"zkc::prelude", installedPrelude,
                      "<installation>/zkc/prelude.zkc",
                      SourceOrigin::Installation});
  checked->sources = sources;
  output->sources = sources;
  detail::Work work{limits};
  auto run = [&]() -> Error {
    if (auto error = checkLimits(limits))
      return error;
    if (auto error =
            detail::checkSources(capture.sources(), capture.assets(), limits))
      return error;
    // Each existing reader has its own structural/work bounds. Aggregate input
    // bytes and file counts are checked before any asset parsing or allocation.
    for (const auto &asset : capture.assets()) {
      auto value = Asset::read(asset);
      if (!value)
        return detail::failure("source.asset", "in " + asset.name + ": " +
                                                   toString(value.takeError()));
      checked->assets.push_back(std::move(*value));
    }
    checked->tokens.resize(sources->size());
    std::vector<detail::SyntaxModule> modules;
    for (unsigned i = 0; i < sources->size(); ++i) {
      if (auto error =
              detail::lex((*sources)[i], ModuleId{i}, work, checked->tokens[i]))
        return error;
      auto syntax =
          detail::parse((*sources)[i], ModuleId{i}, checked->tokens[i], work);
      if (!syntax)
        return syntax.takeError();
      modules.push_back(std::move(*syntax));
    }
    if (auto error = detail::check(std::move(modules), *checked, work))
      return error;
    checked->installation = installedCatalogIdentity();
    checked->work = work.used;
    checked->declarationCount = work.declarations;
    checked->operationCount = work.operations;
    checked->notationDescriptors = work.notationDescriptors;
    checked->notationHoles = work.notationHoles;
    output->checked = CheckedProject(checked);
    return Error::success();
  };
  if (auto diagnostic = detail::diagnose(run()))
    output->diagnostics.push_back(std::move(*diagnostic));
  output->tokens = checked->tokens;
  return Analysis(std::move(output));
}
Expected<std::string> encodeSymbol(StringRef path, const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  // A declaration path has one additional identifier beyond its module path.
  if (path.size() > limits.moduleBytes + limits.identifierBytes + 2)
    return detail::failure("source.limit", "qualified name limit exceeded");
  SmallVector<StringRef> parts;
  path.split(parts, "::");
  for (auto part : parts) {
    if (part.size() > limits.identifierBytes || !detail::isIdentifier(part) ||
        detail::isReserved(part))
      return detail::failure("source.name", "invalid qualified name");
  }
  auto symbol = encodeSourceSymbol(path, limits.symbolBytes);
  if (!symbol)
    return detail::failure("source.limit", "symbol byte limit exceeded");
  return *symbol;
}
std::vector<DeclarationId> CheckedProject::entries() const {
  std::vector<DeclarationId> result;
  for (const auto &decl : declarations())
    if (decl.kind == Declaration::Kind::Entry)
      result.push_back(decl.id);
  llvm::sort(result, [&](DeclarationId a, DeclarationId b) {
    return declarations()[a.index].qualifiedName <
           declarations()[b.index].qualifiedName;
  });
  return result;
}
Expected<DeclarationId> selectEntry(const CheckedProject &project,
                                    StringRef name, const Limits &limits,
                                    std::optional<EntryKind> kind) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (name.size() > limits.moduleBytes + limits.identifierBytes + 2)
    return detail::failure("source.limit", "Entry name byte limit exceeded");
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedNotationDescriptors() > limits.notationDescriptors ||
      project.checkedNotationHoles() > limits.notationHoles)
    return detail::failure("source.limit",
                           "checked project exceeds requested limits");
  auto eligible = [&](DeclarationId id) {
    return !kind || project.declarations()[id.index].entryKind() == *kind;
  };
  auto selected = [&](DeclarationId id) -> Expected<DeclarationId> {
    if (!eligible(id))
      return detail::failure("source.entry-kind",
                             "selected Entry has the wrong execution kind",
                             project.declarations()[id.index].span);
    return id;
  };
  if (name.contains("::")) {
    for (const auto &decl : project.declarations())
      if (decl.qualifiedName == name) {
        if (decl.kind != Declaration::Kind::Entry)
          return detail::failure("source.entry",
                                 "selection must name an Entry declaration",
                                 decl.span);
        return selected(decl.id);
      }
  }
  auto candidates = project.entries();
  std::vector<DeclarationId> matches;
  for (auto id : candidates)
    if (name.empty() ? eligible(id)
                     : project.declarations()[id.index].name == name)
      matches.push_back(id);
  if (matches.size() == 1)
    return selected(matches.front());
  if (candidates.empty())
    return detail::failure("source.entry",
                           "project has no Entries; declare run or proof");
  std::string message;
  if (matches.empty() && name.empty())
    message = "no Entry of the required execution kind; available Entries:";
  else if (matches.empty())
    message = "unknown Entry: " + name.str() + "; available Entries:";
  else if (name.empty())
    message = "multiple Entries; select one by name. Candidates:";
  else
    message = "ambiguous Entry: " + name.str() +
              "; specify a qualified name. Matches:";
  unsigned shown = 0;
  for (auto id : matches.empty() ? candidates : matches) {
    if (shown++ == 16) {
      message +=
          "; further candidates omitted; use check to inspect all Entries";
      break;
    }
    const auto &decl = project.declarations()[id.index];
    message += " " + decl.qualifiedName + " (" +
               (decl.entryKind() == EntryKind::Proof ? "proof" : "run") + ")";
  }
  return detail::failure("source.entry", message);
}
Expected<ClosedEntry> closeEntry(const CheckedProject &project, StringRef name,
                                 const Limits &limits,
                                 std::optional<EntryKind> kind) {
  auto selected = selectEntry(project, name, limits, kind);
  if (!selected)
    return selected.takeError();
  const auto &decl = project.declarations()[selected->index];
  detail::Work work{limits};
  // Metadata is bounded by definition checking. Immutable template bodies
  // are shared; specialization starts with its own phase budget.
  auto storage = std::make_shared<detail::ClosedStorage>();
  storage->declarations.assign(project.declarations().begin(),
                               project.declarations().end());
  if (auto error = detail::specialize(storage->declarations, project.assets(),
                                      work, decl.id))
    return error;
  storage->protocol = *storage->declarations[decl.id.index].target;
  if (auto error = detail::closeAssets(project, *storage, work))
    return error;
  ClosedEntry entry(project, decl.id, std::move(storage));
  Layouts layouts(entry, limits);
  if (auto error = detail::checkSetups(entry, layouts, work))
    return error;
  std::function<Error(const Body &)> checkMessages =
      [&](const Body &body) -> Error {
    for (const auto &op : body.operations) {
      if (auto e = work.charge(1, op.span))
        return e;
      if (auto *exchange = std::get_if<Exchange>(&op.action)) {
        auto layout = layouts.get(body.values[exchange->payload.index].type);
        if (!layout)
          return layout.takeError();
        if ((*layout)->formal)
          return detail::failure(
              "source.formal", "message cannot contain formal values", op.span);
        if ((*layout)->leaves.empty())
          return detail::failure("source.wire",
                                 "message requires a nonempty native payload",
                                 op.span);
      }
      if (auto *repeat = std::get_if<ProtocolRepeat>(&op.action))
        if (auto e = checkMessages(*repeat->region))
          return e;
    }
    return Error::success();
  };
  for (const auto &definition : entry.declarations()) {
    if (definition.body)
      if (auto e = checkMessages(*definition.body))
        return std::move(e);
    if (definition.relation && definition.origin)
      for (const auto &port : definition.inputs) {
        auto layout = layouts.get(port.type);
        if (!layout)
          return layout.takeError();
        if (!(*layout)->permissions.copy || !(*layout)->permissions.drop)
          return detail::failure("source.relation",
                                 "relation inputs require immutable data",
                                 port.span);
        if ((*layout)->leaves.empty())
          return detail::failure(
              "source.relation",
              "relation formal requires a nonempty data layout", port.span);
        for (const auto &leaf : (*layout)->leaves) {
          if (!leaf.data())
            return detail::failure(
                "source.relation",
                "relation formal cannot contain formal mathematics", port.span);
          protocol::TypeParseBudget budget;
          budget.remaining =
              std::min<uint64_t>(budget.remaining, limits.work - work.used);
          auto before = budget.remaining;
          auto native =
              protocol::parseBoundType(*leaf.data(), false, 0, &budget);
          if (!native) {
            consumeError(native.takeError());
            return detail::failure(
                budget.remaining ? "source.relation" : "source.limit",
                "relation native type admission failed", port.span);
          }
          auto result = protocol::logicalRelationData(*native, budget);
          if (auto error = work.charge(before - budget.remaining + leaf.cost(),
                                       port.span))
            return error;
          if (result == protocol::RelationData::Limit)
            return detail::failure("source.limit",
                                   "relation data work or depth limit exceeded",
                                   port.span);
          if (result != protocol::RelationData::Supported)
            return detail::failure(
                "source.relation",
                "relation formal is not immutable logical data", port.span);
        }
      }
  }
  return entry;
}

const Declaration &ClosedEntry::entry() const {
  return storage->declarations[selected.index];
}
const Declaration &ClosedEntry::protocol() const {
  return storage->declarations[storage->protocol.index];
}
ArrayRef<Asset> ClosedEntry::assets() const { return storage->assets; }
ArrayRef<Declaration> ClosedEntry::declarations() const {
  return storage->declarations;
}

std::string installedCatalogIdentity() {
  // Rows are length framed and sorted. The compiler build stamp separately
  // binds executable checking rules and the complete compiled installation.
  std::vector<std::string> rows;
  auto row = [&](std::initializer_list<StringRef> fields) {
    std::string value;
    for (auto field : fields)
      detail::frame(value, field);
    rows.push_back(std::move(value));
  };
  row({"source-name-profile", sourceNameProfileIdentity()});
  row({"prelude", "zkc::prelude", detail::digest(installedPrelude)});
  const auto &catalog = protocol::installedDomains();
  for (const auto &domain : catalog.allDomains()) {
    row({"domain", domain.identity, domain.sort, domain.modulus,
         catalog.defaultProvider(domain.identity)});
    for (const auto &associated : domain.associated)
      row({"associated", domain.identity, associated.member,
           associated.identity});
    for (const auto &capability : domain.capabilities)
      row({"capability", domain.identity, capability});
  }
  for (const auto &codec : catalog.allCodecs())
    row({"codec", codec.identity, codec.kind, codec.domain});
  for (const auto &type : catalog.allLogicalTypes())
    row({"logical", type.kind, type.domain});
  for (const auto &rep : catalog.allRepresentations())
    row({"representation", rep.identity, rep.kind, rep.domain, rep.layout,
         rep.isDefault ? "default" : "explicit"});
  for (const auto &intrinsic : mathematicalIntrinsics())
    row({"mathematical-intrinsic", intrinsic.name,
         std::to_string(static_cast<unsigned>(intrinsic.identity)),
         std::to_string(intrinsic.naturals),
         intrinsic.domainPoints ? "domain" : "none",
         intrinsic.domain == MathematicalIntrinsic::Domain::Boolean ? "bool"
         : intrinsic.domain == MathematicalIntrinsic::Domain::Group ? "group"
                                                                    : "field",
         intrinsic.scalar ? "scalar" : "intrinsic"});
  for (const auto &kernel : protocol::kernels()) {
    std::string value;
    detail::frame(value, "kernel");
    detail::frame(value, kernel.key);
    detail::frame(value, std::to_string(kernel.inputs.size()));
    for (const auto &input : kernel.inputs)
      detail::frame(value, input);
    detail::frame(value, std::to_string(kernel.outputs.size()));
    for (const auto &output : kernel.outputs)
      detail::frame(value, output);
    const auto *parameters = protocol::parameterContract(kernel.key);
    detail::frame(value, parameters ? "present" : "absent");
    if (parameters) {
      detail::frame(
          value, std::to_string(static_cast<unsigned>(parameters->validator)));
      detail::frame(value, std::to_string(parameters->minimum));
      detail::frame(value, parameters->maximum
                               ? std::to_string(*parameters->maximum)
                               : "none");
      detail::frame(value, parameters->fieldTerm
                               ? std::to_string(*parameters->fieldTerm)
                               : "none");
      detail::frame(value, parameters->assetFormat);
    }
    rows.push_back(std::move(value));
  }
  for (const auto &service : protocol::randomServices)
    for (StringRef method : {"draw", "index"})
      if (auto signature = protocol::serviceMethod(service.contract, method)) {
        std::string value;
        for (StringRef field :
             {StringRef("service"), StringRef(service.contract), method})
          detail::frame(value, field);
        for (const auto &input : signature->inputs)
          detail::frame(value, input);
        detail::frame(value, signature->output);
        rows.push_back(std::move(value));
      }
  std::sort(rows.begin(), rows.end());
  std::string bytes;
  detail::frame(bytes, "zkc.language-catalog");
  for (const auto &row : rows)
    detail::frame(bytes, row);
  return detail::digest(bytes);
}
std::string logicalOrigin(const ClosedEntry &entry, const Declaration &decl) {
  const auto &symbol = decl.origin
                           ? entry.declarations()[decl.origin->index].symbol
                           : decl.symbol;
  return symbol.size() <= 128 ? symbol : "zkl_origin_" + detail::digest(symbol);
}
std::string formulaSymbol(const Declaration &decl) {
  return relation::formulaSymbol(decl.symbol);
}
} // namespace zkc::language

#include "Checker.h"
#include "CommonRequirements.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/Relation.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/EntryBoundary.h"
#include "zkc/Language/Layout.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ConvertUTF.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>

using namespace llvm;
namespace zkc::language {
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
  CHECK_LIMIT(apiInspectionBytes);
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
  static const std::set<StringRef> words = {"service", "predicate", "construct",
                                            "while", "extern"};
  return words.count(name);
}
bool isReserved(StringRef name) {
  static const std::set<StringRef> words = {
      "module",    "use",       "pub",        "domain",   "field",
      "group",     "math",      "fn",         "protocol", "roles",
      "let",       "return",    "send",       "bool",     "true",
      "false",     "index",     "type",       "struct",   "enum",
      "interface", "where",     "nat",        "mut",      "if",
      "else",      "max",       "match",      "for",      "in",
      "drop",      "consume",   "require",    "stop",     "opaque",
      "Type",      "Field",     "Group",      "Copy",     "Drop",
      "completes", "finish_if", "builtin",    "kernel",   "pow2",
      "formal",    "intrinsic", "relation",   "spec",     "construction",
      "map",       "each",      "OracleKind", "requires"};
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
  if (cancellation && cancellation->cancelled())
    return failure("source.cancelled", "source analysis cancelled", span);
  if (amount > remaining())
    return failure(
        "source.limit",
        "checked work limit exceeded in " + sourceWorkPhaseName(phase), span);
  used += amount;
  ledger.total += amount;
  ledger.phases[static_cast<size_t>(phase)] += amount;
  if (allowance)
    *allowance -= amount;
  return Error::success();
}
Error chargeSemanticIndex(const std::vector<Declaration> &declarations,
                          Work &work) {
  if (auto e = work.charge(declarations.size() + 1))
    return e;
  for (const auto &decl : declarations) {
    if (auto e = work.charge(
            decl.qualifiedName.size() + decl.parameters.size() + 1, decl.span))
      return e;
    for (const auto &parameter : decl.parameters)
      if (auto e = work.charge(parameter.atom.size() + 1, parameter.span))
        return e;
  }
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
        (source.module == "zkc" || source.module == "zkc::prelude" ||
         source.module == "zkc::records"))
      return failure("source.module", "zkc, zkc::prelude and zkc::records are "
                                      "reserved for installation sources");
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
  if (options.format != "zkc" && options.format != "zkc-layout")
    return detail::failure(
        "source.format",
        "expected explicit source format 'zkc' or 'zkc-layout'");
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
ArrayRef<PendingSpecification> CheckedProject::pendingSpecifications() const {
  return storage->pendingSpecifications;
}
ArrayRef<Token> CheckedProject::tokens(SourceId id) const {
  return id.index < storage->tokens.size()
             ? ArrayRef<Token>(storage->tokens[id.index])
             : ArrayRef<Token>();
}
const DeclarationIndex &CheckedProject::declarationIndex() const {
  return *storage->declarationIndex;
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
StringRef sourceWorkPhaseName(SourceWorkPhase phase) {
  switch (phase) {
  case SourceWorkPhase::Unscoped:
    return "unscoped";
  case SourceWorkPhase::Parsing:
    return "parsing";
  case SourceWorkPhase::InstalledDeclarations:
    return "installed_declarations";
  case SourceWorkPhase::WrittenRetention:
    return "written_retention";
  case SourceWorkPhase::Declarations:
    return "declarations";
  case SourceWorkPhase::Signatures:
    return "signatures";
  case SourceWorkPhase::Conformance:
    return "conformance";
  case SourceWorkPhase::Representations:
    return "representations";
  case SourceWorkPhase::Permissions:
    return "permissions";
  case SourceWorkPhase::Bodies:
    return "bodies";
  case SourceWorkPhase::CommonInputs:
    return "common_inputs";
  case SourceWorkPhase::EntriesAndClaims:
    return "entries_and_claims";
  case SourceWorkPhase::RetainedViews:
    return "retained_views";
  case SourceWorkPhase::ScopedSources:
    return "scoped_sources";
  case SourceWorkPhase::SourceAuthorities:
    return "source_authorities";
  case SourceWorkPhase::EntrySelection:
    return "entry_selection";
  case SourceWorkPhase::Specialization:
    return "specialization";
  case SourceWorkPhase::Assets:
    return "assets";
  case SourceWorkPhase::ClosedData:
    return "closed_data";
  case SourceWorkPhase::HostChildren:
    return "host_children";
  case SourceWorkPhase::ScopedElaboration:
    return "scoped_elaboration";
  case SourceWorkPhase::ScopedSpecialization:
    return "scoped_specialization";
  case SourceWorkPhase::Count:
    break;
  }
  llvm_unreachable("invalid source work phase");
}
uint64_t CheckedProject::checkedWork() const { return storage->work; }
const SourceWorkObservation &CheckedProject::workObservation() const {
  return storage->workObservation;
}
const SourceWorkObservation &Analysis::workObservation() const {
  return storage->workObservation;
}
const SourceWorkObservation &ClosedEntry::workObservation() const {
  return storage->workObservation;
}
uint64_t ClosedEntry::closedWork() const { return storage->work; }
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
ArrayRef<Token> Analysis::tokens(SourceId id) const {
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
Analysis analyze(const CapturedProject &capture, const Limits &limits,
                 source::Cancellation cancellation) {
  auto output = std::make_shared<detail::AnalysisStorage>();
  auto checked = std::make_shared<detail::CheckedStorage>(
      capture, installedCatalogIdentity());
  auto sources = std::make_shared<std::vector<SourceBuffer>>(
      capture.sources().begin(), capture.sources().end());
  // Installed modules are catalog rows with no written text.
  for (const auto &module : detail::installedModules())
    sources->push_back({module, "", "<installation>/catalog/" + module,
                        SourceOrigin::Installation});
  checked->sources = sources;
  output->sources = sources;
  detail::Work work{limits};
  work.cancellation = cancellation;
  detail::Work::Scope phase(work, SourceWorkPhase::Parsing);
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
    checked->layoutHeaders.resize(sources->size());
    checked->layoutBodies.resize(sources->size());
    std::vector<detail::SyntaxDeclaration> modules;
    for (unsigned i = 0; i < sources->size(); ++i) {
      if ((*sources)[i].origin == SourceOrigin::Installation) {
        detail::Work::Scope installedPhase(
            work, SourceWorkPhase::InstalledDeclarations);
        auto installed =
            detail::readInstalledModule((*sources)[i], SourceId{i}, work);
        if (!installed)
          return installed.takeError();
        modules.push_back(std::move(*installed));
        continue;
      }
      if (capture.format() == "zkc-layout" &&
          (*sources)[i].origin == SourceOrigin::Captured) {
        auto syntax = detail::parseLayoutHeaders((*sources)[i], SourceId{i},
                                                 *checked, work);
        if (!syntax)
          return syntax.takeError();
        modules.push_back(std::move(*syntax));
        continue;
      }
      if (auto error =
              detail::lex((*sources)[i], SourceId{i}, work, checked->tokens[i]))
        return error;
      auto syntax =
          detail::parse((*sources)[i], SourceId{i}, checked->tokens[i], work);
      if (!syntax)
        return syntax.takeError();
      modules.push_back(std::move(*syntax));
    }
    if (auto error =
            detail::check(std::move(modules), *checked, work, output.get()))
      return error;
    if (!output->diagnostics.empty())
      return Error::success();
    checked->work = work.used;
    checked->workObservation.charged = work.ledger;
    checked->declarationCount = work.declarations;
    checked->operationCount = work.operations;
    checked->notationDescriptors = work.notationDescriptors;
    checked->notationHoles = work.notationHoles;
    output->checked = CheckedProject(checked);
    return Error::success();
  };
  if (auto diagnostic = detail::diagnose(run()))
    output->diagnostics.push_back(std::move(*diagnostic));
  output->workObservation.charged = work.ledger;
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
    if (decl.kind == Declaration::Kind::Entry ||
        (decl.kind == Declaration::Kind::EntryFunction &&
         decl.parameters.empty()))
      result.push_back(decl.id);
  llvm::sort(result, [&](DeclarationId a, DeclarationId b) {
    return declarations()[a.index].entryName() <
           declarations()[b.index].entryName();
  });
  return result;
}
Expected<EntrySelection>
resolveEntry(const CheckedProject &project, StringRef name,
             const Limits &limits, std::optional<EntryKind> kind,
             std::vector<SourceWorkBudget> *observations) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (name.size() > 4096 ||
      (!name.contains('<') &&
       name.size() > limits.moduleBytes + limits.identifierBytes + 2))
    return detail::failure("source.limit",
                           "Entry selector byte limit exceeded");
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations ||
      project.checkedNotationDescriptors() > limits.notationDescriptors ||
      project.checkedNotationHoles() > limits.notationHoles)
    return detail::failure("source.limit",
                           "checked project exceeds requested limits");
  if (name.contains('<')) {
    detail::Work work{limits};
    detail::Work::Scope phase(work, SourceWorkPhase::EntrySelection);
    detail::Work::Record record(work, SourceWorkPhase::EntrySelection,
                                observations);
    auto syntax = detail::parseEntrySelector(name, work);
    if (!syntax)
      return syntax.takeError();
    // Reuse completed source signatures and the actual import namespaces.
    // Template bodies and source buffers remain shared and immutable.
    detail::CheckedStorage scope(project.capture(),
                                 project.installationIdentity().str());
    if (auto error = work.charge(project.declarations().size()))
      return std::move(error);
    scope.declarations.assign(project.declarations().begin(),
                              project.declarations().end());
    scope.assets.assign(project.assets().begin(), project.assets().end());
    scope.sources = project.storage->sources;
    scope.declarationIndex = project.storage->declarationIndex;
    if (auto error = work.charge(scope.declarationIndex->bindingCount()))
      return std::move(error);
    detail::Checker checker(scope, work, ExternalSelectionAccess{});
    Declaration context{};
    context.kind = Declaration::Kind::EntryFunction;
    StringRef requested = syntax->target.name;
    requested.consume_front("::");
    std::optional<DeclarationId> selected;
    for (const auto &candidate : project.declarations()) {
      if (candidate.kind != Declaration::Kind::Entry &&
          candidate.kind != Declaration::Kind::EntryFunction)
        continue;
      auto entryName = candidate.entryName();
      if (requested.contains("::") ? entryName != requested
                                   : entryName.rsplit("::").second != requested)
        continue;
      if (selected)
        return detail::failure("source.entry",
                               "ambiguous Entry: " + requested +
                                   "; specify a qualified protocol name");
      selected = candidate.id;
    }
    if (!selected)
      return detail::failure("source.entry", "unknown Entry: " + requested);
    const auto &generated = scope.declarations[selected->index];
    if (!generated.generated ||
        generated.generated->operation != HostInvocation::Kind::Run)
      return detail::failure("source.entry",
                             "static Entry selection requires a protocol",
                             generated.span);
    const auto &protocol =
        scope.declarations[generated.generated->target.index];
    if (kind && *kind != EntryKind::Function)
      return detail::failure("source.entry-kind",
                             "selected Entry has the wrong execution kind",
                             protocol.span);
    // Selector text is an external argument, not a captured source buffer.
    // Type diagnostics point to the selected protocol's declared contract.
    context.id = generated.id;
    context.module = generated.module;
    context.span = protocol.span;
    std::function<void(detail::SyntaxType &)> anchor = [&](auto &type) {
      type.span = protocol.span;
      for (auto &label : type.labels)
        label.span = protocol.span;
      for (auto &argument : type.arguments)
        anchor(argument);
    };
    anchor(syntax->target);
    auto arguments =
        checker.arguments(context, protocol, syntax->target.arguments,
                          protocol.span, syntax->target.labels);
    if (!arguments)
      return checker.types.takeError();
    for (const auto &argument : *arguments)
      if (checker.types.symbolic(argument))
        return detail::failure(
            "source.generic",
            "Entry selection requires closed static arguments", protocol.span);
    auto selectedName = protocol.qualifiedName + syntax->arguments;
    if (selectedName.size() > 4096)
      return detail::failure("source.limit",
                             "qualified Entry selector byte limit exceeded",
                             protocol.span);
    return EntrySelection{*selected, std::move(*arguments),
                          std::move(selectedName)};
  }
  auto eligible = [&](DeclarationId id) {
    return !kind || project.declarations()[id.index].entryKind() == *kind;
  };
  auto selected = [&](DeclarationId id) -> Expected<EntrySelection> {
    if (!eligible(id))
      return detail::failure("source.entry-kind",
                             "selected Entry has the wrong execution kind",
                             project.declarations()[id.index].span);
    return EntrySelection{
        id, {}, project.declarations()[id.index].entryName().str()};
  };
  auto candidates = project.entries();
  std::vector<DeclarationId> matches;
  for (auto id : candidates) {
    auto entryName = project.declarations()[id.index].entryName();
    if (name.empty()          ? eligible(id)
        : name.contains("::") ? entryName == name
                              : entryName.rsplit("::").second == name)
      matches.push_back(id);
  }
  if (matches.size() == 1)
    return selected(matches.front());
  if (candidates.empty())
    return detail::failure(
        "source.entry", "project has no Entries; declare a concrete protocol, "
                        "entry fn or proof");
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
    message += " " + decl.entryName().str() + " (" +
               (decl.entryKind() == EntryKind::Proof      ? "proof"
                : decl.entryKind() == EntryKind::Function ? "function"
                                                          : "run") +
               ")";
  }
  return detail::failure("source.entry", message);
}
Expected<DeclarationId> selectEntry(const CheckedProject &project,
                                    StringRef name, const Limits &limits,
                                    std::optional<EntryKind> kind) {
  auto selected = resolveEntry(project, name, limits, kind);
  if (!selected)
    return selected.takeError();
  return selected->declaration;
}
namespace {
Error validateClosedData(const ClosedEntry &entry, const Limits &limits,
                         detail::Work &work) {
  if (entry.protocolOrNull())
    if (auto error = detail::checkClosedSourceClaims(entry, work))
      return error;
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
        return e;
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
          auto result = protocol::logicalRelationData(*leaf.data(), budget);
          if (auto error = work.charge(before - budget.remaining, port.span))
            return error;
          if (auto error = work.charge(leaf.cost(), port.span))
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
  return Error::success();
}
} // namespace
Expected<ClosedEntry> closeEntry(const CheckedProject &project, StringRef name,
                                 const Limits &limits,
                                 std::optional<EntryKind> kind) {
  return closeEntry(project, name, limits, kind, {});
}
Expected<ClosedEntry>
closeEntry(const CheckedProject &project, StringRef name, const Limits &limits,
           std::optional<EntryKind> kind,
           std::optional<HostInvocation::Kind> operation) {
  return ClosedEntry::closeSelected(project, name, limits, kind, operation);
}
Expected<ClosedEntry>
ClosedEntry::closeSelected(const CheckedProject &project, StringRef name,
                           const Limits &limits, std::optional<EntryKind> kind,
                           std::optional<HostInvocation::Kind> operation,
                           std::vector<SourceWorkBudget> priorObservations) {
  auto storage = std::make_shared<detail::ClosedStorage>();
  storage->workObservation.separateBudgets = std::move(priorObservations);
  auto &observations = storage->workObservation.separateBudgets;
  if (auto error = checkScopedElaboration(project, limits, &observations))
    return std::move(error);
  auto selected = resolveEntry(project, name, limits, kind, &observations);
  if (!selected)
    return selected.takeError();
  const auto &decl = project.declarations()[selected->declaration.index];
  if (operation &&
      (!decl.proof() || (*operation != HostInvocation::Kind::Prove &&
                         *operation != HostInvocation::Kind::Verify)))
    return detail::failure(
        "source.host-invocation",
        "proof operation policy requires a proof declaration", decl.span);
  detail::Work work{limits};
  // Metadata is bounded by definition checking. Immutable template bodies
  // are shared; specialization starts with its own phase budget.
  detail::Work::Scope phase(work, SourceWorkPhase::Specialization);
  if (auto error = work.charge(project.declarations().size()))
    return error;
  storage->declarations.assign(project.declarations().begin(),
                               project.declarations().end());
  storage->name = selected->name;
  if (decl.kind == Declaration::Kind::EntryFunction)
    storage->declarations[decl.id.index].staticArguments = selected->arguments;
  if (auto error = detail::specialize(storage->declarations, project.assets(),
                                      work, decl.id, operation))
    return error;
  storage->invocationKind = operation;
  storage->root = *storage->declarations[decl.id.index].target;
  if (decl.kind != Declaration::Kind::EntryFunction)
    storage->protocol = storage->root;
  phase.enter(SourceWorkPhase::Assets);
  if (auto error = detail::closeAssets(project, *storage, work))
    return error;
  ClosedEntry entry(project, decl.id, storage);
  if (auto error = checkScopedSpecialization(entry, limits, &observations))
    return error;
  phase.enter(SourceWorkPhase::ClosedData);
  if (auto error = validateClosedData(entry, limits, work))
    return error;
  phase.enter(SourceWorkPhase::CommonInputs);
  if (auto error =
          detail::retainCommonControlRequirements(entry, *storage, work))
    return error;
  phase.enter(SourceWorkPhase::HostChildren);
  std::set<std::string> invoked;
  std::function<Error(const Body &, unsigned)> collect =
      [&](const Body &body, unsigned depth) -> Error {
    if (depth > limits.callDepth)
      return detail::failure("source.limit",
                             "invocation traversal depth exceeded");
    for (const auto &op : body.operations) {
      if (auto e = work.charge(1, op.span))
        return e;
      if (const auto *call = std::get_if<HostInvocation>(&op.action)) {
        // Counted by lookup key; local to this one traversal.
        std::string key = std::to_string(unsigned(call->kind)) + ":" +
                          std::to_string(call->target.index);
        for (const auto &argument : call->arguments)
          detail::frame(key, typeIdentity(argument));
        if (invoked.insert(key).second) {
          if (invoked.size() > limits.instances)
            return detail::failure("source.limit",
                                   "Host invocation instance limit exceeded",
                                   op.span);
          // These arguments were checked as typed Host data. Closing their
          // deployment must not grant or demand external byte constructors.
          auto child = closeProtocol(project, *call, limits);
          if (!child)
            return child.takeError();
          if (auto e = work.charge(child->storage->work, op.span))
            return e;
          storage->invocations.push_back(
              {call->kind, call->target, call->arguments,
               std::make_shared<ClosedEntry>(std::move(*child))});
        }
      } else if (const auto *control = std::get_if<Control>(&op.action)) {
        for (const auto &region : control->regions)
          if (auto e = collect(*region, depth + 1))
            return e;
      }
    }
    return Error::success();
  };
  for (const auto &definition : entry.declarations())
    if (definition.body)
      if (auto e = collect(*definition.body, 1))
        return e;
  storage->work = work.used;
  storage->workObservation.charged = work.ledger;
  return entry;
}

Expected<ClosedEntry> closeInvocation(const CheckedProject &project,
                                      const HostInvocation &invocation,
                                      const Limits &limits) {
  return ClosedEntry::closeProtocol(project, invocation, limits);
}
Expected<ClosedEntry> ClosedEntry::closeProtocol(
    const CheckedProject &project, const HostInvocation &invocation,
    const Limits &limits, std::vector<SourceWorkBudget> priorObservations) {
  auto storage = std::make_shared<detail::ClosedStorage>();
  storage->workObservation.separateBudgets = std::move(priorObservations);
  auto &observations = storage->workObservation.separateBudgets;
  if (auto e = checkScopedElaboration(project, limits, &observations))
    return e;
  if (invocation.kind != HostInvocation::Kind::Run &&
      invocation.kind != HostInvocation::Kind::Prove &&
      invocation.kind != HostInvocation::Kind::Verify)
    return detail::failure("source.host-invocation", "unknown Host operation");
  if (invocation.target.index >= project.declarations().size())
    return detail::failure("source.host-invocation",
                           "invocation target is outside the project");
  const auto &target = project.declarations()[invocation.target.index];
  if (invocation.kind != HostInvocation::Kind::Run) {
    if (target.kind != Declaration::Kind::Entry || !target.proof() ||
        !invocation.arguments.empty())
      return detail::failure("source.host-invocation",
                             "proof invocation requires a closed proof family",
                             target.span);
    return closeSelected(project, target.qualifiedName, limits,
                         EntryKind::Proof, invocation.kind,
                         std::move(observations));
  }
  if (target.kind != Declaration::Kind::Protocol)
    return detail::failure("source.host-invocation",
                           "run invocation requires a protocol", target.span);
  detail::Work work{limits};
  detail::Work::Scope phase(work, SourceWorkPhase::Specialization);
  if (auto error = work.charge(project.declarations().size()))
    return error;
  storage->declarations.assign(project.declarations().begin(),
                               project.declarations().end());
  Declaration owner;
  owner.kind = Declaration::Kind::Entry;
  owner.id = {uint32_t(storage->declarations.size())};
  owner.module = target.module;
  owner.span = target.span;
  owner.name = target.name + "_deployment";
  Type family(Type::Kind::Record, target.qualifiedName);
  family.arguments = invocation.arguments;
  owner.qualifiedName = target.qualifiedName + "::run";
  if (!invocation.arguments.empty())
    owner.qualifiedName += "_" + detail::digest(spelling(family));
  owner.symbol = target.symbol + "_run";
  owner.target = target.id;
  owner.staticArguments = invocation.arguments;
  owner.setups = target.setups;
  auto selected = owner.id;
  storage->name = owner.qualifiedName;
  storage->declarations.push_back(std::move(owner));
  if (auto e = detail::specialize(storage->declarations, project.assets(), work,
                                  selected))
    return e;
  storage->root = *storage->declarations[selected.index].target;
  storage->protocol = storage->root;
  storage->invocationKind = invocation.kind;
  phase.enter(SourceWorkPhase::Assets);
  if (auto e = detail::closeAssets(project, *storage, work))
    return e;
  ClosedEntry child(project, selected, storage);
  if (auto e = checkScopedSpecialization(child, limits, &observations))
    return e;
  phase.enter(SourceWorkPhase::ClosedData);
  if (auto e = validateClosedData(child, limits, work))
    return e;
  phase.enter(SourceWorkPhase::CommonInputs);
  if (auto error =
          detail::retainCommonControlRequirements(child, *storage, work))
    return error;
  storage->work = work.used;
  storage->workObservation.charged = work.ledger;
  return child;
}

Expected<ClosedEntry> closeSubject(const CheckedProject &project,
                                   StringRef name, const Limits &limits) {
  if (name.empty())
    return detail::failure("source.subject",
                           "a closed subject must be selected");
  std::vector<SourceWorkBudget> observations;
  auto selected = resolveEntry(project, name, limits, {}, &observations);
  if (!selected)
    return selected.takeError();
  const auto &declaration = project.declarations()[selected->declaration.index];
  if (declaration.kind == Declaration::Kind::Entry && declaration.proof())
    return ClosedEntry::closeSelected(project, name, limits, EntryKind::Proof,
                                      {}, std::move(observations));
  if (!declaration.generated ||
      declaration.generated->operation != HostInvocation::Kind::Run)
    return detail::failure("source.subject",
                           "subject must name a closed protocol or proof, not "
                           "a Host Entry function",
                           declaration.span);
  return ClosedEntry::closeProtocol(project,
                                    {HostInvocation::Kind::Run,
                                     declaration.generated->target,
                                     std::move(selected->arguments),
                                     {}},
                                    limits, std::move(observations));
}

const Declaration &ClosedEntry::entry() const {
  return storage->declarations[selected.index];
}
StringRef ClosedEntry::name() const { return storage->name; }
const Declaration &ClosedEntry::root() const {
  return storage->declarations[storage->root.index];
}
const Declaration *ClosedEntry::protocolOrNull() const {
  return storage->protocol ? &storage->declarations[storage->protocol->index]
                           : nullptr;
}
const Declaration &ClosedEntry::protocol() const {
  assert(protocolOrNull() && "entry function has no protocol root");
  return *protocolOrNull();
}
std::optional<HostInvocation::Kind> ClosedEntry::invocationKind() const {
  return storage->invocationKind;
}
ArrayRef<ClosedInvocation> ClosedEntry::invocations() const {
  return storage->invocations;
}
ArrayRef<Asset> ClosedEntry::assets() const { return storage->assets; }
ArrayRef<Declaration> ClosedEntry::declarations() const {
  return storage->declarations;
}
Expected<ArrayRef<CommonControlRequirement>>
ClosedEntry::commonInputs(DeclarationId target) const {
  auto found = storage->commonInputs.find(target.index);
  if (found == storage->commonInputs.end())
    return detail::failure("source.common-provenance",
                           "common target is not a closed concrete Protocol");
  return ArrayRef<CommonControlRequirement>(found->second);
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
  for (const auto &constructor : protocol::frontendConstructors())
    row({"frontend-constructor", constructor.name,
         std::to_string(static_cast<unsigned>(constructor.form))});
  for (const auto &home : protocol::frontendHomes()) {
    row({"frontend-home", home.constructor, home.module});
    for (const auto &member : home.members)
      row({"frontend-home-member", home.constructor, member});
  }
  for (const auto &method : protocol::serviceMethodDeclarations())
    row({"service-method", method.identity, method.constructor, method.name,
         std::to_string(static_cast<unsigned>(method.signature)),
         method.capability});
  // Every field of an installed declaration and notation is semantic: its
  // owner, kind, ordered statics and inputs, output, association and scope.
  auto term = [](const protocol::SourceTerm &value) {
    return value.index
               ? "static:" + std::to_string(*value.index) + ":" + value.member
               : "constructor:" + value.constructor;
  };
  for (const auto &declaration : protocol::frontendDeclarations()) {
    row({"frontend-declaration", declaration.identity, declaration.module,
         declaration.name,
         std::to_string(static_cast<unsigned>(declaration.kind)),
         declaration.rule ? "rule:" + std::to_string(static_cast<unsigned>(
                                          *declaration.rule))
                          : "primitive:" + declaration.primitive,
         declaration.output ? term(*declaration.output) : "none",
         declaration.prelude ? "prelude" : "explicit"});
    for (const auto &[position, value] : llvm::enumerate(declaration.statics))
      row({"frontend-static", declaration.identity, std::to_string(position),
           value.name, value.kind, value.sort});
    for (const auto &[position, value] : llvm::enumerate(declaration.inputs))
      row({"frontend-input", declaration.identity, std::to_string(position),
           value.name, term(value.type)});
  }
  for (const auto &notation : protocol::frontendNotations())
    row({"frontend-notation", notation.module, notation.symbol, notation.fixity,
         std::to_string(notation.precedence), notation.target,
         notation.isPublic ? "public" : "private"});
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
         : intrinsic.domain == MathematicalIntrinsic::Domain::Quotient
             ? "quotient"
             : "field",
         intrinsic.scalar ? "scalar" : "intrinsic"});
  for (const auto &kernel : protocol::operationShapes()) {
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
  for (const auto &service : protocol::randomServices())
    for (StringRef method : {"draw", "index", "indices"})
      if (auto signature = protocol::serviceMethod(service.contract, method)) {
        std::string value;
        for (StringRef field :
             {StringRef("service"), StringRef(service.contract), method})
          detail::frame(value, field);
        for (const auto &input : signature->inputs)
          detail::frame(value, input.spelling());
        detail::frame(value, signature->output.spelling());
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

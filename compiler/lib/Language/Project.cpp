#include "Internal.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Kernels.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ConvertUTF.h"
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

Error checkLimits(const Limits &limits) {
  const Limits ceiling;
#define CHECK_LIMIT(name)                                                      \
  if (limits.name > ceiling.name)                                              \
  return detail::failure("source.limit", "cannot raise " #name " ceiling")
  CHECK_LIMIT(files);
  CHECK_LIMIT(fileBytes);
  CHECK_LIMIT(captureBytes);
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
  CHECK_LIMIT(interfaceBytes);
  CHECK_LIMIT(locationBytes);
#undef CHECK_LIMIT
  return Error::success();
}
namespace detail {
Error failure(StringRef code, const Twine &message, std::optional<Span> span,
              std::vector<Span> related) {
  return make_error<DiagnosticError>(
      Diagnostic{code.str(), message.str(), span, std::move(related)});
}
bool isUnsupported(StringRef name) {
  static const std::set<StringRef> words = {
      "local",     "service",      "predicate", "relation", "requires",
      "construct", "construction", "where",     "struct",   "enum",
      "type",      "nat",          "if",        "else",     "for",
      "while",     "opaque",       "stop"};
  return words.count(name);
}
bool isReserved(StringRef name) {
  static const std::set<StringRef> words = {
      "module", "use",   "pub", "domain", "field", "math", "fn",   "protocol",
      "roles",  "entry", "let", "return", "send",  "bool", "true", "false"};
  return words.count(name) || isUnsupported(name);
}
bool isIdentifier(StringRef name) {
  if (name.empty() || !(isAlpha(name.front()) || name.front() == '_'))
    return false;
  return llvm::all_of(name, [](char c) { return isAlnum(c) || c == '_'; });
}
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
                          const Limits &limits) {
  if (sources.empty())
    return failure("source.capture",
                   "capture must contain at least one module");
  if (sources.size() > limits.files)
    return failure("source.limit", "file count limit exceeded");
  uint64_t total = 0;
  std::set<StringRef> names;
  for (const auto &source : sources) {
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
  return Error::success();
}
} // namespace detail

Expected<CapturedProject> capture(std::vector<SourceBuffer> sources,
                                  const CaptureOptions &options) {
  if (auto error = checkLimits(options.limits))
    return std::move(error);
  if (options.format != "zkc")
    return detail::failure("source.format",
                           "expected explicit source format 'zkc'");
  if (auto error = detail::checkSources(sources, options.limits))
    return std::move(error);
  std::sort(sources.begin(), sources.end(),
            [](const auto &a, const auto &b) { return a.module < b.module; });
  auto storage = std::make_shared<detail::CaptureStorage>();
  storage->sources = std::move(sources);
  storage->format = options.format;
  std::string identity;
  detail::frame(identity, "zkc.capture/1");
  detail::frame(identity, options.format);
  for (const auto &source : storage->sources) {
    detail::frame(identity, source.module);
    detail::frame(identity, source.text);
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
StringRef CapturedProject::identity() const { return storage->identity; }
StringRef CapturedProject::format() const { return storage->format; }
CheckedProject::CheckedProject(
    std::shared_ptr<const detail::CheckedStorage> storage)
    : storage(std::move(storage)) {}
const CapturedProject &CheckedProject::capture() const {
  return storage->capture;
}
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
uint64_t CheckedProject::checkedWork() const { return storage->work; }
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
  detail::Work work{limits};
  auto run = [&]() -> Error {
    if (auto error = checkLimits(limits))
      return error;
    if (auto error = detail::checkSources(capture.sources(), limits))
      return error;
    checked->tokens.resize(capture.sources().size());
    std::vector<detail::SyntaxModule> modules;
    for (unsigned i = 0; i < capture.sources().size(); ++i) {
      if (auto error = detail::lex(capture.sources()[i], ModuleId{i}, work,
                                   checked->tokens[i]))
        return error;
      auto syntax = detail::parse(capture.sources()[i], ModuleId{i},
                                  checked->tokens[i], work);
      if (!syntax)
        return syntax.takeError();
      modules.push_back(std::move(*syntax));
    }
    if (auto error = detail::check(std::move(modules), *checked, work))
      return error;
    checked->installation = installedCatalogIdentity();
    checked->work = work.used;
    output->checked = CheckedProject(checked);
    return Error::success();
  };
  handleAllErrors(
      run(),
      [&](const DiagnosticError &error) {
        output->diagnostics.push_back(error.diagnostic());
      },
      [&](const ErrorInfoBase &error) {
        output->diagnostics.push_back(
            {"source.internal", error.message(), {}, {}});
      });
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
  std::string symbol = "s";
  for (auto part : parts) {
    if (part.size() > limits.identifierBytes || !detail::isIdentifier(part) ||
        detail::isReserved(part))
      return detail::failure("source.name", "invalid qualified name");
    symbol += std::to_string(part.size()) + "_" + part.str();
    if (symbol.size() > limits.symbolBytes)
      return detail::failure("source.limit", "symbol byte limit exceeded");
  }
  return symbol;
}
Expected<ClosedEntry> closeEntry(const CheckedProject &project, StringRef name,
                                 const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (name.size() > limits.moduleBytes + limits.identifierBytes + 2)
    return detail::failure("source.limit", "Entry name byte limit exceeded");
  if (project.checkedWork() > limits.work ||
      project.declarations().size() > limits.declarations)
    return detail::failure("source.limit",
                           "checked project exceeds requested limits");
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name) {
      if (decl.kind != Declaration::Kind::Entry)
        return detail::failure("source.entry",
                               "selection must name an Entry declaration",
                               decl.span);
      return ClosedEntry(project, decl.id);
    }
  return detail::failure("source.entry", "unknown qualified Entry: " + name);
}
const Declaration &ClosedEntry::entry() const {
  return checked.declarations()[selected.index];
}
const Declaration &ClosedEntry::protocol() const {
  return checked.declarations()[entry().target->index];
}
std::string spelling(const Type &type) {
  return type.kind == Type::Kind::Boolean ? "bool"
                                          : "field<" + type.domain + ">";
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
    }
    detail::frame(value, protocol::operationEffect(kernel.key));
    rows.push_back(std::move(value));
  }
  std::sort(rows.begin(), rows.end());
  std::string bytes;
  detail::frame(bytes, "zkc.language-catalog/1");
  for (const auto &row : rows)
    detail::frame(bytes, row);
  return detail::digest(bytes);
}
} // namespace zkc::language

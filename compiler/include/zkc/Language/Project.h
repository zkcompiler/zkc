#ifndef ZKC_LANGUAGE_PROJECT_H
#define ZKC_LANGUAGE_PROJECT_H

#include "zkc/Contracts/Mathematical.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace zkc::language {
struct ModuleId {
  uint32_t index;
};
struct DeclarationId {
  uint32_t index;
};
struct ValueId {
  uint32_t index;
};
struct Span {
  ModuleId module;
  uint32_t begin, end;
};
struct Diagnostic {
  std::string code, message;
  std::optional<Span> primary;
  std::vector<Span> related;
};
class DiagnosticError : public llvm::ErrorInfo<DiagnosticError> {
public:
  static char ID;
  explicit DiagnosticError(Diagnostic diagnostic);
  const Diagnostic &diagnostic() const { return value; }
  void log(llvm::raw_ostream &) const override;
  std::error_code convertToErrorCode() const override;

private:
  Diagnostic value;
};

/// Requests may lower, but never raise, these per-invocation ceilings.
struct Limits {
  uint64_t files = 256, fileBytes = 1048576, captureBytes = 8388608;
  uint64_t tokens = 1000000, tokenBytes = 4096;
  uint64_t identifierBytes = 128, moduleBytes = 2048;
  uint64_t parseDepth = 64, expressionDepth = 64;
  uint64_t importDepth = 64, callDepth = 64;
  uint64_t declarations = 10000, operations = 100000, work = 1000000;
  uint64_t irBytes = 16777216, symbolBytes = 4096;
  uint64_t interfaceBytes = 4194304, locationBytes = 16777216;
};
llvm::Error checkLimits(const Limits &);

/// Names and bytes determine identity. diagnosticPath is never opened here.
struct SourceBuffer {
  std::string module, text, diagnosticPath;
};
struct CaptureOptions {
  std::string format = "zkc";
  Limits limits;
};
enum class TokenKind {
  Word,
  Decimal,
  String,
  Punctuation,
  Whitespace,
  Comment,
  End
};
struct Token {
  TokenKind kind;
  Span span;
};
struct Type {
  enum class Kind { Boolean, Field } kind = Kind::Boolean;
  std::string domain;
  bool operator==(const Type &other) const {
    return kind == other.kind && domain == other.domain;
  }
  bool operator!=(const Type &other) const { return !(*this == other); }
};
struct Port {
  std::string name;
  Type type;
  std::vector<unsigned> roles;
  Span span;
};
struct Value {
  Type type;
  /// Protocol: roster indices. Math: input dependencies. Both are sorted sets.
  std::vector<unsigned> components;
  Span span;
};
struct MathValue {
  MathematicalIdentity identity;
  std::vector<ValueId> operands;
  std::string literal;
};
struct HelperCall {
  DeclarationId callee;
  std::vector<ValueId> operands;
};
struct Exchange {
  unsigned sender, receiver;
  ValueId payload;
};
struct Restriction {
  ValueId input;
  std::vector<unsigned> roles;
};
struct Operation {
  std::variant<MathValue, HelperCall, Exchange, Restriction> action;
  ValueId result;
  Span span;
  uint32_t statement;
};
struct Body {
  enum class Mode { Math, Protocol } mode;
  std::vector<Value> values;
  std::vector<Operation> operations;
  std::vector<ValueId> results;
  /// Includes intermediate dependencies of unused mathematical work.
  std::vector<std::vector<unsigned>> formationRequirements;
};
struct Declaration {
  enum class Kind { Domain, Math, Protocol, Entry } kind;
  DeclarationId id;
  ModuleId module;
  std::string name, qualifiedName, symbol;
  bool isPublic = false;
  Span span;
  Type domain;
  std::vector<std::string> roles;
  std::vector<Port> inputs, outputs;
  std::optional<Body> body;
  std::optional<DeclarationId> target;
};

namespace detail {
struct CaptureStorage;
struct CheckedStorage;
struct AnalysisStorage;
} // namespace detail
class CapturedProject;
class CheckedProject;
class Analysis;
class ClosedEntry;
llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                        const CaptureOptions & = {});
Analysis analyze(const CapturedProject &, const Limits & = {});
llvm::Expected<ClosedEntry> closeEntry(const CheckedProject &, llvm::StringRef,
                                       const Limits & = {});

class CapturedProject {
public:
  llvm::ArrayRef<SourceBuffer> sources() const;
  llvm::StringRef identity() const;
  llvm::StringRef format() const;

private:
  explicit CapturedProject(std::shared_ptr<const detail::CaptureStorage>);
  std::shared_ptr<const detail::CaptureStorage> storage;
  friend llvm::Expected<CapturedProject> capture(std::vector<SourceBuffer>,
                                                 const CaptureOptions &);
};

/// Only successful analysis can construct this immutable owning handle.
class CheckedProject {
public:
  const CapturedProject &capture() const;
  llvm::ArrayRef<Declaration> declarations() const;
  llvm::ArrayRef<Token> tokens(ModuleId) const;
  llvm::StringRef installationIdentity() const;
  uint64_t checkedWork() const;

private:
  explicit CheckedProject(std::shared_ptr<const detail::CheckedStorage>);
  std::shared_ptr<const detail::CheckedStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &);
};

/// Recovery tokens and diagnostics cannot be promoted to checked state.
class Analysis {
public:
  llvm::ArrayRef<Diagnostic> diagnostics() const;
  llvm::ArrayRef<Token> tokens(ModuleId) const;
  llvm::Expected<CheckedProject> checkedProject() const;

private:
  explicit Analysis(std::shared_ptr<const detail::AnalysisStorage>);
  std::shared_ptr<const detail::AnalysisStorage> storage;
  friend Analysis analyze(const CapturedProject &, const Limits &);
};
class ClosedEntry {
public:
  const CheckedProject &project() const { return checked; }
  const Declaration &entry() const;
  const Declaration &protocol() const;

private:
  ClosedEntry(CheckedProject checked, DeclarationId selected)
      : checked(std::move(checked)), selected(selected) {}
  CheckedProject checked;
  DeclarationId selected;
  friend llvm::Expected<ClosedEntry>
  closeEntry(const CheckedProject &, llvm::StringRef, const Limits &);
};
llvm::Expected<std::string> encodeSymbol(llvm::StringRef qualifiedName,
                                         const Limits & = {});
std::string spelling(const Type &);
/// Canonical identity of the installed Contracts data, not caller-supplied
/// data.
std::string installedCatalogIdentity();
} // namespace zkc::language

#endif

#ifndef ZKC_LANGUAGE_PROJECT_H
#define ZKC_LANGUAGE_PROJECT_H

#include "zkc/Contracts/Mathematical.h"
#include "zkc/Language/Types.h"
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
struct ServiceId {
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
  uint64_t typeDepth = 32, typeNodes = 100000, instances = 4096;
  uint64_t aggregateLeaves = 1024, naturalTerms = 1024, naturalFactors = 64;
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
struct Port {
  std::string name;
  Type type;
  std::vector<unsigned> roles;
  Span span;
};
/// A managed port is a borrowed service root, never an ordinary data type.
struct ServicePort {
  std::string name;
  Type field;
  unsigned owner;
  Span span;
  std::string contract; // Filled by selected Entry closure.
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
  std::vector<Type> arguments;
  std::optional<Type> component;
  std::optional<unsigned> owner;
};
struct ProtocolApplication {
  DeclarationId callee;
  std::vector<ValueId> operands;
  std::vector<Type> arguments;
  /// Caller roster indices, in the callee's declared role order.
  std::vector<unsigned> roles;
  std::vector<ServiceId> services;
};
struct ServiceQuery {
  ServiceId service;
};
struct ProtocolGuard {
  ValueId condition;
  unsigned owner;
};
struct Exchange {
  unsigned sender, receiver;
  ValueId payload;
};
struct Restriction {
  ValueId input;
  std::vector<unsigned> roles;
};
struct Body;
struct Construct {
  enum class Kind { Aggregate, Variant, Unpack };
  std::vector<ValueId> operands;
  std::string alternative;
  Kind kind = Kind::Aggregate;
};
struct Projection {
  ValueId input;
  std::vector<unsigned> path;
};
struct LocalPrimitive {
  std::string contract;
  std::vector<ValueId> operands;
  std::vector<std::string> parameters;
  std::vector<Type> staticArguments;
  LocalPrimitive(std::string contract, std::vector<ValueId> operands,
                 std::vector<std::string> parameters,
                 std::vector<Type> statics = {})
      : contract(std::move(contract)), operands(std::move(operands)),
        parameters(std::move(parameters)), staticArguments(std::move(statics)) {
  }
};
struct Consume {
  ValueId input;
};
struct LocalControl {
  enum class Kind { If, Match, For } kind;
  std::vector<ValueId> operands;
  std::vector<std::shared_ptr<const Body>> regions;
  std::vector<std::string> alternatives;
  unsigned carried = 0;
};
struct Operation {
  std::variant<MathValue, HelperCall, Exchange, Restriction, Construct,
               Projection, LocalPrimitive, Consume, LocalControl,
               ProtocolApplication, ServiceQuery, ProtocolGuard>
      action;
  /// Each result has its own type and participant availability.
  std::vector<ValueId> results;
  Span span;
  uint32_t statement;
};
struct Body {
  enum class Mode { Math, Local, Protocol } mode;
  std::vector<ServicePort> services;
  std::vector<Value> values;
  std::vector<Operation> operations;
  std::vector<ValueId> results;
  unsigned inputs = 0;
  bool stopped = false;
  std::string stopReason;
  bool mayStop = false, opaque = false;
  /// Includes intermediate dependencies of unused mathematical work.
  std::vector<std::vector<unsigned>> formationRequirements;
};
struct Parameter {
  enum class Sort { Type, Field, Group, Natural, Component } sort;
  std::string name, atom;
  Permissions permissions;
  std::optional<DeclarationId> interface;
  std::vector<Type> arguments;
  Span span;
};
struct TypeField {
  std::string name;
  Type type;
  bool isPublic = true;
  Span span;
};
struct Alternative {
  std::string name;
  std::vector<TypeField> fields;
  Span span;
};
struct NaturalBound {
  Natural lhs, rhs;
  Span span;
};
struct PermissionBound {
  Type type;
  Permissions permissions;
  Span span;
};
/// Upper bounds on the observable effects of a callable.
struct Effects {
  bool mayStop = false;
  bool opaque = false;
};
struct Declaration {
  enum class Kind {
    Domain,
    Math,
    Local,
    Protocol,
    Entry,
    Alias,
    Record,
    Variant,
    Interface,
    Component,
    Associated
  } kind;
  DeclarationId id;
  ModuleId module;
  std::string name, qualifiedName, symbol;
  bool isPublic = false;
  Span span;
  Type domain;
  std::vector<Parameter> parameters;
  std::vector<NaturalBound> bounds;
  std::vector<PermissionBound> permissionBounds;
  std::optional<Permissions> permissions;
  std::vector<TypeField> fields;
  std::vector<Alternative> alternatives;
  std::vector<DeclarationId> members;
  std::optional<DeclarationId> parent;
  std::optional<Type> implementation;
  std::optional<Effects> effectAllowance;
  bool abstract = false;
  /// Empty or Type is a private representation; Field and Group expose a
  /// domain.
  std::string associatedSort;
  /// A closed definition records its template and exact static substitution.
  std::optional<DeclarationId> origin;
  std::vector<Type> staticArguments;
  std::vector<std::string> roles;
  std::vector<Port> inputs, outputs;
  std::vector<ServicePort> services;
  std::optional<Body> body;
  std::optional<DeclarationId> target;
};

namespace detail {
struct CaptureStorage;
struct CheckedStorage;
struct ClosedStorage;
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
  /// Original type declarations and the selected Entry's closed instances.
  /// Only the reachable instances have bodies; declaration IDs remain local.
  llvm::ArrayRef<Declaration> declarations() const;

private:
  ClosedEntry(CheckedProject checked, DeclarationId selected,
              std::shared_ptr<const detail::ClosedStorage> storage)
      : checked(std::move(checked)), selected(selected),
        storage(std::move(storage)) {}
  CheckedProject checked;
  DeclarationId selected;
  std::shared_ptr<const detail::ClosedStorage> storage;
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

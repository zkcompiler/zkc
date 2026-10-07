#ifndef ZKC_LANGUAGE_INTERNAL_H
#define ZKC_LANGUAGE_INTERNAL_H

#include "zkc/Language/Project.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Support/JSON.h"
#include <map>
#include <set>

namespace zkc::language::detail {
struct CaptureStorage {
  std::vector<SourceBuffer> sources;
  std::string identity, format;
};
struct CheckedStorage {
  explicit CheckedStorage(CapturedProject capture)
      : capture(std::move(capture)) {}
  CapturedProject capture;
  std::vector<std::vector<Token>> tokens;
  std::vector<Declaration> declarations;
  std::string installation;
  uint64_t work = 0;
};
struct ClosedStorage {
  std::vector<Declaration> declarations;
  DeclarationId protocol;
};
struct AnalysisStorage {
  std::vector<Diagnostic> diagnostics;
  std::vector<std::vector<Token>> tokens;
  std::optional<CheckedProject> checked;
};
llvm::Error failure(llvm::StringRef code, const llvm::Twine &message,
                    std::optional<Span> span = {},
                    std::vector<Span> related = {});
bool isIdentifier(llvm::StringRef);
bool isPath(llvm::StringRef, const Limits &);
bool isReserved(llvm::StringRef);
bool isUnsupported(llvm::StringRef);
std::string digest(llvm::StringRef);
void frame(std::string &, llvm::StringRef);

struct Work {
  const Limits &limits;
  uint64_t used = 0, tokens = 0, declarations = 0, operations = 0;
  llvm::Error charge(uint64_t amount = 1, std::optional<Span> span = {});
  llvm::Error count(uint64_t &counter, uint64_t limit, llvm::StringRef what,
                    std::optional<Span> span = {});
};

struct SyntaxType {
  enum class Kind {
    Name,
    Natural,
    Add,
    Multiply,
    Array,
    Tuple
  } kind = Kind::Name;
  std::string name;
  Span span;
  std::vector<SyntaxType> arguments;
};
struct SyntaxPort {
  std::string name;
  SyntaxType type;
  std::vector<std::string> roles;
  Span span;
  bool isPublic = true;
};
struct SyntaxParameter {
  std::string name;
  SyntaxType constraint;
  Permissions permissions;
  Span span;
};
struct SyntaxRequirement {
  std::string permission;
  SyntaxType lhs, rhs;
  Span span;
};
struct Expression {
  enum class Kind {
    Name,
    Decimal,
    Boolean,
    Call,
    Apply,
    MethodCall,
    Add,
    Subtract,
    Multiply,
    Equal,
    Tuple,
    Array,
    Record,
    Projection,
    If,
    Match,
    For
  } kind;
  std::string text;
  std::vector<uint32_t> children;
  Span span;
  std::vector<SyntaxType> arguments;
  std::vector<std::string> labels;
  std::vector<std::string> captures;
  std::vector<std::string> services;
  std::optional<std::vector<std::string>> roles;
  std::vector<uint32_t> regions;
  std::vector<std::vector<std::string>> payloads;
};
struct Statement {
  enum class Kind {
    Let,
    Drop,
    Consume,
    Require,
    Alias,
    Guard
  } kind = Kind::Let;
  std::string name;
  std::optional<std::vector<std::string>> resultNames;
  std::optional<SyntaxType> type;
  std::optional<std::vector<std::string>> roles;
  std::optional<std::pair<std::string, std::string>> exchange;
  std::optional<std::string> owner;
  uint32_t expression;
  Span span;
};
struct SyntaxBody {
  std::vector<Statement> statements;
  std::vector<std::pair<std::string, uint32_t>> results;
  bool stopped = false;
  std::string stopReason;
  Span span;
};
struct SyntaxAlternative {
  std::string name;
  std::vector<SyntaxPort> fields;
  Span span;
};
struct SyntaxDeclaration {
  Declaration::Kind kind;
  std::string name, domain, target;
  bool isPublic = false;
  Span span;
  std::vector<std::string> roles;
  std::vector<SyntaxPort> inputs, outputs, services;
  std::vector<Expression> expressions;
  // Root body is kept in the first slot; nested bodies use stable indices.
  std::vector<SyntaxBody> bodies;
  std::vector<SyntaxParameter> parameters;
  std::vector<SyntaxRequirement> requirements;
  std::optional<Permissions> permissions;
  std::optional<Effects> effects;
  std::optional<SyntaxType> definition;
  std::vector<SyntaxType> targetArguments;
  std::vector<SyntaxPort> fields;
  std::vector<SyntaxAlternative> alternatives;
  std::vector<SyntaxDeclaration> members;
  bool abstract = false;
  std::string associatedSort;
};
struct Import {
  std::string module;
  std::vector<std::string> names;
  Span span;
};
struct SyntaxModule {
  ModuleId id;
  std::vector<Import> imports;
  std::vector<SyntaxDeclaration> declarations;
};
llvm::Error lex(const SourceBuffer &, ModuleId, Work &, std::vector<Token> &);
llvm::Expected<SyntaxModule> parse(const SourceBuffer &, ModuleId,
                                   llvm::ArrayRef<Token>, Work &);
llvm::Error check(std::vector<SyntaxModule>, CheckedStorage &, Work &);
} // namespace zkc::language::detail

#endif

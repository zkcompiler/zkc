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
  std::string name;
  Span span;
};
struct SyntaxPort {
  std::string name;
  SyntaxType type;
  std::vector<std::string> roles;
  Span span;
};
struct Expression {
  enum class Kind {
    Name,
    Decimal,
    Boolean,
    Call,
    Add,
    Subtract,
    Multiply,
    Equal
  } kind;
  std::string text;
  std::vector<uint32_t> children;
  Span span;
};
struct Statement {
  std::string name;
  std::optional<SyntaxType> type;
  std::optional<std::vector<std::string>> roles;
  std::optional<std::pair<std::string, std::string>> exchange;
  uint32_t expression;
  Span span;
};
struct SyntaxDeclaration {
  Declaration::Kind kind;
  std::string name, domain, target;
  bool isPublic = false;
  Span span;
  std::vector<std::string> roles;
  std::vector<SyntaxPort> inputs, outputs;
  std::vector<Expression> expressions;
  std::vector<Statement> statements;
  std::vector<std::pair<std::string, uint32_t>> results;
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

#ifndef ZKC_LANGUAGE_LAYOUTREADER_H
#define ZKC_LANGUAGE_LAYOUTREADER_H
#include "Internal.h"
namespace zkc::language::detail {
/// Fallible projection from one immutable layout tree into authored language
/// records. This reader makes no type, placement, proof or realization
/// decisions.
class LayoutReader {
  using K = syntax::Kind;
  using Id = syntax::NodeId;
  using Position = NotationDescriptor::Position;
  using Association = NotationDescriptor::Association;
  const syntax::Snapshot &tree;
  Work &work;
  std::map<uint32_t, uint32_t> writtenTokens;
  std::optional<uint32_t> scope;
  std::shared_ptr<const NotationEnvironment> environment;
  std::vector<Id> attributes;
  llvm::ArrayRef<Id> children(Id id) const;
  K kind(Id id) const;
  Span span(Id id) const;
  llvm::Error fail(Id id, llvm::StringRef message,
                   llvm::StringRef code = "source.layout") const;
  llvm::Error charge(Id id);
  std::optional<Id> first(Id id, K wanted) const;
  llvm::Expected<std::vector<llvm::StringRef>> words(Id id);
  llvm::Expected<std::string> name(Id id);
  llvm::StringRef head(Id id) const;
  bool visible(Id id) const;
  llvm::StringRef between(Id left, Id right) const;
  llvm::Error runtimeArgument(Id id) const;
  llvm::Expected<llvm::ArrayRef<Id>> parts(Id, size_t minimum,
                                           size_t maximum) const;
  llvm::Expected<Id> argument(Id id) const;
  llvm::Expected<std::vector<std::string>> roles(Id id);
  llvm::Expected<SyntaxType> type(Id id);
  llvm::Error staticArguments(Id id, std::vector<SyntaxType> &values,
                              std::vector<ArgumentLabel> &labels);
  llvm::Expected<SyntaxPort> port(Id id, bool unnamed = false);
  llvm::Expected<Id> permissionBound(Id id, Permissions &permissions,
                                     std::vector<std::string> &written);
  llvm::Error parameters(Id id, SyntaxDeclaration &decl);
  llvm::Error requirements(Id id, SyntaxDeclaration &decl);
  llvm::Error formal(Id id, SyntaxDeclaration &module);
  llvm::Error import(Id id, SyntaxDeclaration &module);
  llvm::Error notation(Id id, SyntaxDeclaration &module);
  llvm::Error declaration(Id id, SyntaxDeclaration &parent);
  llvm::Expected<Pattern> pattern(Id id);
  llvm::Expected<std::shared_ptr<const NotationDescriptor>>
  descriptor(Id id, llvm::StringRef symbol, Position position);
  llvm::Expected<uint32_t> expression(Id id, SyntaxDeclaration &decl);
  llvm::Expected<Expression> oracleSend(Id id, SyntaxDeclaration &decl);
  llvm::Error oracleShapes(SyntaxDeclaration &decl);
  llvm::Error body(Id id, SyntaxDeclaration &decl, bool region = false);

public:
  LayoutReader(const syntax::Snapshot &, llvm::ArrayRef<Token>, Work &);
  llvm::Expected<SyntaxDeclaration> headers();
  llvm::Error bodies(llvm::ArrayRef<BodyParseScope> scopes,
                     std::vector<Diagnostic> *recovery = nullptr);
};
} // namespace zkc::language::detail
#endif

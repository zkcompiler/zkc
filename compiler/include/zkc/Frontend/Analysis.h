#ifndef ZKC_FRONTEND_ANALYSIS_H
#define ZKC_FRONTEND_ANALYSIS_H

#include "zkc/Frontend/Diagnostic.h"
#include "zkc/Frontend/Input.h"
#include "zkc/Frontend/Module.h"
#include "zkc/Frontend/Work.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc::frontend {
namespace model {
struct AnalysisAccess;
} // namespace model
enum class AnalysisState {
  SyntaxPartial,
  SemanticError,
  ResourceLimit,
  SourceChecked
};
class Analysis {
  std::shared_ptr<const model::Module> model;
  std::shared_ptr<const model::CompletedAnalysis> completed;
  explicit Analysis(std::shared_ptr<const model::Module>);
  explicit Analysis(std::shared_ptr<const model::CompletedAnalysis>);
  friend struct model::AnalysisAccess;

public:
  llvm::StringRef sourceText() const;
  llvm::StringRef filename() const;
  const ProjectInput *project() const;
  /// Complete source analysis is deliberately distinct from PIR admission.
  bool complete() const;
  AnalysisState state() const;
  /// Deterministic logical charges, including work retained on failure.
  WorkUsage workUsage() const;
  bool resolutionComplete() const;
  llvm::Expected<CheckedModule> checkedModule() const;
  llvm::ArrayRef<Scope> scopes() const;
  llvm::ArrayRef<Declaration> declarations() const;
  llvm::ArrayRef<Type> types() const;
  llvm::ArrayRef<Domain> domains() const;
  llvm::ArrayRef<ResolvedUse> uses() const;
  llvm::ArrayRef<LocalBinding> bindings() const;
  llvm::ArrayRef<ValueUse> valueUses() const;
  llvm::ArrayRef<Instantiation> instantiations() const;
  llvm::ArrayRef<Diagnostic> diagnostics() const;
  llvm::ArrayRef<SemanticDependency> dependencies() const;
  const Declaration *declaration(DeclId) const;
  const Type *type(TypeId) const;
  const Domain *domain(DomainId) const;
  /// Lookup in exactly this scope. There is no fallback by textual name.
  std::optional<DeclId> lookup(ScopeId, llvm::StringRef) const;
  std::string display(TypeId) const;
  std::string display(DomainId) const;
  /// Emit structurally checked common source; callers independently admit it
  /// with checkProtocolDocument. Partial/failed analysis cannot emit.
  llvm::Expected<source::Content> lower() const;
};
/// Own text, parse, stage exactly once and analyze. Errors retain query data.
Analysis analyzeProtocol(llvm::StringRef text,
                         llvm::StringRef filename = "<stdin>");
Analysis analyzeProtocol(llvm::StringRef text, llvm::StringRef filename,
                         WorkLimits);
Analysis analyzeProtocol(const Input &input);
Analysis analyzeProtocol(const Input &input, WorkLimits);
Analysis analyzeProject(const ProjectInput &);
Analysis analyzeProject(const ProjectInput &, WorkLimits);
} // namespace zkc::frontend
#endif

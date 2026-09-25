#ifndef ZKC_FRONTEND_DIAGNOSTIC_H
#define ZKC_FRONTEND_DIAGNOSTIC_H

#include "zkc/Source/Model.h"
#include "llvm/Support/Error.h"

namespace zkc::frontend {
class ProjectInput;
struct RelatedLocation {
  std::string message;
  std::optional<source::Span> location;
};
/// Exact subjects supplied by the owning checker, never inferred from prose.
struct DiagnosticCause {
  enum class Kind {
    Declaration,
    ImportedInterface,
    SelectedComponent,
    UnsatisfiedObligation,
    CapturedSubject,
    Checker,
    Premise
  };
  Kind kind = Kind::Declaration;
  std::string subject, explanation;
  std::optional<source::Span> location;
};
struct Diagnostic {
  std::string code, message;
  std::optional<source::Span> location;
  std::vector<RelatedLocation> related = {};
  std::vector<DiagnosticCause> causes = {};
};
/// Resource exhaustion is an unavailable judgment, not a semantic refutation.
bool isResourceLimitDiagnostic(llvm::StringRef code);

/// One structured diagnostic, with a bounded source excerpt for CLI consumers.
/// Tools inspect the fields; rendered prose is not a diagnostic identifier.
class SourceDiagnostic : public llvm::ErrorInfo<SourceDiagnostic> {
public:
  static char ID;
  std::string code, message, rendered;
  source::Span location;
  std::vector<RelatedLocation> related;
  std::vector<DiagnosticCause> causes;

  SourceDiagnostic(std::string code, std::string message, std::string rendered,
                   source::Span location)
      : code(std::move(code)), message(std::move(message)),
        rendered(std::move(rendered)), location(location) {}
  void log(llvm::raw_ostream &) const override;
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }
};

llvm::Error diagnostic(llvm::StringRef text, llvm::StringRef filename,
                       size_t offset, llvm::StringRef code,
                       const llvm::Twine &message);
llvm::Error diagnostic(const ProjectInput &, source::Span, llvm::StringRef code,
                       const llvm::Twine &message);
llvm::Error diagnostic(const ProjectInput &, const Diagnostic &);
} // namespace zkc::frontend
#endif

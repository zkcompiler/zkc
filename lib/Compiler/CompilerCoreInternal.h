//===- CompilerCoreInternal.h - Compiler judgment internals -----*- C++ -*-===//
#ifndef ZKC_LIB_COMPILER_COMPILERCOREINTERNAL_H
#define ZKC_LIB_COMPILER_COMPILERCOREINTERNAL_H

#include "zkc/Compiler/CompilerCore.h"

namespace zkc::compiler {

/// Internal judgment products used to implement and directly test checked
/// compilation. They are not producer inputs or public compiler results.
struct PlanDomain {
  ComparisonScopeKind scope = ComparisonScopeKind::ClosedDomain;
  std::vector<CompilerPlan> plans;
};

struct CheckedTransformTrace {
  AuthenticatedArtifactHandle source;
  AuthenticatedArtifactHandle finalArtifact;
  std::vector<ClaimCorrespondence> correspondences;
  /// In application order. Empty when every family along the trace claims
  /// nothing, which is the ordinary case and is not a gap in the record.
  std::vector<PreservationClaim> preservationClaims;
};

struct ResolvedDerivation {
  std::string targetKey;
  std::string schemaKey;
  soundness::DerivationResult result;
};

struct Candidate {
  uint64_t ordinal = 0;
  CompilerPlan plan;
  CheckedTransformTrace trace;
  std::vector<ResolvedDerivation> derivations;
};

struct ValidCandidate {
  Candidate candidate;
};

struct ScoredCandidate {
  ValidCandidate candidate;
  std::vector<registry::Rational> objectiveValues;
};

struct Selection {
  std::optional<uint64_t> selectedOrdinal;
};

llvm::Expected<PlanDomain> domain(const CompilerSemanticContext &context,
                                  const CompilerRequest &request);

llvm::Expected<CheckedTransformTrace>
realizeTransform(const CompilerSemanticContext &context,
                 const CompilerRequest &request, const TransformPlan &plan);

llvm::Expected<Candidate> realize(const CompilerSemanticContext &context,
                                  const CompilerRequest &request,
                                  const PlanDomain &planDomain,
                                  uint64_t ordinal);

llvm::Expected<ValidCandidate> validate(const CompilerSemanticContext &context,
                                        const CompilerRequest &request,
                                        const PlanDomain &planDomain,
                                        uint64_t ordinal);

llvm::Expected<ScoredCandidate> score(const CompilerSemanticContext &context,
                                      const CompilerRequest &request,
                                      const PlanDomain &planDomain,
                                      uint64_t ordinal);

llvm::Expected<Selection> select(const CompilerSemanticContext &context,
                                 const CompilerRequest &request,
                                 const PlanDomain &planDomain);

bool derivationPlansEqual(const soundness::DerivationPlan &lhs,
                          const soundness::DerivationPlan &rhs);
bool compilerPlansEqual(const CompilerPlan &lhs, const CompilerPlan &rhs);

} // namespace zkc::compiler

#endif // ZKC_LIB_COMPILER_COMPILERCOREINTERNAL_H

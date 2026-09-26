#ifndef ZKC_TARGET_CATALOG_H
#define ZKC_TARGET_CATALOG_H

#include "zkc/Contracts/Bindings.h"

namespace zkc::target {
/// Same-version, in-process policy seam. Candidates are preferences, not new
/// contracts or laws. Every answer must still resolve through installed
/// Contracts. Provider queries must be read-only and deterministic for replay
/// of a compilation; no concurrent input/context mutation is supported.
class CandidateCatalog {
public:
  virtual ~CandidateCatalog() = default;
  virtual llvm::Expected<std::vector<std::string>>
  implementations(const protocol::BindingApplication &) const = 0;
  /// Optional contraction preferences, separate from ordinary default order.
  /// The default derives the installed diagonal alternative; an override may
  /// withhold or reorder candidates but cannot install an implementation.
  virtual std::vector<std::string>
  diagonalImplementations(const protocol::BindingApplication &) const;
  virtual std::vector<protocol::BindingApplication>
  conversions(const protocol::BoundType &from,
              const protocol::BoundType &to) const = 0;
};

const CandidateCatalog &installedCandidates();

/// Admit the exact installed diagonal contract instance and all its ports,
/// independently of candidate policy. A matching signature is insufficient.
llvm::Expected<protocol::BoundOperation>
resolveDiagonalImplementation(const protocol::BindingApplication &);

/// Check the installed direct adapter relation, independently of a provider.
/// A matching unary signature alone never establishes a conversion law.
llvm::Error checkDirectConversion(const protocol::BindingApplication &,
                                  const protocol::BoundType &from,
                                  const protocol::BoundType &to);
} // namespace zkc::target
#endif

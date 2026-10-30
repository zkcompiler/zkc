#ifndef ZKC_TARGET_CATALOG_H
#define ZKC_TARGET_CATALOG_H

#include "zkc/Contracts/Implementations.h"
#include "zkc/Dialect/Bindings.h"

namespace zkc::target {
struct NativeBindingChoice {
  std::string name;
  NativeBindingApplication application;
};
/// Read actual native arguments and independently admit the declaration.
llvm::Expected<NativeBindingChoice> readPlanBinding(runtime::BindingOp);
/// Resolve native installation facts, optionally selecting one complete family
/// layout. No byte encoding, plan production or temporary IR is involved.
llvm::Expected<mlir::FunctionType>
resolveNativeApplication(const NativeBindingApplication &, bool physical = true,
                         mlir::Type familyLayout = {},
                         const protocol::ImplementationCatalog & =
                             protocol::installedImplementations());
llvm::Expected<std::string>
defaultNativeImplementation(const NativeBindingApplication &);

/// In-process policy interface for the selected compiler build. Candidates are
/// preferences, not new contracts or laws. Every answer must still resolve
/// through installed Contracts. Provider queries must be read-only and
/// deterministic for replay of a compilation; no concurrent input/context
/// mutation is supported.
class CandidateCatalog {
public:
  virtual ~CandidateCatalog() = default;
  virtual llvm::Expected<std::vector<std::string>>
  implementations(const NativeBindingApplication &) const = 0;
  /// Optional contraction preferences, separate from ordinary default order.
  /// The default ranks installed alternatives by identity; an override may
  /// withhold or reorder candidates but cannot install an implementation.
  virtual std::vector<std::string>
  diagonalImplementations(const NativeBindingApplication &) const;
  virtual std::vector<NativeBindingApplication>
  conversions(mlir::Type from, mlir::Type to) const = 0;
};

const CandidateCatalog &installedCandidates();

/// Enumerate applicable diagonal implementations by identity, independent of
/// registration order, within this build's installed domains and contracts.
/// Lexical implementation identity is the deterministic default preference;
/// a CandidateCatalog may supply its own candidate ordering.
/// This supplies candidates, not installation authority; physical plan
/// validation still resolves against the installed implementation catalog.
std::vector<std::string>
diagonalCandidates(const NativeBindingApplication &,
                   const protocol::ImplementationCatalog &);

/// Admit the exact installed diagonal contract instance and all its ports,
/// independently of candidate policy. A matching signature is insufficient.
llvm::Expected<mlir::FunctionType>
resolveDiagonalImplementation(const NativeBindingApplication &);

/// Check the installed direct adapter relation, independently of a provider.
/// A matching unary signature alone never establishes a conversion law.
llvm::Error checkDirectConversion(const NativeBindingApplication &,
                                  mlir::Type from, mlir::Type to);
} // namespace zkc::target
#endif

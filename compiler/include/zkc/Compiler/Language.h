#ifndef ZKC_COMPILER_LANGUAGE_H
#define ZKC_COMPILER_LANGUAGE_H
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Translation/Language.h"
#include <memory>

namespace zkc::language {
namespace detail {
struct OriginalAccess;
}
class CheckedOriginal;
llvm::Expected<CheckedOriginal> prepareOriginal(const ClosedEntry &,
                                                const Limits & = {});
/// Admit canonical original and interface bytes against the checked source.
/// Parses once, verifies formation, predicates, source/SSA correspondence and
/// logical interface correspondence. The retained bytes, not caller JSON
/// equivalence, are the artifact that a Host must authenticate.
llvm::Expected<CheckedOriginal> admitOriginal(const ClosedEntry &,
                                              llvm::StringRef original,
                                              llvm::StringRef interface,
                                              const Limits & = {});
/// Retains immutable source, exact unsimplified MLIR, correspondence and public
/// interface data. There is deliberately no mutable ModuleOp success handle.
class CheckedOriginal {
public:
  const ClosedEntry &entry() const;
  llvm::StringRef bytes() const;
  llvm::StringRef identity() const;
  llvm::StringRef interfaceJson() const;
  const LanguageInterface &interface() const;
  llvm::StringRef toolchain() const;
  llvm::StringRef locationsIdentity() const;
  llvm::ArrayRef<SourceLocation> locations() const;
  const Correspondence &correspondence() const;
  /// Ceilings under which this immutable original and interface were admitted.
  const Limits &admissionLimits() const;

private:
  friend struct detail::OriginalAccess;
  static llvm::Expected<CheckedOriginal> admit(const ClosedEntry &,
                                               llvm::StringRef, llvm::StringRef,
                                               const Limits &,
                                               bool requireCanonical);
  friend llvm::Expected<CheckedOriginal> prepareOriginal(const ClosedEntry &,
                                                         const Limits &);
  struct Storage;
  std::shared_ptr<const Storage> storage;
  explicit CheckedOriginal(std::shared_ptr<const Storage> storage)
      : storage(std::move(storage)) {}
  friend llvm::Expected<CheckedOriginal> admitOriginal(const ClosedEntry &,
                                                       llvm::StringRef,
                                                       llvm::StringRef,
                                                       const Limits &);
};
/// Strict comparison with the independently retained interface. Unknown fields,
/// duplicate keys, another Entry, another environment, and dangling port edits
/// all refuse. JSON member order and whitespace are ignored by this comparison.
/// This diagnostic query does not admit a publication; use admitOriginal to
/// authorize canonical bytes against source.
llvm::Error checkInterface(const CheckedOriginal &, llvm::StringRef,
                           const Limits & = {});
/// Derive the logical proof policy from the admitted source/interface. Draw
/// occurrence selection remains the responsibility of common construction.
/// Refuses Host and run Entries. Machine targets consume this same mapping.
llvm::Expected<NativeProofPolicy> proofPolicy(const CheckedOriginal &);
std::string compilerToolchainIdentity();
} // namespace zkc::language
#endif

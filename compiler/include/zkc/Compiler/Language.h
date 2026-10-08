#ifndef ZKC_COMPILER_LANGUAGE_H
#define ZKC_COMPILER_LANGUAGE_H
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Translation/Language.h"
#include <memory>
#include <variant>

namespace zkc::language {
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
std::string compilerToolchainIdentity();
struct EntryOptions {
  bool simplify = true;
  bool releaseStorage = false;
};
using EntryArtifact = std::variant<CompiledRun, CompiledNativeProof>;
class CompiledEntry {
public:
  const CheckedOriginal &original() const { return source; }
  const EntryArtifact &artifact() const { return compiled; }
  const EntryOptions &options() const { return configuration; }
  /// Exact selected run bundle or proof deployment, as identified by
  /// artifact().
  llvm::StringRef bytes() const;

private:
  CompiledEntry(CheckedOriginal source, EntryArtifact compiled,
                EntryOptions options)
      : source(std::move(source)), compiled(std::move(compiled)),
        configuration(options) {}
  CheckedOriginal source;
  EntryArtifact compiled;
  EntryOptions configuration;
  friend llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                                    const EntryOptions &);
};
/// Compile the explicitly selected run or proof job. Derived challenge
/// occurrences are resolved through native construction admission. Uses the
/// built-in registry; caller extensions cannot replace its models.
llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                           const EntryOptions & = {});
} // namespace zkc::language
#endif

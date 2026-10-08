#ifndef ZKC_COMPILER_LANGUAGE_H
#define ZKC_COMPILER_LANGUAGE_H
#include "zkc/Compiler/LanguageInterface.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Translation/Language.h"
#include <memory>

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
/// all refuse. JSON member order and whitespace do not determine identity.
llvm::Error checkInterface(const CheckedOriginal &, llvm::StringRef,
                           const Limits & = {});
std::string compilerToolchainIdentity();
struct EntryRunOptions {
  bool simplify = true;
  bool releaseStorage = false;
};
class CompiledEntry {
public:
  const CheckedOriginal &original() const { return source; }
  const CompiledRun &run() const { return compiled; }

private:
  CompiledEntry(CheckedOriginal source, CompiledRun compiled)
      : source(std::move(source)), compiled(std::move(compiled)) {}
  CheckedOriginal source;
  CompiledRun compiled;
  friend llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                                    const EntryRunOptions &);
};
/// Selects the checked Entry's protocol symbol. Source aliases and the legacy
/// default 'main' are never interpreted as run symbols. Uses the same built-in
/// registry as original checking; caller extensions cannot replace its models.
llvm::Expected<CompiledEntry> compileEntry(const CheckedOriginal &,
                                           const EntryRunOptions & = {});
} // namespace zkc::language
#endif

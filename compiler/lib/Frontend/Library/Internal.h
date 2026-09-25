#ifndef ZKC_FRONTEND_LIBRARY_INTERNAL_H
#define ZKC_FRONTEND_LIBRARY_INTERNAL_H
#include "zkc/Frontend/Library.h"
#include <functional>

namespace zkc::frontend::library::detail {
llvm::Error fail(llvm::StringRef code, llvm::Twine message);
struct Writer {
  std::string bytes;
  void add(llvm::StringRef s) {
    bytes += std::to_string(s.size()) + ":" + s.str();
  }
  void add(uint64_t n) { add(std::to_string(n)); }
  template <typename T, typename F> void list(const T &xs, F f) {
    add(xs.size());
    for (const auto &x : xs)
      f(x);
  }
};
std::string encode(const Environment &);
std::string encode(const InterfaceDecl &);
std::string encode(const Body &);
std::string hash(llvm::StringRef);
// Empty success means no installed interpretation (e.g. a public parameter).
llvm::Expected<std::string>
installedDomain(const StaticTerm &, const Environment &, unsigned depth = 0);
llvm::Expected<std::string> normalizedTypeIdentity(const Type &,
                                                   const Environment &);
// Exact structural counterpart for self-contained descriptor interning.
llvm::Expected<std::string> normalizedTypeTree(const Type &,
                                               const Environment &);
bool sameSort(const Sort &, const Sort &);
const StaticDeclaration *findStatic(const QualifiedDecl &, const Environment &);
llvm::Error validateEnvironment(const Environment &);
llvm::Error extends(const Environment &assumed, const Environment &actual);
/// Check only the declarations and contracts reached by a public interface.
/// The interface's own judgment still retains its full owner environment.
llvm::Error importsInterface(const Interface &, const Environment &);
llvm::Error captured(const QualifiedDecl &, const Environment &);
llvm::Error validateSort(const Sort &);
llvm::Error validateRequirements(const std::vector<Requirement> &,
                                 const Environment &);
llvm::Error prove(const std::vector<Requirement> &assumptions,
                  const std::vector<Requirement> &goals, const Environment &);
llvm::Expected<std::vector<Requirement>>
assumptions(const std::vector<TypeBound> &, const std::vector<Import> &,
            std::vector<Requirement>, const Environment &);
struct TypeContext {
  const Environment &environment;
  const std::vector<Import> &imports;
  const std::vector<TypeBound> &bounds;
  const InterfaceDecl *forming = nullptr;
};
llvm::Expected<Permissions> permissions(const Type &, const TypeContext &,
                                        unsigned depth = 0);
llvm::Error signature(const Signature &, const TypeContext &);
llvm::Expected<Signature> sourceSignature(const SourceCall &,
                                          const TypeContext &);
llvm::Error matchesCallable(const Callable &, const CheckedBody &);
llvm::Expected<Type> placeType(const Type &, llvm::ArrayRef<unsigned>,
                               const TypeContext &);
llvm::Expected<std::vector<Type>> children(const Type &, const Environment &);
StaticTerm replace(const StaticTerm &, const StaticTerm &, const StaticTerm &);
Type replace(const Type &, const StaticTerm &, const StaticTerm &);
Signature replace(const Signature &, const StaticTerm &, const StaticTerm &);
Requirement replace(const Requirement &, const StaticTerm &,
                    const StaticTerm &);
llvm::Error checkAttributes(const LogicalCall &,
                            const std::vector<std::string> &,
                            const Environment &);
llvm::Expected<Signature> logicalSignature(const LogicalCall &,
                                           const Environment &);
llvm::Error equalTypes(const Type &, const Type &,
                       const std::vector<Requirement> &, const Environment &);
} // namespace zkc::frontend::library::detail
#endif

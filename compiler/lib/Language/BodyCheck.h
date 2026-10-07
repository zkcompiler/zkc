#ifndef ZKC_LANGUAGE_BODYCHECK_H
#define ZKC_LANGUAGE_BODYCHECK_H
#include "Checker.h"
namespace zkc::language::detail {
class BodyChecker {
public:
  BodyChecker(Checker &, Declaration &, const SyntaxDeclaration &, Body &,
              unsigned);
  bool run(const SyntaxBody &, llvm::ArrayRef<Port>, bool protocol);
  bool addService(const ServicePort &);
  bool addInput(llvm::StringRef, const Type &, std::vector<unsigned>, Span);

private:
  Checker &checker;
  Declaration &decl;
  const SyntaxDeclaration &syntax;
  Body &body;
  unsigned callDepth;
  uint32_t statement = 0;
  std::optional<unsigned> owner;
  std::optional<std::vector<unsigned>> activeRoles;
  std::map<std::string, ValueId> bindings;
  std::map<std::string, ServiceId> services;
  std::optional<ServiceId> service(const Expression &);
  struct Uses {
    std::vector<std::vector<unsigned>> used, moved;
  };
  std::vector<Uses> uses;
  bool math() const { return body.mode == Body::Mode::Math; }
  bool local() const { return body.mode == Body::Mode::Local; }
  bool protocol() const { return body.mode == Body::Mode::Protocol; }
  bool fail(llvm::StringRef, const llvm::Twine &, Span);
  std::vector<unsigned> allRoles() const;
  std::optional<std::vector<unsigned>> combine(llvm::ArrayRef<ValueId>, Span);
  std::optional<ValueId> emit(decltype(Operation::action), const Type &,
                              std::vector<unsigned>, Span);
  std::optional<std::vector<ValueId>> emitResults(decltype(Operation::action),
                                                  std::vector<Value>, Span);
  bool application(const Statement &);
  bool repeat(const Statement &);
  bool complete(const Statement &);
  std::optional<ValueId> kernel(const Expression &, unsigned);
  std::optional<Checker::CallSignature> kernelSignature(const Expression &,
                                                        std::vector<Type> &);
  std::optional<ValueId> intrinsic(const Expression &, unsigned);
  std::optional<Checker::CallSignature> intrinsicSignature(const Expression &,
                                                           std::vector<Type> &);
  bool active(llvm::ArrayRef<unsigned>, Span);
  bool use(ValueId, Span, llvm::ArrayRef<unsigned> = {});
  bool finish(Span);
  bool data(const Type &, Span);
  bool restricted(const Type &);
  std::optional<Type> projected(Type, llvm::ArrayRef<unsigned>, Span);
  std::optional<Type> hint(uint32_t, unsigned = 1);
  std::optional<ValueId> expression(uint32_t, std::optional<Type> = {},
                                    unsigned = 1);
  std::optional<ValueId> call(const Expression &, std::optional<Type>,
                              unsigned);
  std::optional<ValueId> control(const Expression &, std::optional<Type>,
                                 unsigned);
  std::optional<ValueId> construct(const Expression &, std::optional<Type>,
                                   unsigned);
  std::optional<std::pair<ValueId, std::vector<unsigned>>> place(uint32_t,
                                                                 unsigned = 1);
  std::optional<std::pair<DeclarationId, std::optional<Type>>>
  callable(const Expression &);
  bool infer(const Type &, const Type &, Substitution &, Span);
  std::optional<std::vector<Type>> actuals(const Declaration &,
                                           const Expression &,
                                           llvm::ArrayRef<std::optional<Type>>,
                                           std::optional<Type>,
                                           std::optional<Type>);
};
} // namespace zkc::language::detail
#endif

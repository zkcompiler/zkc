#ifndef ZKC_LANGUAGE_BODYCHECK_H
#define ZKC_LANGUAGE_BODYCHECK_H
#include "Checker.h"
#include "Placement.h"
namespace zkc::language::detail {
class BodyChecker {
public:
  BodyChecker(Checker &, Declaration &, const SyntaxDeclaration &, Body &,
              unsigned);
  bool run(const SyntaxBody &, llvm::ArrayRef<Port>, bool protocol);
  bool addService(BindingId, const ServicePort &);
  bool addInput(BindingId, const Type &, std::vector<unsigned>, Span);

private:
  Checker &checker;
  Declaration &decl;
  const SyntaxDeclaration &syntax;
  Body &body;
  unsigned callDepth;
  uint32_t statement = 0;
  Placement *placement = nullptr;
  struct StatementPlacement {
    BodyChecker &checker;
    Placement *outer;
    std::optional<Placement> state;
    explicit StatementPlacement(BodyChecker &);
    StatementPlacement(const StatementPlacement &) = delete;
    StatementPlacement &operator=(const StatementPlacement &) = delete;
    ~StatementPlacement();
    bool commit();
  };
  Components components(ValueId) const;
  bool demand(ValueId, llvm::ArrayRef<unsigned>, Span);
  bool settle(Placement &);
  std::optional<std::vector<unsigned>> activeRoles;
  struct BindingState {
    Type type;
    std::vector<unsigned> roles;
    std::optional<ValueId> value;
    // Inferred free-place inputs retain their original source projection paths.
    std::vector<std::pair<std::vector<unsigned>, ValueId>> pieces;
  };
  std::map<BindingId, BindingState> bindings;
  std::map<BindingId, ServiceId> services;
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
  std::optional<Components> combine(llvm::ArrayRef<ValueId>, Span);
  std::optional<ValueId> emit(decltype(Operation::action), const Type &,
                              Components, Span);
  std::optional<std::vector<ValueId>> emitResults(decltype(Operation::action),
                                                  std::vector<Value>, Span);
  std::optional<std::vector<ValueId>> application(const Expression &);
  bool repeat(const Expression &);
  std::optional<std::vector<ValueId>> complete(const Statement &);
  std::optional<ValueId> kernel(const Expression &, unsigned);
  std::optional<Semantics::CallSignature> kernelSignature(const Expression &,
                                                          std::vector<Type> &);
  std::optional<ValueId> intrinsic(const Expression &, unsigned);
  std::optional<Semantics::CallSignature>
  intrinsicSignature(const Expression &, std::vector<Type> &);
  bool active(llvm::ArrayRef<unsigned>, Span);
  bool use(ValueId, Span, llvm::ArrayRef<unsigned> = {});
  bool finish(Span);
  bool finishValue(ValueId, Span);
  bool available(ValueId, llvm::ArrayRef<unsigned> = {});
  bool intersectUses(Uses &, const Uses &, Span);
  std::optional<ValueId> input(const Type &, std::vector<unsigned>, Span);
  bool bindPattern(const Pattern &, ValueId, unsigned = 1);
  bool bindResults(const Statement &, llvm::ArrayRef<ValueId>);
  bool assign(BindingId, ValueId, Span);
  bool discard(ValueId, Span);
  std::optional<ValueId> restrictRoles(ValueId, llvm::ArrayRef<unsigned>, Span);
  std::optional<ValueId> fresh(ValueId, Span);
  std::optional<ValueId> pack(llvm::ArrayRef<ValueId>, Span);
  std::optional<ValueId> project(ValueId, llvm::ArrayRef<unsigned>, Span);
  bool statements(const SyntaxBody &);
  std::optional<ValueId> tail(const SyntaxBody &, std::optional<Type>,
                              bool allowUntypedStop = false);
  std::optional<ValueId> block(const Expression &, std::optional<Type>,
                               bool allowUntypedStop);
  std::optional<std::pair<BindingId, std::vector<unsigned>>>
  sourcePlace(uint32_t, unsigned = 1);
  struct FreePlace {
    BindingId binding;
    std::vector<unsigned> path;
    bool operator<(const FreePlace &other) const {
      return binding == other.binding ? path < other.path
                                      : binding < other.binding;
    }
  };
  struct RegionInputs {
    std::set<FreePlace> places;
    std::set<BindingId> writes, services;
  };
  std::optional<RegionInputs> regionInputs(const Expression &);
  std::optional<std::set<BindingId>> regionStates(const RegionInputs &, Span);
  std::optional<ValueId> capturePlace(const FreePlace &, Span);
  std::optional<std::pair<ValueId, std::vector<unsigned>>>
  place(const FreePlace &, Span);
  bool importPlace(BodyChecker &, const FreePlace &, ValueId, Span);
  bool inheritBinding(BodyChecker &, BindingId, Span);
  bool data(const Type &, Span);
  bool restricted(const Type &);
  std::optional<Type> projected(Type, llvm::ArrayRef<unsigned>, Span);
  std::optional<Type> hint(uint32_t, unsigned = 1);
  std::optional<ValueId> expression(uint32_t, std::optional<Type> = {},
                                    unsigned = 1,
                                    bool allowUntypedStop = false);
  std::optional<ValueId> evaluate(uint32_t, std::optional<Type>, unsigned,
                                  bool allowUntypedStop);
  std::optional<ValueId> call(const Expression &, std::optional<Type>,
                              unsigned);
  std::optional<ValueId> control(const Expression &, std::optional<Type>,
                                 unsigned, bool allowUntypedStop);
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

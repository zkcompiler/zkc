#ifndef ZKC_LANGUAGE_SCOPEDWITNESS_H
#define ZKC_LANGUAGE_SCOPEDWITNESS_H
#include "Internal.h"
#include "TypeInference.h"
namespace zkc::language::detail {
/// Formation has already resolved the carrier and validated/canonicalized the
/// decimal using the ordinary literal rules. Candidate values never own these.
using SourceLiterals = std::map<uint32_t, std::pair<Type, std::string>>;
/// Usage resolution determines which authored states remain wholly available.
/// Recipe operands are eager references in the owning authored value space.
/// Neither record supplies expected evaluation order or mutable generations.
struct SourceControlSnapshot {
  std::vector<BindingId> initial, joined;
  std::vector<ValueId> recipes;
};
using SourceControlSnapshots = std::map<uint32_t, SourceControlSnapshot>;
struct ScopedSource {
  DeclarationId owner;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
  struct Place {
    Type type;
    std::optional<ValueId> value;
    std::vector<std::pair<std::vector<unsigned>, ValueId>> pieces;
  };
  std::map<BindingId, Place> environment;
  std::map<BindingId, unsigned> scoped, domains;
  ScopedSignature signature;
  std::shared_ptr<const NotationFamilies> notationFamilies;
  /// Frozen resolved nominal instantiations, like SourceCall::arguments.
  /// Independent replay never takes static arguments from candidate values.
  std::shared_ptr<const std::map<uint32_t, Type>> enumTypes;
  std::shared_ptr<const SelectedCallable> named = {};
  /// Resolved static source terms, retained before constructing repeat bodies.
  std::shared_ptr<const std::map<uint32_t, Natural>> repeatMaxima;
  std::shared_ptr<const SourceLiterals> literals;
  std::shared_ptr<const SourceControlSnapshots> controlSnapshots;
};
struct ScopedInvocationSource {
  DeclarationId owner;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
};
/// An immutable resolved source occurrence. SSA operands and service slots are
/// reconstructed from syntax and the candidate graph, never copied here.
struct SourceCall {
  DeclarationId owner, target;
  uint32_t expression;
  std::shared_ptr<const SyntaxDeclaration> syntax;
  std::optional<Type> module = {};
  std::vector<Type> arguments = {};
  ResolvedReference reference = {};
};
struct DomainCallSource {
  CallableReference target;
  std::vector<Type> arguments;
};
struct ScopedCallSource : SourceCall {
  std::map<BindingId, unsigned> scoped, domains;
  std::map<uint32_t, DomainCallSource> domainCalls;
  std::shared_ptr<const AuthoredOperatorFamily> notationFamily = {};
};
/// One replay's source-derived inventory. Selected Protocol Math wrappers have
/// their own key within the containing lexical region. Candidate associations
/// are populated only after exact control coverage has been authenticated.
struct SourceOccurrences {
  using Region = std::pair<uint32_t, std::optional<uint32_t>>;
  struct Binding {
    BindingId binding;
    Span span;
    std::optional<uint32_t> expression;
    std::optional<unsigned> parameter;
    std::vector<std::string> path;
    std::optional<Span> exchange = {};
    bool input = false;
  };
  std::map<Region, std::vector<Binding>> bindings;
  std::map<Region, std::vector<uint32_t>> controls;
  /// Continuing control/block values cannot opt out by omitting their map.
  std::map<Region, std::vector<uint32_t>> values;
  std::map<const Body *, Region> candidates;
};
bool checkScopedValues(Semantics &, const CheckedStorage &,
                       const ScopedSource &, const ScopedBinding &);
bool checkInvocationValues(Semantics &, const CheckedStorage &,
                           const ScopedSource &, const Body &,
                           const SourceOccurrences &);
llvm::Error checkScopedSources(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif

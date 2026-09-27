#ifndef ZKC_CONTRACTS_GENERIC_H
#define ZKC_CONTRACTS_GENERIC_H

#include "zkc/Contracts/Requirements.h"
#include <map>

namespace zkc::generic {

/// A static scope is a topologically ordered, interned requirement-term DAG.
/// Sort tokens encode kinds injectively: Domain uses its installed sort name,
/// Type uses reserved "Type", and Nat uses reserved "Nat". Owning declaration
/// admission preserves the original kind and forbids domain sorts named Type
/// or Nat; these strings do not erase kinds or introduce another type model.
/// Only roots without constants or arguments are formal static arguments, in
/// term order. Applications (including nullary ones) have sort Type, an
/// installed constructor head, ordered arguments, and no parent or constant.
struct Scope {
  std::vector<requirements::Term> terms;
  std::vector<std::string> sorts;
  /// Rigid roots introduced by partial configuration, never caller arguments.
  /// Identity is the pair (sort token, canonical identity), not the term name.
  /// Strings are kind-interpreted at owning admission: Domain is an installed
  /// identity, Type is a canonical logical spelling, and Nat is canonical
  /// decimal in 0..1048576. Generic checking validates Type and Nat through
  /// their canonical admission validators. Domain identity admission remains
  /// with the owner. Type constants use the logical type spelling bounds;
  /// non-Type constant storage is bounded at 255 bytes. No capability or copy
  /// permission follows from a constant without the corresponding admission.
  std::map<unsigned, std::string> constants = {};
};

/// A shallow logical head with scope indices. Nested Type arguments are
/// requirements::Term applications in that scope, not erased domain names.
struct Type {
  std::string constructor;
  std::vector<unsigned> arguments;
};

struct TypeConstructor {
  std::string name;
  /// The same injective kind/sort tokens as Scope::sorts, supplied only by
  /// installed declarations. A source signature cannot declare constructor
  /// facts by introducing an application.
  std::vector<std::string> parameters;
  /// Base affinity. An application is also affine if any Type argument is
  /// affine; a Type root/projection has unknown permission and is conservative
  /// affine because this generic profile has no copy bounds.
  bool affine = false;
};

struct Signature {
  Scope scope;
  std::vector<Type> inputs, outputs;
  std::vector<requirements::Predicate> requirements;
};

/// Installed logical signatures; selecting a physical implementation is later.
struct Operation {
  std::string name;
  Signature signature;
};

struct Call {
  std::string site;
  std::string operation;
  std::vector<unsigned> staticArguments;
  std::vector<unsigned> inputs;
  // Region-local value indices: if inputs are condition then captures; for
  // inputs are bounds, carried values, then captures. Region arguments follow
  // captures for if, or induction/carried/captures for for. Result indices are
  // allocated in the enclosing scope only; regions cannot refer to outer SSA.
  enum class Kind { Operation, Conditional, For };
  Kind kind = Kind::Operation;
  unsigned carried = 0;
  std::vector<Call> body = {}, elseBody = {};
  std::vector<unsigned> yields = {}, elseYields = {};
};

/// Static view of a local body. The owning source retains operation attributes,
/// origins and effect/resource contracts. Result positions follow arguments and
/// earlier results. This checker does not reorder or erase the actual source.
struct Function {
  Signature signature;
  std::vector<Call> body;
  std::vector<unsigned> returns;
};

struct Inference {
  Scope scope;
  std::vector<Type> values;
  std::vector<requirements::Predicate> obligations;
};

struct CheckedFunction {
  Inference inferred;
  requirements::Result derivation;
};

/// Infer every operation/signature obligation, including unused producers.
/// Unknown operations, bad sorts and malformed references are errors. This
/// does not establish that a public signature promises enough for the body.
llvm::Expected<Inference> infer(const Function &function,
                                llvm::ArrayRef<TypeConstructor> constructors,
                                llvm::ArrayRef<Operation> operations);

/// Check the public promise against actual inferred needs, with derivations.
llvm::Expected<CheckedFunction>
check(const Function &function, llvm::ArrayRef<TypeConstructor> constructors,
      llvm::ArrayRef<Operation> operations,
      llvm::ArrayRef<requirements::Implication> implications);

/// Instantiate a signature into a copied caller scope. The returned signature
/// owns the extended scope: no shared definition or caller binding is mutated.
/// This checks scope formation and substitution, not constructor declarations;
/// infer/check validate applications against the supplied installed table.
llvm::Expected<Signature> instantiate(const Signature &signature,
                                      llvm::ArrayRef<unsigned> arguments,
                                      const Scope &caller);

} // namespace zkc::generic

#endif

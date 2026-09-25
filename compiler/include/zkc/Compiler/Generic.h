#ifndef ZKC_COMPILER_GENERIC_H
#define ZKC_COMPILER_GENERIC_H

#include "zkc/Compiler/Requirements.h"
#include <map>

namespace zkc::generic {

/// A static scope has ordered, interned identities and their declared sorts.
/// Roots of a signature are its formal static arguments, in term order.
struct Scope {
  std::vector<requirements::Term> terms;
  std::vector<std::string> sorts;
  /// Fixed nominal roots introduced by partial configuration. These are not
  /// formal arguments and are never supplied by the caller. No capability
  /// follows from a fixed root without checking the installed domain facts.
  std::map<unsigned, std::string> constants = {};
};

struct Type {
  std::string constructor;
  std::vector<unsigned> arguments;
};

struct TypeConstructor {
  std::string name;
  std::vector<std::string> parameters;
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
llvm::Expected<Signature> instantiate(const Signature &signature,
                                      llvm::ArrayRef<unsigned> arguments,
                                      const Scope &caller);

} // namespace zkc::generic

#endif

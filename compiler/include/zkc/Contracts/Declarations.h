#ifndef ZKC_CONTRACTS_DECLARATIONS_H
#define ZKC_CONTRACTS_DECLARATIONS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include <optional>
#include <string>
#include <vector>

namespace zkc::protocol {
enum class StaticKind { Domain, Type, Nat };
struct StaticParameter {
  StaticKind kind;
  /// Only Domain parameters carry an installed sort name.
  std::string sort;
  bool operator==(const StaticParameter &other) const {
    return kind == other.kind && sort == other.sort;
  }
};
struct CapabilityDeclaration {
  std::string name;
  std::vector<StaticParameter> parameters;
};
struct AssociatedMemberDeclaration {
  std::string name;
  StaticParameter owner, result;
};
struct TypeDeclaration {
  std::string name;
  std::vector<StaticParameter> parameters;
  bool common;
};
llvm::ArrayRef<TypeDeclaration> typeDeclarations();
const TypeDeclaration *typeDeclaration(llvm::StringRef name);
llvm::ArrayRef<std::string> domainSorts();
llvm::ArrayRef<CapabilityDeclaration> capabilityDeclarations();
llvm::ArrayRef<AssociatedMemberDeclaration> associatedMemberDeclarations();

enum class AuthoringStage { Source, Construction, CompilerGenerated, Physical };
/// Unknown contracts are CompilerGenerated, and never source authorable.
AuthoringStage authoringStage(llvm::StringRef contract);

struct SourceTypeExport {
  std::string module, name, constructor;
};
struct SourceOperationExport {
  std::string module, name, contract;
  std::vector<std::string> inputLabels;
};
/// A finite source type family reduces after its element head is known.
/// It does not introduce a new common logical constructor.
struct SourceTypeFamilyCase {
  std::string family, elementConstructor, resultConstructor;
};
struct SourceAssociatedType {
  std::string sort, member, constructor;
};
struct SourceCapabilityExport {
  std::string module, name, predicate;
};
llvm::ArrayRef<SourceTypeFamilyCase> sourceTypeFamilies();
llvm::ArrayRef<SourceAssociatedType> sourceAssociatedTypes();
llvm::ArrayRef<SourceCapabilityExport> sourceCapabilityExports();
struct SourceOperatorBinding {
  std::string symbol;
  std::vector<std::string> operands;
  std::string contract;
  /// order[k] is the written operand passed to logical input k.
  std::vector<unsigned> order;
};
llvm::ArrayRef<SourceTypeExport> sourceTypeExports();
llvm::ArrayRef<SourceOperationExport> sourceOperationExports();
llvm::ArrayRef<SourceOperatorBinding> sourceOperatorBindings();

enum class Custody { Unknown, PublicValue, PrivateImmutable, Affine };
struct TypePermissions {
  bool copy, drop;
  Custody custody;
};
/// Constructor permissions only; formation and variant recursion are separate.
const TypePermissions *typePermissions(llvm::StringRef constructor);

enum class ParameterValidator {
  None,
  Natural,
  Extent,
  FieldLiteral,
  FieldLiterals,
  MatrixShape,
  MatrixIdentity,
  AssetIdentity,
  MatrixVector,
  GatherIndices,
  ScatterIndices,
  NativeOrigin
};
struct ParameterContract {
  ParameterValidator validator;
  unsigned minimum;
  std::optional<unsigned> maximum;
  /// Scoped Field term used by literal validation; not a root argument index.
  std::optional<unsigned> fieldTerm = {};
};
const ParameterContract *parameterContract(llvm::StringRef contract);
} // namespace zkc::protocol
#endif

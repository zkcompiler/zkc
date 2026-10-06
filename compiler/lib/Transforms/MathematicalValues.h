#ifndef ZKC_TRANSFORMS_MATHEMATICALVALUES_H
#define ZKC_TRANSFORMS_MATHEMATICALVALUES_H
#include "zkc/Dialect/Operations.h"
#include "llvm/ADT/DenseMap.h"
#include <map>
#include <memory>
namespace zkc::mathematical {
// Invocation-local terms over positional inputs and ordered action results.
// This checker never emits MLIR or invokes an expansion/rewrite producer.
class ValueCorrespondence {
public:
  using Term = unsigned;
  using Environment = unsigned;
  struct Expression {
    mlir::Type type;
    mlir::StringAttr name;
    mlir::DictionaryAttr attributes;
    llvm::SmallVector<Term> operands;
    unsigned coordinate = 0;
  };
  explicit ValueCorrespondence(mlir::Operation *diagnostic,
                               bool roleComponents = false);
  ~ValueCorrespondence();
  Environment environment();
  Term anchor(mlir::Type type);
  Expression expression(Term term) const;
  Term expression(llvm::StringRef name, mlir::Type type,
                  mlir::DictionaryAttr attributes, llvm::ArrayRef<Term> inputs,
                  unsigned coordinate = 0);
  Term restrictRoles(Term input, mlir::Type type, mlir::ArrayAttr roles);
  void roleMap(Environment environment, mlir::ArrayAttr from,
               mlir::ArrayAttr to);
  void roleComponent(Environment environment, mlir::StringAttr role);
  void bind(Environment environment, mlir::Value value, Term term);
  Term value(Environment environment, mlir::Value value);
  bool equal(Term a, Term b);
  bool compare(Environment a, mlir::Value x, Environment b, mlir::Value y);
  bool charge(size_t amount = 1);
  mlir::LogicalResult refuse(llvm::StringRef detail);

private:
  struct Implementation;
  std::unique_ptr<Implementation> implementation;
};
struct PolynomialValueCache {
  llvm::DenseMap<unsigned, unsigned> normal;
  std::map<std::pair<unsigned, std::vector<unsigned>>, unsigned> evaluations;
  llvm::DenseMap<unsigned, llvm::SmallVector<unsigned>> coefficients;
};
ValueCorrespondence::Term
normalizePolynomialFixings(ValueCorrespondence &terms,
                           ValueCorrespondence::Term value,
                           PolynomialValueCache &cache);
ValueCorrespondence::Term
normalizePolynomialValues(ValueCorrespondence &terms,
                          ValueCorrespondence::Term value,
                          PolynomialValueCache &cache);
mlir::LogicalResult verifyPreparedValues(protocol_ir::ProtocolModuleOp before,
                                         protocol_ir::ProtocolModuleOp after);
mlir::LogicalResult
verifyParticipantValues(protocol_ir::ProtocolModuleOp before,
                        protocol_ir::ProtocolModuleOp after);
mlir::LogicalResult verifyProjectedValues(protocol_ir::ProtocolModuleOp before,
                                          protocol_ir::ProtocolModuleOp after);
} // namespace zkc::mathematical
#endif

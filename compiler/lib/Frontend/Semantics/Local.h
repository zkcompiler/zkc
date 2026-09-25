#ifndef ZKC_FRONTEND_SEMANTICS_LOCAL_H
#define ZKC_FRONTEND_SEMANTICS_LOCAL_H

#include "../Syntax/Tree.h"
#include "Aggregates.h"
#include "Bindings.h"
#include "zkc/Frontend/Analysis.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/Twine.h"
#include <functional>
#include <map>

namespace zkc::frontend {
using LocalTypes = std::map<std::string, std::string>;
/// Struct information exchanged around one call. `operands` and `results`
/// have one entry per authored operand and result; `outputs` are the flat
/// result names the call binds.
struct CallShapes {
  Shapes operands, results;
  source::Names outputs;
};
/// One authored field initializer of a struct construction.
struct ConstructedField {
  std::string name;
  source::Names values;
  std::optional<AggregateShape> shape;
};
/// The call a declared operator stands for. `order[k]` is the authored
/// operand passed as the target's k-th argument.
struct OperatorTarget {
  std::string callee;
  bool qualified = false;
  std::vector<unsigned> order;
};
struct LocalCallbacks {
  std::function<std::optional<std::vector<unsigned>>(const syntax::Call &)>
      argumentOrder;
  // Formal expected types, queried only after the label bijection is checked.
  std::function<std::vector<std::optional<syntax::Type>>(
      const syntax::Call &, const LocalTypes &, const Shapes &)>
      argumentTypes;
  std::function<std::vector<std::optional<syntax::Type>>(
      const syntax::Expression &,
      const std::optional<std::vector<syntax::Type>> &)>
      fieldTypes;
  /// `inputs` are flat values; `outputs` are the authored result names.
  std::function<std::optional<source::Instruction::Value>(
      const syntax::Call &, LocalTypes &, llvm::StringRef, CallShapes &)>
      call;
  std::function<std::string(const syntax::Type &)> type;
  std::function<std::optional<AggregateShape>(const syntax::Type &)> aggregate;
  std::function<bool(llvm::StringRef, llvm::StringRef, const source::Node &)>
      same;
  /// Check a construction and return the shape of the constructed value.
  std::function<std::optional<AggregateShape>(const syntax::Expression &,
                                              llvm::ArrayRef<ConstructedField>,
                                              const LocalTypes &)>
      construct;
  std::function<AggregateShape(llvm::ArrayRef<ConstructedField>,
                               const LocalTypes &)>
      product;
  std::function<bool(const AggregateShape &, const AggregateShape &,
                     const source::Node &)>
      sameAggregate;
  /// Select the one declaration for a symbol and the operands' logical types.
  std::function<std::optional<OperatorTarget>(const syntax::Expression &,
                                              llvm::ArrayRef<std::string>)>
      resolveOperator;
  std::function<void(const source::Node &, llvm::StringRef,
                     const llvm::Twine &)>
      fail;
  std::function<bool()> good;
  /// The enclosing function's authored results, one entry per result.
  bool inferResult = false;
  std::function<void(const source::Names &,
                     const std::optional<AggregateShape> &, const LocalTypes &)>
      returned;
  Shapes results;
  source::Names resultTypes;
  std::optional<syntax::Type> resultAnnotation;
};
/// Elaborate lexical bindings into explicit, isolated SSA control regions.
source::Body elaborateLocal(const syntax::Body &, LocalTypes, LocalAggregates,
                            const LocalCallbacks &, semantics::LocalSymbols &);
} // namespace zkc::frontend
#endif

#ifndef ZKC_RELATION_R1CS_H
#define ZKC_RELATION_R1CS_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <array>
#include <cstdint>
#include <string>
#include <vector>

namespace zkc::relation {

/// Limits on external relation data, independent of protocol ports or runtime
/// witness allocation. Readers validate counts before allocating storage.
struct Limits {
  static constexpr size_t bytes = 64 * 1024 * 1024;
  static constexpr uint32_t rows = 65536;
  static constexpr uint32_t columns = 65536;
  static constexpr size_t terms = 1 << 20;
};

struct Term {
  uint32_t column;
  std::string coefficient;
  bool operator==(const Term &other) const {
    return column == other.column && coefficient == other.coefficient;
  }
};
using LinearForm = std::vector<Term>;
using Constraint = std::array<LinearForm, 3>;

/// A fixed rank-one relation over an installed nominal field. Assignment layout
/// is [ONE, public outputs, public inputs, private witness]. An assignment is a
/// witness only when ONE=1, the public prefix matches the statement, and every
/// A(z)*B(z)=C(z) row holds. Signal labels/provenance belong to adapter
/// receipts; they do not authorize a different public layout.
///
/// Forms are normalized by combining repeated columns modulo the exact field,
/// removing zeros, and sorting columns. This does not deduplicate constraints
/// or reorder public values. Construction is the only mutation boundary.
class R1CS {
public:
  static llvm::Expected<R1CS> create(std::string field, uint32_t columns,
                                     uint32_t publicOutputs,
                                     uint32_t publicInputs,
                                     std::vector<Constraint> constraints);

  llvm::StringRef field() const { return fieldName; }
  uint32_t columns() const { return columnCount; }
  uint32_t publicOutputs() const { return outputCount; }
  uint32_t publicInputs() const { return inputCount; }
  uint32_t publicCount() const { return outputCount + inputCount; }
  uint32_t witnessCount() const { return columnCount - 1 - publicCount(); }
  llvm::ArrayRef<Constraint> constraints() const { return rows; }
  size_t nonzeros() const;

  /// Representation identity of this normalized relation, including field,
  /// public layout and ordered constraints. Not a decision procedure for
  /// semantic equivalence. Source provenance is deliberately excluded.
  std::string identity() const;
  llvm::json::Value encode() const;

  /// Preserve every assignment and public binding; remove only byte-equal
  /// normalized constraint rows, keeping the first occurrence's order.
  R1CS deduplicate() const;

private:
  R1CS(std::string field, uint32_t columns, uint32_t publicOutputs,
       uint32_t publicInputs, std::vector<Constraint> constraints);
  std::string fieldName;
  uint32_t columnCount, outputCount, inputCount;
  std::vector<Constraint> rows;
};

/// Strict canonical, versioned zkc interchange. No witness or generator state.
llvm::Expected<R1CS> decodeR1CS(const llvm::json::Value &);
/// Circom-compatible R1CS v1 container; reject custom gates and unknown
/// sections. The field is resolved by the exact modulus, never a
/// caller-selected default. This validates the target relation, not its
/// correspondence to a source circuit.
llvm::Expected<R1CS> readR1CS(llvm::StringRef bytes);

struct Evaluation {
  std::array<std::vector<std::string>, 3> products;
  bool bound = false;
  bool satisfied = false;
};
/// Independent interpreter for imported structure. Canonical field inputs and
/// exact vector lengths are required even when a row does not use a coordinate.
llvm::Expected<Evaluation> evaluate(const R1CS &,
                                    llvm::ArrayRef<std::string> statement,
                                    llvm::ArrayRef<std::string> assignment);

} // namespace zkc::relation

#endif

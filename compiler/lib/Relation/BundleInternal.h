#ifndef ZKC_RELATION_BUNDLE_INTERNAL_H
#define ZKC_RELATION_BUNDLE_INTERNAL_H

#include "zkc/Relation/Bundle.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace zkc::relation::bundle {

// Carrier helpers shared by the bundle, supplied-data and staged codecs.
bool validName(llvm::StringRef);
bool installedField(llvm::StringRef);
bool primeField(llvm::StringRef);
const llvm::json::Array *row(const llvm::json::Value &, size_t arity,
                             llvm::StringRef tag = {});
std::optional<uint64_t> natural(const llvm::json::Value &, uint64_t limit);
std::optional<int32_t> signedOffset(const llvm::json::Value &);
std::string printOffset(int32_t);
std::optional<std::string> string(const llvm::json::Value &);

llvm::Error checkScope(const BundleScope &);
llvm::json::Value encodeScope(const BundleScope &);
llvm::Expected<BundleScope> readScope(const llvm::json::Value &);
/// Active row range [lo,hi) of a scope on a present table. The caller has
/// already checked Interval's stop <= height.
std::pair<uint32_t, uint32_t> scopeRows(const BundleScope &, uint32_t height);
/// Static finite-window feasibility: the read is defined on every row of the
/// scope at every height on which the scope is nonempty.
bool staticWindow(const BundleScope &, int32_t offset);
/// Height-dependent remainder for one admitted height. Cyclic tables only
/// need the Interval stop condition.
llvm::Error windowAt(const BundleScope &, BundleReadModel, uint32_t height,
                     llvm::ArrayRef<int32_t> offsets);
/// Index of `row + offset` in a present table, for an admitted window.
uint32_t readRow(BundleReadModel, uint32_t height, uint32_t row,
                 int32_t offset);

/// Closed reference presentations for supplied-data value encoding and the
/// reference interpreter. A prime field has degree 1. The installed
/// extension `koala-bear.ext8-binomial3` is F_p[X]/(X^8 - 3) over koala-bear
/// with the ascending basis (docs/spec/domains/values.md). The domain catalog
/// records the base association but not the degree or defining polynomial.
struct Presentation {
  std::string prime;
  unsigned degree = 1;
  std::string nonresidue; // Empty for a prime field.
};
llvm::Expected<Presentation> presentation(llvm::StringRef field);

using Scalar = std::vector<llvm::APInt>;
class Arithmetic {
public:
  static llvm::Expected<Arithmetic> create(llvm::StringRef field);
  llvm::StringRef field() const { return field_; }
  llvm::StringRef prime() const { return prime_; }
  unsigned degree() const { return degree_; }
  llvm::Expected<llvm::APInt> parseCoordinate(llvm::StringRef) const;
  llvm::Expected<Scalar> parse(llvm::ArrayRef<std::string> coordinates) const;
  Scalar zero() const;
  Scalar constant(const llvm::APInt &) const;
  Scalar add(const Scalar &, const Scalar &) const;
  Scalar neg(const Scalar &) const;
  Scalar mul(const Scalar &, const Scalar &) const;
  bool isZero(const Scalar &) const;
  BundleColumns print(const Scalar &) const;
  /// The canonical natural representative of a prime-field element, if it
  /// fits in 64 bits.
  std::optional<uint64_t> natural(const Scalar &) const;

private:
  Arithmetic() = default;
  std::string field_, prime_;
  unsigned degree_ = 1, width_ = 0;
  llvm::APInt modulus_, nonresidue_;
};
class Fields {
public:
  llvm::Expected<const Arithmetic *> get(llvm::StringRef field);

private:
  std::vector<std::unique_ptr<Arithmetic>> fields;
};

llvm::json::Value encodeValue(const BundleColumns &);
/// Decode one element: a canonical decimal string for degree 1, otherwise an
/// array of exactly `degree` strings. Canonical ranges are checked later.
llvm::Error readValue(const llvm::json::Value &, unsigned degree,
                      BundleColumns &out);
llvm::Expected<std::vector<BundleColumns>>
readValues(const llvm::json::Value &, llvm::ArrayRef<std::string> fields);
llvm::Expected<BundleColumns>
readGroupValues(const llvm::json::Value &, unsigned degree, uint64_t &budget);
llvm::json::Value encodeGroupValues(const BundleColumns &, unsigned degree);

/// Ring algebra evaluating one row through ring::Expression::evaluate.
/// Constants are parsed once per (field, literal) across all rows.
struct RowAlgebra {
  Fields &fields;
  llvm::function_ref<llvm::Expected<Scalar>(uint32_t)> fetch;
  std::map<std::pair<std::string, std::string>, Scalar> &constants;
  llvm::Expected<Scalar> input(uint32_t index, llvm::StringRef) {
    return fetch(index);
  }
  llvm::Expected<Scalar> constant(llvm::StringRef field,
                                  llvm::StringRef literal);
  llvm::Expected<Scalar> add(llvm::StringRef field, const Scalar &,
                             const Scalar &);
  llvm::Expected<Scalar> mul(llvm::StringRef field, const Scalar &,
                             const Scalar &);
  llvm::Expected<Scalar> neg(llvm::StringRef field, const Scalar &);
  llvm::Expected<Scalar> embed(llvm::StringRef source, llvm::StringRef target,
                               const Scalar &);
};

/// Admitted supplied data: presence and heights per table, parsed public
/// slots and parsed group coordinates (bundle groups in group order).
struct Admitted {
  struct Table {
    bool present = false;
    uint32_t height = 0;
    std::vector<std::vector<llvm::APInt>> groups;
  };
  std::vector<Scalar> publics;
  std::vector<Table> tables;
  uint64_t work = 0;
};
llvm::Expected<Admitted> admitData(const Bundle &, const BundleConfiguration &,
                                   const BundleInstance &,
                                   const BundleWitness &, Fields &,
                                   llvm::StringRef identity);
Scalar element(const std::vector<llvm::APInt> &coordinates, unsigned degree,
               uint32_t width, uint32_t row, uint32_t column);
llvm::Error checkColumns(const BundleColumns &, uint64_t elements,
                         const Arithmetic &, std::vector<llvm::APInt> &out);

/// Output positions read by an interaction, in record order.
inline std::vector<uint32_t>
interactionOutputs(const BundleInteraction &interaction) {
  std::vector<uint32_t> outputs = interaction.tuple;
  outputs.push_back(interaction.count);
  return outputs;
}

/// Cumulative formation bounds, checked before traversing an arena for each
/// output or assertion and before retaining per-output input facts.
struct AnalysisBudget {
  uint64_t work = 0, inputs = 0;
  llvm::Error account(const ring::Expression &, uint64_t traversals,
                      uint64_t retainedOutputs);
};

/// Re-home a refusal with a diagnostic location, keeping its identifier.
llvm::Error withDetail(llvm::Error, llvm::StringRef detail);
/// Every declared input must be used and every output must be referenced.
llvm::Error checkOutputsUsed(const ring::Expression &,
                             llvm::ArrayRef<uint32_t> referenced);

} // namespace zkc::relation::bundle
#endif

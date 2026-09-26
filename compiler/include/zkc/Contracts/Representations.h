#ifndef ZKC_CONTRACTS_REPRESENTATIONS_H
#define ZKC_CONTRACTS_REPRESENTATIONS_H

#include "zkc/Contracts/Domains.h"
#include <cstdint>

namespace zkc::protocol {

/// Evidence about an actual installed (field, group, representation) tuple.
/// This licenses algebra on values of the subgroup carrier only. The consumer
/// must bind the tuple to its SSA value/version; it grants no transcript
/// rewrite.
class EdwardsScalarModule {
public:
  static llvm::Expected<EdwardsScalarModule>
  admit(const DomainCatalog &catalog, llvm::StringRef group,
        llvm::StringRef representation, llvm::StringRef scalar);
  const NominalDomain &scalarDomain() const { return scalar; }
  const NominalDomain &groupDomain() const { return group; }
  const DomainRepresentation &arithmeticRepresentation() const { return repr; }

private:
  EdwardsScalarModule(NominalDomain scalar, NominalDomain group,
                      DomainRepresentation repr);
  NominalDomain scalar, group;
  DomainRepresentation repr;
};

/// Logical Boolean coordinates in increasing bit significance. Admission checks
/// the supplied value extent; zero axes describes a scalar table of extent one.
class OrderedBooleanDomain {
public:
  static llvm::Expected<OrderedBooleanDomain> admit(std::vector<uint32_t> axes,
                                                    uint64_t valueExtent);
  const std::vector<uint32_t> &axes() const { return orderedAxes; }
  uint64_t extent() const { return valueExtent; }

private:
  OrderedBooleanDomain(std::vector<uint32_t> axes, uint64_t extent);
  std::vector<uint32_t> orderedAxes;
  uint64_t valueExtent;
};

enum class FoldConvention { Adjacent, HalfFirst };

/// Retains both domains and the actual selected axis. Its index law is
/// output[i] = (1-r) * input[low(i)] + r * input[high(i)].
class BooleanFold {
public:
  static llvm::Expected<BooleanFold> admit(const OrderedBooleanDomain &source,
                                           uint32_t axis, FoldConvention order);
  const OrderedBooleanDomain &source() const { return input; }
  const OrderedBooleanDomain &target() const { return output; }
  uint32_t axis() const { return selectedAxis; }
  llvm::Expected<std::pair<uint64_t, uint64_t>> pair(uint64_t row) const;

private:
  BooleanFold(OrderedBooleanDomain source, OrderedBooleanDomain target,
              uint32_t axis, FoldConvention order);
  OrderedBooleanDomain input, output;
  uint32_t selectedAxis;
  FoldConvention order;
};

/// Checked permutation witness, not a physical layout policy.
class BooleanAxisMap {
public:
  static llvm::Expected<BooleanAxisMap>
  admit(const OrderedBooleanDomain &source, const OrderedBooleanDomain &target);
  const OrderedBooleanDomain &source() const { return input; }
  const OrderedBooleanDomain &target() const { return output; }
  llvm::Expected<uint64_t> sourceIndex(uint64_t targetIndex) const;

private:
  BooleanAxisMap(OrderedBooleanDomain source, OrderedBooleanDomain target);
  OrderedBooleanDomain input, output;
};

/// Row permutation only; does not establish an evaluation-point substitution.
llvm::Expected<uint64_t> rotatedBooleanRow(const OrderedBooleanDomain &domain,
                                           uint64_t shift, uint64_t row);

} // namespace zkc::protocol
#endif

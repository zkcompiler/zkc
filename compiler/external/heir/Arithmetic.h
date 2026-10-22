#pragma once

#include "mlir/Support/LogicalResult.h"
#include <cstdint>
#include <map>
#include <vector>

namespace zkc::heir {
// Checker values, not an executable graph. Variables denote ordered input
// elements of the quotient ring. This normalization uses only ring laws;
// quotient elements are never assumed to form a field.
using Monomial = std::vector<unsigned>;
using Expression = std::map<Monomial, uint64_t>;
enum class ArithmeticOperation { Add, Subtract, Multiply };
struct ArithmeticMeaning {
  uint64_t modulus = 0;
  uint64_t degree = 0;
  unsigned inputs = 0;
  std::vector<Expression> outputs;
};
bool qualifiedProfile(uint64_t modulus, uint64_t degree);
uint64_t modularPower(uint64_t value, uint64_t exponent, uint64_t modulus);
// A shared, monotonically decreasing allowance bounds normalization and
// allocation. Failure gives no equality claim; exhaustion leaves zero.
mlir::FailureOr<Expression> combine(ArithmeticOperation operation,
                                    const Expression &left,
                                    const Expression &right, uint64_t modulus,
                                    uint64_t &remaining,
                                    bool *exhausted = nullptr);
} // namespace zkc::heir

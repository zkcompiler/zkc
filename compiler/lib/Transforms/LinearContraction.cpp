#include "zkc/Transforms/LinearContraction.h"

using namespace mlir;
namespace zkc {
void printLinearContractionStats(const LinearContractionStats &stats,
                                 llvm::raw_ostream &out) {
  out << "linear-contractions: producers=" << stats.producers
      << " eligible=" << stats.eligiblePairs
      << " selected=" << stats.selectedPairs << '\n';
  out << "linear-contractions: eligible-producers=" << stats.eligibleProducers
      << " selected-producers=" << stats.selectedProducers << '\n';
}

} // namespace zkc

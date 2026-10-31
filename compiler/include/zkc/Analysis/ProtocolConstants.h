#ifndef ZKC_ANALYSIS_PROTOCOLCONSTANTS_H
#define ZKC_ANALYSIS_PROTOCOLCONSTANTS_H

#include "zkc/Analysis/MathematicalFacts.h"
#include "llvm/ADT/StringRef.h"

namespace zkc {
/// Observe an exact ui64 or Boolean (0/1) in an admitted immutable Protocol
/// module. A named participant selects its actual assembled component. An
/// empty participant requires every component to agree; it never selects one
/// party's value as a common count. Restrictions and invariant repeat captures
/// forward values; induction variables, carried initializers and loop results
/// supply no implicit constants. Pure helper observations reuse mathematics.
///
/// This is a value fact, not evidence of reachability, custody, authentication
/// or successful execution. It neither reads guards nor changes operations.
/// All observations share caller Work, including forwarding and helper reads.
/// Query-local memoization keeps shared value DAGs bounded. Clear mathematics
/// before source mutation; no separate persistent cache is retained here.
facts::Result<uint64_t> observeProtocolConstant(mlir::Value,
                                                llvm::StringRef participant,
                                                MathematicalFactAnalysis &,
                                                facts::Work &,
                                                unsigned depth = 0);
} // namespace zkc

#endif

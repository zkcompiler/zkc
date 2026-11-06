#ifndef ZKC_LANGUAGE_SIGNATUREWITNESS_H
#define ZKC_LANGUAGE_SIGNATUREWITNESS_H
#include "State.h"
namespace zkc::language::detail {
class Semantics;
/// Independent header-witness inclusion, with one cumulative allowance for
/// both the candidate and authored obligations. Keys confer no authority.
bool requiredAdmissionsIncluded(Semantics &, const Declaration &actual,
                                const Declaration &written, bool exact);
llvm::Error checkViewSources(const CheckedStorage &, Work &);
/// Recheck callback contracts against independently retained authored syntax.
llvm::Error checkSignatureSources(const CheckedStorage &, Work &);
/// Freeze the source-check inference product and independently reconstruct
/// static header premises once, after the original inference lifecycle.
llvm::Error retainHeaderPremises(CheckedStorage &, Work &);
/// Replay authored static/data premises, consumer demands, signature admissions
/// and managed inputs in one private header snapshot with lazy nominal/static
/// dependencies.
/// The immutable source inventory applies even when candidate metadata is
/// empty.
llvm::Expected<std::map<uint32_t, std::vector<ServicePort>>>
replayHeaderContracts(const CheckedStorage &, Work &);
/// Reconstruct exact conformance edges from immutable authored headers, replay
/// signatures, and independently judge all implementation obligations.
llvm::Error checkModuleContracts(const CheckedStorage &, Work &);
} // namespace zkc::language::detail
#endif

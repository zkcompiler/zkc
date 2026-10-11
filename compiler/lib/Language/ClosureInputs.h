#ifndef ZKC_LANGUAGE_CLOSUREINPUTS_H
#define ZKC_LANGUAGE_CLOSUREINPUTS_H
#include "ValueOrigins.h"
namespace zkc::language::detail {
/// Runtime inputs of a closed helper. Unknown authored inputs occur while
/// forming a callback whose explicit arguments will be supplied at invocation.
struct ClosureInputs {
  std::vector<std::optional<ValueId>> operands;
  ClosureLayout layout;
};
/// Preserve authored ports and share Copy/Drop capture ports by immutable SSA
/// place. The layout records all aliases; it never depends on runtime contents.
std::optional<ClosureInputs> closeInputs(Semantics &, const Body &,
                                         llvm::ArrayRef<std::optional<ValueId>>,
                                         llvm::ArrayRef<ValueId> captures,
                                         Span);
/// Check a supplied layout relationally against caller SSA identities. This
/// does not compute a preferred layout or invoke the specialization producer.
std::optional<std::vector<std::optional<ValueId>>>
bindClosureInputs(Semantics &, const Body &,
                  llvm::ArrayRef<std::optional<ValueId>> authored,
                  llvm::ArrayRef<ValueId> captures, const ClosureLayout &,
                  unsigned ports, Span);
} // namespace zkc::language::detail
#endif

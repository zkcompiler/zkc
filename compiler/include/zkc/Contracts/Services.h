#ifndef ZKC_CONTRACTS_SERVICES_H
#define ZKC_CONTRACTS_SERVICES_H

#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Operations.h"

namespace zkc::protocol {

/// A nullary entropy query backed by an installed state transition. The
/// capability root owns the current state; neither the state nor its successor
/// is mathematical query data. Aliases of one root use the same current state.
/// This descriptor does not prove a sampler's distribution or native adequacy.
struct EntropyService {
  BindingApplication transition;
  BoundType state, reply;
  SamplingContract sampling;
};

/// Resolve from the common operation owner. This initial profile admits scalar
/// and nonzero-scalar draws only, with one RNG input, one reply, one successor,
/// no attributes and no physical implementation selection.
llvm::Expected<EntropyService>
resolveEntropyService(const BindingApplication &);

} // namespace zkc::protocol

#endif

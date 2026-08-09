//===- SoundnessProjection.h - Closed fact projection/deciders -*- C++ -*-===//
//
// Pure, MLIR-free resolution of authenticated soundness facts.  This layer
// is shared by APPLY and any consumer that needs to evaluate a declared
// machine condition; it accepts no callbacks, caller verdicts, or legacy hop
// state.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SOUNDNESSPROJECTION_H
#define ZKC_SOUNDNESS_SOUNDNESSPROJECTION_H

#include "zkc/Soundness/SealedSoundnessView.h"
#include "zkc/Soundness/SoundnessRuntime.h"
#include "llvm/Support/Error.h"

#include <vector>

namespace zkc::soundness {

/// Evaluate one closed artifact projection at an exact application site.
/// Reduction projections require a ReductionOccurrence; PathBindingField
/// requires a PathOccurrence and reads only the authenticated construction
/// facts owned by `sealed`.
llvm::Expected<RuntimeValue>
projectArtifactFact(const SealedSoundnessView &sealed,
                    const ApplicationSite &site,
                    const ArtifactProjection &projection);

/// Resolve the ApplicationPathTransition binding form.  `authorizedBinding`
/// is the exact binding selected by the enclosing soundness context and is the
/// sole authority for the transition. The binding must carry an exact
/// PathTransition anchor.
llvm::Expected<RuntimeValue>
resolveApplicationPathTransition(const SealedSoundnessView &sealed,
                                 const ApplicationSite &site,
                                 const RuleBinding &authorizedBinding);

/// Execute one built-in, closed machine decider over already-resolved typed
/// values.  Predicate failure is `false`; malformed/unavailable semantic
/// input is an Error.  In particular, unsupported preservation-only
/// predicates fail closed rather than acquiring inferred semantics.
llvm::Expected<bool>
evaluateMachineDecider(MachineDeciderKind kind,
                       const std::vector<RuntimeValue> &arguments);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SOUNDNESSPROJECTION_H

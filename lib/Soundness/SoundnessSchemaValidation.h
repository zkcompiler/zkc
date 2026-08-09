//===- SoundnessSchemaValidation.h - Internal schema invariants -*- C++ -*-===//
//
// Shared per-entry schema validation used by both RULE_WF and immutable
// catalog construction.  This is an internal boundary, not a second public
// schema API.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_LIB_SOUNDNESS_SOUNDNESSSCHEMAVALIDATION_H
#define ZKC_LIB_SOUNDNESS_SOUNDNESSSCHEMAVALIDATION_H

#include "zkc/Soundness/SoundnessKernel.h"

#include <string>

namespace zkc::soundness::detail {

bool validSubjectSchema(const std::string &lookupRef,
                        const SubjectSchema &schema);

bool validMachineDecider(const std::string &lookupRef,
                         const MachineDeciderDefinition &definition);

} // namespace zkc::soundness::detail

#endif // ZKC_LIB_SOUNDNESS_SOUNDNESSSCHEMAVALIDATION_H

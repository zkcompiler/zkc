//===- SoundnessCatalog.h - Immutable executable declarations -*- C++ -*-===//
//
// A native, registry-independent catalog for the soundness kernel.  The
// mutable construction phase ends at freezeSoundnessCatalog: every stored rule
// and binding has passed RULE_WF, and every exact reference is resolved inside
// this owned snapshot.
//
//===----------------------------------------------------------------------===//
#ifndef ZKC_SOUNDNESS_SOUNDNESSCATALOG_H
#define ZKC_SOUNDNESS_SOUNDNESSCATALOG_H

#include "zkc/Soundness/SoundnessKernel.h"
#include "llvm/Support/Error.h"

#include <map>
#include <string>
#include <utility>

namespace zkc::soundness {

/// An immutable semantic authority for APPLY and DERIVE.
///
/// This is a kernel object.  It contains no registry handle, evidence,
/// certificate, release state, or migration metadata.
class SoundnessCatalog {
public:
  const SchemaContext schemas;
  const std::map<std::string, SoundnessRule, std::less<>> rules;
  const std::map<std::string, RuleBinding, std::less<>> bindings;

  SoundnessCatalog(const SoundnessCatalog &) = default;
  SoundnessCatalog(SoundnessCatalog &&) = default;
  SoundnessCatalog &operator=(const SoundnessCatalog &) = delete;
  SoundnessCatalog &operator=(SoundnessCatalog &&) = delete;

private:
  friend llvm::Expected<SoundnessCatalog>
      freezeSoundnessCatalog(SchemaContext,
                             std::map<std::string, SoundnessRule, std::less<>>,
                             std::map<std::string, RuleBinding, std::less<>>);

  SoundnessCatalog(SchemaContext schemas,
                   std::map<std::string, SoundnessRule, std::less<>> rules,
                   std::map<std::string, RuleBinding, std::less<>> bindings)
      : schemas(std::move(schemas)), rules(std::move(rules)),
        bindings(std::move(bindings)) {}
};

/// Validate and freeze one complete native catalog.
///
/// Map keys are part of the input contract: they must equal the exact
/// reference id stored in each declaration.  Every binding must resolve an
/// exact rule revision in the same snapshot.  The function re-runs RULE_WF for
/// every declaration, so callers cannot bypass the kernel by constructing
/// aggregate values directly.
llvm::Expected<SoundnessCatalog> freezeSoundnessCatalog(
    SchemaContext schemas,
    std::map<std::string, SoundnessRule, std::less<>> rules,
    std::map<std::string, RuleBinding, std::less<>> bindings);

} // namespace zkc::soundness

#endif // ZKC_SOUNDNESS_SOUNDNESSCATALOG_H

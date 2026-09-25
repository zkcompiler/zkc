#ifndef ZKC_PROTOCOL_PHYSICALOPTIONS_H
#define ZKC_PROTOCOL_PHYSICALOPTIONS_H

#include "zkc/Source/Model.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol {

/// Caller-selected implementations, optionally bound to the exact source that
/// enters physical planning. For an artifact this is the constructed protocol,
/// not the original interactive source or the candidate participant program.
struct ImplementationSelection {
  std::string sourceSnapshot;
  source::Assignments choices;
};

/// Settings for the installed physical pipeline. These are compilation inputs,
/// not evidence of a transformation's mathematical or cryptographic validity.
struct PhysicalOptions {
  ImplementationSelection implementations;
  bool linearContractions = false;
  bool releaseStorage = false;
};

llvm::Expected<ImplementationSelection>
decodeImplementationSelection(const llvm::json::Value &);
llvm::Error checkImplementationSelection(const ImplementationSelection &,
                                         const source::Content &);

} // namespace zkc::protocol
#endif

#ifndef ZKC_LANGUAGE_NAMES_H
#define ZKC_LANGUAGE_NAMES_H

#include "zkc/Source/Names.h"

namespace zkc::language {
using source::decodeNominalIdentity;
using source::decodeSourceScalar;
using source::encodeNominalIdentity;
using source::encodeSourceSymbol;
using source::isMathematicalSymbol;
using source::isSourceDelimiterCloser;
using source::isSourceIdentifier;
using source::isSourceNFC;
using source::matchingSourceDelimiter;
using source::nativeAlternativeName;
using source::nativeRoleName;
using source::nativeSetupName;
using source::nativeSiteName;
using source::sourceIdentifierContinue;
using source::sourceIdentifierStart;
using source::sourceNameProfileIdentity;
using source::SourceScalar;
} // namespace zkc::language

#endif

#ifndef ZKC_FRONTEND_STATIC_ATTRIBUTES_H
#define ZKC_FRONTEND_STATIC_ATTRIBUTES_H

#include "zkc/Contracts/Declarations.h"

namespace zkc::frontend {
/// Only operation-owned natural slots participate in static name resolution.
/// Field literals and opaque codec/origin strings retain their own validators.
inline bool naturalAttribute(llvm::StringRef operation, size_t index) {
  const auto *contract = protocol::parameterContract(operation);
  if (!contract || (contract->maximum && index >= *contract->maximum))
    return false;
  using V = protocol::ParameterValidator;
  switch (contract->validator) {
  case V::Natural:
  case V::Extent:
  case V::MatrixShape:
  case V::MatrixVector:
  case V::GatherIndices:
  case V::ScatterIndices:
    return true;
  case V::None:
  case V::FieldLiteral:
  case V::FieldLiterals:
  case V::MatrixIdentity:
  case V::NativeOrigin:
  case V::TranscriptOrigin:
    return false;
  }
  return false;
}
} // namespace zkc::frontend
#endif

#include "envelope/Envelope.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
namespace envelope {
using EnvelopeAdapter = zkc::protocol::type_adapters::TypeNatAdapter<
    EnvelopeType, &EnvelopeType::getElementType, &EnvelopeType::getLength>;
}
#include "zkc/Dialect/TypeAdapters/EnvelopeAdapters.inc"

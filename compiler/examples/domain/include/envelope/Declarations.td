#ifndef EXAMPLE_ENVELOPE_DECLARATIONS
#define EXAMPLE_ENVELOPE_DECLARATIONS
include "zkc/Contracts/Declarations.td"
def EnvelopeValue : ZKC_Type<"envelope", [TypeParameter, NatParameter], PrivateImmutable>;
def EnvelopeExport : ZKC_TypeExport<"zkc::envelope", "Envelope", EnvelopeValue>;
def EnvelopeElement : ZKC_Root<"Element", TypeParameter>;
def EnvelopeLength : ZKC_Root<"Length", NatParameter>;
def EnvelopeKeep : ZKC_Operation<"envelope.keep", [EnvelopeElement, EnvelopeLength],
  [ZKC_Apply<EnvelopeValue, [EnvelopeElement, EnvelopeLength]>],
  [ZKC_Apply<EnvelopeValue, [EnvelopeElement, EnvelopeLength]>]>;
// A second operation exercises generic multi-result contract declarations without
// claiming that every logical declaration has a native implementation.
def EnvelopeOther : ZKC_Root<"Other", NatParameter>;
def EnvelopePair : ZKC_Operation<"envelope.pair",
    [EnvelopeElement, EnvelopeLength, EnvelopeOther],
    [ZKC_Apply<CatalogType_fixed_5fvector, [EnvelopeElement, EnvelopeLength]>,
     ZKC_Apply<CatalogType_fixed_5fvector, [EnvelopeElement, EnvelopeOther]>],
    [ZKC_Apply<CatalogType_fixed_5fvector, [EnvelopeElement, EnvelopeLength]>,
     ZKC_Apply<CatalogType_fixed_5fvector, [EnvelopeElement, EnvelopeOther]>]>;
def EnvelopeSort : ZKC_Sort<"EnvelopeDomain">;
def EnvelopeDomain : ZKC_Domain<EnvelopeSort>;
def EnvelopeCapability : ZKC_Capability<"EnvelopeCapability", [EnvelopeDomain]>;
def EnvelopeCapabilityExport : ZKC_CapabilityExport<"zkc::envelope", "Capability",
    EnvelopeCapability>;
#endif

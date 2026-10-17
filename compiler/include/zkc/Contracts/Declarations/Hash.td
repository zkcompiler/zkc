// Snapshot SHAKE128 with explicit read position; no managed transcript authority.
def OpShake128Init : ZKC_Operation<"shake128.init", [], [],
    [ZKC_Apply<TypeShake128State, []>], []> { int ordinal = 168; }
def OpShake128Absorb : ZKC_Operation<"shake128.absorb", [],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeShake128State, []>], []> {
  int ordinal = 169;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}
def OpShake128Squeeze : ZKC_Operation<"shake128.squeeze", [],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 170;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

// Raw Keccak-256; no domain separator, framing, or scalar reduction.
def OpHashKeccak256 : ZKC_Operation<"hash.keccak256", [],
    [ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 184; }

// Raw SHA-256 (FIPS 180-4); no domain separator, framing, or scalar reduction.
def OpHashSha256 : ZKC_Operation<"hash.sha256", [],
    [ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 191; }

// The width-16 Poseidon2 permutation of F's installed parameters, applied to
// each consecutive 16-element state; the length must be a multiple of 16.
def HashPoseidon2Width16Domain : ZKC_Root<"F", FieldDomain>;
def OpHashPoseidon2Width16 : ZKC_Operation<"hash.poseidon2_16", [HashPoseidon2Width16Domain],
    [ZKC_Apply<TypeVector, [HashPoseidon2Width16Domain]>],
    [ZKC_Apply<TypeVector, [HashPoseidon2Width16Domain]>],
    [ZKC_Holds<CapabilityField, [HashPoseidon2Width16Domain]>]> { int ordinal = 198; }

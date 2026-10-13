// Snapshot SHAKE128 with explicit read position; no managed transcript authority.
def OpShake128Init : ZKC_Operation<"shake128.init", [], [],
    [ZKC_Apply<TypeShake128State, []>], []> { int ordinal = 168; }
def ExportShake128Init : ZKC_OperationExport<"zkc::shake128", "init", OpShake128Init, []>;
def OpShake128Absorb : ZKC_Operation<"shake128.absorb", [],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeShake128State, []>], []> {
  int ordinal = 169;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}
def ExportShake128Absorb : ZKC_OperationExport<"zkc::shake128", "absorb", OpShake128Absorb, ["state", "bytes"]>;
def OpShake128Squeeze : ZKC_Operation<"shake128.squeeze", [],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeShake128State, []>, ZKC_Apply<TypeBytes, []>], []> {
  int ordinal = 170;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}
def ExportShake128Squeeze : ZKC_OperationExport<"zkc::shake128", "squeeze", OpShake128Squeeze, ["state", "length"]>;

// Raw Keccak-256; no domain separator, framing, or scalar reduction.
def OpHashKeccak256 : ZKC_Operation<"hash.keccak256", [],
    [ZKC_Apply<TypeBytes, []>], [ZKC_Apply<TypeBytes, []>], []> { int ordinal = 184; }
def ExportHashKeccak256 : ZKC_OperationExport<"zkc::bytes", "keccak256", OpHashKeccak256, ["value"]>;

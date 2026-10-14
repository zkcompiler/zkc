// Logical contracts and curated exports owned by this domain.
def OpExternalMoneroInit : ZKC_Operation<"external.monero.init", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 3;
}

def OpExternalMoneroHash : ZKC_Operation<"external.monero.hash", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 4;
}

def OpExternalMoneroUpdate : ZKC_Operation<"external.monero.update", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 5;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

def OpExternalOpenvmInit : ZKC_Operation<"external.openvm.init", [],
    [],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 6;
}

def OpExternalOpenvmObserve : ZKC_Operation<"external.openvm.observe", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 7;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

def OpExternalOpenvmSample : ZKC_Operation<"external.openvm.sample", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 8;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

def OpExternalOpenvmSampleExt : ZKC_Operation<"external.openvm.sample_ext", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 9;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

def OpExternalOpenvmSampleBits : ZKC_Operation<"external.openvm.sample_bits", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 10;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

def OpExternalOpenvmCheckWitness : ZKC_Operation<"external.openvm.check_witness", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 11;
  let facets = [ZKC_History<0, 0>, SourceHistory];
}

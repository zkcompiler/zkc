// Logical contracts and curated exports owned by this domain.
def OpExternalMoneroInit : ZKC_Operation<"external.monero.init", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 3;
}
def ExportExternalMoneroInit : ZKC_OperationExport<"zkc::external", "monero_init",
    OpExternalMoneroInit, ["indices"]>;

def OpExternalMoneroHash : ZKC_Operation<"external.monero.hash", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 4;
}
def ExportExternalMoneroHash : ZKC_OperationExport<"zkc::external", "monero_hash",
    OpExternalMoneroHash, ["indices"]>;

def OpExternalMoneroUpdate : ZKC_Operation<"external.monero.update", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 5;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalMoneroUpdate : ZKC_OperationExport<"zkc::external", "monero_update",
    OpExternalMoneroUpdate, ["indices0", "indices1"]>;

def OpExternalOpenvmInit : ZKC_Operation<"external.openvm.init", [],
    [],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 6;
}
def ExportExternalOpenvmInit : ZKC_OperationExport<"zkc::external", "openvm_init",
    OpExternalOpenvmInit, []>;

def OpExternalOpenvmObserve : ZKC_Operation<"external.openvm.observe", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 7;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalOpenvmObserve : ZKC_OperationExport<"zkc::external", "openvm_observe",
    OpExternalOpenvmObserve, ["indices0", "indices1"]>;

def OpExternalOpenvmSample : ZKC_Operation<"external.openvm.sample", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 8;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalOpenvmSample : ZKC_OperationExport<"zkc::external", "openvm_sample",
    OpExternalOpenvmSample, ["indices"]>;

def OpExternalOpenvmSampleExt : ZKC_Operation<"external.openvm.sample_ext", [],
    [ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndices, []>], []> {
  int ordinal = 9;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalOpenvmSampleExt : ZKC_OperationExport<"zkc::external", "openvm_sample_ext",
    OpExternalOpenvmSampleExt, ["indices"]>;

def OpExternalOpenvmSampleBits : ZKC_Operation<"external.openvm.sample_bits", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>], []> {
  int ordinal = 10;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalOpenvmSampleBits : ZKC_OperationExport<"zkc::external", "openvm_sample_bits",
    OpExternalOpenvmSampleBits, ["indices", "index"]>;

def OpExternalOpenvmCheckWitness : ZKC_Operation<"external.openvm.check_witness", [],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeIndices, []>, ZKC_Apply<TypeBool, []>], []> {
  int ordinal = 11;
  let facets = [ZKC_History<0, 0>];
}
def ExportExternalOpenvmCheckWitness : ZKC_OperationExport<"zkc::external", "openvm_check_witness",
    OpExternalOpenvmCheckWitness, ["indices", "index1", "index2"]>;

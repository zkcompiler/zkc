#ifndef ZKC_DIALECT_CRYPTO_IR_CRYPTOOPS_TD
#define ZKC_DIALECT_CRYPTO_IR_CRYPTOOPS_TD

include "zkc/Dialect/Types.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/ControlFlowInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "zkc/Dialect/Kernels.td"

def CurveCommitOp : KernelOp<CryptoDialect, "exec.curve_commit", [OpCurveCommit]>;

def CurveResponseOp : KernelOp<CryptoDialect, "exec.curve_response", [OpCurveResponse]>;

def ExternalMoneroHashOp : KernelOp<CryptoDialect, "exec.monero_hash", [OpExternalMoneroHash]> {
  let description = [{
    Hashes concatenated words to Monero scalar bytes without a chain state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalMoneroInitOp : KernelOp<CryptoDialect, "exec.monero_init", [OpExternalMoneroInit]> {
  let description = [{
    Starts the pinned Monero scalar hash chain from its initial bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalMoneroUpdateOp : KernelOp<CryptoDialect, "exec.monero_update", [OpExternalMoneroUpdate]> {
  let description = [{
    Absorbs concatenated words into the Monero hash chain; returns the successor state and the derived scalar bytes.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmCheckWitnessOp : KernelOp<CryptoDialect, "exec.openvm_check_witness", [OpExternalOpenvmCheckWitness]> {
  let description = [{
    Checks a grinding witness against the requested number of bits on the live state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmInitOp : KernelOp<CryptoDialect, "exec.openvm_init", [OpExternalOpenvmInit]> {
  let description = [{
    Starts the pinned OpenVM BabyBear Poseidon2 duplex state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmObserveOp : KernelOp<CryptoDialect, "exec.openvm_observe", [OpExternalOpenvmObserve]> {
  let description = [{
    Absorbs field words into the OpenVM duplex; returns the successor state.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmSampleOp : KernelOp<CryptoDialect, "exec.openvm_sample", [OpExternalOpenvmSample]> {
  let description = [{
    Squeezes one base-field sample from the OpenVM duplex.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmSampleBitsOp : KernelOp<CryptoDialect, "exec.openvm_sample_bits", [OpExternalOpenvmSampleBits]> {
  let description = [{
    Squeezes a sample and masks it to the requested number of bits, as the pinned query sampler does.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def ExternalOpenvmSampleExtOp : KernelOp<CryptoDialect, "exec.openvm_sample_ext", [OpExternalOpenvmSampleExt]> {
  let description = [{
    Squeezes the four coefficients of one quartic-extension sample.
    States are explicit values, so grouping and order stay in the authored body;
    the operation is one exact upstream transition (docs/spec/realization/external-constructions.md).
  }];
}

def RandomDrawOp : KernelOp<CryptoDialect, "exec.random_draw", [OpRandomDraw]>;

def RandomIndexOp : KernelOp<CryptoDialect, "exec.random_index", [OpRandomIndex]>;

def RandomVectorOp : KernelOp<CryptoDialect, "exec.random_vector", [OpRandomVector]>;

def TranscriptChallengeOp : KernelOp<CryptoDialect, "exec.transcript_challenge", [OpTranscriptChallenge]>;

def TranscriptDrawIndexOp : KernelOp<CryptoDialect, "exec.transcript_draw_index", [OpTranscriptDrawIndex]>;

def TranscriptObserveOp : KernelOp<CryptoDialect, "exec.transcript_observe", []> {
  // Payloads differ deliberately; each remains a distinct checked contract.
  let observationContracts = [
    OpTranscriptObserveBool, OpTranscriptObserveField, OpTranscriptObserveTable,
    OpTranscriptObservePoint, OpTranscriptObserveRound,
    OpTranscriptObserveCommitment, OpTranscriptObserveProof,
    OpTranscriptObserveGroup, OpTranscriptObserveGroups,
    OpTranscriptObserveMatrix, OpTranscriptObserveVector,
    OpTranscriptObservePolynomial, OpTranscriptObserveIndex,
    OpTranscriptObserveIndices, OpTranscriptObserveCommitments
  ];
}

def NativeTranscriptChallengeOp : KernelOp<CryptoDialect,
    "exec.native_transcript_challenge", [OpNativeTranscriptChallenge]>;

def NativeTranscriptObserveOp : KernelOp<CryptoDialect,
    "exec.native_transcript_observe", []> {
  let observationContracts = [OpNativeTranscriptObserveBool,
    OpNativeTranscriptObserveField, OpNativeTranscriptObserveGroup];
}

def IndexedTranscriptChallengeOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_challenge", [OpIndexedTranscriptChallenge]>;
def IndexedTranscriptObserveBoolOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_bool", [OpIndexedTranscriptObserveBool]>;
def IndexedTranscriptObserveFieldOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_field", [OpIndexedTranscriptObserveField]>;
def IndexedTranscriptObserveGroupOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_group", [OpIndexedTranscriptObserveGroup]>;
def IndexedTranscriptObserveCommitmentOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_commitment", [OpIndexedTranscriptObserveCommitment]>;
def IndexedTranscriptObserveProofOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_proof", [OpIndexedTranscriptObserveProof]>;
def IndexedTranscriptObserveIndexOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_index", [OpIndexedTranscriptObserveIndex]>;
def IndexedTranscriptObserveFieldArrayOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_field_array", [OpIndexedTranscriptObserveFieldArray]>;

def IndexedTranscriptObserveDataOp : KernelOp<CryptoDialect,
    "exec.indexed_transcript_observe_data", [OpIndexedTranscriptObserveData]>;

#endif

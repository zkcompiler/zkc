// Native source templates receive explicit dynamic occurrence coordinates.
def OpIndexedTranscriptChallengeT : ZKC_Root<"T", TranscriptDomain>;
def OpIndexedTranscriptChallengeChallengeField : ZKC_Project<OpIndexedTranscriptChallengeT, TranscriptChallengeField>;
def OpIndexedTranscriptChallenge : ZKC_Operation<"transcript.native.indexed.challenge", [OpIndexedTranscriptChallengeT, OpIndexedTranscriptChallengeChallengeField],
    [ZKC_Apply<TypeTranscript, [OpIndexedTranscriptChallengeT]>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeField, [OpIndexedTranscriptChallengeChallengeField]>, ZKC_Apply<TypeTranscript, [OpIndexedTranscriptChallengeT]>], [ZKC_Holds<CapabilityFieldTranscript, [OpIndexedTranscriptChallengeT]>]> {
  let stage = Construction;
  let parameters = NativeOrigin;
  let facets = [ZKC_Sampling<TranscriptProvider, FieldSample, -1>, ZKC_History<0, 1>];
}

// The payload type fixes the codec; it is not peer-selected.
def IndexedDataTranscript : ZKC_Root<"T", TranscriptDomain>;
def IndexedDataPayload : ZKC_Root<"D", TypeParameter>;
def OpIndexedTranscriptObserveData : ZKC_Operation<"transcript.native.indexed.observe.data",
    [IndexedDataTranscript, IndexedDataPayload],
    [ZKC_Apply<TypeTranscript, [IndexedDataTranscript]>, IndexedDataPayload,
     ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeTranscript, [IndexedDataTranscript]>],
    [ZKC_Holds<CapabilityTranscript, [IndexedDataTranscript]>]> {
  let commonGeneric = 0;
  let stage = Construction;
  let parameters = NativeOrigin;
  let facets = [ZKC_Observation<0, 1, 0>, ZKC_History<0, 0>];
}

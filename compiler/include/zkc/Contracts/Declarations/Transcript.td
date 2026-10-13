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

// UniformIndex(bound) from the same state. The bound is the static
// power-of-two domain; the transition absorbs it before squeezing.
def OpIndexedTranscriptIndexT : ZKC_Root<"T", TranscriptDomain>;
def OpIndexedTranscriptIndex : ZKC_Operation<"transcript.native.indexed.index", [OpIndexedTranscriptIndexT],
    [ZKC_Apply<TypeTranscript, [OpIndexedTranscriptIndexT]>, ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeIndices, []>],
    [ZKC_Apply<TypeIndex, []>, ZKC_Apply<TypeTranscript, [OpIndexedTranscriptIndexT]>], [ZKC_Holds<CapabilityIndexTranscript, [OpIndexedTranscriptIndexT]>]> {
  let stage = Construction;
  let parameters = NativeOrigin;
  let facets = [ZKC_Sampling<TranscriptProvider, IndexSample, 1>, ZKC_History<0, 1>];
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

// Source methods consume an existing managed state. Labels are explicit byte
// values, without a generated event origin or implicit occurrence coordinates.
def SourceTranscript : ZKC_Root<"T", TranscriptDomain>;
def SourceChallengeField : ZKC_Project<SourceTranscript, TranscriptChallengeField>;
def SourceFieldSample : ZKC_Sampling<TranscriptProvider, FieldSample> {
  let valueOutput = 1;
  let stateOutput = 0;
}
def SourceIndexSample : ZKC_Sampling<TranscriptProvider, IndexSample, 2> {
  let valueOutput = 1;
  let stateOutput = 0;
}
def OpTranscriptObserve : ZKC_Operation<"transcript.observe", [SourceTranscript],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>, ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>],
    [ZKC_Holds<CapabilityTranscript, [SourceTranscript]>]> {
  int ordinal = 176;
  let facets = [ZKC_Observation<0, 2, 0>, ZKC_History<0, 0>, ManagedHistory];
}
def OpTranscriptChallenge : ZKC_Operation<"transcript.challenge", [SourceTranscript, SourceChallengeField],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>, ZKC_Apply<TypeBytes, []>],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>, ZKC_Apply<TypeField, [SourceChallengeField]>],
    [ZKC_Holds<CapabilityFieldTranscript, [SourceTranscript]>]> {
  int ordinal = 177;
  let facets = [SourceFieldSample, ZKC_History<0, 0>, ManagedHistory];
}
def OpTranscriptIndex : ZKC_Operation<"transcript.index", [SourceTranscript],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>, ZKC_Apply<TypeBytes, []>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Apply<TypeTranscript, [SourceTranscript]>, ZKC_Apply<TypeIndex, []>],
    [ZKC_Holds<CapabilityIndexTranscript, [SourceTranscript]>]> {
  int ordinal = 178;
  let facets = [SourceIndexSample, ZKC_History<0, 0>, ManagedHistory];
}

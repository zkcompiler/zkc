module

public import Zkc.Core.ThreadEntrySerialize
public import Zkc.Core.ThreadEntryFiatShamir

public section

/-! What the entries of the two rules do, and that they do it.

`serializeEntry` and `serializeEntry_sound` (`Core/ThreadEntrySerialize.lean`): the prover
opens a writer and, after the body, closes it into the proof, which is the first output;
the verifier opens a reader on the proof, which is the first input, and after the body
guards with `reject` that the reader is exhausted.

`fiatShamirEntry` and `fiatShamirEntry_sound` (`Core/ThreadEntryFiatShamir.lean`): each
transcript role starts its state and absorbs its copies of the statement, or calls the
start function of a source suite on them; after the body the two final states are dropped.
-/

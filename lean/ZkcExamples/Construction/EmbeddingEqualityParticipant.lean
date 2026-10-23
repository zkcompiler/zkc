module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.EmbeddingEqualityParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:fc9a282a5ab377d24c58983c7b3c8fdef4361068612f63462deef5318fbb7510"
  candidate := "sha256:a2ca57b0992606b9a96139d519f29ea7e8874ce2e2f8bf103067bc4cf33e7c68"
  policy := ⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [2], [0, 1], [("label_6368616c6c656e6765", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  instructions := [
    ⟨.receive "label_6d657373616765_0" "label_6d657373616765_0" "role00000000" (.field "koala-bear.ext8-binomial3"), [], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", [], ["message", "s7h6578616d706c6517h456d62656464696e67457175616c697479", "label_6d657373616765_0", "label_6d657373616765_0", "role00000000", "role00000001"]⟩, [2, 3, 4], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.koala-bear.ext8-binomial3.rejection31le/0" "koala-bear.ext8-binomial3" ⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", [], ["query", "s7h6578616d706c6517h456d62656464696e67457175616c697479", "label_6368616c6c656e6765", "input_2", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, [5, 6], [.data (.field "koala-bear.ext8-binomial3"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s7h6578616d706c6517h456d62656464696e67457175616c697479", [], ["message", "s7h6578616d706c6517h456d62656464696e67457175616c697479", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [8, 7, 9], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [3, 7], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s7h6578616d706c655h656d626564", [0], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [12, 7], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldEqual "koala-bear.ext8-binomial3"), [11, 13], [.data .boolean], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [3, 7], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s7h6578616d706c655h656d626564", [1], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [16, 7], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldEqual "koala-bear.ext8-binomial3"), [15, 17], [.data .boolean], []⟩,
    ⟨.calculate .booleanAnd, [14, 18], [.data .boolean], []⟩]
  returned := [19, 10]

end ZkcExamples.Construction.EmbeddingEqualityParticipant

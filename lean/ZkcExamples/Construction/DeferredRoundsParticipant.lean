module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.DeferredRoundsParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:d10211ddcac6af993f4b1b596adc438905d96756035ede1169ac345ecbe2203d"
  candidate := "sha256:b8e61c8cca045acb16bb45ca3851739c377ab6dfce1579726f959aa3e709a4af"
  policy := ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [2], [0], [("label_6330", "label_6430_0"), ("label_6331", "label_6431_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.receive "label_6d30_0" "label_6d30_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"]⟩, [1, 2, 3], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [4, 5], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6430_0", "label_6430_0", "role00000001", "role00000000"]⟩, [7, 6, 8], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [2, 6], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.receive "label_6d31_0" "label_6d31_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"]⟩, [9, 11, 12], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [13, 14], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", [], ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b", "label_6431_0", "label_6431_0", "role00000001", "role00000000"]⟩, [16, 15, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [10, 15], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [19, 0], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [11, 15], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldAdd "bls12-381.fr"), [21, 0], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldEqual "bls12-381.fr"), [20, 22], [.data .boolean], []⟩]
  returned := [23, 18]

end ZkcExamples.Construction.DeferredRoundsParticipant

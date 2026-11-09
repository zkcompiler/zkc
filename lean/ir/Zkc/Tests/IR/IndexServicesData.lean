module

public import Zkc.IR.Construction.AuthoredPair

@[expose] public section




/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.IndexServices.Scalar.Source
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:0daea40dd19f974c57469de2efa795fe2d8920cd12c9ae2a97d3ff22abbcb6d3"
  entry := "s14h696e6465785f73657276696365736h5363616c6172"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s14h696e6465785f73657276696365736h5363616c6172", .protocol, .publicDef, [.service "random.koala-bear.ext4-binomial3/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"index_services::Scalar", []⟩), (.block [.instruction (.indexConstant "8") [] [.index] [] "", .instruction (.sampleIndex "role00000001" "random.koala-bear.ext4-binomial3/0") [1, 0] [.index] [] "label_706f736974696f6e", .instruction (.exchange "role00000001" "role00000000") [0] [.index] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.index] [] "", .instruction (.indexEqual) [2, 2] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h696e6465785f73657276696365736h5363616c6172", []⟩]
  catalogue := { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }
  sourceDeclarations := { records := [], protocols := [], authorities := [] }

end Tests.IndexServices.Scalar.Source



namespace Tests.IndexServices.Scalar.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:0daea40dd19f974c57469de2efa795fe2d8920cd12c9ae2a97d3ff22abbcb6d3"
  candidate := "sha256:fcffd79da91b0a54fb562a4ac7306f31cc968aec17f363a447b9d383c82f110e"
  policy := ⟨"s14h696e6465785f73657276696365736h5363616c6172", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365736h5363616c6172", [], ["query", "s14h696e6465785f73657276696365736h5363616c6172", "label_706f736974696f6e", "input_0", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [0, 1, 2], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365736h5363616c6172", [], ["message", "s14h696e6465785f73657276696365736h5363616c6172", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [4, 3, 5], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩]
  returned := [6]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Scalar.Producer

namespace Tests.IndexServices.Scalar.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:0daea40dd19f974c57469de2efa795fe2d8920cd12c9ae2a97d3ff22abbcb6d3"
  candidate := "sha256:fcffd79da91b0a54fb562a4ac7306f31cc968aec17f363a447b9d383c82f110e"
  policy := ⟨"s14h696e6465785f73657276696365736h5363616c6172", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365736h5363616c6172", [], ["query", "s14h696e6465785f73657276696365736h5363616c6172", "label_706f736974696f6e", "input_0", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [0, 2, 3], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365736h5363616c6172", [], ["message", "s14h696e6465785f73657276696365736h5363616c6172", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [5, 4, 6], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate .indexEqual, [4, 4], [.data .boolean], []⟩]
  returned := [8, 7]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Scalar.Validator

namespace Tests.IndexServices.Scalar

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.IndexServices.Scalar



/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.IndexServices.Block.Source
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:0e8fc796ae26ca1001db057d0e95e7011f26fc983fef5bcfe530522fc05f45a3"
  entry := "s14h696e6465785f73657276696365735h426c6f636b"
  domains := []
  relations := []
  bindings := [⟨"zkl_binding_0", "indices.length", [], "", some ⟨[], [.indices], [.index]⟩⟩]
  definitions := [.function ⟨"s14h696e6465785f73657276696365735h426c6f636b", .protocol, .publicDef, [.service "random.koala-bear.ext4-binomial3/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"index_services::Block", []⟩), (.block [.instruction (.indexConstant "8") [] [.index] [] "", .instruction (.indexConstant "3") [] [.index] [] "", .instruction (.sampleIndices "role00000001" "random.koala-bear.ext4-binomial3/0") [2, 1, 0] [.indices] [] "label_706f736974696f6e73", .instruction (.exchange "role00000001" "role00000000") [0] [.indices] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.indices] [] "", .instruction (.localCall "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468" "role00000001") [2] [.index] [] "s4", .instruction (.indexConstant "3") [] [.index] [] "", .instruction (.indexEqual) [1, 0] [.boolean] [] ""] (.ret [0]))⟩, .function ⟨"s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", .local, .privateDef, [.indices], [.index], none, [], some (.local "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468" []), (.block [.instruction (.exec "exec.apply" "zkl_binding_0" []) [0] [.index] [] "s0"] (.ret [0]))⟩]
  contracts := [⟨"s14h696e6465785f73657276696365735h426c6f636b", []⟩]
  catalogue := { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }
  sourceDeclarations := { records := [], protocols := [], authorities := [] }

end Tests.IndexServices.Block.Source



namespace Tests.IndexServices.Block.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:0e8fc796ae26ca1001db057d0e95e7011f26fc983fef5bcfe530522fc05f45a3"
  candidate := "sha256:74ec568f0fecb216dafbe19edd7ab5af18c458d58af913ffe7448c05a632492f"
  policy := ⟨"s14h696e6465785f73657276696365735h426c6f636b", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e73", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.blockChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 3 ⟨"s14h696e6465785f73657276696365735h426c6f636b", [], ["query", "s14h696e6465785f73657276696365735h426c6f636b", "label_706f736974696f6e73", "input_0", "random.koala-bear.ext4-binomial3/0", "indices", "role00000001"]⟩, [0, 1], [.data .indices, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365735h426c6f636b", [], ["message", "s14h696e6465785f73657276696365735h426c6f636b", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [3, 2, 4], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩]
  returned := [5]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Block.Producer

namespace Tests.IndexServices.Block.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:0e8fc796ae26ca1001db057d0e95e7011f26fc983fef5bcfe530522fc05f45a3"
  candidate := "sha256:74ec568f0fecb216dafbe19edd7ab5af18c458d58af913ffe7448c05a632492f"
  policy := ⟨"s14h696e6465785f73657276696365735h426c6f636b", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e73", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.blockChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 3 ⟨"s14h696e6465785f73657276696365735h426c6f636b", [], ["query", "s14h696e6465785f73657276696365735h426c6f636b", "label_706f736974696f6e73", "input_0", "random.koala-bear.ext4-binomial3/0", "indices", "role00000001"]⟩, [0, 3], [.data .indices, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365735h426c6f636b", [], ["message", "s14h696e6465785f73657276696365735h426c6f636b", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [5, 4, 6], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.call "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", [4], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.calculate .indexEqual, [8, 9], [.data .boolean], []⟩]
  returned := [10, 7]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Block.Validator

namespace Tests.IndexServices.Block

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.IndexServices.Block



/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.IndexServices.Local.Source
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:88e2988c6474ab310661bf5d64fa4e1bd560188ef433858bf3d3710947c79fe2"
  entry := "s14h696e6465785f73657276696365735h4c6f63616c"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s14h696e6465785f73657276696365735h4c6f63616c", .protocol, .publicDef, [.service "random.koala-bear.ext4-binomial3/0", .service "random.koala-bear.ext4-binomial3/0", .service "random.koala-bear.ext4-binomial3/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000000"], ["role00000001"], ["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"index_services::Local", []⟩), (.block [.instruction (.indexConstant "3") [] [.index] [] "", .instruction (.sampleIndex "role00000000" "random.koala-bear.ext4-binomial3/0") [1, 0] [.index] [] "s0", .instruction (.indexConstant "3") [] [.index] [] "", .instruction (.indexConstant "2") [] [.index] [] "", .instruction (.sampleIndices "role00000000" "random.koala-bear.ext4-binomial3/0") [4, 1, 0] [.indices] [] "s2", .instruction (.indexConstant "3") [] [.index] [] "", .instruction (.sampleIndex "role00000001" "random.koala-bear.ext4-binomial3/0") [7, 0] [.index] [] "s4", .instruction (.indexConstant "8") [] [.index] [] "", .instruction (.sampleIndex "role00000001" "random.koala-bear.ext4-binomial3/0") [10, 0] [.index] [] "label_706f736974696f6e", .instruction (.exchange "role00000001" "role00000000") [0] [.index] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.index] [] "", .instruction (.indexEqual) [2, 2] [.boolean] [] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h696e6465785f73657276696365735h4c6f63616c", []⟩]
  catalogue := { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }
  sourceDeclarations := { records := [], protocols := [], authorities := [] }

end Tests.IndexServices.Local.Source



namespace Tests.IndexServices.Local.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:88e2988c6474ab310661bf5d64fa4e1bd560188ef433858bf3d3710947c79fe2"
  candidate := "sha256:a7375e388cf49fd0af56d7d14e90d1245cc66a309a7f841f566471d93010d0fb"
  policy := ⟨"s14h696e6465785f73657276696365735h4c6f63616c", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [2], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.localService (⟨"service_0", "role00000000", 0, 0, "random.koala-bear.ext4-binomial3/0"⟩) (Request.sampleIndex 3) ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["query", "s14h696e6465785f73657276696365735h4c6f63616c", "s0", "input_0", "random.koala-bear.ext4-binomial3/0", "index", "role00000000"]⟩ [], [1], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 2), [], [.data .index], []⟩,
    ⟨.localService (⟨"service_0", "role00000000", 0, 0, "random.koala-bear.ext4-binomial3/0"⟩) (Request.sampleIndices 3 2) ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["query", "s14h696e6465785f73657276696365735h4c6f63616c", "s2", "input_0", "random.koala-bear.ext4-binomial3/0", "indices", "role00000000"]⟩ [], [3, 4], [.data .indices], []⟩,
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["query", "s14h696e6465785f73657276696365735h4c6f63616c", "label_706f736974696f6e", "input_2", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [0, 6, 7], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["message", "s14h696e6465785f73657276696365735h4c6f63616c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [9, 8, 10], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩]
  returned := [11]
  servicePorts := [⟨"service_0", "role00000000", 0, 0, "random.koala-bear.ext4-binomial3/0"⟩]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }

end Tests.IndexServices.Local.Producer

namespace Tests.IndexServices.Local.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:88e2988c6474ab310661bf5d64fa4e1bd560188ef433858bf3d3710947c79fe2"
  candidate := "sha256:a7375e388cf49fd0af56d7d14e90d1245cc66a309a7f841f566471d93010d0fb"
  policy := ⟨"s14h696e6465785f73657276696365735h4c6f63616c", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [2], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.localService (⟨"service_0", "role00000001", 1, 0, "random.koala-bear.ext4-binomial3/0"⟩) (Request.sampleIndex 3) ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["query", "s14h696e6465785f73657276696365735h4c6f63616c", "s4", "input_1", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩ [], [1], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["query", "s14h696e6465785f73657276696365735h4c6f63616c", "label_706f736974696f6e", "input_2", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [0, 4, 5], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365735h4c6f63616c", [], ["message", "s14h696e6465785f73657276696365735h4c6f63616c", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [7, 6, 8], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate .indexEqual, [6, 6], [.data .boolean], []⟩]
  returned := [10, 9]
  servicePorts := [⟨"service_0", "role00000001", 1, 0, "random.koala-bear.ext4-binomial3/0"⟩]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }

end Tests.IndexServices.Local.Validator

namespace Tests.IndexServices.Local

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.IndexServices.Local



/-! Constructor data from the retained actual MLIR export.
Regenerate with bridges/structured/snapshot.py; admission and semantic proofs
are separate. The native bridge checks exact regeneration against the source. -/

namespace Tests.IndexServices.Repeated.Source
open Zkc.Source.Structured

def snapshot : Snapshot where
  source := "sha256:133a7b929ba2eb8e76c66597974a50ee4b83b94e80ec2b098cfc48b08b3f0376"
  entry := "s14h696e6465785f73657276696365738h5265706561746564"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"s14h696e6465785f73657276696365738h5265706561746564", .protocol, .publicDef, [.service "random.koala-bear.ext4-binomial3/0"], [.boolean], some ⟨["role00000000", "role00000001"], [["role00000001"]], [["role00000001"]]⟩, [], some (.protocol ⟨"index_services::Repeated", []⟩), (.block [.instruction (.booleanConstant true) [] [.boolean] [] "", .instruction (.restrict ["role00000001"]) [0] [.boolean] [] "", .instruction (.indexConstant "3") [] [.index] [] "", .instruction (.protocolRepeat 1 3 ["role00000000", "role00000001"] [["role00000001"]]) [0, 1, 3] [.boolean] [.region [.index, .boolean, .service "random.koala-bear.ext4-binomial3/0"] [.boolean] (.block [.instruction (.indexConstant "8") [] [.index] [] "", .instruction (.sampleIndex "role00000001" "random.koala-bear.ext4-binomial3/0") [3, 0] [.index] [] "label_706f736974696f6e", .instruction (.exchange "role00000001" "role00000000") [0] [.index] [] "label_64656c6976657279_0", .instruction (.restrict ["role00000000"]) [0] [.index] [] "", .instruction (.call "zks_392204dc39f87acfad882f141c168cae20c93f8b0cb6444f3dfdbb3d25434d33") [5, 2] [.boolean] [] ""] (.yield [0]))] "s4"] (.ret [0]))⟩, .function ⟨"zks_392204dc39f87acfad882f141c168cae20c93f8b0cb6444f3dfdbb3d25434d33", .math, .privateDef, [.boolean, .index], [.boolean], none, [], none, (.block [.instruction (.mathBranch) [0, 1] [.boolean] [.region [.index] [.boolean] (.block [.instruction (.indexEqual) [0, 0] [.boolean] [] ""] (.yield [0])), .region [.index] [.boolean] (.block [.instruction (.booleanConstant false) [] [.boolean] [] ""] (.yield [0]))] ""] (.ret [0]))⟩]
  contracts := [⟨"s14h696e6465785f73657276696365738h5265706561746564", []⟩]
  catalogue := { nominals := [⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [⟨"random.koala-bear.ext4-binomial3/0", "koala-bear.ext4-binomial3", ["draw", "index", "indices"]⟩] }
  sourceDeclarations := { records := [], protocols := [], authorities := [] }

end Tests.IndexServices.Repeated.Source



namespace Tests.IndexServices.Repeated.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:133a7b929ba2eb8e76c66597974a50ee4b83b94e80ec2b098cfc48b08b3f0376"
  candidate := "sha256:535e453a57d7c48b1dfebdd630ee80583544be60c4d15f0af1652fc6a698af58"
  policy := ⟨"s14h696e6465785f73657276696365738h5265706561746564", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.loop "s4" 3, [1, 0], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], [⟨[.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], [
        ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [5, 2], [.indices], []⟩,
        ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365738h5265706561746564", [.repeat "s14h696e6465785f73657276696365738h5265706561746564" "s4"], ["query", "s14h696e6465785f73657276696365738h5265706561746564", "label_706f736974696f6e", "input_0", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [3, 4, 6], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [9, 2], [.indices], []⟩,
        ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365738h5265706561746564", [.repeat "s14h696e6465785f73657276696365738h5265706561746564" "s4"], ["message", "s14h696e6465785f73657276696365738h5265706561746564", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [8, 7, 10], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩], [11]⟩]⟩]
  returned := [2]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Repeated.Producer

namespace Tests.IndexServices.Repeated.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:133a7b929ba2eb8e76c66597974a50ee4b83b94e80ec2b098cfc48b08b3f0376"
  candidate := "sha256:535e453a57d7c48b1dfebdd630ee80583544be60c4d15f0af1652fc6a698af58"
  policy := ⟨"s14h696e6465785f73657276696365738h5265706561746564", "role00000000", "role00000001", 0, "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", [0], [], [("label_706f736974696f6e", "label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"]
  instructions := [
    ⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩,
    ⟨.calculate (.indexConstant 3), [], [.data .index], []⟩,
    ⟨.loop "s4" 3, [2, 1, 0], [.data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], [⟨[.data .index, .data .boolean, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], [
        ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
        ⟨.calculate (.indexConstant 8), [], [.data .index], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [8, 3], [.indices], []⟩,
        ⟨.indexChallenge "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" 8 ⟨"s14h696e6465785f73657276696365738h5265706561746564", [.repeat "s14h696e6465785f73657276696365738h5265706561746564" "s4"], ["query", "s14h696e6465785f73657276696365738h5265706561746564", "label_706f736974696f6e", "input_0", "random.koala-bear.ext4-binomial3/0", "index", "role00000001"]⟩, [5, 7, 9], [.data .index, .transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [12, 3], [.indices], []⟩,
        ⟨.observe "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" ⟨"s14h696e6465785f73657276696365738h5265706561746564", [.repeat "s14h696e6465785f73657276696365738h5265706561746564" "s4"], ["message", "s14h696e6465785f73657276696365738h5265706561746564", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [11, 10, 13], [.transcript "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"], []⟩,
        ⟨.mathBranch, [4, 10], [.data .boolean], [⟨[.data .index], [
            ⟨.calculate .indexEqual, [0, 0], [.data .boolean], []⟩], [1]⟩, ⟨[.data .index], [
            ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩], [1]⟩]⟩], [15, 14]⟩]⟩]
  returned := [3, 4]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0", .transcript, [("ChallengeField", "koala-bear.ext4-binomial3")], ["FieldTranscript", "IndexTranscript", "IndexBlockTranscript", "Transcript"], none⟩, ⟨"koala-bear", .field, [], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"], (some 2130706433)⟩, ⟨"koala-bear.ext4-binomial3", .field, [("BaseField", "koala-bear")], ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField", "IndexRandomness", "IndexBlockRandomness"], (some 2130706433)⟩], services := [] }

end Tests.IndexServices.Repeated.Validator

namespace Tests.IndexServices.Repeated

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end Tests.IndexServices.Repeated
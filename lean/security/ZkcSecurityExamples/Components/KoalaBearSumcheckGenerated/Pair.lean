module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:58d9f720d2e530b34f23366aae4907b511c2cc70b5b772c9fced7cc65549b831"
  candidate := "sha256:ed9858172e768f10fb53b8667d41b5d1805e8c5ba70479110a93d67ab4862fa1"
  policy := ⟨"s14h6d697865645f73756d636865636b4h526f6f74", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [3], [0, 1, 2], [("apply_16_label_726f756e64_label_6368616c6c656e6765", "apply_16_label_726f756e64_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  outputs := [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  instructions := [
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [0], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [1], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.send "apply_16_label_726f756e64_label_6c6f77_0" "apply_16_label_726f756e64_label_6c6f77_0" "role00000001", [3], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6c6f77_0", "label_6c6f77_0", "role00000000", "role00000001"]⟩, [2, 3, 5], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.send "apply_16_label_726f756e64_label_68696768_0" "apply_16_label_726f756e64_label_68696768_0" "role00000001", [4], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_68696768_0", "label_68696768_0", "role00000000", "role00000001"]⟩, [6, 4, 7], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.koala-bear.ext8-binomial3.rejection31le/0" "koala-bear.ext8-binomial3" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["query", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6368616c6c656e6765", "input_4", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, [8, 9], [.data (.field "koala-bear.ext8-binomial3"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [11, 10, 12], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩]
  returned := [13]

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Producer

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:58d9f720d2e530b34f23366aae4907b511c2cc70b5b772c9fced7cc65549b831"
  candidate := "sha256:ed9858172e768f10fb53b8667d41b5d1805e8c5ba70479110a93d67ab4862fa1"
  policy := ⟨"s14h6d697865645f73756d636865636b4h526f6f74", "role00000000", "role00000001", 0, "merlin3.koala-bear.ext8-binomial3.rejection31le/0", [3], [0, 1, 2], [("apply_16_label_726f756e64_label_6368616c6c656e6765", "apply_16_label_726f756e64_label_64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.field "koala-bear"), .data (.field "koala-bear"), .data (.field "koala-bear"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  outputs := [.data .boolean, .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"]
  instructions := [
    ⟨.call "s14h6d697865645f73756d636865636b5h656d626564", [2], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b7h70656e64696e67", [4], [.data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b10h6f70656e5f636c61696d", [5, 6], [.data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.receive "apply_16_label_726f756e64_label_6c6f77_0" "apply_16_label_726f756e64_label_6c6f77_0" "role00000000" (.field "koala-bear.ext8-binomial3"), [], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6c6f77_0", "label_6c6f77_0", "role00000000", "role00000001"]⟩, [3, 9, 10], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.receive "apply_16_label_726f756e64_label_68696768_0" "apply_16_label_726f756e64_label_68696768_0" "role00000000" (.field "koala-bear.ext8-binomial3"), [], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_68696768_0", "label_68696768_0", "role00000000", "role00000001"]⟩, [11, 12, 13], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [9, 12], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldEqual "koala-bear.ext8-binomial3"), [15, 8], [.data .boolean], []⟩,
    ⟨.guard "apply_16_label_726f756e64_s13", [16], [], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.challenge "merlin3.koala-bear.ext8-binomial3.rejection31le/0" "koala-bear.ext8-binomial3" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["query", "s14h6d697865645f73756d636865636b5h526f756e64", "label_6368616c6c656e6765", "input_4", "random.koala-bear.ext8-binomial3/0", "draw", "role00000001"]⟩, [14, 17], [.data (.field "koala-bear.ext8-binomial3"), .transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.observe "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ⟨"s14h6d697865645f73756d636865636b4h526f6f74", [⟨"apply", "s14h6d697865645f73756d636865636b4h526f6f74", "label_726f756e64"⟩], ["message", "s14h6d697865645f73756d636865636b5h526f756e64", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [19, 18, 20], [.transcript "merlin3.koala-bear.ext8-binomial3.rejection31le/0"], []⟩,
    ⟨.calculate (.fieldSubtract "koala-bear.ext8-binomial3"), [12, 9], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldMultiply "koala-bear.ext8-binomial3"), [22, 18], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.calculate (.fieldAdd "koala-bear.ext8-binomial3"), [9, 23], [.data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", [7, 18], [.data (.vector "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b8h61745f706f696e74", [25, 24], [.data (.vector "koala-bear.ext8-binomial3"), .data (.field "koala-bear.ext8-binomial3")], []⟩,
    ⟨.call "s14h6d697865645f73756d636865636b5h636865636b", [0, 1, 26, 27], [.data .boolean], []⟩]
  returned := [28, 21]

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair.Validator

namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Pair

module

public import Zkc.Construction.Participant

@[expose] public section

/-! Constructor data from the retained `zkc.constructed-participant/0` export.
Regenerate with bridges/construction/check.py --write; the Lean rule and its proofs are
separate. The bridge checks exact regeneration against the compiler. -/

namespace ZkcExamples.Construction.GkrProofParticipant
open Zkc.Construction

def participant : Participant where
  source := "sha256:1821aa9e25a8ddb68a0a62a95697a785cf83bb5039c7df9847d2dcff35010849"
  candidate := "sha256:6c550a9bedd4c139e28c08cec5d84948143e56aec6d24a0985542f116ffb2a1d"
  policy := ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3, 4, 5, 6], [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"), ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"), ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data .index, .data .index, .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "s4" 4 [19, 18], [6, 8, 7], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [12, 9], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s4"⟩], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f7574707574", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [11, 13], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [16, 9], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s4"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f75747075745f64656c6976657279_0", "label_6f75747075745f64656c6976657279_0", "role00000001", "role00000000"]⟩, [15, 14, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [10, 14], [.data (.vector "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", [1, 9], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.loop "s23" 4 [51, 50, 49], [4, 9, 11, 10], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "apply_14_label_6c656674_s6" 4 [49, 53, 48], [6, 16, 14, 15], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [22, 12], [.indices], []⟩,
            ⟨.indicesAppend, [23, 17], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [20, 21, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [27, 12], [.indices], []⟩,
            ⟨.indicesAppend, [28, 17], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [25, 26, 29], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_2" "apply_14_label_6c656674_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [32, 12], [.indices], []⟩,
            ⟨.indicesAppend, [33, 17], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [30, 31, 34], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [21, 21], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [36, 26], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [37, 31], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldEqual "bls12-381.fr"), [19, 38], [.data .boolean], []⟩,
            ⟨.guard "apply_14_label_6c656674_s18", [39], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [40, 12], [.indices], []⟩,
            ⟨.indicesAppend, [41, 17], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [35, 42], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [45, 12], [.indices], []⟩,
            ⟨.indicesAppend, [46, 17], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [44, 43, 47], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [18, 43], [.data (.vector "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [43, 31], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [26, 50], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [43, 51], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [21, 52], [.data (.field "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "apply_16_label_7269676874_s6" 4 [53, 57, 52], [6, 20, 18, 19], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [26, 12], [.indices], []⟩,
            ⟨.indicesAppend, [27, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [24, 25, 28], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [31, 12], [.indices], []⟩,
            ⟨.indicesAppend, [32, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [29, 30, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_2" "apply_16_label_7269676874_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [36, 12], [.indices], []⟩,
            ⟨.indicesAppend, [37, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [34, 35, 38], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [25, 25], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [40, 30], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [41, 35], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldEqual "bls12-381.fr"), [23, 42], [.data .boolean], []⟩,
            ⟨.guard "apply_16_label_7269676874_s18", [43], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [44, 12], [.indices], []⟩,
            ⟨.indicesAppend, [45, 21], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [39, 46], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [49, 12], [.indices], []⟩,
            ⟨.indicesAppend, [50, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [48, 47, 51], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [22, 47], [.data (.vector "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [47, 35], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [30, 54], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [47, 55], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [25, 56], [.data (.field "bls12-381.fr")], []⟩]⟩,
        ⟨.receive "label_6c696e655f636f6e7374616e74_0" "label_6c696e655f636f6e7374616e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [25, 12], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f6e7374616e74_0", "label_6c696e655f636f6e7374616e74_0", "role00000000", "role00000001"]⟩, [23, 24, 26], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [28, 24], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "s48" 4 [38, 37], [6, 29, 27], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "label_6c696e655f636f656666696369656e74_0" "label_6c696e655f636f656666696369656e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [34, 12], [.indices], []⟩,
            ⟨.indicesAppend, [35, 30], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s48"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f656666696369656e74_0", "label_6c696e655f636f656666696369656e74_0", "role00000000", "role00000001"]⟩, [32, 33, 36], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [31, 33], [.data (.vector "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", [30], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [2, 12, 5], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [33, 13, 17, 21], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [3, 12, 5], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [35, 13, 17, 21], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [24, 32], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [34, 37], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [36, 24], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [39, 32], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [38, 40], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [22, 41], [.data .boolean], []⟩,
        ⟨.guard "s75", [42], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [43, 12], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [31, 44], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [47, 12], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f64656c6976657279_0", "label_6c696e655f64656c6976657279_0", "role00000001", "role00000000"]⟩, [46, 45, 48], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", [30, 45], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", [17, 21, 45], [.data (.vector "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", [0, 12], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldEqual "bls12-381.fr"), [15, 13], [.data .boolean], []⟩]
  returned := [16, 14]

end ZkcExamples.Construction.GkrProofParticipant

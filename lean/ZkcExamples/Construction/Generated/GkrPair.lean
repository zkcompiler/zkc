module

public import Zkc.Construction.AuthoredPair

@[expose] public section

namespace ZkcExamples.Construction.Generated.GkrPair.Producer
open Zkc.Construction

def participant : Participant where
  source := "sha256:b8d4a08c910b4c6ae7326518656c1fc274045b055dc26cfcba21b878c6e41334"
  candidate := "sha256:88a1ae4bfff52f3496a2163625b409c4be8f031df3cb8724381350d60dde560c"
  policy := ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3, 4, 5, 6], [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"), ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"), ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_0"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data .index, .data .index, .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "s37" 4 [18, 17], [5, 7, 6], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [11, 8], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s37"], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f7574707574", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [10, 12], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [15, 8], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s37"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f75747075745f64656c6976657279_0", "label_6f75747075745f64656c6976657279_0", "role00000001", "role00000000"]⟩, [14, 13, 16], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [9, 13], [.data (.vector "bls12-381.fr")], []⟩]⟩,
    ⟨.loop "s57" 4 [48, 47], [3, 8, 9], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", [1, 2, 0, 3, 4, 5, 10], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [1, 10, 4], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [2, 10, 4], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", [14, 15, 11, 13, 5], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "apply_14_label_6c656674_s9" 4 [52, 53, 54, 55, 56, 51], [5, 16, 17, 18, 19, 20, 12], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.call "zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", [22, 23, 24, 25], [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
            ⟨.send "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000001", [28], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [31, 10], [.indices], []⟩,
            ⟨.indicesAppend, [32, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [27, 28, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.send "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000001", [29], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [35, 10], [.indices], []⟩,
            ⟨.indicesAppend, [36, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [34, 29, 37], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.send "apply_14_label_6c656674_label_726f756e64_2" "apply_14_label_6c656674_label_726f756e64_2" "role00000001", [30], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [39, 10], [.indices], []⟩,
            ⟨.indicesAppend, [40, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [38, 30, 41], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [43, 10], [.indices], []⟩,
            ⟨.indicesAppend, [44, 21], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_8", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [42, 45], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [48, 10], [.indices], []⟩,
            ⟨.indicesAppend, [49, 21], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [47, 46, 50], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", [22, 23, 24, 25, 46], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr")], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [26, 46], [.data (.vector "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "apply_16_label_7269676874_s9" 4 [59, 60, 61, 62, 63, 58], [5, 21, 22, 23, 24, 27, 26], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.call "zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", [29, 30, 31, 32], [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
            ⟨.send "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000001", [35], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [38, 10], [.indices], []⟩,
            ⟨.indicesAppend, [39, 28], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [34, 35, 40], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.send "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000001", [36], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [42, 10], [.indices], []⟩,
            ⟨.indicesAppend, [43, 28], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [41, 36, 44], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.send "apply_16_label_7269676874_label_726f756e64_2" "apply_16_label_7269676874_label_726f756e64_2" "role00000001", [37], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [46, 10], [.indices], []⟩,
            ⟨.indicesAppend, [47, 28], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [45, 37, 48], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [50, 10], [.indices], []⟩,
            ⟨.indicesAppend, [51, 28], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_8", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [49, 52], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [55, 10], [.indices], []⟩,
            ⟨.indicesAppend, [56, 28], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [54, 53, 57], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", [29, 30, 31, 32, 53], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr")], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [33, 53], [.data (.vector "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", [13, 25, 32, 5], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.calculate (.indexConstant 0), [], [.data .index], []⟩,
        ⟨.call "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", [34, 35], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.send "label_6c696e655f636f6e7374616e74_0" "label_6c696e655f636f6e7374616e74_0" "role00000001", [36], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [37, 10], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f6e7374616e74_0", "label_6c696e655f636f6e7374616e74_0", "role00000000", "role00000001"]⟩, [33, 36, 38], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.loop "s93" 4 [46], [5, 39], [.transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.call "zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", [34, 40], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.send "label_6c696e655f636f656666696369656e74_0" "label_6c696e655f636f656666696369656e74_0" "role00000001", [42], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [43, 10], [.indices], []⟩,
            ⟨.indicesAppend, [44, 40], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s93"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f656666696369656e74_0", "label_6c696e655f636f656666696369656e74_0", "role00000000", "role00000001"]⟩, [41, 42, 45], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [41, 10], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [40, 42], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [45, 10], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f64656c6976657279_0", "label_6c696e655f64656c6976657279_0", "role00000001", "role00000000"]⟩, [44, 43, 46], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", [25, 32, 43], [.data (.vector "bls12-381.fr")], []⟩]⟩]
  returned := [11]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.Generated.GkrPair.Producer

namespace ZkcExamples.Construction.Generated.GkrPair.Validator
open Zkc.Construction

def participant : Participant where
  source := "sha256:b8d4a08c910b4c6ae7326518656c1fc274045b055dc26cfcba21b878c6e41334"
  candidate := "sha256:88a1ae4bfff52f3496a2163625b409c4be8f031df3cb8724381350d60dde560c"
  policy := ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "role00000000", "role00000001", 0, "merlin3.bls12-381.fr64be/0", [7], [0, 1, 2, 3, 4, 5, 6], [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"), ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"), ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"), ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")], "zkc.framed/0", ""⟩
  symbol := "_math_1"
  inputs := [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data .index, .data .index, .data .index, .transcript "merlin3.bls12-381.fr64be/0"]
  outputs := [.data .boolean, .transcript "merlin3.bls12-381.fr64be/0"]
  instructions := [
    ⟨.calculate (.indexConstant 4), [], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [8, 6], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [9, 10], [.data .boolean], []⟩,
    ⟨.guard "s4", [11], [], []⟩,
    ⟨.calculate (.indexConstant 4), [], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [12, 4], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [13, 14], [.data .boolean], []⟩,
    ⟨.guard "s9", [15], [], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", [0, 6, 16], [.data .boolean], []⟩,
    ⟨.guard "s12", [17], [], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", [1, 6, 18], [.data .boolean], []⟩,
    ⟨.guard "s15", [19], [], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [5, 6], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [20, 6], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [21, 6], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", [2, 22, 23], [.data .boolean], []⟩,
    ⟨.guard "s21", [24], [], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [5, 6], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [25, 6], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h7072656c7564659h696e6465785f616464", [26, 6], [.data .index], []⟩,
    ⟨.calculate (.indexConstant 1), [], [.data .index], []⟩,
    ⟨.call "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", [3, 27, 28], [.data .boolean], []⟩,
    ⟨.guard "s27", [29], [], []⟩,
    ⟨.call "s3h676b7212h706f7765725f6f665f74776f", [5], [.data .index], []⟩,
    ⟨.call "s3h7a6b637h696e64696365734h6c657373", [30, 4], [.data .boolean], []⟩,
    ⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
    ⟨.calculate .booleanEqual, [31, 32], [.data .boolean], []⟩,
    ⟨.guard "s32", [33], [], []⟩,
    ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
    ⟨.loop "s37" 4 [45, 44], [6, 34, 7], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [38, 35], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s37"], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f7574707574", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [37, 39], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [42, 35], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s37"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f75747075745f64656c6976657279_0", "label_6f75747075745f64656c6976657279_0", "role00000001", "role00000000"]⟩, [41, 40, 43], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [36, 40], [.data (.vector "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", [1, 35], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.call "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", [35, 37], [.data (.resourceUnit "zkl_resource_58b8d01538daf350e8922c1ff5eb530b8574005055adf8dd259237e225318f63"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
    ⟨.loop "s57" 4 [102, 103, 104, 99], [4, 38, 39, 40, 36], [.data (.resourceUnit "zkl_resource_58b8d01538daf350e8922c1ff5eb530b8574005055adf8dd259237e225318f63"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.call "zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", [42, 43, 44], [.data (.resourceUnit "zkl_resource_58b8d01538daf350e8922c1ff5eb530b8574005055adf8dd259237e225318f63"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", [50], [.data (.resourceUnit "zkl_resource_dbe13cb2a1fb7bfa08289b9828283a1e44368797e9bca45ea1c33789b9b72beb"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", [51, 52, 53], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.loop "apply_14_label_6c656674_s9" 4 [88, 92, 87], [6, 54, 55, 45], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [61, 41], [.indices], []⟩,
            ⟨.indicesAppend, [62, 56], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [59, 60, 63], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [66, 41], [.indices], []⟩,
            ⟨.indicesAppend, [67, 56], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [64, 65, 68], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_14_label_6c656674_label_726f756e64_2" "apply_14_label_6c656674_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [71, 41], [.indices], []⟩,
            ⟨.indicesAppend, [72, 56], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [69, 70, 73], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [60, 60], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [75, 65], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [76, 70], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldEqual "bls12-381.fr"), [58, 77], [.data .boolean], []⟩,
            ⟨.guard "apply_14_label_6c656674_s21", [78], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [79, 41], [.indices], []⟩,
            ⟨.indicesAppend, [80, 56], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_8", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [74, 81], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [84, 41], [.indices], []⟩,
            ⟨.indicesAppend, [85, 56], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_6c656674", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [83, 82, 86], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [57, 82], [.data (.vector "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [82, 70], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [65, 89], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [82, 90], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [60, 91], [.data (.field "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", [56, 57], [.data (.resourceUnit "zkl_resource_dbe13cb2a1fb7bfa08289b9828283a1e44368797e9bca45ea1c33789b9b72beb"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", [59, 60, 61], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.loop "apply_16_label_7269676874_s9" 4 [96, 100, 95], [6, 62, 63, 58], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [69, 41], [.indices], []⟩,
            ⟨.indicesAppend, [70, 64], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [67, 68, 71], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [74, 41], [.indices], []⟩,
            ⟨.indicesAppend, [75, 64], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [72, 73, 76], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.receive "apply_16_label_7269676874_label_726f756e64_2" "apply_16_label_7269676874_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [79, 41], [.indices], []⟩,
            ⟨.indicesAppend, [80, 64], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [77, 78, 81], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [68, 68], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [83, 73], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [84, 78], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldEqual "bls12-381.fr"), [66, 85], [.data .boolean], []⟩,
            ⟨.guard "apply_16_label_7269676874_s21", [86], [], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [87, 41], [.indices], []⟩,
            ⟨.indicesAppend, [88, 64], [.indices], []⟩,
            ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_8", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [82, 89], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [92, 41], [.indices], []⟩,
            ⟨.indicesAppend, [93, 64], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .apply "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "label_7269676874", .repeat "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba" "s9"], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [91, 90, 94], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [65, 90], [.data (.vector "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [90, 78], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [73, 97], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldMultiply "bls12-381.fr"), [90, 98], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.calculate (.fieldAdd "bls12-381.fr"), [68, 99], [.data (.field "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", [64, 65], [.data (.resourceUnit "zkl_resource_dbe13cb2a1fb7bfa08289b9828283a1e44368797e9bca45ea1c33789b9b72beb"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", [67, 68, 69], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", [70], [.data (.vector "bls12-381.fr"), .data (.vector "bls12-381.fr")], []⟩,
        ⟨.receive "label_6c696e655f636f6e7374616e74_0" "label_6c696e655f636f6e7374616e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [75, 41], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f6e7374616e74_0", "label_6c696e655f636f6e7374616e74_0", "role00000000", "role00000001"]⟩, [66, 74, 76], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [78, 74], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.loop "s93" 4 [88, 87], [6, 79, 77], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], [
            ⟨.receive "label_6c696e655f636f656666696369656e74_0" "label_6c696e655f636f656666696369656e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
            ⟨.indicesEmpty, [], [.indices], []⟩,
            ⟨.indicesAppend, [84, 41], [.indices], []⟩,
            ⟨.indicesAppend, [85, 80], [.indices], []⟩,
            ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57", .repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s93"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f656666696369656e74_0", "label_6c696e655f636f656666696369656e74_0", "role00000000", "role00000001"]⟩, [82, 83, 86], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
            ⟨.call "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [81, 83], [.data (.vector "bls12-381.fr")], []⟩]⟩,
        ⟨.call "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", [80], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [2, 41, 5], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [83, 49, 72, 73], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [3, 41, 5], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [85, 49, 72, 73], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [74, 82], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [84, 87], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [86, 74], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldMultiply "bls12-381.fr"), [89, 82], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [88, 90], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.calculate (.fieldEqual "bls12-381.fr"), [71, 91], [.data .boolean], []⟩,
        ⟨.guard "s122", [92], [], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [93, 41], [.indices], []⟩,
        ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [81, 94], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [97, 41], [.indices], []⟩,
        ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [.repeat "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" "s57"], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f64656c6976657279_0", "label_6c696e655f64656c6976657279_0", "role00000001", "role00000000"]⟩, [96, 95, 98], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
        ⟨.call "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", [72, 73, 95], [.data (.vector "bls12-381.fr")], []⟩,
        ⟨.call "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", [80, 95], [.data (.field "bls12-381.fr")], []⟩,
        ⟨.call "zkl_744f32fd2e4e542d6467fe3f764e183881171708947eb2bd852cea6f32a0407e", [46, 47, 48, 100, 101], [.data (.resourceUnit "zkl_resource_58b8d01538daf350e8922c1ff5eb530b8574005055adf8dd259237e225318f63"), .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr")], []⟩]⟩,
    ⟨.call "zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", [0, 41, 42, 43], [.data .boolean], []⟩]
  returned := [45, 44]

/-- The exported catalogue rows of the identities the participant names, for
`Participant.checkCatalogue` to admit. -/
def catalogue : Zkc.Source.Structured.Catalogue :=
  { nominals := [⟨"bls12-381.fr", .field, [("PairingG1", "bls12-381.g1"), ("PairingG2", "bls12-381.g2"), ("PairingGT", "bls12-381.gt")], ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], (some 52435875175126190479447740508185965837690552500527637822603658699938581184513)⟩, ⟨"bls12-381.g2", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.gt", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"bls12-381.g1", .group, [("Scalar", "bls12-381.fr")], ["Group", "ScalarAction"], none⟩, ⟨"merlin3.bls12-381.fr64be/0", .transcript, [("ChallengeField", "bls12-381.fr")], ["FieldTranscript", "Transcript"], none⟩], services := [] }

end ZkcExamples.Construction.Generated.GkrPair.Validator

namespace ZkcExamples.Construction.Generated.GkrPair

def artifacts : Zkc.Construction.AuthoredPair.Artifacts :=
  ⟨Producer.participant, Validator.participant⟩

end ZkcExamples.Construction.Generated.GkrPair

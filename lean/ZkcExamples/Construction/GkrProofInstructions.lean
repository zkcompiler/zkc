module

public import ZkcExamples.Construction.GkrProof
public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcExamples.Structured.GkrVerifierProcess
public import Zkc.Construction.Reading

@[expose] public section

/-! The exported instructions of the compiled GKR verifier and the equations its
interactive reading uses.

`instructions_eq` names the loop bodies of the constructed validator
(`GkrProofParticipant`) and its segments around the inner loops. The context the
check derives is a literal (`context_eq`), and every template, site and peer
equation holds by definition, so the reading can rewrite inside the actions of
its processes (`normalize_sites`). Helper calls are read with the admitted
unit's own helper equations (`ZkcExamples.Structured.GkrSourceLaws`), and the
plain verifier's invariants (`Yields`) record what its steps return.
`read_instructions` unfolds the reading of literal instructions on an
environment of known prefix length.

The instruction literals are copied from `GkrProofParticipant`, which the
construction bridge regenerates: each loop body is the last component of its
loop instruction, split into the segments below. When the export changes,
`instructions_eq` fails until they are copied again.
-/

namespace ZkcExamples.Construction.GkrProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Structured.GkrSourceLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr

set_option linter.unusedSimpArgs false

/-! ## The exported instructions -/

/-- The output-point loop's body. -/
def outputBody : List Zkc.Construction.Instruction := [
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [12, 9], [.indices], []⟩,
  ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s4"⟩], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f7574707574", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [11, 13], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [16, 9], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s4"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6f75747075745f64656c6976657279_0", "label_6f75747075745f64656c6976657279_0", "role00000001", "role00000000"]⟩, [15, 14, 17], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [10, 14], [.data (.vector "bls12-381.fr")], []⟩]

def leftBodyA : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_14_label_6c656674_label_726f756e64_0" "apply_14_label_6c656674_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [22, 12], [.indices], []⟩,
  ⟨.indicesAppend, [23, 17], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [20, 21, 24], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def leftBodyB : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_14_label_6c656674_label_726f756e64_1" "apply_14_label_6c656674_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [27, 12], [.indices], []⟩,
  ⟨.indicesAppend, [28, 17], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [25, 26, 29], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def leftBodyC : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_14_label_6c656674_label_726f756e64_2" "apply_14_label_6c656674_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [32, 12], [.indices], []⟩,
  ⟨.indicesAppend, [33, 17], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [30, 31, 34], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def leftBodyD : List Zkc.Construction.Instruction := [
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [21, 21], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [36, 26], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [37, 31], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldEqual "bls12-381.fr"), [19, 38], [.data .boolean], []⟩,
  ⟨.guard "apply_14_label_6c656674_s18", [39], [], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [40, 12], [.indices], []⟩,
  ⟨.indicesAppend, [41, 17], [.indices], []⟩,
  ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [35, 42], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def leftBodyE : List Zkc.Construction.Instruction := [
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [45, 12], [.indices], []⟩,
  ⟨.indicesAppend, [46, 17], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c656674"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [44, 43, 47], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [18, 43], [.data (.vector "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [43, 31], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [26, 50], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [43, 51], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [21, 52], [.data (.field "bls12-381.fr")], []⟩]

/-- The first `Rounds` application's loop body. -/
def leftBody : List Zkc.Construction.Instruction :=
  leftBodyA ++ (leftBodyB ++ (leftBodyC ++ (leftBodyD ++ leftBodyE)))

def rightBodyA : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_16_label_7269676874_label_726f756e64_0" "apply_16_label_7269676874_label_726f756e64_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [26, 12], [.indices], []⟩,
  ⟨.indicesAppend, [27, 21], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩, [24, 25, 28], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def rightBodyB : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_16_label_7269676874_label_726f756e64_1" "apply_16_label_7269676874_label_726f756e64_1" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [31, 12], [.indices], []⟩,
  ⟨.indicesAppend, [32, 21], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩, [29, 30, 33], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def rightBodyC : List Zkc.Construction.Instruction := [
  ⟨.receive "apply_16_label_7269676874_label_726f756e64_2" "apply_16_label_7269676874_label_726f756e64_2" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [36, 12], [.indices], []⟩,
  ⟨.indicesAppend, [37, 21], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_726f756e64_2", "label_726f756e64_2", "role00000000", "role00000001"]⟩, [34, 35, 38], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def rightBodyD : List Zkc.Construction.Instruction := [
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [25, 25], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [40, 30], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [41, 35], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldEqual "bls12-381.fr"), [23, 42], [.data .boolean], []⟩,
  ⟨.guard "apply_16_label_7269676874_s18", [43], [], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [44, 12], [.indices], []⟩,
  ⟨.indicesAppend, [45, 21], [.indices], []⟩,
  ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["query", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [39, 46], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def rightBodyE : List Zkc.Construction.Instruction := [
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [49, 12], [.indices], []⟩,
  ⟨.indicesAppend, [50, 21], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"apply", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_7269676874"⟩, ⟨"repeat", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "s6"⟩], ["message", "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩, [48, 47, 51], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [22, 47], [.data (.vector "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [47, 35], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [30, 54], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [47, 55], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [25, 56], [.data (.field "bls12-381.fr")], []⟩]

/-- The second `Rounds` application's loop body. -/
def rightBody : List Zkc.Construction.Instruction :=
  rightBodyA ++ (rightBodyB ++ (rightBodyC ++ (rightBodyD ++ rightBodyE)))

/-- The line coefficients' loop body. -/
def coefficientBody : List Zkc.Construction.Instruction := [
  ⟨.receive "label_6c696e655f636f656666696369656e74_0" "label_6c696e655f636f656666696369656e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [34, 12], [.indices], []⟩,
  ⟨.indicesAppend, [35, 30], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩, ⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s48"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f656666696369656e74_0", "label_6c696e655f636f656666696369656e74_0", "role00000000", "role00000001"]⟩, [32, 33, 36], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [31, 33], [.data (.vector "bls12-381.fr")], []⟩]

def leftLoop : Zkc.Construction.Instruction :=
  ⟨.loop "apply_14_label_6c656674_s6" 4 [49, 53, 48], [6, 16, 14, 15], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], leftBody⟩

def rightLoop : Zkc.Construction.Instruction :=
  ⟨.loop "apply_16_label_7269676874_s6" 4 [53, 57, 52], [6, 20, 18, 19], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], rightBody⟩

def coefficientLoop : Zkc.Construction.Instruction :=
  ⟨.loop "s48" 4 [38, 37], [6, 29, 27], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], coefficientBody⟩

def layerStart : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", [], [.data (.vector "bls12-381.fr")], []⟩]

def layerMiddle : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", [], [.data (.vector "bls12-381.fr")], []⟩]

def layerLine : List Zkc.Construction.Instruction := [
  ⟨.receive "label_6c696e655f636f6e7374616e74_0" "label_6c696e655f636f6e7374616e74_0" "role00000000" (.field "bls12-381.fr"), [], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [25, 12], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f636f6e7374616e74_0", "label_6c696e655f636f6e7374616e74_0", "role00000000", "role00000001"]⟩, [23, 24, 26], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", [], [.data (.vector "bls12-381.fr")], []⟩,
  ⟨.call "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [28, 24], [.data (.vector "bls12-381.fr")], []⟩]

def layerTailA : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_be7976639f3a008cbb8e0434318fcf706bb5fc7884c4737fa9efb008c72e6d91", [30], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [2, 12, 5], [.data (.vector "bls12-381.fr")], []⟩,
  ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [33, 13, 17, 21], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.call "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", [3, 12, 5], [.data (.vector "bls12-381.fr")], []⟩,
  ⟨.call "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", [35, 13, 17, 21], [.data (.field "bls12-381.fr")], []⟩]

def layerTailB : List Zkc.Construction.Instruction := [
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [24, 32], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [34, 37], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [36, 24], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldMultiply "bls12-381.fr"), [39, 32], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldAdd "bls12-381.fr"), [38, 40], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldEqual "bls12-381.fr"), [22, 41], [.data .boolean], []⟩,
  ⟨.guard "s75", [42], [], []⟩]

def layerTailC : List Zkc.Construction.Instruction := [
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [43, 12], [.indices], []⟩,
  ⟨.challenge "merlin3.bls12-381.fr64be/0" "bls12-381.fr" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["query", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f6368616c6c656e6765", "input_7", "random.bls12-381.fr/0", "draw", "role00000001"]⟩, [31, 44], [.data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], []⟩]

def layerTailD : List Zkc.Construction.Instruction := [
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [47, 12], [.indices], []⟩,
  ⟨.observe "merlin3.bls12-381.fr64be/0" ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", [⟨"repeat", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "s23"⟩], ["message", "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", "label_6c696e655f64656c6976657279_0", "label_6c696e655f64656c6976657279_0", "role00000001", "role00000000"]⟩, [46, 45, 48], [.transcript "merlin3.bls12-381.fr64be/0"], []⟩,
  ⟨.call "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", [30, 45], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.call "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", [17, 21, 45], [.data (.vector "bls12-381.fr")], []⟩]

def layerTail : List Zkc.Construction.Instruction :=
  layerTailA ++ (layerTailB ++ (layerTailC ++ layerTailD))

/-- The layer loop's body. -/
def layerBody : List Zkc.Construction.Instruction :=
  layerStart ++ leftLoop :: (layerMiddle ++ rightLoop :: (layerLine ++ coefficientLoop :: layerTail))

def outputLoop : Zkc.Construction.Instruction :=
  ⟨.loop "s4" 4 [19, 18], [6, 8, 7], [.data (.vector "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], outputBody⟩

def layerLoop : Zkc.Construction.Instruction :=
  ⟨.loop "s23" 4 [51, 50, 49], [4, 9, 11, 10], [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "merlin3.bls12-381.fr64be/0"], layerBody⟩

def topStart : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", [], [.data (.vector "bls12-381.fr")], []⟩]

def topMiddle : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", [1, 9], [.data (.field "bls12-381.fr")], []⟩]

def topTail : List Zkc.Construction.Instruction := [
  ⟨.call "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", [0, 12], [.data (.field "bls12-381.fr")], []⟩,
  ⟨.calculate (.fieldEqual "bls12-381.fr"), [15, 13], [.data .boolean], []⟩]

/-- The top-level instructions. -/
def topInstructions : List Zkc.Construction.Instruction :=
  topStart ++ outputLoop :: (topMiddle ++ layerLoop :: topTail)


theorem instructions_eq : participant.instructions = topInstructions := rfl

theorem returned_eq : participant.returned = [16, 14] := rfl

/-- The occurrence context the check derives, as a literal. -/
def readingContext : Context where
  entry := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"
  roles := ["role00000000", "role00000001"]
  producer := 0
  validator := 1
  service := 7
  contract := "random.bls12-381.fr/0"
  request := some (.draw "bls12-381.fr")
  suite := "merlin3.bls12-381.fr64be/0"
  draws := [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"),
    ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),
    ("apply_16_label_7269676874_label_6368616c6c656e6765",
      "apply_16_label_7269676874_label_64656c6976657279_0"),
    ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")]

theorem context_eq : context = readingContext := by decide +kernel

theorem reading_producer : readingContext.producer = 0 := rfl

theorem reading_role : readingContext.role readingContext.validator = "role00000001" := rfl

/-! ## Templates and sites

Every equation here holds by definition, so the reading can rewrite the sites
and peers inside the actions of its processes. -/

theorem origin_query (context : Context) (entry : String) (steps : List Step)
    (caller site port contract owner : String) :
    Template.origin context ⟨entry, steps, ["query", caller, site, port, contract, "draw", owner]⟩ =
      context.request.map (context.query
        (Template.qualify ⟨entry, steps, ["query", caller, site, port, contract, "draw", owner]⟩ site)) :=
  rfl

theorem origin_message (context : Context) (entry : String) (steps : List Step)
    (caller site sender receiver : String) :
    Template.origin context ⟨entry, steps, ["message", caller, site, site, sender, receiver]⟩ =
      some (Origin.message context.entry
        (Template.qualify ⟨entry, steps, ["message", caller, site, site, sender, receiver]⟩ site)
        sender receiver) :=
  ite_eq_left rfl

theorem querySite_query (entry : String) (steps : List Step) (caller site port contract owner : String) :
    Template.querySite? ⟨entry, steps, ["query", caller, site, port, contract, "draw", owner]⟩ =
      some (Template.qualify ⟨entry, steps, ["query", caller, site, port, contract, "draw", owner]⟩ site) :=
  rfl

theorem messageSite_message (entry : String) (steps : List Step) (caller site schema sender receiver : String) :
    Template.messageSite? ⟨entry, steps, ["message", caller, site, schema, sender, receiver]⟩ =
      some (Template.qualify ⟨entry, steps, ["message", caller, site, schema, sender, receiver]⟩ site) :=
  rfl

theorem sentBy_message (entry : String) (steps : List Step) (caller site schema sender receiver role : String) :
    Template.sentBy ⟨entry, steps, ["message", caller, site, schema, sender, receiver]⟩ role =
      (sender == role) :=
  rfl

theorem qualify_repeat (entry protocol step : String) (event : List String) (site : String) :
    Template.qualify ⟨entry, [⟨"repeat", protocol, step⟩], event⟩ site = site := rfl

theorem qualify_repeats (entry outer outerStep inner innerStep : String) (event : List String)
    (site : String) :
    Template.qualify ⟨entry, [⟨"repeat", outer, outerStep⟩, ⟨"repeat", inner, innerStep⟩], event⟩ site =
      site := rfl

theorem qualify_application (entry outer outerStep caller application inner innerStep : String)
    (event : List String) (site : String) :
    Template.qualify ⟨entry, [⟨"repeat", outer, outerStep⟩, ⟨"apply", caller, application⟩,
      ⟨"repeat", inner, innerStep⟩], event⟩ site = qualifyProtocolSite (some application) site := rfl

theorem qualify_none (site : String) : qualifyProtocolSite none site = site := rfl

theorem producer_role : ("role00000000" == "role00000001") = false := by decide
theorem validator_self : ("role00000001" == "role00000001") = true := by decide

theorem output_site : GkrVerifier.outputSite {} = "label_6f7574707574" := rfl
theorem output_delivery_site : GkrVerifier.outputDeliverySite {} =
    "label_6f75747075745f64656c6976657279_0" := rfl
theorem line_constant_site : GkrVerifier.lineConstantSite {} = "label_6c696e655f636f6e7374616e74_0" := rfl
theorem line_coefficient_site : GkrVerifier.lineCoefficientSite {} =
    "label_6c696e655f636f656666696369656e74_0" := rfl
theorem line_challenge_site : GkrVerifier.lineChallengeSite {} = "label_6c696e655f6368616c6c656e6765" := rfl
theorem line_delivery_site : GkrVerifier.lineDeliverySite {} = "label_6c696e655f64656c6976657279_0" := rfl

theorem left_round_0 : GkrVerifier.roundSite (GkrVerifier.leftContext {}) "0" =
    "apply_14_label_6c656674_label_726f756e64_0" := rfl
theorem left_round_1 : GkrVerifier.roundSite (GkrVerifier.leftContext {}) "1" =
    "apply_14_label_6c656674_label_726f756e64_1" := rfl
theorem left_round_2 : GkrVerifier.roundSite (GkrVerifier.leftContext {}) "2" =
    "apply_14_label_6c656674_label_726f756e64_2" := rfl
theorem left_challenge : GkrVerifier.challengeSite (GkrVerifier.leftContext {}) =
    "apply_14_label_6c656674_label_6368616c6c656e6765" := rfl
theorem left_delivery : GkrVerifier.deliverySite (GkrVerifier.leftContext {}) =
    "apply_14_label_6c656674_label_64656c6976657279_0" := rfl
theorem left_qualified_challenge : qualifyProtocolSite (some "label_6c656674") "label_6368616c6c656e6765" =
    "apply_14_label_6c656674_label_6368616c6c656e6765" := rfl
theorem left_qualified_delivery : qualifyProtocolSite (some "label_6c656674") "label_64656c6976657279_0" =
    "apply_14_label_6c656674_label_64656c6976657279_0" := rfl
theorem right_round_0 : GkrVerifier.roundSite (GkrVerifier.rightContext {}) "0" =
    "apply_16_label_7269676874_label_726f756e64_0" := rfl
theorem right_round_1 : GkrVerifier.roundSite (GkrVerifier.rightContext {}) "1" =
    "apply_16_label_7269676874_label_726f756e64_1" := rfl
theorem right_round_2 : GkrVerifier.roundSite (GkrVerifier.rightContext {}) "2" =
    "apply_16_label_7269676874_label_726f756e64_2" := rfl
theorem right_challenge : GkrVerifier.challengeSite (GkrVerifier.rightContext {}) =
    "apply_16_label_7269676874_label_6368616c6c656e6765" := rfl
theorem right_delivery : GkrVerifier.deliverySite (GkrVerifier.rightContext {}) =
    "apply_16_label_7269676874_label_64656c6976657279_0" := rfl
theorem right_qualified_challenge :
    qualifyProtocolSite (some "label_7269676874") "label_6368616c6c656e6765" =
      "apply_16_label_7269676874_label_6368616c6c656e6765" := rfl
theorem right_qualified_delivery :
    qualifyProtocolSite (some "label_7269676874") "label_64656c6976657279_0" =
      "apply_16_label_7269676874_label_64656c6976657279_0" := rfl

theorem root_roles : ({} : ProtocolContext).roles 0 = 0 := rfl
theorem left_roles : (GkrVerifier.leftContext {}).roles 0 = 0 := rfl
theorem right_roles : (GkrVerifier.rightContext {}).roles 0 = 0 := rfl

/-! ## Environments -/

section Environments
variable {F G : Type}

theorem read_nil (env : List (Value F G)) : Zkc.Construction.read env [] = some [] := rfl

theorem read_cons (env : List (Value F G)) (reference : Nat) (rest : List Nat) :
    Zkc.Construction.read env (reference :: rest) =
      (env[reference]?).bind fun value => (Zkc.Construction.read env rest).map (value :: ·) := by
  simp only [Zkc.Construction.read, List.mapM_cons]
  cases env[reference]? <;> cases rest.mapM (env[·]?) <;> rfl

end Environments

/-! ## Helper calls -/

section Calls
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The admitted program's helper table. -/
abbrev meanings : Structured.Meanings F G := helperTable program F G

theorem call_of_invoke (helper : Helper)
    (member : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (arguments : List (Value F G)) (values : Values (assignment F G) helper.inputs)
    (decoded : decodeValues helper.inputs arguments = some values)
    (results : Values (assignment F G) helper.outputs)
    (invoked : invoke (helpers (G := G)) helper values = .done results) :
    callHelper (meanings (F := F) (G := G)) helper.name arguments = .returned (encodeValues results) := by
  rw [callHelper_invoke _ helper (helperTable_lookup program helper member) arguments values decoded]
  change (match Zkc.Construction.closedOutcome (invoke (helpers (G := G)) helper values) with
    | .returned results => PIR.Outcome.returned (encodeValues results)
    | .stopped reason => .stopped reason) = _
  rw [invoked]
  rfl

theorem call_empty :
    callHelper (meanings (F := F) (G := G))
        "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46" [] =
      .returned [.vector "bls12-381.fr" []] :=
  call_of_invoke SumcheckHelperBodies.emptyHelper (List.mem_map.mpr ⟨_, empty_member, empty_signature⟩)
    [] .nil rfl (.cons [] .nil) empty_equation

theorem call_append (xs : List F) (x : F) :
    callHelper (meanings (F := F) (G := G))
        "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58"
        [.vector "bls12-381.fr" xs, .data (.field "bls12-381.fr" x)] =
      .returned [.vector "bls12-381.fr" (xs ++ [x])] :=
  call_of_invoke SumcheckHelperBodies.appendHelper (List.mem_map.mpr ⟨_, append_member, append_signature⟩)
    _ (.cons xs (.cons x .nil)) (by simp [decodeValues, Value.decode]) _ (append_equation xs x)

theorem call_sum (xs : List F) :
    callHelper (meanings (F := F) (G := G))
        "zkl_be7976639f3a008cbb8e0434318fcf706bb5fc7884c4737fa9efb008c72e6d91"
        [.vector "bls12-381.fr" xs] =
      .returned [.data (.field "bls12-381.fr" xs.sum)] :=
  call_of_invoke GkrSourceBodies.sumHelper (List.mem_map.mpr ⟨_, sum_member, sum_signature⟩)
    _ (.cons xs .nil) (by simp [decodeValues, Value.decode]) _ (sum_equation xs)

theorem call_evaluate (n : Nat) (xs point : List F) (table : Table F n)
    (decoded : ofList? n xs = some table) (length : point.length = n) (small : n < 64)
    (vectorBound : xs.length < indexLimit) :
    callHelper (meanings (F := F) (G := G))
        "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496"
        [.vector "bls12-381.fr" xs, .vector "bls12-381.fr" point] =
      .returned [.data (.field "bls12-381.fr" (extension n table (coordinates n point)))] :=
  call_of_invoke GkrSourceBodies.evaluateHelper (List.mem_map.mpr ⟨_, evaluate_member, evaluate_signature⟩)
    _ (.cons xs (.cons point .nil)) (by simp [decodeValues, Value.decode]) _
    (evaluate_extension n xs point table decoded length small vectorBound)

theorem call_selectBlock (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    callHelper (meanings (F := F) (G := G))
        "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e"
        [.vector "bls12-381.fr" xs, .index position, .index bits] =
      .returned [.vector "bls12-381.fr" (block xs position size)] :=
  call_of_invoke GkrSourceBodies.selectBlockHelper
    (List.mem_map.mpr ⟨_, selectBlock_member, selectBlock_signature⟩)
    _ (.cons xs (.cons position (.cons bits .nil))) (by simp [decodeValues, Value.decode]) _
    (selectBlock_equation xs position bits size shape positive inside vectorBound)

theorem call_evaluateWiring (w : Nat) (xs gate left right : List F) (table : Table F (w + w + w))
    (decoded : ofList? (w + w + w) xs = some table) (gateLength : gate.length = w)
    (leftLength : left.length = w) (rightLength : right.length = w) (small : w + w + w < 64)
    (vectorBound : xs.length < indexLimit) :
    callHelper (meanings (F := F) (G := G))
        "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f"
        [.vector "bls12-381.fr" xs, .vector "bls12-381.fr" gate, .vector "bls12-381.fr" left,
          .vector "bls12-381.fr" right] =
      .returned [.data (.field "bls12-381.fr" (extension (w + w + w) table
        (coordinates (w + w + w) (gate ++ left ++ right))))] :=
  call_of_invoke GkrSourceBodies.evaluateWiringHelper
    (List.mem_map.mpr ⟨_, evaluateWiring_member, evaluateWiring_signature⟩)
    _ (.cons xs (.cons gate (.cons left (.cons right .nil)))) (by simp [decodeValues, Value.decode]) _
    (evaluateWiring_extension w xs gate left right table decoded gateLength leftLength rightLength small
      vectorBound)

theorem call_evaluateCoefficients (coefficients : List F) (point : F)
    (small : coefficients.length < indexLimit) :
    callHelper (meanings (F := F) (G := G))
        "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7"
        [.vector "bls12-381.fr" coefficients, .data (.field "bls12-381.fr" point)] =
      .returned [.data (.field "bls12-381.fr" (powerSum coefficients point))] :=
  call_of_invoke GkrSourceBodies.evaluateCoefficientsHelper
    (List.mem_map.mpr ⟨_, evaluateCoefficients_member, evaluateCoefficients_signature⟩)
    _ (.cons coefficients (.cons point .nil)) (by simp [decodeValues, Value.decode]) _
    (evaluateCoefficients_equation coefficients point small)

theorem call_linePoint (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    callHelper (meanings (F := F) (G := G))
        "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434"
        [.vector "bls12-381.fr" start, .vector "bls12-381.fr" finish, .data (.field "bls12-381.fr" t)] =
      .returned [.vector "bls12-381.fr" (linePoints start finish t)] :=
  call_of_invoke GkrSourceBodies.linePointHelper
    (List.mem_map.mpr ⟨_, linePoint_member, linePoint_signature⟩)
    _ (.cons start (.cons finish (.cons t .nil))) (by simp [decodeValues, Value.decode]) _
    (linePoint_equation start finish t sameLength small)

end Calls

/-! ## Calculations -/

section Calculations
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem calculate_add (x y : F) :
    Zkc.Construction.calculate (G := G) (.fieldAdd "bls12-381.fr")
        [.data (.field "bls12-381.fr" x), .data (.field "bls12-381.fr" y)] =
      .returned [.data (.field "bls12-381.fr" (x + y))] := by
  simp [Zkc.Construction.calculate, Calculation.op, Op.arguments, Zkc.Construction.decodeValues,
    Zkc.Construction.Value.decode, Calculation.evaluate]
  rfl

theorem calculate_multiply (x y : F) :
    Zkc.Construction.calculate (G := G) (.fieldMultiply "bls12-381.fr")
        [.data (.field "bls12-381.fr" x), .data (.field "bls12-381.fr" y)] =
      .returned [.data (.field "bls12-381.fr" (x * y))] := by
  simp [Zkc.Construction.calculate, Calculation.op, Op.arguments, Zkc.Construction.decodeValues,
    Zkc.Construction.Value.decode, Calculation.evaluate]
  rfl

theorem calculate_equal (x y : F) :
    Zkc.Construction.calculate (G := G) (.fieldEqual "bls12-381.fr")
        [.data (.field "bls12-381.fr" x), .data (.field "bls12-381.fr" y)] =
      .returned [.data (.boolean (decide (x = y)))] := by
  simp [Zkc.Construction.calculate, Calculation.op, Op.arguments, Zkc.Construction.decodeValues,
    Zkc.Construction.Value.decode, Calculation.evaluate]
  rfl

end Calculations

set_option hygiene false in
/-- Unfold the interactive reading of literal instructions on an environment
`env ++ suffix` whose prefix has the length `length` states. -/
macro "read_instructions" : tactic => `(tactic|
  simp only [specK, specStep, List.append_assoc, List.cons_append, List.nil_append,
    List.getElem?_append_right, List.getElem?_append_left, length, List.length_cons, List.length_nil,
    List.length_append, List.getElem?_cons_zero, List.getElem?_cons_succ, indicesAt, indexAt, dataAt,
    transcriptAt, Option.toList, Option.getD, origin_query, origin_message, querySite_query,
    messageSite_message, sentBy_message, reading_role, validator_self, producer_role, reading_producer,
    read_cons, read_nil, Option.bind_some, Option.map_some, sendPayload, afterIteration,
    scalarType, Zkc.Construction.Payload.ofValue, calculate_add, calculate_multiply, calculate_equal,
    call_append, call_empty, call_sum, pointValues, claimValues, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true,
    List.length_singleton, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT,
    reduceIte, String.reduceEq, String.reduceBEq, String.reduceAppend, decide_true, decide_false,
    qualify_repeat, qualify_repeats, qualify_application, qualify_none, eq_self, and_self, root_roles,
    left_roles, right_roles, output_site, output_delivery_site, line_constant_site, line_coefficient_site,
    line_challenge_site, line_delivery_site, left_round_0, left_round_1, left_round_2, left_challenge,
    left_delivery, left_qualified_challenge, left_qualified_delivery, right_round_0, right_round_1,
    right_round_2, right_challenge, right_delivery, right_qualified_challenge, right_qualified_delivery])

set_option hygiene false in
/-- `read_instructions` with the further equations `calls` states (helper calls
with their premises). -/
macro "read_instructions_with_calls" : tactic => `(tactic|
  simp only [specK, specStep, List.append_assoc, List.cons_append, List.nil_append,
    List.getElem?_append_right, List.getElem?_append_left, length, List.length_cons, List.length_nil,
    List.length_append, List.getElem?_cons_zero, List.getElem?_cons_succ, indicesAt, indexAt, dataAt,
    transcriptAt, Option.toList, Option.getD, origin_query, origin_message, querySite_query,
    messageSite_message, sentBy_message, reading_role, validator_self, producer_role, reading_producer,
    read_cons, read_nil, Option.bind_some, Option.map_some, sendPayload, afterIteration,
    scalarType, Zkc.Construction.Payload.ofValue, calculate_add, calculate_multiply, calculate_equal,
    call_append, call_empty, call_sum, pointValues, claimValues, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true,
    List.length_singleton, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT,
    reduceIte, String.reduceEq, String.reduceBEq, String.reduceAppend, decide_true, decide_false,
    qualify_repeat, qualify_repeats, qualify_application, qualify_none, eq_self, and_self, root_roles,
    left_roles, right_roles, output_site, output_delivery_site, line_constant_site, line_coefficient_site,
    line_challenge_site, line_delivery_site, left_round_0, left_round_1, left_round_2, left_challenge,
    left_delivery, left_qualified_challenge, left_qualified_delivery, right_round_0, right_round_1,
    right_round_2, right_challenge, right_delivery, right_qualified_challenge, right_qualified_delivery, calls])

/-- Rewrite sites and peers inside actions to literals, by definition. -/
macro "normalize_sites" : tactic => `(tactic|
  dsimp only [reading_producer, root_roles, left_roles, right_roles, output_site, output_delivery_site,
    line_constant_site, line_coefficient_site, line_challenge_site, line_delivery_site, left_round_0,
    left_round_1, left_round_2, left_challenge, left_delivery, left_qualified_challenge,
    left_qualified_delivery, right_round_0, right_round_1, right_round_2, right_challenge, right_delivery,
    right_qualified_challenge, right_qualified_delivery, qualify_repeat, qualify_repeats,
    qualify_application, qualify_none])

section Values
variable {F G : Type}

/-- A point and its transcript, as the output-point and coefficient loops carry them. -/
def pointValues (point : List F) : List (Value F G) :=
  [.vector "bls12-381.fr" point, .transcript []]

/-- A point, a claim and a transcript, as the `Rounds` and layer loops carry them. -/
def claimValues (point : List F) (claim : F) : List (Value F G) :=
  [.vector "bls12-381.fr" point, .data (.field "bls12-381.fr" claim), .transcript []]

end Values

/-! ## Invariants of the plain verifier -/

section Invariants
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (handle : Nat)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem outputRound_yields (count : Nat) (point : List F) (length : point.length = count) :
    Yields (fun point' : List F => point'.length = count + 1)
      (GkrVerifier.outputRound (G := G) {} handle point) := by
  intro r _
  simp [Yields, length]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_yields (ctx : ProtocolContext) (count : Nat) (state : List F × F)
    (length : state.1.length = count) :
    Yields (fun state' : List F × F => state'.1.length = count + 1)
      (GkrVerifier.round (G := G) ctx handle state) := by
  intro c0 c1 c2
  simp only [GkrVerifier.roundCheck]
  split
  · intro r _
    simp [Yields, length]
  · trivial

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem rounds_yields (ctx : ProtocolContext) (count : Nat) (claim : F) :
    Yields (fun state : List F × F => state.1.length = count)
      (GkrVerifier.rounds (G := G) ctx handle count claim) := by
  have repeated := Yields.repeatN (invariant := fun index (state : List F × F) => state.1.length = index)
    (step := GkrVerifier.round (G := G) ctx handle)
    (fun index state length => round_yields handle ctx index state length) count 0 ([], claim) rfl
  unfold GkrVerifier.rounds
  simpa using repeated

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lineCoefficient_yields (count : Nat) (coefficients : List F) (length : coefficients.length = count) :
    Yields (fun coefficients' : List F => coefficients'.length = count + 1)
      (GkrVerifier.lineCoefficient (G := G) {} coefficients) := by
  intro c
  simp [Yields, length]

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layerStep_yields (width : Nat) (add mul : Nat → Wiring F width) (index : Nat)
    (state : GkrVerifier.State F) (valid : state.1 = index ∧ state.2.1.length = width) :
    Yields (fun state' : GkrVerifier.State F => state'.1 = index + 1 ∧ state'.2.1.length = width)
      (GkrVerifier.layerStep (G := G) {} handle width add mul state) := by
  unfold GkrVerifier.layerStep
  refine (rounds_yields handle _ width _).bind fun left leftLength => ?_
  unfold GkrVerifier.layerAfterLeft
  refine (rounds_yields handle _ width _).bind fun right rightLength => ?_
  intro first
  unfold GkrVerifier.layerAfterConstant
  refine (Yields.repeatN (invariant := fun _ (_ : List F) => True)
    (step := GkrVerifier.lineCoefficient (G := G) {}) (fun _ _ _ _ => trivial) width 0 [first]
    trivial).bind fun coefficients _ => ?_
  unfold GkrVerifier.lineCheck
  split
  · intro t _
    simp [Yields, valid.1, linePoints_length, leftLength, rightLength]
  · trivial

end Invariants

end ZkcExamples.Construction.GkrProof

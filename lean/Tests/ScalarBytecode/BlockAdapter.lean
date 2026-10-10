import Zkc.Protocols.ScalarBytecode.OneRound.AdapterCompilation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Tests.ScalarBytecode.BlockAdapter
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution Zkc.Protocols.ScalarBytecode.OneRound.Adapter

theorem honest_accepts : (probe (fun _ => []) 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0])).2.2.stopped =
    some .accept := by decide
theorem short_read_retained :
    (probe id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).2.2.world.verifier.offset = 8 ∧
    (probe id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).2.2.stopped =
      some (.reject "abi_decode_failure:underrun") := by decide
theorem noncanonical_consumed :
    (probe id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 2305843009213697249)).2.2.world.verifier.offset = 8 ∧
    (probe id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 2305843009213697249)).2.2.stopped =
      some (.reject "abi_decode_failure:noncanonical") := by decide

-- Same rejected word and verdict, but a speculative absorb changes the retained
-- state. This is a model of an illicit read+absorb fusion, not the native code.
def badWord : Bytes := Zkc.Protocols.ScalarBytecode.Codec.enc 2305843009213697249
def v := (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial 2 badWord).verifier
def goodRead := update id ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩
  (⟨badWord,by decide⟩ : Word) v
def speculative : Local := {v with core := {v.core with
  provider := v.core.provider ++ [⟨0,by decide⟩] ++ badWord}}
def badRead := update id ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩
  (⟨badWord,by decide⟩ : Word) speculative
theorem premature_absorb_distinguished :
    exitOf goodRead = exitOf badRead ∧
    (stateOf goodRead).core.provider ≠ (stateOf badRead).core.provider := by decide

end Tests.ScalarBytecode.BlockAdapter

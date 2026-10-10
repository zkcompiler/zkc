import Zkc.Protocols.ScalarBytecode.OneRound.AdapterCompilation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Tests.ScalarBytecode.BlockExtraction
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution Zkc.Protocols.ScalarBytecode.BlockExtraction

def start : World Bytes :=
  ⟨⟨⟨"r24","scratch",0⟩,⟨fun n => if n=9 then 2 else if n=25 then 3 else 0,[],0⟩,0,0,[]⟩,[]⟩
def testScratch : Instr := ⟨300,.check,.reg 26,.binding,0,[],"scratch",40⟩
def badPost : List Instr := [testScratch,⟨301,.accept,.binding,.binding,0,[],"",41⟩]
def kill : Instr := ⟨299,.constant,.binding,.binding,0,[],"",26⟩

def old (post : List Instr) := run (openStep (fun _ => []) bufferSupplier) (flatBody ++ post) start
def factored (post : List Instr) := asTerminal (baseline (fun _ => []) bufferSupplier [] (next post) start)

theorem removed_scratch_observable :
    (old badPost).outcome = .reject "check_failure" ∧ (factored badPost).outcome = .accept := by decide

theorem unsafe_continuation_refused : ¬ Zkc.Protocols.ScalarBytecode.Frames.Safe Live testScratch := by
  simp [testScratch,Zkc.Protocols.ScalarBytecode.Frames.Safe,Zkc.Protocols.ScalarBytecode.Frames.Reads,Live]

theorem bookkeeping_not_equal :
    (old []).state.verifier.pc = 5 ∧ (factored []).state.verifier.pc = 0 ∧
    (old []).state.verifier.history.length = 5 ∧ (factored []).state.verifier.history.length = 0 := by decide

-- Sufficient fixed footprints need not be complete: overwriting scratch before
-- reading it is legal. This is an input for a later backward validator, not a
-- reason to weaken the preservation premise.
theorem overwrite_before_observation :
    (old (kill :: badPost)).outcome = .accept ∧
    (factored (kill :: badPost)).outcome = .accept ∧
    (old (kill :: badPost)).events = (factored (kill :: badPost)).events := by decide

theorem fixed_footprint_rejects_safe_overwrite :
    ¬ (∀ i ∈ kill :: badPost, Zkc.Protocols.ScalarBytecode.Frames.Safe Live i) := by
  intro h
  exact unsafe_continuation_refused (h testScratch (by simp [badPost]))

-- A failing read does not kill its previous destination. An ordinary successful
-- assignment's backward transfer cannot be used unchanged on failure paths.
def readScratch : Instr := ⟨299,.read,.binding,.binding,11,[],"overwrite",26⟩
theorem failed_overwrite_retains_old_scratch :
    (old [readScratch]).outcome = (factored [readScratch]).outcome ∧
    (old [readScratch]).state.verifier.core.regs 26 = 6 ∧
    (factored [readScratch]).state.verifier.core.regs 26 = 0 := by decide

def siteSupplier : Supplier Unit where
  read := fun _ _ s => (⟨[],by decide⟩,s)
  ended := fun k s => (k.site == 15,s)
  challenge := fun _ _ s => s
def endAt (site : Nat) :=
  run (openStep (fun _ => []) siteSupplier)
    [⟨site,.expectEnd,.binding,.binding,0,[],"",0⟩] ⟨start.verifier,()⟩
theorem external_key_not_administrative :
    (endAt 15).outcome = .incomplete ∧ (endAt 20).outcome = .reject "proof_trailing_data" := by decide

-- Whole represented runs, with malformed and trailing tapes, exercise the
-- composed source theorem. These controls are not its all-input proof.
def source (hash : Hash) (claim : Nat) (bs : Bytes) :=
  run (openStep hash bufferSupplier)
    (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post)) (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs)
theorem accepts : (source (fun _ => []) 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0])).outcome = .accept := by decide
theorem short : (source id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).state.verifier.offset = 8 ∧
    (source id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).outcome =
      .reject "abi_decode_failure:underrun" := by decide
theorem noncanonical : (source id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc Zkc.Protocols.ScalarBytecode.Parameters.modulus)).state.verifier.offset = 8 ∧
    (source id 2 (Zkc.Protocols.ScalarBytecode.Codec.enc Zkc.Protocols.ScalarBytecode.Parameters.modulus)).outcome = .reject "abi_decode_failure:noncanonical" := by decide
theorem trailing : (source (fun _ => []) 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0] ++ [⟨1,by decide⟩])).outcome =
    .reject "proof_trailing_data" := by decide

end Tests.ScalarBytecode.BlockExtraction

import Zkc.Protocols.ScalarBytecode.OneRound.Adapter
import Zkc.Protocols.ScalarBytecode.BlockExtraction

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.OneRound.Adapter
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution Zkc.Protocols.ScalarBytecode.BlockExtraction

theorem post_safe : ∀ i ∈ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post, Zkc.Protocols.ScalarBytecode.Frames.Safe Live i := by
  simp [Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post,Zkc.Protocols.ScalarBytecode.Frames.Safe,Zkc.Protocols.ScalarBytecode.Frames.Reads,Live]


theorem all_tapes (hash : Hash) (claim : Nat) (bs : Bytes) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash bufferSupplier)
        (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post)) (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs))
      (asTerminal (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.probe hash claim bs)) := by
  exact (source_optimized hash bufferSupplier Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post post_safe
    (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs) (fun _ _ => true) Zkc.Protocols.ScalarBytecode.OneRound.Adapter.noCache
    (by intro k v h; cases h)).1

-- Dispatch is checked at the flat program's own remaining length. No equality
-- of fuel, instruction count or administrative history is asserted.
theorem dispatch (hash : Hash) (claim : Nat) (bs : Bytes) :
    TerminalRel (OpenRel Live Eq)
      (endpoint hash bufferSupplier
        (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post))
        (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post)).length
        (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs))
      (asTerminal (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.probe hash claim bs)) := by
  have dispatch := endpoint_list hash bufferSupplier []
    (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post)) (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs) rfl
  simp only [List.nil_append] at dispatch
  rw [dispatch]
  exact all_tapes hash claim bs

-- Explicit public preflight has the same placement on both sides, before init
-- or supplier interaction. Its presence does not turn the source adapter into
-- a theorem about arbitrary Rust or the native hash implementation.
def preflight (claim : Nat) (bs : Bytes)
    (execute : Unit → Terminal (World Bytes) Event) : Terminal (World Bytes) Event :=
  if claim < Zkc.Protocols.ScalarBytecode.Parameters.modulus then execute ()
  else ⟨.reject "public_binding_failure",Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs,[]⟩

theorem with_preflight (hash : Hash) (claim : Nat) (bs : Bytes) :
    TerminalRel (OpenRel Live Eq)
      (preflight claim bs (fun _ => run (openStep hash bufferSupplier)
        (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.pre ++ (flatBody ++ Zkc.Protocols.ScalarBytecode.OneRound.Adapter.post)) (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs)))
      (preflight claim bs (fun _ => asTerminal (Zkc.Protocols.ScalarBytecode.OneRound.Adapter.probe hash claim bs))) := by
  unfold preflight
  split
  · exact all_tapes hash claim bs
  · exact ⟨rfl,⟨local_refl Live _,rfl⟩,rfl⟩

end Zkc.Protocols.ScalarBytecode.OneRound.Adapter

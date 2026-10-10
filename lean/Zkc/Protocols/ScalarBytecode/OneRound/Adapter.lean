import Zkc.Protocols.ScalarBytecode.BlockOptimization
import Zkc.Protocols.ScalarBytecode.OneRound.Source

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.OneRound.Adapter
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

-- Zkc.Protocols.Sumcheck.ProductFamily n1's actual effect order and domains, adapted to the existing Zkc.Protocols.ScalarBytecode.Suppliers
-- primitive semantics. This adapter is source-inspected, not an extraction theorem.
def pre : List Instr := [
  ⟨0,.init,.binding,.binding,0,Zkc.Realization.ByteEncoding.utf8 "sha256:af01e27b6cf7a6128d5ae54ed3f6415e3eb1212786b6b29ad6dda8ed06b758c9","",0⟩,
  ⟨1,.absorb,.binding,.binding,0,[],"s",2⟩,
  ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩,
  ⟨3,.absorb,.reg 5,.binding,0,[],"g1_0",6⟩,
  ⟨4,.read,.binding,.binding,2305843009213697249,[],"g1_1",9⟩,
  ⟨5,.absorb,.reg 9,.binding,0,[],"g1_1",10⟩,
  ⟨6,.read,.binding,.binding,2305843009213697249,[],"g1_2",13⟩,
  ⟨7,.absorb,.reg 13,.binding,0,[],"g1_2",14⟩,
  ⟨8,.add,.reg 5,.reg 5,0,[],"",16⟩,
  ⟨9,.add,.reg 16,.reg 9,0,[],"",18⟩,
  ⟨10,.add,.reg 18,.reg 13,0,[],"",20⟩,
  ⟨11,.check,.reg 20,.binding,0,[],"round1",22⟩,
  ⟨12,.draw,.binding,.binding,0,Zkc.Realization.ByteEncoding.utf8 "r16.sumcheck.c1","c1",25⟩]
def post : List Instr := [
  ⟨13,.add,.reg 25,.reg 25,0,[],"",31⟩,
  ⟨14,.check,.reg 30,.reg 31,0,[],"final",32⟩,
  ⟨15,.expectEnd,.binding,.binding,0,[],"",33⟩,
  ⟨16,.accept,.binding,.binding,0,[],"",34⟩]
def next (xs : List Zkc.Protocols.ScalarBytecode.Residue) : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit :=
  .action (.publish 30 (xs.headD 0)) (fun _ => guarded post (.done ()))
def noCache : Cache := fun _ => none
def probe (hash : Hash) (claim : Nat) (bs : Bytes) : Result Bytes :=
  (optimized hash bufferSupplier pre next (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs) (fun _ _ => true) noCache).1
def observed (r : Result Bytes) :=
  (r.2.2.stopped, r.2.2.world.verifier.offset, r.2.2.world.verifier.core.provider,
   r.1.map Event.op)

theorem joined (hash : Hash) (claim : Nat) (bs : Bytes) :
    Zkc.Compiler.Blocks.StateRefinement.RunRel (Related CursorRel)
      (baseline hash cursorSupplier pre next ⟨(Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs).verifier,⟨bs,0⟩⟩)
      (probe hash claim bs) :=
  (cursor_admission hash pre next _ ⟨bs,0⟩ (fun _ _ => true) noCache
    (by intro k v h; cases h)).1

end Zkc.Protocols.ScalarBytecode.OneRound.Adapter

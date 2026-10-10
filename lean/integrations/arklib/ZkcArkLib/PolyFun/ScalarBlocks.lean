import ZkcArkLib.PolyFun.Blocks
import Zkc.Protocols.ScalarBytecode.BlockOptimization

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.PolyFun.ScalarBlocks
open Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution ZkcArkLib.PolyFun.Blocks

variable {S : Type}

def baselineViaFree (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (supplier : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier S)
    (pre : List Zkc.Protocols.ScalarBytecode.Execution.Instr) (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : Zkc.Protocols.ScalarBytecode.Endpoint.World S) : Result S :=
  let p := Zkc.Realization.InstructionSequence.run (Zkc.Protocols.ScalarBytecode.Endpoint.openStep hash supplier) pre s
  if p.outcome = .incomplete then
    let r := execute Zkc.Compiler.Blocks.arithmetic (handler hash supplier)
      (Zkc.Compiler.Blocks.moduleCall truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source [8] (inputs p.state.verifier) next) ⟨p.state,none⟩
    (p.events ++ r.1,r.2)
  else (p.events,(),⟨p.state,some p.outcome⟩)

theorem baseline_agrees (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (supplier : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier S)
    (pre : List Zkc.Protocols.ScalarBytecode.Execution.Instr) (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : Zkc.Protocols.ScalarBytecode.Endpoint.World S) :
    baselineViaFree hash supplier pre next s = baseline hash supplier pre next s := by
  simp only [baselineViaFree,baseline,execute_agrees]

theorem effectful {T : Type} (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash)
    (lSup : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier S) (rSup : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier T) (R : S → T → Prop)
    (suppliers : Zkc.Protocols.ScalarBytecode.Suppliers.SupplierRel lSup rSup R) (pre : List Zkc.Protocols.ScalarBytecode.Execution.Instr)
    (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : Zkc.Protocols.ScalarBytecode.Endpoint.World S) (t : Zkc.Protocols.ScalarBytecode.Endpoint.World T)
    (states : Zkc.Protocols.ScalarBytecode.Suppliers.WorldRel R s t) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid Zkc.Compiler.Blocks.arithmetic cache) :
    Zkc.Compiler.Blocks.StateRefinement.RunRel (Related R) (baselineViaFree hash lSup pre next s)
      (optimized hash rSup pre next t store cache).1 ∧
    Zkc.Modules.ImmutableCache.Valid Zkc.Compiler.Blocks.arithmetic (optimized hash rSup pre next t store cache).2 := by
  rw [baseline_agrees]
  exact effectful_admission hash lSup rSup R suppliers pre next s t states store cache valid

-- The same concrete failure-state relation transfers without a second proof
-- of decoder correctness or Zkc.Compiler.Blocks's module algebra.
theorem related {T : Type} (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash)
    (lSup : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier S) (rSup : Zkc.Protocols.ScalarBytecode.Endpoint.Supplier T) (R : S → T → Prop)
    (suppliers : Zkc.Protocols.ScalarBytecode.Suppliers.SupplierRel lSup rSup R)
    (p : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : Packet S) (t : Packet T)
    (states : Related R s t) :
    Zkc.Compiler.Blocks.StateRefinement.RunRel (Related R)
      (execute Zkc.Compiler.Blocks.arithmetic (handler hash lSup) p s)
      (execute Zkc.Compiler.Blocks.arithmetic (handler hash rSup) p t) := by
  simp only [execute_agrees]
  exact Zkc.Compiler.Blocks.StateRefinement.run_related _ _ _ _ (handlers_related hash lSup rSup R suppliers) p s t states

end ZkcArkLib.PolyFun.ScalarBlocks

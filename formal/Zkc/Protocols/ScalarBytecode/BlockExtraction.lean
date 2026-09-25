import Zkc.Protocols.ScalarBytecode.BlockOptimization
import Zkc.Protocols.ScalarBytecode.Endpoint.Frames

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.BlockExtraction
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

-- The five arithmetic rows of the represented Zkc.Protocols.Sumcheck.ProductFamily n1 body. Pure row sites
-- are internal receipts; the following external keys remain Zkc.Protocols.ScalarBytecode.BlockExecution's fixed keys.
def flatBody : List Instr := [
  ⟨100,.mul,.reg 9,.reg 25,0,[],"",26⟩,
  ⟨101,.mul,.reg 25,.reg 25,0,[],"",27⟩,
  ⟨102,.mul,.reg 13,.reg 27,0,[],"",28⟩,
  ⟨103,.add,.reg 26,.reg 28,0,[],"",29⟩,
  ⟨104,.add,.reg 5,.reg 29,0,[],"",30⟩]

def Live (n : Nat) : Prop := n ≠ 26 ∧ n ≠ 27 ∧ n ≠ 28 ∧ n ≠ 29
instance (n : Nat) : Decidable (Live n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def moduleResult (v : Local) : Zkc.Protocols.ScalarBytecode.Residue :=
  (runBlock Zkc.Compiler.Blocks.arithmetic Zkc.Protocols.ScalarBytecode.BlockExecution.truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source (inputs v)) 8

theorem module_formula (v : Local) :
    moduleResult v = (v.core.regs 5 : Zkc.Protocols.ScalarBytecode.Residue) +
      ((v.core.regs 9 : Zkc.Protocols.ScalarBytecode.Residue) * (v.core.regs 25 : Zkc.Protocols.ScalarBytecode.Residue) +
      (v.core.regs 13 : Zkc.Protocols.ScalarBytecode.Residue) * ((v.core.regs 25 : Zkc.Protocols.ScalarBytecode.Residue) * (v.core.regs 25 : Zkc.Protocols.ScalarBytecode.Residue))) := by
  simp [moduleResult,Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source,runBlock,assign,eval,Zkc.Compiler.Blocks.arithmetic,inputs]

theorem module_nat (v : Local) :
    (moduleResult v).val =
      (v.core.regs 5 + ((v.core.regs 9 * v.core.regs 25) % Zkc.Protocols.ScalarBytecode.Parameters.modulus +
        (v.core.regs 13 * ((v.core.regs 25 * v.core.regs 25) % Zkc.Protocols.ScalarBytecode.Parameters.modulus)) % Zkc.Protocols.ScalarBytecode.Parameters.modulus)
        % Zkc.Protocols.ScalarBytecode.Parameters.modulus) % Zkc.Protocols.ScalarBytecode.Parameters.modulus := by
  rw [module_formula]
  simp only [ZMod.val_add, ZMod.val_mul, ZMod.val_natCast]
  simp [Zkc.Protocols.ScalarBytecode.Parameters.modulus, Nat.add_mod, Nat.mul_mod]

def published (v : Local) : Local :=
  {v with core := put v.core 30 (moduleResult v).val}

-- The relation holds for arbitrary Nat registers: modular arithmetic commutes
-- with interpretation, so canonical live-ins are not an algebraic premise.
theorem body_export (hash : Hash) (g : World Bytes) :
    TerminalRel (Zkc.Protocols.ScalarBytecode.Frames.Rel Live)
      (run (tailStep hash) flatBody (toTail g))
      ⟨.incomplete,toTail ⟨published g.verifier,g.external⟩,[]⟩ := by
  simp [TerminalRel,Zkc.Protocols.ScalarBytecode.Frames.Rel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,flatBody,run,tailStep,tailHandler,
    effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put,toTail,published,module_nat]
  intro n hn
  rcases hn with ⟨h26,h27,h28,h29⟩
  simp [h26,h27,h28,h29]

def next (post : List Instr) (xs : List Zkc.Protocols.ScalarBytecode.Residue) : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit :=
  .action (.publish 30 (xs.headD 0)) (fun _ => guarded post (.done ()))

theorem body_open {S : Type} (hash : Hash) (supplier : Supplier S) (g : World S) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash supplier) flatBody g)
      ⟨.incomplete,⟨published g.verifier,g.external⟩,[]⟩ := by
  simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,flatBody,run,
    openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put,
    published,module_nat]
  intro n hn
  rcases hn with ⟨h26,h27,h28,h29⟩
  simp [h26,h27,h28,h29]

theorem module_execution {S : Type} (hash : Hash) (supplier : Supplier S)
    (post : List Instr) (g : World S) :
    asTerminal (runProgram Zkc.Compiler.Blocks.arithmetic (handler hash supplier)
      (moduleCall Zkc.Protocols.ScalarBytecode.BlockExecution.truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source [8] (inputs g.verifier) (next post))
      ⟨g,none⟩) =
    run (openStep hash supplier) post ⟨published g.verifier,g.external⟩ := by
  unfold moduleCall
  rw [compile_block_correct]
  change asTerminal (runProgram arithmetic (handler hash supplier)
    (.action (.publish 30 (moduleResult g.verifier))
      (fun _ => guarded post (.done ()))) ⟨g,none⟩) = _
  simp only [runProgram,Zkc.Protocols.ScalarBytecode.BlockExecution.handler]
  change asTerminal (runProgram arithmetic (handler hash supplier)
    (guarded post (.done ())) ⟨⟨published g.verifier,g.external⟩,none⟩) = _
  rw [guarded_done]
  generalize run (openStep hash supplier) post
    (⟨published g.verifier,g.external⟩ : World S) = t
  rcases t with ⟨out,state,events⟩
  simp only [asTerminal]
  split <;> simp_all

theorem baseline_resume {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre post : List Instr) (g : World S) :
    asTerminal (baseline hash supplier pre (next post) g) =
      Zkc.Realization.InstructionSequence.resume (fun s => run (openStep hash supplier) post
        ⟨published s.verifier,s.external⟩) (run (openStep hash supplier) pre g) := by
  unfold baseline
  dsimp only
  split
  · have h := module_execution hash supplier post (run (openStep hash supplier) pre g).state
    simp only [asTerminal] at h ⊢
    simp only [Zkc.Realization.InstructionSequence.resume,‹(run (openStep hash supplier) pre g).outcome = .incomplete›,if_true]
    cases ht : runProgram arithmetic (handler hash supplier)
      (moduleCall Zkc.Protocols.ScalarBytecode.BlockExecution.truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source [8]
        (inputs (run (openStep hash supplier) pre g).state.verifier) (next post))
      ⟨(run (openStep hash supplier) pre g).state,none⟩
    simp only [ht] at h
    rw [← h]
  · simp_all [asTerminal,Zkc.Realization.InstructionSequence.resume]

-- Reuses the older open-context frame law, now with actual module publication.
-- Arbitrary deterministic supplier states and all malformed answers are allowed.
theorem source_factorization {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre post : List Instr) (safe : ∀ i ∈ post, Zkc.Protocols.ScalarBytecode.Frames.Safe Live i) (g : World S) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash supplier) (pre ++ (flatBody ++ post)) g)
      (asTerminal (baseline hash supplier pre (next post) g)) := by
  rw [baseline_resume]
  exact encapsulate_context hash supplier Live flatBody pre post
    (fun s => ⟨published s.verifier,s.external⟩) (body_open hash supplier) safe g

theorem source_optimized {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre post : List Instr) (safe : ∀ i ∈ post, Zkc.Protocols.ScalarBytecode.Frames.Safe Live i) (g : World S)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash supplier) (pre ++ (flatBody ++ post)) g)
      (asTerminal (optimized hash supplier pre (next post) g store cache).1) ∧
    Zkc.Modules.ImmutableCache.Valid arithmetic (optimized hash supplier pre (next post) g store cache).2 := by
  have h := effectful_admission hash supplier supplier Eq (supplier_refl supplier)
    pre (next post) g g ⟨rfl,rfl⟩ store cache valid
  have he := related_eq_result _ _ h.1
  exact ⟨he ▸ source_factorization hash supplier pre post safe g,h.2⟩

end Zkc.Protocols.ScalarBytecode.BlockExtraction

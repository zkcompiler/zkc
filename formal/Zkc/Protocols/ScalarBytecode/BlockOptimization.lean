import Zkc.Protocols.ScalarBytecode.BlockExecution
import Zkc.Protocols.BlockProfiles
import Zkc.Protocols.AlgebraicRounds.BlockTemplates

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.BlockExecution
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks

def tag := "scalar:q2305843009213697249"
def registry := Zkc.Protocols.BlockProfiles.registry "sumcheck:q2305843009213697249"
def typeOf (_ : Zkc.Protocols.ScalarBytecode.Residue) := tag
def ctx : Context String := fun i => if i < 4 then some tag else none
def truth (_ : Zkc.Protocols.ScalarBytecode.Residue) := false
def ss : List (Nat × String) := [(8,tag)]
def ts : List (Nat × String) := [(7,tag)]

theorem fits (env : Nat → Zkc.Protocols.ScalarBytecode.Residue) : Fits typeOf ctx env := by
  intro i t h
  simp only [ctx] at h
  split at h <;> simp_all [typeOf]

theorem respects : Respects registry typeOf (arithmetic (F := Zkc.Protocols.ScalarBytecode.Residue)) := by
  intro op s x y h _ _
  simp only [registry,Zkc.Protocols.BlockProfiles.registry,BEq.rfl,ite_true] at h
  split at h
  · have hs := Option.some.inj h
    cases hs
    rfl
  · cases h

theorem admitted : admission registry typeOf "flag" ctx
    (Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source : Block Zkc.Protocols.ScalarBytecode.Residue) Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.target ss ts .horner = true := by rfl

theorem meaning : HornerMeaning (arithmetic (F := Zkc.Protocols.ScalarBytecode.Residue)) truth (Fits typeOf ctx) :=
  fun env _ => horner_semiring truth env

def inputs (v : Local) : Nat → Zkc.Protocols.ScalarBytecode.Residue
  | 0 => v.core.regs 5
  | 1 => v.core.regs 9
  | 2 => v.core.regs 13
  | 3 => v.core.regs 25
  | _ => 0

abbrev Cache := Zkc.Modules.ImmutableCache.Cache (Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue) Zkc.Protocols.ScalarBytecode.Residue
def baseline {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre : List Instr) (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : World S) : Result S :=
  let p := run (openStep hash supplier) pre s
  if p.outcome = .incomplete then
    let r := runProgram arithmetic (handler hash supplier)
      (moduleCall truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source [8] (inputs p.state.verifier) next) ⟨p.state,none⟩
    (p.events ++ r.1,r.2)
  else (p.events,(),⟨p.state,some p.outcome⟩)

def optimized {S : Type} (hash : Hash) (supplier : Supplier S)
    (pre : List Instr) (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : World S)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache) : Result S × Cache :=
  let p := run (openStep hash supplier) pre s
  if p.outcome = .incomplete then
    let r := Zkc.Transformations.Memoization.runMemo arithmetic store cache (lower (handler hash supplier)
      (moduleCall truth Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.target [7] (inputs p.state.verifier) next) ⟨p.state,none⟩)
    ((p.events ++ r.1.1,r.1.2),r.2)
  else ((p.events,(),⟨p.state,some p.outcome⟩),cache)

-- Actual Zkc.Protocols.ScalarBytecode.Suppliers prefixes and arbitrary Zkc.Protocols.ScalarBytecode.BlockExecution effectful continuations surround the
-- actual Zkc.Compiler.Blocks admitted module. Both terminal states, not only verdicts, relate.
theorem effectful_admission {S T : Type} (hash : Hash)
    (lSup : Supplier S) (rSup : Supplier T) (R : S → T → Prop)
    (suppliers : SupplierRel lSup rSup R) (pre : List Instr)
    (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (s : World S) (t : World T)
    (states : WorldRel R s t) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    Zkc.Compiler.Blocks.StateRefinement.RunRel (Related R) (baseline hash lSup pre next s)
      (optimized hash rSup pre next t store cache).1 ∧
    Zkc.Modules.ImmutableCache.Valid arithmetic (optimized hash rSup pre next t store cache).2 := by
  have preRel := supplier_run suppliers hash pre s t states
  rcases preRel with ⟨out,worlds,events⟩
  unfold baseline optimized
  dsimp only
  rw [out]
  by_cases h : (run (openStep hash rSup) pre t).outcome = .incomplete
  · rw [if_pos h,if_pos h]
    have join := Zkc.Compiler.Blocks.StateRefinement.admitted_related registry typeOf "flag" arithmetic truth respects
      (Related R) (handler hash lSup) (handler hash rSup)
      (handlers_related hash lSup rSup R suppliers) ctx Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.source Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates.target
      ss ts .horner (fun _ => meaning) admitted
      (inputs (run (openStep hash lSup) pre s).state.verifier) (fits _) next
      ⟨(run (openStep hash lSup) pre s).state,none⟩
      ⟨(run (openStep hash rSup) pre t).state,none⟩ ⟨worlds,rfl⟩ store cache valid
    have veq := worlds.1
    change (run (openStep hash lSup) pre s).state.verifier =
      (run (openStep hash rSup) pre t).state.verifier at veq
    simp only [ss,ts,List.map_cons,List.map_nil] at join
    rw [veq] at join ⊢
    exact ⟨⟨by dsimp [Zkc.Compiler.Blocks.StateRefinement.RunRel] at join; rw [events,join.1.1],join.1.2⟩,join.2⟩
  · rw [if_neg h,if_neg h]
    exact ⟨⟨events,rfl,worlds,by simp⟩,valid⟩

-- Exact buffer/cursor instantiation: no second implementation of decoding or
-- supplier simulation, and no premise that all reads succeed.
theorem cursor_admission (hash : Hash) (pre : List Instr)
    (next : List Zkc.Protocols.ScalarBytecode.Residue → Program Zkc.Protocols.ScalarBytecode.Residue Action Unit) (v : Local) (s : TapeCursor)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    Zkc.Compiler.Blocks.StateRefinement.RunRel (Related CursorRel)
      (baseline hash cursorSupplier pre next ⟨v,s⟩)
      (optimized hash bufferSupplier pre next ⟨v,s.full.drop s.position⟩ store cache).1 ∧
    Zkc.Modules.ImmutableCache.Valid arithmetic
      (optimized hash bufferSupplier pre next ⟨v,s.full.drop s.position⟩ store cache).2 :=
  effectful_admission hash cursorSupplier bufferSupplier CursorRel cursor_represents
    pre next ⟨v,s⟩ ⟨v,s.full.drop s.position⟩ ⟨rfl,rfl⟩ store cache valid

end Zkc.Protocols.ScalarBytecode.BlockExecution

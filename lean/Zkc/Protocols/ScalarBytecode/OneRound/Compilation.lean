import Zkc.Protocols.ScalarBytecode.OneRound.Source
import Zkc.Protocols.ScalarBytecode.BlockExtraction
import Zkc.Protocols.BackendProfiles.Consumers

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.OneRound.Compilation
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

/-- Consumer-owned finite source selection, separate from the proposed module.
    Hash strings identify the selected input; this type does not authenticate
    a file or prove a native parser. -/
structure Ref where
  artifact : String
  source : String
  first : Nat
  length : Nat
  inputs : List Nat
  output : Nat
  guards : List Nat
  externalSites : List Nat
  deriving DecidableEq, Repr

def selectedRef : Ref := ⟨Zkc.Protocols.ScalarBytecode.OneRound.Source.artifactId,Zkc.Protocols.ScalarBytecode.OneRound.Source.sourceId,13,5,
  Zkc.Protocols.ScalarBytecode.OneRound.Source.inputRegs,Zkc.Protocols.ScalarBytecode.OneRound.Source.exportReg,[11,19],[2,4,6,12,20]⟩
def checkCaller (proposed : Ref) : Bool := decide (proposed = selectedRef)

theorem selected_caller (r : Ref) (ok : checkCaller r = true) : r = selectedRef :=
  of_decide_eq_true ok

def loadInputs (regs : List Nat) (v : Local) (i : Nat) : Zkc.Protocols.ScalarBytecode.Residue :=
  match regs[i]? with | some n => v.core.regs n | none => 0

theorem selected_inputs (v : Local) : loadInputs selectedRef.inputs v = Zkc.Protocols.ScalarBytecode.BlockExecution.inputs v := by
  funext i
  rcases i with _ | _ | _ | _ | i <;> rfl

def Live (n : Nat) : Prop := n ≠ 26 ∧ n ≠ 28 ∧ n ≠ 30 ∧ n ≠ 32
instance (n : Nat) : Decidable (Live n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def published (v : Local) : Local :=
  {v with core := put v.core Zkc.Protocols.ScalarBytecode.OneRound.Source.exportReg (Zkc.Protocols.ScalarBytecode.BlockExtraction.moduleResult v).val}

theorem body_open {S : Type} (hash : Hash) (supplier : Supplier S) (g : World S) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.body g)
      ⟨.incomplete,⟨published g.verifier,g.external⟩,[]⟩ := by
  simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,Zkc.Protocols.ScalarBytecode.OneRound.Source.body,Zkc.Protocols.ScalarBytecode.OneRound.Source.code,run,
    openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put,
    published,Zkc.Protocols.ScalarBytecode.OneRound.Source.exportReg,Zkc.Protocols.ScalarBytecode.BlockExtraction.module_nat]
  intro n hn
  rcases hn with ⟨h26,h28,h30,h32⟩
  simp [h26,h28,h30,h32]

theorem post_safe : ∀ i ∈ Zkc.Protocols.ScalarBytecode.OneRound.Source.post, Zkc.Protocols.ScalarBytecode.Frames.Safe Live i := by
  simp [Zkc.Protocols.ScalarBytecode.OneRound.Source.post,Zkc.Protocols.ScalarBytecode.OneRound.Source.code,Zkc.Protocols.ScalarBytecode.Frames.Safe,Zkc.Protocols.ScalarBytecode.Frames.Reads,Live]

def continuation (xs : List Zkc.Protocols.ScalarBytecode.Residue) : Program Zkc.Protocols.ScalarBytecode.Residue Action Unit :=
  .action (.publish Zkc.Protocols.ScalarBytecode.OneRound.Source.exportReg (xs.headD 0))
    (fun _ => guarded Zkc.Protocols.ScalarBytecode.OneRound.Source.post (.done ()))

theorem module_execution {S : Type} (hash : Hash) (supplier : Supplier S) (g : World S) :
    Zkc.Protocols.ScalarBytecode.BlockExecution.asTerminal (runProgram arithmetic (handler hash supplier)
      (moduleCall truth Zkc.Protocols.BackendProfiles.Horner.source [8] (inputs g.verifier) continuation) ⟨g,none⟩) =
    run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.post ⟨published g.verifier,g.external⟩ := by
  unfold moduleCall
  rw [compile_block_correct]
  change Zkc.Protocols.ScalarBytecode.BlockExecution.asTerminal (runProgram arithmetic (handler hash supplier)
    (.action (.publish Zkc.Protocols.ScalarBytecode.OneRound.Source.exportReg (Zkc.Protocols.ScalarBytecode.BlockExtraction.moduleResult g.verifier))
      (fun _ => guarded Zkc.Protocols.ScalarBytecode.OneRound.Source.post (.done ()))) ⟨g,none⟩) = _
  simp only [runProgram,handler]
  change Zkc.Protocols.ScalarBytecode.BlockExecution.asTerminal (runProgram arithmetic (handler hash supplier)
    (guarded Zkc.Protocols.ScalarBytecode.OneRound.Source.post (.done ())) ⟨⟨published g.verifier,g.external⟩,none⟩) = _
  rw [Zkc.Protocols.ScalarBytecode.BlockExecution.guarded_done]
  generalize run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.post
    (⟨published g.verifier,g.external⟩ : World S) = t
  rcases t with ⟨out,state,events⟩
  simp only [Zkc.Protocols.ScalarBytecode.BlockExecution.asTerminal]
  split <;> simp_all

def call {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache) (g : World S) :=
  Zkc.Protocols.ScalarBytecode.BlockExecution.asTerminal (Zkc.Transformations.Memoization.runMemo arithmetic store cache (lower (handler hash supplier)
    (Zkc.Protocols.BackendProfiles.nativeModule Zkc.Protocols.BackendProfiles.Certificates.aliasAdmitted.request literal truth
      (loadInputs r.inputs g.verifier) continuation) ⟨g,none⟩)).1

theorem call_meaning {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (ok : checkCaller r = true) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) (g : World S) :
    call hash supplier r literal store cache g =
      run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.post ⟨published g.verifier,g.external⟩ := by
  rw [selected_caller r ok]
  unfold call
  rw [selected_inputs,Zkc.Protocols.BackendProfiles.Consumers.alias_source_refinement literal truth
    (handler hash supplier) (inputs g.verifier) continuation ⟨g,none⟩ store cache valid]
  exact module_execution hash supplier g

/-- The source prefix fixes input availability and runs the guard before the
    selected call. The suffix retains raw source occurrences, including 20. -/
def integrated {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache) (g : World S) :=
  Zkc.Realization.InstructionSequence.resume (call hash supplier r literal store cache)
    (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.pre g)

theorem caller_refinement {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (ok : checkCaller r = true) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) (g : World S) :
    TerminalRel (OpenRel Live Eq)
      (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.code g)
      (integrated hash supplier r literal store cache g) := by
  have h := Zkc.Protocols.ScalarBytecode.Endpoint.encapsulate_context hash supplier Live Zkc.Protocols.ScalarBytecode.OneRound.Source.body Zkc.Protocols.ScalarBytecode.OneRound.Source.pre Zkc.Protocols.ScalarBytecode.OneRound.Source.post
    (fun s => ⟨published s.verifier,s.external⟩) (body_open hash supplier) post_safe g
  rw [← Zkc.Protocols.ScalarBytecode.OneRound.Source.split_code] at h
  have hc : call hash supplier r literal store cache =
      fun s => run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.post
        ⟨published s.verifier,s.external⟩ :=
    funext (call_meaning hash supplier r ok literal store cache valid)
  unfold integrated
  rw [hc]
  exact h

/-- The admitted proposal cannot change caller selection by changing its own
    metadata. These refusals are separate from the Zkc.Protocols.BackendProfiles internal module check. -/
theorem swapped_inputs_refused :
    checkCaller {selectedRef with inputs := [5,13,9,25]} = false := by decide
theorem short_adapter_sites_refused :
    checkCaller {selectedRef with externalSites := [2,4,6,12,15]} = false := by decide
theorem different_artifact_refused :
    checkCaller {selectedRef with artifact := "other"} = false := by decide

def observed {S : Type} (t : Terminal (World S) Event) :=
  (t.outcome,t.events,t.state.verifier.subject,t.state.verifier.offset,
   t.state.verifier.core.provider,t.state.verifier.core.binding,t.state.external)

theorem observation {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (ok : checkCaller r = true) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache)
    (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) (g : World S) :
    observed (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.code g) =
      observed (integrated hash supplier r literal store cache g) := by
  rcases caller_refinement hash supplier r ok literal store cache valid g with
    ⟨ho,⟨⟨hp,hf,hprov,hbind,_⟩,hex⟩,hev⟩
  simp only [observed,ho,hev,hp,hf,hprov,hbind,hex]

/-- A stopped prefix cannot enter the replacement module at all. This law
    does not require the module's cache or source-selection premises. -/
theorem prefix_rejection_skips_call {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Ref) (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue)
    (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool) (cache : Cache) (g : World S)
    (reason : String)
    (failed : (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.pre g).outcome = .reject reason) :
    integrated hash supplier r literal store cache g =
      run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.pre g := by
  unfold integrated Zkc.Realization.InstructionSequence.resume
  simp [failed]

end Zkc.Protocols.ScalarBytecode.OneRound.Compilation

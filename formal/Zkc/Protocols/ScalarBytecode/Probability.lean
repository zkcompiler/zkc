import Zkc.Protocols.ScalarBytecode.OneRound.Compilation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.ScalarBytecode.Probability
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

def challengeBound : Nat := Zkc.Protocols.ScalarBytecode.Parameters.challengeBound

/-- Sampling the same complete experiment preserves the bytecode observer.
    The joint law may correlate the initial world, supplier and hash.
    This constructs a PMF, without assuming an executor-function equality.
    It asserts no conditional freshness, native refinement or strategy coverage. -/
theorem sampled_caller {Ω S : Type} (μ : PMF Ω)
    (hash : Ω → Hash) (supplier : Ω → Supplier S) (world : Ω → World S)
    (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref) (ok : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.checkCaller r = true)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool)
    (cache : Cache) (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    μ.map (fun ω => Zkc.Protocols.ScalarBytecode.OneRound.Compilation.observed
      (run (openStep (hash ω) (supplier ω)) Zkc.Protocols.ScalarBytecode.OneRound.Source.code (world ω))) =
    μ.map (fun ω => Zkc.Protocols.ScalarBytecode.OneRound.Compilation.observed
      (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.integrated (hash ω) (supplier ω) r literal store cache (world ω))) := by
  congr 1
  funext ω
  exact Zkc.Protocols.ScalarBytecode.OneRound.Compilation.observation (hash ω) (supplier ω) r ok literal store cache valid (world ω)

/-- The advertised observation tuple omits registers, but the stronger relation
    does preserve the caller's actual exported result register 34. -/
theorem exported_result {S : Type} (hash : Hash) (supplier : Supplier S)
    (r : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.Ref) (ok : Zkc.Protocols.ScalarBytecode.OneRound.Compilation.checkCaller r = true)
    (literal : Zkc.Protocols.BackendProfiles.Literal → Zkc.Protocols.ScalarBytecode.Residue) (store : Cache → Zkc.Compiler.Blocks.Key Zkc.Protocols.ScalarBytecode.Residue → Bool)
    (cache : Cache) (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) (g : World S) :
    (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.code g).state.verifier.core.regs 34 =
    (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.integrated hash supplier r literal store cache g).state.verifier.core.regs 34 := by
  rcases Zkc.Protocols.ScalarBytecode.OneRound.Compilation.caller_refinement hash supplier r ok literal store cache valid g with
    ⟨_,⟨⟨_,_,_,_,hregs⟩,_⟩,_⟩
  exact hregs 34 (by decide)

/-- The actual draw primitive has a strict support cap for EVERY hash. -/
theorem effect_draw_bound (hash : Hash) (r : Request sig) (c : Core) (bs : Bytes)
    (e : Event) (he : e ∈ (effect hash r c bs).2.2.2) (hd : e.op = .draw) :
    e.value < challengeBound := by
  rcases r with ⟨site,op,arg⟩
  cases op <;> simp_all [effect]
  all_goals try { split_ifs at he <;> simp_all }
  exact Nat.mod_lt _ (by decide)

/-- Public event output of openStep is exactly that of its inherited effect. -/
theorem open_events {S : Type} (hash : Hash) (supplier : Supplier S)
    (i : Instr) (g : World S) :
    eventsOf (openStep hash supplier i g) =
      (effect hash (request i g.verifier.core) g.verifier.core
        (inputBytes i.op (serve supplier i g.verifier g.external).1)).2.2.2 := by
  have map_events {A B : Type} (f : A → B) (s : Step A Event) :
      eventsOf (mapStep f s) = eventsOf s := by cases s <;> rfl
  simp only [openStep, map_events]
  unfold update
  generalize effect hash (request i g.verifier.core) g.verifier.core
    (inputBytes i.op (serve supplier i g.verifier g.external).1) = out
  rcases out with ⟨reply,core,consumed,events⟩
  cases reply <;> by_cases hi : i.op = .accept <;> simp [hi,eventsOf]

theorem run_draw_bound {S : Type} (hash : Hash) (supplier : Supplier S)
    (code : List Instr) (g : World S) (e : Event)
    (he : e ∈ (run (openStep hash supplier) code g).events) (hd : e.op = .draw) :
    e.value < challengeBound := by
  induction code generalizing g with
  | nil => simp [run] at he
  | cons i code ih =>
    have hb : ∀ e ∈ eventsOf (openStep hash supplier i g), e.op = .draw →
        e.value < challengeBound := by
      intro e he hd
      rw [open_events] at he
      exact effect_draw_bound hash _ _ _ e he hd
    cases hs : openStep hash supplier i g with
    | halt out state events =>
      simp only [run,hs] at he
      exact hb e (by simpa [hs,eventsOf] using he) hd
    | next state events =>
      simp only [run,hs,List.mem_append] at he
      rcases he with he | he
      · exact hb e (by simpa [hs,eventsOf] using he) hd
      · exact ih state he

/-- First outside-support field element is perfectly canonical. -/
theorem cap_is_canonical : challengeBound < Zkc.Protocols.ScalarBytecode.Parameters.modulus := by decide

local instance : Nonempty (Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus) := ⟨⟨0,by decide⟩⟩

def actualDraw (hash : Hash) (provider domain : Bytes) : Nat :=
  Zkc.Realization.ByteEncoding.valueBE ((hash (provider ++ [⟨1,by decide⟩] ++ domain)).take 8) % challengeBound

/-- No distribution on pure hashes and pre-draw states can make this primitive
    exactly uniform on all q canonical field representatives. -/
theorem no_full_field_uniform {Ω : Type} (μ : PMF Ω)
    (hash : Ω → Hash) (provider domain : Ω → Bytes) :
    μ.map (fun ω => actualDraw (hash ω) (provider ω) (domain ω)) ≠
      (PMF.uniformOfFintype (Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus)).map Fin.val := by
  intro eq
  have hm : challengeBound ∈
      ((PMF.uniformOfFintype (Fin Zkc.Protocols.ScalarBytecode.Parameters.modulus)).map Fin.val).support := by
    apply (PMF.mem_support_map_iff _ _ _).2
    exact ⟨⟨challengeBound,cap_is_canonical⟩,PMF.mem_support_uniformOfFintype _,rfl⟩
  rw [← eq] at hm
  obtain ⟨ω,_,hω⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  have hlt : actualDraw (hash ω) (provider ω) (domain ω) < challengeBound :=
    Nat.mod_lt _ (by decide)
  omega

end Zkc.Protocols.ScalarBytecode.Probability

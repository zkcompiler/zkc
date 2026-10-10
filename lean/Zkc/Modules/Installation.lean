import Zkc.Modules.FactorBinding

set_option autoImplicit false

namespace Zkc.Modules.Installation
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding
variable {K : Type}

/-- Immutable source interpretation and actual captured values. Only one base
    key is installed. The source evaluator is the existing first-order fragment. -/
structure Request (K : Type) where
  namespaceId : Namespace
  source : Zkc.Source.FactorInputs.Source
  handle : Nat
  base : List K → K
  fallback : K
  captured : List K

def Request.ids (r : Request K) := (List.range r.captured.length).map (addr r.namespaceId)
def Request.localWorld (r : Request K) := snapshot (fun _ => r.base) r.fallback r.captured
def Request.exported (r : Request K) := fact r.namespaceId (Zkc.Source.FactorInputs.fact r.source r.handle)
def Request.writes (r : Request K) : Writes :=
  ⟨[key r.namespaceId r.source.key], [addr r.namespaceId r.handle], r.ids⟩
def Request.admitted (r : Request K) := Zkc.Source.FactorInputs.check (List.range r.captured.length) r.source

/-- Finite support, although the denotation uses total maps. The payload and
    source captures are snapshots; the outer state supplies all other entries. -/
def patch (r : Request K) (s : World K) : World K where
  values := {
    base := fun k => if k = key r.namespaceId r.source.key then r.base else s.values.base k
    view := fun h => if h = addr r.namespaceId r.handle then
      r.source.eval r.localWorld.values else s.values.view h
    challenge := fun i => if i ∈ r.ids then
      r.captured[(Nat.unpair i).2]?.getD r.fallback else s.values.challenge i }
  known := r.ids ++ s.known.filter (fun i => decide (i ∉ r.ids))

theorem patch_frames (r : Request K) (s : World K) : Frames r.writes s.values (patch r s).values := by
  constructor
  · intro k hk; have hn : k ≠ key r.namespaceId r.source.key := by simpa [Request.writes] using hk
    simp [patch,hn]
  · intro h hh; have hn : h ≠ addr r.namespaceId r.handle := by simpa [Request.writes] using hh
    simp [patch,hn]
  · intro i hi; simp only [Request.writes] at hi; simp [patch,hi]

theorem patch_capture (r : Request K) (s : World K) (i : Nat) (hi : i < r.captured.length) :
    (patch r s).values.challenge (addr r.namespaceId i) = r.localWorld.values.challenge i := by
  have mem : addr r.namespaceId i ∈ r.ids := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  simp only [patch,if_pos mem]
  simp [addr,Request.localWorld,snapshot]

theorem patch_means (r : Request K) (s : World K) (good : r.admitted = true) :
    Means (patch r s).values r.exported := by
  have checked : Zkc.Source.FactorInputs.Good (List.range r.captured.length) r.source := of_decide_eq_true good
  have mapped : (r.source.prefix.map (addr r.namespaceId)).map (patch r s).values.challenge =
      r.source.prefix.map r.localWorld.values.challenge := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact patch_capture r s i (List.mem_range.mp (checked.2 i hi))
  intro tail _
  simp only [Request.exported,fact,Zkc.Source.FactorInputs.fact,patch,ite_true]
  change r.source.eval r.localWorld.values tail =
    r.base ((r.source.prefix.map (addr r.namespaceId)).map (patch r s).values.challenge ++ tail)
  rw [mapped,Zkc.Source.FactorInputs.source_meaning]
  rfl

def successSummary (r : Request K) : Summary := ⟨some r.writes,[r.exported],[],r.ids⟩
def emptyWrites : Writes := ⟨[],[],[]⟩
def failureSummary : Summary := ⟨some emptyWrites,[],[],[]⟩

theorem patch_justifies (r : Request K) (s : World K) (good : r.admitted = true) :
    Justifies (successSummary r) s (patch r s) := by
  refine ⟨patch_frames r s,?_,?_,?_⟩
  · intro f hf
    have he : f = r.exported := by simpa [successSummary] using hf
    subst f; exact patch_means r s good
  · intro i hi
    have hi' : i ∈ s.known ∧ i ∉ r.ids := by
      simpa [keptKnown,successSummary,Request.writes] using hi
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hi'.1,by simpa using hi'.2⟩)
  · intro i hi; exact List.mem_append_left _ hi

theorem failure_justifies (s : World K) : Justifies failureSummary s s := by
  refine ⟨?_,?_,?_,?_⟩
  · constructor <;> intros <;> rfl
  · simp [failureSummary,Valid]
  · intro i hi; simpa [keptKnown,failureSummary,emptyWrites] using hi
  · simp [Known,failureSummary]

inductive Event where
  | initialized (namespaceId : Namespace)
  | rejected (namespaceId : Namespace)
  deriving DecidableEq, Repr

/-- Capacity is an explicit input to this reserved-name operation. No claim
    that a global allocator is framed by writes to base/view/challenge alone. -/
def execute (capacity : Nat) (r : Request K) : Implementation K Event := fun s =>
  if r.admitted && decide (r.captured.length ≤ capacity) then
    ⟨true,patch r s,[.initialized r.namespaceId]⟩
  else ⟨false,s,[.rejected r.namespaceId]⟩

def contract (r : Request K) : Spec K :=
  ⟨fun _ => True,fun ok => if ok then successSummary r else failureSummary⟩

theorem execute_satisfies (capacity : Nat) (r : Request K) :
    Satisfies (contract r) (execute capacity r) := by
  intro s _
  unfold execute
  split
  · rename_i h
    have hg : r.admitted = true ∧ r.captured.length ≤ capacity := by simpa using h
    exact patch_justifies r s hg.1
  · exact failure_justifies s

/-- Disjoint namespaces suffice for retaining an old renamed assertion. Aliased
    writes remain supported, but their dependent old assertions are killed. -/
theorem other_fact_unaffected (r : Request K) (n : Namespace) (f : Fact)
    (different : n ≠ r.namespaceId) : unaffected r.writes (fact n f) = true := by
  apply decide_eq_true
  refine ⟨?_,?_,?_⟩
  · simp only [Request.writes,fact,List.mem_singleton]
    intro h
    exact instances_disjoint n r.namespaceId different f.key.origin r.source.key.origin
      (congrArg Key.origin h)
  · simp only [Request.writes,fact,List.mem_singleton]
    exact instances_disjoint n r.namespaceId different f.handle r.handle
  · intro i hi hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    obtain ⟨k,_,he⟩ := List.mem_map.mp hm
    exact instances_disjoint n r.namespaceId different j k he.symm

theorem other_fact_preserved (r : Request K) (s : World K) (n : Namespace) (f : Fact)
    (different : n ≠ r.namespaceId) (valid : Means s.values (fact n f)) :
    Means (patch r s).values (fact n f) :=
  means_frame r.writes s.values (patch r s).values (fact n f)
    (patch_frames r s) valid (other_fact_unaffected r n f different)

end Zkc.Modules.Installation

import Zkc.Modules.Allocation
import Zkc.Polynomial.Bilinear.Factor

set_option autoImplicit false

namespace Zkc.Polynomial.Bilinear.Installation
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation

structure Input where
  (origin a b c d x y : Nat)
  deriving DecidableEq, Repr

def Input.prepKey (i : Input) := Zkc.Polynomial.Bilinear.key i.origin i.a i.b i.c i.d i.x
def Input.request (i : Input) (n : Namespace) : Request Nat :=
  ⟨n,Zkc.Polynomial.Bilinear.Factor.source i.origin,0,
   fun xs => i.a+i.b*(xs[0]?.getD 0)+(i.c+i.d*(xs[0]?.getD 0))*(xs[1]?.getD 0),
   0,[i.x,i.y]⟩

/-- The actual installed view consumes the materialized coefficient table.
    Namespace and the uncaptured y coordinate are not table-cache identities. -/
def tableWorld (i : Input) (n : Namespace) (t : List Nat) (s : World Nat) : World Nat :=
  let out := patch (i.request n) s
  {out with values := {out.values with view := (fun h => if h = addr n 0 then (fun tail => Zkc.Polynomial.Bilinear.consume t (tail[0]?.getD 0)) else s.values.view h)}}

theorem table_world_eq (i : Input) (n : Namespace) (s : World Nat) :
    tableWorld i n (Zkc.Source.TablePreparation.provider i.prepKey).1 s = patch (i.request n) s := by
  have hv : (tableWorld i n (Zkc.Source.TablePreparation.provider i.prepKey).1 s).values.view =
      (patch (i.request n) s).values.view := by
    funext h tail
    by_cases hh : h = addr n 0
    · subst h
      simp [tableWorld,patch,Input.request,Input.prepKey,Zkc.Polynomial.Bilinear.table_exact,
        Zkc.Polynomial.Bilinear.consume,Zkc.Polynomial.Bilinear.Factor.source,Zkc.Source.FactorInputs.Source.eval,
        Request.localWorld,snapshot]
    · simp [tableWorld,patch,Input.request,hh]
  simp only [tableWorld] at hv ⊢
  rw [hv]

structure Result where
  allocation : Zkc.Modules.Allocation.Result Nat
  cache : Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat)
  (work saved overhead : Nat)

/-- Both direct and memo variants materialize the same table after successful
    allocation. Failed admission/quota/capacity performs no preparation.
    The comparison baseline is this direct-materializing variant, separate from the
    cost-free mathematical function closure or a native polynomial library. -/
def allocatePrepared (mode : Zkc.Modules.Preparation.Mode) (cache : Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat))
    (quota cap : Nat) (p : Pool) (i : Input) (s : World Nat) : Result :=
  let out := allocate quota cap p (i.request ⟨0,0⟩) s
  match out.allocated with
  | none => ⟨out,cache,0,0,0⟩
  | some n =>
    let a := Zkc.Modules.Preparation.acquire Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode cache i.prepKey
    ⟨{out with returned := {out.returned with world := tableWorld i n a.value s}},
     a.cache,a.work,a.saved,a.overhead⟩

/-- Full allocator-result equality, including distinct returned names, finite
    writes and exact events. Cache/work are separate, observer-qualified fields. -/
theorem allocation_same (mode : Zkc.Modules.Preparation.Mode) (cache : Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat))
    (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider cache)
    (quota cap : Nat) (p : Pool) (i : Input) (s : World Nat) :
    (allocatePrepared mode cache quota cap p i s).allocation =
      allocate quota cap p (i.request ⟨0,0⟩) s := by
  cases hn : (allocate quota cap p (i.request ⟨0,0⟩) s).allocated with
  | none => simp [allocatePrepared,hn]
  | some n =>
    simp only [allocatePrepared,hn]
    have value := (Zkc.Modules.Preparation.acquire_law Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode cache i.prepKey valid).1
    rw [value,table_world_eq]
    obtain ⟨name,world,_⟩ := Zkc.Modules.Allocation.allocated_some quota cap p (i.request ⟨0,0⟩) s n hn
    have request : i.request n = renamed p (i.request ⟨0,0⟩) := by rw [name]; rfl
    rw [request,← world,← hn]

theorem cache_valid (mode : Zkc.Modules.Preparation.Mode) (cache : Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat))
    (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider cache)
    (quota cap : Nat) (p : Pool) (i : Input) (s : World Nat) :
    Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider (allocatePrepared mode cache quota cap p i s).cache := by
  cases hn : (allocate quota cap p (i.request ⟨0,0⟩) s).allocated with
  | none => simpa [allocatePrepared,hn] using valid
  | some n => simpa only [allocatePrepared,hn] using (Zkc.Modules.Preparation.acquire_law Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode cache i.prepKey valid).2.1

theorem failed_no_work (mode : Zkc.Modules.Preparation.Mode) (cache : Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat))
    (quota cap : Nat) (p : Pool) (i : Input) (s : World Nat)
    (h : (allocate quota cap p (i.request ⟨0,0⟩) s).allocated = none) :
    (allocatePrepared mode cache quota cap p i s).work = 0 ∧
    (allocatePrepared mode cache quota cap p i s).overhead = 0 := by
  simp [allocatePrepared,h]

theorem allocator_observer {O : Type} (obs : Zkc.Modules.Allocation.Result Nat → O)
    (quota cap : Nat) (p : Pool) (i : Input) (s : World Nat) :
    obs (allocatePrepared .direct Zkc.Modules.Preparation.empty quota cap p i s).allocation =
      obs (allocatePrepared .memo Zkc.Modules.Preparation.empty quota cap p i s).allocation := by
  rw [allocation_same _ _ (Zkc.Modules.ImmutableCache.empty_valid _) , allocation_same _ _ (Zkc.Modules.ImmutableCache.empty_valid _)]

end Zkc.Polynomial.Bilinear.Installation

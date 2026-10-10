import Zkc.Polynomial.Bilinear.Installation

set_option autoImplicit false

namespace Tests.BilinearInstallation
open Zkc.Polynomial.Bilinear.Installation Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation

def initial : World Nat := ⟨⟨fun _ _ => 91,fun _ _ => 92,fun _ => 93⟩,[]⟩
def input : Input := ⟨100,1,2,3,4,2,3⟩
def pair (mode : Zkc.Modules.Preparation.Mode) (second : Input) (quota cap : Nat) : Result × Result :=
  let first := allocatePrepared mode Zkc.Modules.Preparation.empty quota cap empty input initial
  (first,allocatePrepared mode first.cache quota cap first.allocation.pool second first.allocation.returned.world)
/-- Two actual calls, including state/cache transfer and any allocation failure. -/
theorem pair_same (mode : Zkc.Modules.Preparation.Mode) (second : Input) (quota cap : Nat) :
    let reference := allocate quota cap empty (input.request ⟨0,0⟩) initial
    (pair mode second quota cap).1.allocation = reference ∧
    (pair mode second quota cap).2.allocation =
      allocate quota cap reference.pool (second.request ⟨0,0⟩) reference.returned.world := by
  have first := allocation_same mode Zkc.Modules.Preparation.empty (Zkc.Modules.ImmutableCache.empty_valid _) quota cap empty input initial
  have valid := cache_valid mode Zkc.Modules.Preparation.empty (Zkc.Modules.ImmutableCache.empty_valid _) quota cap empty input initial
  constructor
  · exact first
  · change (allocatePrepared mode _ quota cap _ second _).allocation = _
    rw [allocation_same mode _ valid,first]


def row (mode : Zkc.Modules.Preparation.Mode) (second : Input) (quota cap : Nat) : List Nat :=
  let (a,b) := pair mode second quota cap
  let q := Zkc.Polynomial.Bilinear.Factor.originKey 100
  [a.allocation.allocated.map Namespace.instanceId |>.getD 999,
   b.allocation.allocated.map Namespace.instanceId |>.getD 999,b.allocation.pool.next,
   a.work+b.work,a.saved+b.saved,a.overhead+b.overhead,
   runQuery b.allocation.returned.world.values (query ⟨0,0⟩ ⟨q,[0,1]⟩),
   runQuery b.allocation.returned.world.values (query ⟨1,0⟩ ⟨q,[0,1]⟩)]

theorem shared_data_distinct_names :
    (pair .memo {input with y := 5} 2 2).1.allocation.allocated = some ⟨0,0⟩ ∧
    (pair .memo {input with y := 5} 2 2).2.allocation.allocated = some ⟨1,0⟩ ∧
    (pair .memo {input with y := 5} 2 2).2.work = 0 := by decide

end Tests.BilinearInstallation

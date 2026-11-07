module

public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! Relational composition for the existing closed local range. The callback
connects its actual body and yield, including the continuation flag. The common
rule supplies finite iteration, early exit, caller retention and final routing.
It proves neither a controller invariant nor adequacy of a transition bound. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionLocalRange
open Zkc.Source

variable {carriers : Structured.Carriers} {A : Type}

/-- A successful callback identifies the complete checked yield. In particular,
an output with the right value but the wrong continuation flag is not related. -/
def Yield (relation : A → Domain.Environment carriers → Prop)
    (conditional : Bool) (declared : List ValueSort) (yielded : List Nat)
    (result : Bool × A) (frame : Domain.Environment carriers) : Prop :=
  ∃ carried, (Domain.read frame yielded).bind (Domain.rangeResult conditional declared) =
    some (result.1, carried) ∧ relation result.2 carried

def Carry (relation : A → Domain.Environment carriers → Prop)
    (source : Bool × A) (target : Bool × Domain.Environment carriers) : Prop :=
  source.1 = target.1 ∧ relation source.2 target.2

/-- Decode the actual result references after the connected body. A malformed
yield cannot satisfy this rule, and a stopped body keeps its original stop. -/
noncomputable def yieldPropertySimulation
    {relation : A → Domain.Environment carriers → Prop}
    {property : Bool × A → Prop}
    {live : Domain.Environment carriers → Prop}
    {conditional : Bool} {declared : List ValueSort} {yielded : List Nat}
    {source : PIR.Process (Domain.effects carriers) (Bool × A)}
    {target : PIR.Process (Domain.effects carriers) (Domain.Environment carriers)}
    (body : Original.Simulation
      (fun result frame ↦ Yield relation conditional declared yielded result frame ∧ property result)
      (fun _ frame ↦ live frame) source target) :
    Original.Simulation (fun value carried ↦ Carry relation value carried ∧ property value)
      (fun _ frame ↦ live frame) source
      (target.bind fun final ↦
        match (Domain.read final yielded).bind (Domain.rangeResult conditional declared) with
        | some next => .done next
        | none => .halt .refused) := by
  have composed := body.bind
    (returnRelation := fun value carried ↦ Carry relation value carried ∧ property value)
    (sourceNext := PIR.Process.done)
    (targetNext := fun final ↦
      match (Domain.read final yielded).bind (Domain.rangeResult conditional declared) with
      | some next => .done next
      | none => .halt .refused)
    (nextLive := fun _ frame ↦ live frame) (fun _ _ held ↦ held)
    (fun result final related ↦ by
      split
      · rename_i next found
        apply Original.Simulation.done
        obtain ⟨⟨carried, read, related⟩, holds⟩ := related
        cases Option.some.inj (found.symm.trans read)
        exact ⟨⟨rfl, related⟩, holds⟩
      · rename_i absent
        exfalso
        obtain ⟨⟨carried, read, _⟩, _⟩ := related
        rw [absent] at read
        contradiction)
  simpa only [PIR.Process.bind_done] using composed

noncomputable def yieldSimulation
    {relation : A → Domain.Environment carriers → Prop}
    {live : Domain.Environment carriers → Prop}
    {conditional : Bool} {declared : List ValueSort} {yielded : List Nat}
    {source : PIR.Process (Domain.effects carriers) (Bool × A)}
    {target : PIR.Process (Domain.effects carriers) (Domain.Environment carriers)}
    (body : Original.Simulation (Yield relation conditional declared yielded)
      (fun _ frame ↦ live frame) source target) :
    Original.Simulation (Carry relation) (fun _ frame ↦ live frame) source
      (target.bind fun final ↦
        match (Domain.read final yielded).bind (Domain.rangeResult conditional declared) with
        | some next => .done next
        | none => .halt .refused) :=
  (yieldPropertySimulation (property := fun _ ↦ True)
    (body.mapRelations (fun _ _ held ↦ ⟨held, trivial⟩) (fun _ _ held ↦ held))).mapRelations
      (fun _ _ held ↦ held.1) (fun _ _ held ↦ held)

/-- This is the continuation gate already used by `Domain.executeRange`,
stated over the source callback so it can be reused by loop invariants. -/
def gated (step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A))
    (current : Bool × A) (index : Nat) : PIR.Process (Domain.effects carriers) (Bool × A) :=
  if current.1 then step current.2 index else .done current

/-- An early false yield preserves its value and executes no later callback,
even when that callback would interact or stop. -/
theorem fold_inactive (step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A))
    (items : List Nat) (value : A) :
    Finite.fold (gated step) items (false, value) = .done (false, value) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simpa only [Finite.fold, gated, Bool.false_eq_true,
      ↓reduceIte, PIR.Process.bind] using ih

/-- Compose a conditional or unconditional range at its actual caller frame.
The formation check still runs for an empty interval. All callbacks must be
connected at their related state; no totality or honest-reply premise is used. -/
noncomputable def activeSimulation (program : Structured.Program)
    (conditional : Bool) (declared : List ValueSort) (region : InstructionRegion)
    (body : Domain.Environment carriers →
      PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A))
    (relation : A → Domain.Environment carriers → Prop)
    (active : A → Prop)
    (live : Domain.Environment carriers → Prop)
    (caller captured : Domain.Environment carriers)
    (formed : (checkClosedRangeResults conditional declared (captured.map Domain.Value.sort)
      region (checkClosedFrom .local (Domain.closedOperationMatches program)
        region.inputs region.instructions)).isOk = true)
    (sorts : ∀ value carried, relation value carried → Domain.sortsMatch declared carried = true)
    (callback : ∀ value carried index, relation value carried → active value →
      Original.Simulation
        (fun result frame ↦ Yield relation conditional declared region.yielded result frame ∧
          (result.1 = true → active result.2))
        (fun _ frame ↦ live frame) (step value index)
        ((body (.data (.index index) :: (carried ++ captured))).interpret
          (Domain.withCallerFrame caller)))
    (lower upper : Nat) (references : List Nat) (lo hi : Nat)
    (readLower : caller[lower]? = some (.data (.index lo)))
    (readUpper : caller[upper]? = some (.data (.index hi)))
    (initial : A) (carried : Domain.Environment carriers)
    (read : Domain.read caller references = some (carried ++ captured))
    (width : carried.length = declared.length) (related : relation initial carried)
    (starts : active initial) :
    Original.Simulation
      (fun value final ↦ ∃ next, relation value next ∧ final = caller ++ next)
      (fun _ frame ↦ live frame)
      ((Finite.fold (gated step) (List.range' lo (hi - lo)) (true, initial)).bind
        fun result ↦ .done result.2)
      (Domain.executeRange program conditional lower upper references declared region
        body caller) := by
  have initialSorts := sorts initial carried related
  unfold Domain.executeRange
  rw [readLower, readUpper, read]
  simp only [← width, List.take_left, List.drop_left, initialSorts, formed,
    and_self, ↓reduceIte, Finite.execute, Finite.Domain.admit, Finite.admitThen]
  let physical := fun (current : Bool × Domain.Environment carriers) index ↦
    if current.1 then
      ((body (.data (.index index) :: (current.2 ++ captured))).interpret
        (Domain.withCallerFrame caller)).bind fun final ↦
          match (Domain.read final region.yielded).bind
              (Domain.rangeResult conditional declared) with
          | some next => .done next
          | none => .halt .refused
    else .done current
  let carry := fun value target ↦ Carry relation value target ∧
    (value.1 = true → active value.2)
  have iteration : ∀ value target index, carry value target →
      Original.Simulation carry (fun _ frame ↦ live frame)
        (gated step value index) (physical target index) := by
    intro value target index holds
    obtain ⟨⟨flag, related⟩, enabled⟩ := holds
    unfold gated physical
    rw [flag]
    cases selected : target.1
    · exact .done ⟨⟨flag, related⟩, enabled⟩
    · exact yieldPropertySimulation
        (callback value.2 target.2 index related (enabled (flag.trans selected)))
  have loop := Original.Simulation.finite (relation := carry) (gated step) physical iteration
    (fun _ _ _ held ↦ held) (List.range' lo (hi - lo)) (true, initial) (true, carried)
    ⟨⟨rfl, related⟩, fun _ ↦ starts⟩
  exact loop.bind (fun _ _ held ↦ held) (fun value result holds ↦ by
    rw [sorts value.2 result.2 holds.1.2]
    exact .done ⟨result.2, holds.1.2, rfl⟩)

/-- The unrestricted range rule is the same gated construction with a trivial
entry premise. There is one iteration proof for both interfaces. -/
noncomputable def simulation (program : Structured.Program)
    (conditional : Bool) (declared : List ValueSort) (region : InstructionRegion)
    (body : Domain.Environment carriers →
      PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A))
    (relation : A → Domain.Environment carriers → Prop)
    (live : Domain.Environment carriers → Prop)
    (caller captured : Domain.Environment carriers)
    (formed : (checkClosedRangeResults conditional declared (captured.map Domain.Value.sort)
      region (checkClosedFrom .local (Domain.closedOperationMatches program)
        region.inputs region.instructions)).isOk = true)
    (sorts : ∀ value carried, relation value carried → Domain.sortsMatch declared carried = true)
    (callback : ∀ value carried index, relation value carried →
      Original.Simulation (Yield relation conditional declared region.yielded)
        (fun _ frame ↦ live frame) (step value index)
        ((body (.data (.index index) :: (carried ++ captured))).interpret
          (Domain.withCallerFrame caller)))
    (lower upper : Nat) (references : List Nat) (lo hi : Nat)
    (readLower : caller[lower]? = some (.data (.index lo)))
    (readUpper : caller[upper]? = some (.data (.index hi)))
    (initial : A) (carried : Domain.Environment carriers)
    (read : Domain.read caller references = some (carried ++ captured))
    (width : carried.length = declared.length) (related : relation initial carried) :
    Original.Simulation
      (fun value final ↦ ∃ next, relation value next ∧ final = caller ++ next)
      (fun _ frame ↦ live frame)
      ((Finite.fold (gated step) (List.range' lo (hi - lo)) (true, initial)).bind
        fun result ↦ .done result.2)
      (Domain.executeRange program conditional lower upper references declared region
        body caller) :=
  activeSimulation program conditional declared region body step relation (fun _ ↦ True)
    live caller captured formed sorts
    (fun value carried index related _ ↦
      (callback value carried index related).mapRelations
        (fun _ _ held ↦ ⟨held, fun _ ↦ trivial⟩) (fun _ _ held ↦ held))
    lower upper references lo hi readLower readUpper initial carried read width related trivial

end Zkc.Construction.ConnectionLocalRange

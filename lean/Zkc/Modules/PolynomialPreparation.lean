import Zkc.Polynomial.Coordinates
import Zkc.Modules.FactorContract

/-! A fixed polynomial binding and actual residual-coefficient preparation.

The binding is chosen before adaptive coordinate assignment. Preparation writes
a polynomial-derived view, assignment updates only one coordinate, and a failed
overwrite still changes its destination. Each operation supplies its own frame,
availability and exported-fact laws for the compiler to consume.
-/

set_option autoImplicit false

namespace Zkc.Modules.PolynomialPreparation

open Polynomial Factor FactorState

variable {F : Type} [CommSemiring F] {n m : Nat}

structure Binding (F : Type) (arity : Nat) where
  key : Key
  size : key.axes.length = arity
  distinct : key.axes.Nodup
  polynomial : Quadratic F arity

def Bound {arity : Nat} (binding : Binding F arity) (world : World F) : Prop :=
  ∀ values, world.values.base binding.key values =
    binding.polynomial.eval (coordinates arity values)

structure Request (fixedCount : Nat) where
  handle : Nat
  fixed : List Nat
  size : fixed.length = fixedCount

def fact (binding : Binding F (n + m)) (request : Request m) : Fact :=
  ⟨binding.key, request.handle, request.fixed, n⟩

def install (binding : Binding F (n + m)) (request : Request m) (world : World F) : World F :=
  let residual := binding.polynomial.materialize m
    (coordinates m (request.fixed.map world.values.challenge))
  { world with values := (Zkc.Modules.Factor.overwrite world.values request.handle
      (fun tail => residual.eval (coordinates n tail))) }

theorem install_means (binding : Binding F (n + m)) (request : Request m)
    (world : World F) (bound : Bound binding world) :
    Means (install binding request world).values (fact binding request) := by
  intro tail size
  change _ = world.values.base binding.key (request.fixed.map world.values.challenge ++ tail)
  rw [bound]
  simpa [install, fact, Zkc.Modules.Factor.overwrite] using
    materialize_coordinates m binding.polynomial
      (request.fixed.map world.values.challenge) tail (by simp [request.size]) size

inductive Event (F : Type) where
  | prepared (handle : Nat)
  | unavailable (handle : Nat)
  | assigned (coordinate : Nat) (value : F)
  | overwritten (handle : Nat) (success : Bool)
  deriving DecidableEq, Repr

inductive Call (F : Type) (fixedCount : Nat) where
  | prepare : Request fixedCount → Call F fixedCount
  | assign : Nat → F → Call F fixedCount
  | overwrite : Nat → (List F → F) → Bool → Call F fixedCount

def assign (world : World F) (coordinate : Nat) (value : F) : World F :=
  { values := { world.values with challenge :=
      fun other => if other = coordinate then value else world.values.challenge other }
    known := coordinate :: world.known }

def execute (binding : Binding F (n + m)) : Call F m → Implementation F (Event F)
  | .prepare request, world =>
      if Known world request.fixed then
        ⟨true, install binding request world, [.prepared request.handle]⟩
      else ⟨false, world, [.unavailable request.handle]⟩
  | .assign coordinate value, world =>
      ⟨true, assign world coordinate value, [.assigned coordinate value]⟩
  | .overwrite handle value success, world =>
      ⟨success, { world with values := Zkc.Modules.Factor.overwrite world.values handle value },
        [.overwritten handle success]⟩

def summary (binding : Binding F (n + m)) : Call F m → Bool → Summary
  | .prepare request, true =>
      ⟨some ⟨[], [request.handle], []⟩, [fact binding request], [], request.fixed⟩
  | .prepare _, false => ⟨some ⟨[], [], []⟩, [], [], []⟩
  | .assign coordinate _, _ => ⟨some ⟨[], [], [coordinate]⟩, [], [], [coordinate]⟩
  | .overwrite handle _ _, _ => ⟨some ⟨[], [handle], []⟩, [], [], []⟩

theorem preserves_binding (binding : Binding F (n + m)) (call : Call F m)
    (world : World F) (bound : Bound binding world) :
    Bound binding (execute binding call world).world := by
  cases call with
  | prepare request =>
      by_cases ready : Known world request.fixed <;>
        simpa [execute, ready, Bound, install, Zkc.Modules.Factor.overwrite] using bound
  | assign coordinate value => exact bound
  | overwrite handle value success => exact bound

theorem justifies (binding : Binding F (n + m)) (call : Call F m)
    (world : World F) (bound : Bound binding world) :
    Justifies (summary binding call (execute binding call world).success)
      world (execute binding call world).world := by
  cases call with
  | prepare request =>
      by_cases ready : Known world request.fixed
      · simp only [execute, if_pos ready, summary]
        constructor
        · constructor
          · intro key _; rfl
          · intro handle different
            have ne : handle ≠ request.handle := by simpa using different
            simp [install, Zkc.Modules.Factor.overwrite, ne]
          · intro coordinate _; rfl
        · intro exported member
          have same : exported = fact binding request := by simpa using member
          subst exported
          exact install_means binding request world bound
        · intro coordinate member
          simpa [keptKnown, install] using member
        · exact ready
      · simp only [execute, if_neg ready, summary]
        constructor
        · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
        · simp [Valid]
        · intro coordinate member
          simpa [keptKnown] using member
        · simp [Known]
  | assign coordinate value =>
      constructor
      · constructor
        · intro key _; rfl
        · intro handle _; rfl
        · intro other different
          have ne : other ≠ coordinate := by simpa [summary] using different
          simp [execute, assign, ne]
      · simp [execute, summary, Valid]
      · intro other member
        have before : other ∈ world.known := (List.mem_filter.mp member).1
        exact List.mem_cons_of_mem coordinate before
      · intro other member
        have same : other = coordinate := by simpa [summary] using member
        subst other
        exact List.mem_cons_self
  | overwrite handle value success =>
      constructor
      · constructor
        · intro key _; rfl
        · intro other different
          have ne : other ≠ handle := by simpa [summary] using different
          simp [execute, Zkc.Modules.Factor.overwrite, ne]
        · intro coordinate _; rfl
      · simp [execute, summary, Valid]
      · intro coordinate member
        simpa [execute, summary, keptKnown] using member
      · simp [execute, summary, Known]

/-- Actual initial binding; unrelated objects/views and runtime coordinates may
be supplied independently. It is not inferred from the selected source's name. -/
def bind {arity : Nat} (binding : Binding F arity) (world : World F) : World F :=
  { world with values := { world.values with base := (fun key values =>
      if key = binding.key then binding.polynomial.eval (coordinates arity values)
      else world.values.base key values) } }

theorem bind_bound {arity : Nat} (binding : Binding F arity) (world : World F) :
    Bound binding (bind binding world) := by
  intro values
  simp [bind]

end Zkc.Modules.PolynomialPreparation

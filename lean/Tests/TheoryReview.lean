import Zkc.Polynomial.Bilinear.Compilation
import Zkc.Semantics.Interaction

set_option autoImplicit false
namespace PIR.TheoryReview
open PIR Zkc.Modules.Factor Zkc.Modules.FactorBinding

def initial : Zkc.Modules.FactorState.World Nat := ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩, []⟩
def request (value : Nat) : Zkc.Modules.Installation.Request Nat :=
  ⟨⟨0,0⟩, .base ⟨0,[]⟩, 0, fun _ => value, 0, []⟩
def first := Zkc.Modules.Installation.execute 0 (request 1) initial
def second := Zkc.Modules.Installation.execute 0 (request 2) first.world

theorem reserved_name_can_be_overwritten :
    first.success = true ∧ second.success = true ∧
    first.world.values.base (key ⟨0,0⟩ ⟨0,[]⟩) [] = 1 ∧
    second.world.values.base (key ⟨0,0⟩ ⟨0,[]⟩) [] = 2 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem fresh_pool_can_overwrite_existing_world :
    Zkc.Modules.Allocation.empty.Good ∧
    (Zkc.Modules.Allocation.allocate 1 0 Zkc.Modules.Allocation.empty (request 2) first.world).returned.success = true ∧
    (Zkc.Modules.Allocation.allocate 1 0 Zkc.Modules.Allocation.empty (request 2) first.world).returned.world.values.base
      (key ⟨0,0⟩ ⟨0,[]⟩) [] = 2 :=
  ⟨Zkc.Modules.Allocation.empty_good,rfl,rfl⟩

def missingQuery : Query := ⟨⟨0,[0]⟩,[0]⟩
def missingSource : Zkc.Compiler.FactorProgram.Source := .demand missingQuery .stop

theorem refused_source_not_legal (spec : Nat → Zkc.Modules.FactorState.Spec Nat)
    (impl : Nat → Zkc.Modules.FactorState.Implementation Nat Unit) :
    ¬ Zkc.Compiler.FactorProgram.Legal spec impl [] missingSource initial := by
  intro h
  have bad := h.1.2 0 (by simp [missingQuery])
  simp at bad

theorem actual_refusal (impl : Nat → Zkc.Modules.FactorState.Implementation Nat Unit) :
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct missingSource)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler impl)) initial =
      ⟨.stopped .refused,initial,[]⟩ := rfl

theorem direct_check_accepts_missing_input :
    check [] [] missingQuery .direct = true ∧ ¬ Zkc.Modules.FactorState.Ready [] missingQuery := by
  refine ⟨rfl,?_⟩
  intro h
  have bad := h.2 0 (by simp [missingQuery])
  simp at bad

theorem owner_irrelevant {I : Signature} {A : Type} (p : Interaction I)
    (owner : I.Op → p.Role) (body : Proc I A) (phase : p.Phase) :
    Conforms {p with owner := owner} body phase ↔ Conforms p body phase := by
  induction body generalizing phase with
  | done a => rfl
  | halt why => rfl
  | call op next ih =>
    exact and_congr Iff.rfl (forall_congr' (fun reply => ih reply _))

/-- A failed call writes state and emits an event before the first refused demand.
    The next call has an impossible precondition and is never executed. -/
def mutating : Nat → Zkc.Modules.FactorState.Implementation Nat Nat := fun id s =>
  ⟨false, {s with values := {s.values with challenge := fun _ => 7}, known := []}, [id]⟩
def mutationSpec : Nat → Zkc.Modules.FactorState.Spec Nat := fun id =>
  ⟨fun _ => id = 0, fun _ => ⟨none, [], [], []⟩⟩

theorem mutation_laws (id : Nat) : Zkc.Modules.FactorState.Satisfies (mutationSpec id) (mutating id) := by
  intro s _
  refine ⟨trivial, ?_, ?_, ?_⟩ <;>
    simp [mutationSpec, Zkc.Modules.Factor.Valid, Zkc.Modules.FactorState.Known, Zkc.Modules.FactorState.keptKnown]

def afterRefusal : Zkc.Compiler.FactorProgram.Source := .call 1 .stop .stop
def failingSource : Zkc.Compiler.FactorProgram.Source := .call 0 .stop (.demand missingQuery afterRefusal)

theorem calls_stop_at_refusal : Zkc.Compiler.FactorGuards.CallsBeforeRefusal mutationSpec mutating failingSource initial := by
  refine ⟨rfl, ?_⟩
  change Zkc.Modules.FactorState.Ready [] missingQuery → _
  exact fun h => False.elim (direct_check_accepts_missing_input.2 h)

theorem failure_is_outside_old_legality :
    ¬ Zkc.Compiler.FactorProgram.Legal mutationSpec mutating [] failingSource initial := by
  intro h
  exact direct_check_accepts_missing_input.2 h.2.1

theorem prefix_effects_are_retained :
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct failingSource)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler mutating)) initial =
    ⟨.stopped .refused, (mutating 0 initial).world, [0]⟩ := rfl

theorem inference_preserves_actual_refusal :
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (mutationSpec id).post) [] [] failingSource)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler mutating)) initial =
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct failingSource)).run
      (Zkc.Modules.FactorExecution.guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler mutating)) initial :=
  Zkc.Compiler.FactorGuards.guarded_analysis_until_refusal mutationSpec mutating mutation_laws
    failingSource initial [] [] (by simp [Zkc.Modules.Factor.Valid]) (by simp [Zkc.Modules.FactorState.Known])
    calls_stop_at_refusal

theorem preparation_join_covers_actual_refusal :
    Related Zkc.Polynomial.Bilinear.Execution.SameWorld Preparation.view Preparation.view
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (mutationSpec id).post) [] [] failingSource)).run
        (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .memo mutating Zkc.Polynomial.Bilinear.Execution.Call.external) (initial, fun _ => none))
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct failingSource)).run
        (Zkc.Polynomial.Bilinear.Compilation.mixedHandler .direct mutating Zkc.Polynomial.Bilinear.Execution.Call.external) (initial, fun _ => none)) := by
  apply Zkc.Polynomial.Bilinear.Compilation.compile_until_refusal mutationSpec mutating mutation_laws
    Zkc.Polynomial.Bilinear.Execution.Call.external failingSource initial (fun _ => none) [] []
  · exact Zkc.Modules.ImmutableCache.empty_valid _
  · simp [Zkc.Modules.Factor.Valid]
  · simp [Zkc.Modules.FactorState.Known]
  · refine ⟨rfl, ?_⟩
    change Zkc.Modules.FactorState.Ready [] missingQuery → _
    exact fun h => False.elim (direct_check_accepts_missing_input.2 h)

/-- Exact counts under two equiprobable coins: each marginal is uniform, but the
    joint supports are disjoint across secrets. This is finite counting evidence. -/
def released (secret coin : Bool) : Bool × Bool := (coin, xor secret coin)
def countRelease {A : Type} [DecidableEq A] (f : Bool → A) (value : A) : Nat :=
  ([false, true].filter fun coin => f coin == value).length

theorem uniform_marginals : ∀ secret value : Bool,
    countRelease (fun coin => (released secret coin).1) value = 1 ∧
    countRelease (fun coin => (released secret coin).2) value = 1 := by decide

theorem joint_reveals_secret :
    countRelease (released false) (false, false) = 1 ∧
    countRelease (released true) (false, false) = 0 ∧
    (∀ secret coin : Bool, xor (released secret coin).1 (released secret coin).2 = secret) := by decide

end PIR.TheoryReview

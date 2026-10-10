import Zkc.Compiler.Blocks.Execution

/-! Backward demand and projected block execution. This auxiliary block representation retains assignment order and selected exports. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section
variable {V A O S E : Type}
abbrev Block (V : Type) := List (Nat × Expr V)

def assign (f : Key V → V) (truth : V → Bool) (env : Nat → V) (dst : Nat) (e : Expr V) : Nat → V :=
  Function.update env dst (eval f truth env e)

def runBlock (f : Key V → V) (truth : V → Bool) : Block V → (Nat → V) → (Nat → V)
  | [], env => env
  | (dst,e) :: rest, env => runBlock f truth rest (assign f truth env dst e)

def beforeAssignment (dst : Nat) (e : Expr V) (demand : Finset Nat) : Finset Nat :=
  demand.erase dst ∪ if dst ∈ demand then dependencies e else ∅

-- Backward demand analysis for a selected residual context, not just unioning
-- every source input. Unknown/failing/effectful operations are not in Block.
def requiredInputs : Block V → Finset Nat → Finset Nat
  | [], demand => demand
  | (dst,e) :: rest, demand => beforeAssignment dst e (requiredInputs rest demand)

theorem assignment_agreement (f : Key V → V) (truth : V → Bool)
    (dst : Nat) (e : Expr V) (demand : Finset Nat) (a b : Nat → V)
    (h : AgreeOn (beforeAssignment dst e demand) a b) :
    AgreeOn demand (assign f truth a dst e) (assign f truth b dst e) := by
  intro i hi
  by_cases he : i = dst
  · subst i
    have hd : AgreeOn (dependencies e) a b := by
      intro j hj
      apply h j
      simp only [beforeAssignment, hi, if_true]
      exact Finset.mem_union_right _ hj
    simpa [assign] using dependency_sound f truth e a b hd
  · have hv : a i = b i := h i (by
      apply Finset.mem_union_left
      exact Finset.mem_erase.mpr ⟨he,hi⟩)
    simpa [assign, Function.update_of_ne he] using hv

theorem backward_dependencies_sound (f : Key V → V) (truth : V → Bool)
    (block : Block V) (demand : Finset Nat) (a b : Nat → V)
    (h : AgreeOn (requiredInputs block demand) a b) :
    AgreeOn demand (runBlock f truth block a) (runBlock f truth block b) := by
  induction block generalizing a b with
  | nil => exact h
  | cons step rest ih =>
    exact ih _ _ (assignment_agreement f truth step.1 step.2 _ a b h)

def blockDependencyCheck (block : Block V) (demand declared : Finset Nat) : Bool :=
  decide (requiredInputs block demand ⊆ declared)

theorem checked_block_dependencies_sound (f : Key V → V) (truth : V → Bool)
    (block : Block V) (demand declared : Finset Nat) (a b : Nat → V)
    (hc : blockDependencyCheck block demand declared = true) (ha : AgreeOn declared a b) :
    AgreeOn demand (runBlock f truth block a) (runBlock f truth block b) := by
  have hs : requiredInputs block demand ⊆ declared := of_decide_eq_true hc
  apply backward_dependencies_sound f truth block demand a b
  intro i hi; exact ha i (hs hi)

def compileBlock (truth : V → Bool) :
    Block V → (Nat → V) → ((Nat → V) → Program V A O) → Program V A O
  | [], env, next => next env
  | (dst,e) :: rest, env, next =>
    compile env truth e (fun v => compileBlock truth rest (Function.update env dst v) next)

theorem compile_block_correct (f : Key V → V) (truth : V → Bool)
    (handler : A → S → V × S × List E) (block : Block V) (env : Nat → V)
    (next : (Nat → V) → Program V A O) (s : S) :
    runProgram f handler (compileBlock truth block env next) s =
      runProgram f handler (next (runBlock f truth block env)) s := by
  induction block generalizing env with
  | nil => rfl
  | cons step rest ih =>
    simp only [compileBlock,runBlock]
    rw [compile_correct]
    exact ih _

theorem memoized_block_correct [DecidableEq V]
    (f : Key V → V) (truth : V → Bool) (handler : A → S → V × S × List E)
    (block : Block V) (env : Nat → V) (next : (Nat → V) → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (Zkc.Transformations.Memoization.runMemo f store cache (lower handler (compileBlock truth block env next) s)).1 =
      runProgram f handler (next (runBlock f truth block env)) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache (lower handler (compileBlock truth block env next) s)).2 := by
  obtain ⟨ho,hv⟩ := Zkc.Transformations.Memoization.client_preservation f store
    (lower handler (compileBlock truth block env next) s) cache valid
  exact ⟨ho.trans ((lower_correct f handler _ s).trans
    (compile_block_correct f truth handler block env next s)),hv⟩

def demandProjection (demand : Finset Nat) (env : Nat → V) :
    {i : Nat // i ∈ demand} → V := fun i => env i.1

def restoreContext (needed : Finset Nat) (fallback : V)
    (key : {i : Nat // i ∈ needed} → V) (i : Nat) : V :=
  if h : i ∈ needed then key ⟨i,h⟩ else fallback

def blockFunction (f : Key V → V) (truth : V → Bool) (block : Block V)
    (demand : Finset Nat) (fallback : V)
    (key : {i : Nat // i ∈ requiredInputs block demand} → V) :
    {i : Nat // i ∈ demand} → V :=
  demandProjection demand (runBlock f truth block
    (restoreContext (requiredInputs block demand) fallback key))

-- A whole-block function really factors through the inferred input projection.
-- This supplies a second cache granularity; it is not primitive-call caching.
theorem block_function_correct (f : Key V → V) (truth : V → Bool)
    (block : Block V) (demand : Finset Nat) (fallback : V) (env : Nat → V) :
    blockFunction f truth block demand fallback
      (demandProjection (requiredInputs block demand) env) =
    demandProjection demand (runBlock f truth block env) := by
  funext i
  apply backward_dependencies_sound f truth block demand _ env _ i.1 i.2
  intro j hj
  simp [restoreContext,hj,demandProjection]

theorem opaque_block_memo_correct (f : Key V → V) (truth : V → Bool)
    (block : Block V) (demand : Finset Nat)
    [DecidableEq ({i : Nat // i ∈ requiredInputs block demand} → V)]
    (fallback : V) (env : Nat → V)
    (next : ({i : Nat // i ∈ demand} → V) →
      Zkc.Transformations.Memoization.Client ({i : Nat // i ∈ requiredInputs block demand} → V)
        ({i : Nat // i ∈ demand} → V) E O)
    (store : Zkc.Modules.ImmutableCache.Cache ({i : Nat // i ∈ requiredInputs block demand} → V)
        ({i : Nat // i ∈ demand} → V) →
      ({i : Nat // i ∈ requiredInputs block demand} → V) → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache ({i : Nat // i ∈ requiredInputs block demand} → V)
        ({i : Nat // i ∈ demand} → V))
    (valid : Zkc.Modules.ImmutableCache.Valid (blockFunction f truth block demand fallback) cache) :
    (Zkc.Transformations.Memoization.runMemo (blockFunction f truth block demand fallback) store cache
      (.call (demandProjection (requiredInputs block demand) env) next)).1 =
      Zkc.Transformations.Memoization.run (blockFunction f truth block demand fallback)
        (next (demandProjection demand (runBlock f truth block env))) ∧
    Zkc.Modules.ImmutableCache.Valid (blockFunction f truth block demand fallback)
      (Zkc.Transformations.Memoization.runMemo (blockFunction f truth block demand fallback) store cache
        (.call (demandProjection (requiredInputs block demand) env) next)).2 := by
  obtain ⟨ho,hv⟩ := Zkc.Transformations.Memoization.client_preservation
    (blockFunction f truth block demand fallback) store
    (.call (demandProjection (requiredInputs block demand) env) next) cache valid
  simp only [Zkc.Transformations.Memoization.run] at ho
  rw [block_function_correct] at ho
  exact ⟨ho,hv⟩

-- This joins dependency coverage and local compilation under the context that
-- actually observes only the selected final variables. The next program can
-- perform stateful actions; equality includes its final state and full trace.
theorem memoized_projected_block_correct [DecidableEq V]
    (f : Key V → V) (truth : V → Bool) (handler : A → S → V × S × List E)
    (block : Block V) (demand declared : Finset Nat) (a b : Nat → V)
    (hc : blockDependencyCheck block demand declared = true) (ha : AgreeOn declared a b)
    (next : ({i : Nat // i ∈ demand} → V) → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (compileBlock truth block a (fun env => next (demandProjection demand env))) s)).1 =
      runProgram f handler (next (demandProjection demand (runBlock f truth block b))) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (compileBlock truth block a (fun env => next (demandProjection demand env))) s)).2 := by
  have he : demandProjection demand (runBlock f truth block a) =
      demandProjection demand (runBlock f truth block b) := by
    funext i
    exact checked_block_dependencies_sound f truth block demand declared a b hc ha i.1 i.2
  obtain ⟨ho,hv⟩ := memoized_block_correct f truth handler block a
    (fun env => next (demandProjection demand env)) s store cache valid
  exact ⟨ho.trans (congrArg (fun v => runProgram f handler (next v) s) he),hv⟩


end

end Zkc.Compiler.Blocks

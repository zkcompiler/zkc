import Zkc.Compiler.FreshAllocation
import Zkc.Compiler.FactorBinding

/-! Concrete clients of conservative and registered scoped factor compilation.

Nested bindings query the outer lexical slot after installing a distinct inner
instance. Expected results specify all world functions, allocation state, values
and notices independently of the compiler. Quota/capacity refusal, clobbering and
an unreconciled imported name exercise the boundaries of fact retention.
-/

set_option autoImplicit false

namespace Tests.ScopedAllocation

open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding
open Zkc.Modules.Installation Zkc.Modules.Allocation Zkc.Modules.FactorScopes
open Zkc.Modules.FreshAllocation

def localKey : Key := ⟨2, [0, 1]⟩
def demand : Query := ⟨localKey, [0, 1]⟩
def linear (scale : Nat) (point : List Nat) : Nat :=
  scale * point[0]?.getD 0 + point[1]?.getD 0

def outer : Request Nat :=
  ⟨⟨9, 7⟩, .fix (.base localKey) 0, 0, linear 10, 0, [2, 3]⟩
def inner : Request Nat :=
  ⟨⟨9, 7⟩, .fix (.base localKey) 0, 1, linear 100, 0, [4, 5, 6]⟩

def outerFact : Fact := ⟨localKey, 0, [0], 1⟩
def innerFact : Fact := ⟨localKey, 1, [0], 1⟩
def outerName : Namespace := ⟨0, 0⟩
def innerName : Namespace := ⟨1, 0⟩
def initial : World Nat := ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩, []⟩

/-- Explicit total maps: the outer instance occupies base origin 4 and slots 0, 1. -/
def outerWorld : World Nat where
  values := {
    base := fun k => if k = ⟨4, [0, 1]⟩ then linear 10 else fun _ => 0
    view := fun h => if h = 0 then fun tail => 20 + tail[0]?.getD 0 else fun _ => 0
    challenge := fun i => if i = 0 then 2 else if i = 1 then 3 else 0 }
  known := [0, 1]

/-- The inner instance has base origin 8, view 7 and captured slots 6, 7, 8. -/
def nestedWorld : World Nat where
  values := {
    base := fun k => if k = ⟨8, [0, 1]⟩ then linear 100 else outerWorld.values.base k
    view := fun h => if h = 7 then fun tail => 400 + tail[0]?.getD 0 else outerWorld.values.view h
    challenge := fun i => if i = 6 then 4 else if i = 7 then 5 else if i = 8 then 6
      else outerWorld.values.challenge i }
  known := [6, 7, 8, 0, 1]

theorem outer_world : patch {outer with namespaceId := outerName} initial = outerWorld := by
  change World.mk _ _ = World.mk _ _
  rw [World.mk.injEq, State.mk.injEq]
  refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
  funext i
  change (if i ∈ [0, 1] then [2, 3][(Nat.unpair i).2]?.getD 0 else 0) =
    (if i = 0 then 2 else if i = 1 then 3 else 0)
  by_cases zero : i = 0
  · subst i; rfl
  by_cases one : i = 1
  · subst i; rfl
  simp [zero, one]

theorem nested_world : patch {inner with namespaceId := innerName}
    (patch {outer with namespaceId := outerName} initial) = nestedWorld := by
  rw [outer_world]
  change World.mk _ _ = World.mk _ _
  rw [World.mk.injEq, State.mk.injEq]
  refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
  funext i
  change (if i ∈ [6, 7, 8] then [4, 5, 6][(Nat.unpair i).2]?.getD 0
      else outerWorld.values.challenge i) =
    (if i = 6 then 4 else if i = 7 then 5 else if i = 8 then 6
      else outerWorld.values.challenge i)
  by_cases six : i = 6
  · subst i; rw [show Nat.unpair 6 = (2, 0) from Nat.unpair_pair 2 0]; rfl
  by_cases seven : i = 7
  · subst i; rw [show Nat.unpair 7 = (2, 1) from Nat.unpair_pair 2 1]; rfl
  by_cases eight : i = 8
  · subst i; rw [show Nat.unpair 8 = (2, 2) from Nat.unpair_pair 2 2]; rfl
  simp [six, seven, eight]

def useBoth : Source Nat := .demand 1 demand (.demand 0 demand .stop)
def fallback : Source Nat := .demand 0 demand .stop
def nested : Source Nat := .bind outer (.bind inner useBoth fallback) fallback

def nestedExpected : Zkc.Modules.FactorScopes.Result Nat :=
  ⟨⟨2, [1, 0]⟩, nestedWorld, [23, 405],
    [.allocation (.initialized outerName), .allocation (.initialized innerName)]⟩

theorem nested_reference : run 2 3 (direct nested) emptyNames empty initial = nestedExpected := by
  let finalWorld := patch {inner with namespaceId := innerName}
    (patch {outer with namespaceId := outerName} initial)
  change (⟨⟨2, [1, 0]⟩, finalWorld,
    [runQuery finalWorld.values (query outerName demand),
      runQuery finalWorld.values (query innerName demand)],
    [.allocation (.initialized outerName), .allocation (.initialized innerName)]⟩ :
      Zkc.Modules.FactorScopes.Result Nat) = nestedExpected
  have final : finalWorld = nestedWorld := nested_world
  rw [final]
  rfl

def compiled (registered : Bool) (src : Source Nat) : Code Nat :=
  if registered then Zkc.Compiler.FreshAllocation.compile emptyFacts src
  else Zkc.Compiler.FactorScopes.compile emptyFacts src

theorem closed_execution (registered : Bool) (src : Source Nat) (quota capacity : Nat) :
    run quota capacity (compiled registered src) emptyNames empty initial =
      run quota capacity (direct src) emptyNames empty initial := by
  cases registered with
  | false => exact Zkc.Compiler.FactorScopes.closed_correct quota capacity src empty initial
  | true => exact Zkc.Compiler.FreshAllocation.closed_correct quota capacity src initial

theorem nested_execution (registered : Bool) :
    run 2 3 (compiled registered nested) emptyNames empty initial = nestedExpected := by
  rw [closed_execution, nested_reference]

/-- The expected plans retain the inner fact in both passes and the outer only
    in the pass whose proof tracks the allocation registry. -/
def nestedPlans (outerPlan : Plan) : Code Nat :=
  .bind outer
    (.bind inner
      (.demand 1 demand outerPlan (.demand 0 demand (.reuse innerFact [1]) .stop))
      (.demand 0 demand (.reuse outerFact [1]) .stop))
    (.demand 0 demand .direct .stop)

theorem conservative_outer_is_direct : compiled false nested = nestedPlans .direct := rfl
theorem registered_outer_is_reused :
    compiled true nested = nestedPlans (.reuse outerFact [1]) := rfl

def refusedInnerExpected : Zkc.Modules.FactorScopes.Result Nat :=
  ⟨⟨1, [0]⟩, outerWorld, [23],
    [.allocation (.initialized outerName), .allocation (.rejected innerName)]⟩

/-- Quota refusal enters the failure continuation without pushing a lexical slot. -/
theorem quota_refusal (registered : Bool) :
    run 1 3 (compiled registered nested) emptyNames empty initial = refusedInnerExpected := by
  rw [closed_execution]
  change (⟨⟨1, [0]⟩, patch {outer with namespaceId := outerName} initial, [23],
    [.allocation (.initialized outerName), .allocation (.rejected innerName)]⟩ :
      Zkc.Modules.FactorScopes.Result Nat) = refusedInnerExpected
  rw [outer_world]
  rfl

/-- The three-coordinate inner request is refused independently of the quota. -/
theorem capacity_refusal (registered : Bool) :
    run 2 2 (compiled registered nested) emptyNames empty initial = refusedInnerExpected := by
  rw [closed_execution]
  change (⟨⟨1, [0]⟩, patch {outer with namespaceId := outerName} initial, [23],
    [.allocation (.initialized outerName), .allocation (.rejected innerName)]⟩ :
      Zkc.Modules.FactorScopes.Result Nat) = refusedInnerExpected
  rw [outer_world]
  rfl

theorem outer_refusal_keeps_empty_scope (registered : Bool) :
    run 0 3 (compiled registered nested) emptyNames empty initial =
      ⟨empty, initial, [], [.allocation (.rejected outerName), .missing 0]⟩ := by
  rw [closed_execution]
  rfl

def clobbered : Source Nat :=
  .bind outer
    (.bind inner (.demand 1 demand (.clobber 1 0 (fun _ => 999) useBoth)) fallback)
    fallback

def clobberedWorld : World Nat :=
  {nestedWorld with values := {nestedWorld.values with
    view := fun h => if h = 0 then fun _ => 999 else nestedWorld.values.view h}}

def clobberedExpected : Zkc.Modules.FactorScopes.Result Nat :=
  ⟨⟨2, [1, 0]⟩, clobberedWorld, [23, 23, 405],
    [.allocation (.initialized outerName), .allocation (.initialized innerName),
      .changed outerName 0]⟩

theorem clobber_execution (registered : Bool) :
    run 2 3 (compiled registered clobbered) emptyNames empty initial = clobberedExpected := by
  rw [closed_execution]
  let before := patch {inner with namespaceId := innerName}
    (patch {outer with namespaceId := outerName} initial)
  let after := {before with values := overwrite before.values 0 (fun _ => 999)}
  change (⟨⟨2, [1, 0]⟩, after,
    [runQuery before.values (query outerName demand),
      runQuery after.values (query outerName demand), runQuery after.values (query innerName demand)],
    [.allocation (.initialized outerName), .allocation (.initialized innerName),
      .changed outerName 0]⟩ : Zkc.Modules.FactorScopes.Result Nat) = clobberedExpected
  have final : before = nestedWorld := nested_world
  dsimp only [after]
  rw [final]
  rfl

def clobberPlans (before : Plan) : Code Nat :=
  .bind outer
    (.bind inner
      (.demand 1 demand before (.clobber 1 0 (fun _ => 999)
        (.demand 1 demand .direct (.demand 0 demand .direct .stop))))
      (.demand 0 demand (.reuse outerFact [1]) .stop))
    (.demand 0 demand .direct .stop)

theorem clobber_discards_facts :
    compiled false clobbered = clobberPlans .direct ∧
    compiled true clobbered = clobberPlans (.reuse outerFact [1]) := ⟨rfl, rfl⟩

theorem stale_clobbered_view_is_wrong :
    runPlan clobberedWorld.values (query outerName demand)
      (.reuse (fact outerName outerFact) [addr outerName 1]) = 999 ∧
    runQuery clobberedWorld.values (query outerName demand) = 23 := by decide

def importedNames : Names := push outerName emptyNames
def importedFacts : Facts := entered outerFact
def importedCaller : Source Nat := .bind inner useBoth fallback
def reconciledPool : Pool := ⟨1, [0]⟩

theorem imported_facts_sound : Sound importedFacts importedNames outerWorld := by
  rw [← outer_world]
  exact entered_sound 2 3 empty outer initial emptyNames outerName rfl

/-- An imported instance can have a valid factor while lying outside a good pool. -/
theorem good_pool_does_not_register_imports : empty.Good ∧ ¬ Registered empty importedNames := by
  refine ⟨empty_good, ?_⟩
  intro registered
  have member := (registered 0 outerName rfl).2
  simp [empty] at member

theorem reconciled_good : reconciledPool.Good := by simp [Pool.Good, reconciledPool]

theorem reconciled_registered : Registered reconciledPool importedNames := by
  intro i n bound
  cases i with
  | zero =>
      have same : outerName = n := Option.some.inj bound
      subst n
      exact ⟨rfl, by decide⟩
  | succ i => simp [importedNames, push, emptyNames] at bound

/-- Without registration, the next allocation overwrites the imported base and
    captures but leaves its old handle 0 intact. -/
def aliasedWorld : World Nat where
  values := {
    base := fun k => if k = ⟨4, [0, 1]⟩ then linear 100 else fun _ => 0
    view := fun h => if h = 1 then fun tail => 400 + tail[0]?.getD 0 else outerWorld.values.view h
    challenge := fun i => if i = 0 then 4 else if i = 1 then 5 else if i = 4 then 6 else 0 }
  known := [0, 1, 4]

theorem aliased_world : patch {inner with namespaceId := outerName} outerWorld = aliasedWorld := by
  change World.mk _ _ = World.mk _ _
  rw [World.mk.injEq, State.mk.injEq]
  refine ⟨⟨?_, rfl, ?_⟩, rfl⟩
  · funext k
    change (if k = ⟨4, [0, 1]⟩ then linear 100 else
        if k = ⟨4, [0, 1]⟩ then linear 10 else fun _ => 0) =
      (if k = ⟨4, [0, 1]⟩ then linear 100 else fun _ => 0)
    split <;> simp_all
  · funext i
    change (if i ∈ [0, 1, 4] then [4, 5, 6][(Nat.unpair i).2]?.getD 0
        else outerWorld.values.challenge i) =
      (if i = 0 then 4 else if i = 1 then 5 else if i = 4 then 6 else 0)
    by_cases zero : i = 0
    · subst i; rfl
    by_cases one : i = 1
    · subst i; rfl
    by_cases four : i = 4
    · subst i; rw [show Nat.unpair 4 = (0, 2) from Nat.unpair_pair 0 2]; rfl
    simp [outerWorld, zero, one, four]

def aliasedExpected : Zkc.Modules.FactorScopes.Result Nat :=
  ⟨⟨1, [0]⟩, aliasedWorld, [405, 405], [.allocation (.initialized outerName)]⟩

theorem conservative_imported_execution :
    run 2 3 (Zkc.Compiler.FactorScopes.compile importedFacts importedCaller)
      importedNames empty outerWorld = aliasedExpected := by
  rw [Zkc.Compiler.FactorScopes.compile_correct 2 3 importedCaller importedFacts
    importedNames empty outerWorld imported_facts_sound]
  let finalWorld := patch {inner with namespaceId := outerName} outerWorld
  change (⟨⟨1, [0]⟩, finalWorld,
    [runQuery finalWorld.values (query outerName demand),
      runQuery finalWorld.values (query outerName demand)], [.allocation (.initialized outerName)]⟩ :
      Zkc.Modules.FactorScopes.Result Nat) = aliasedExpected
  have final : finalWorld = aliasedWorld := aliased_world
  rw [final]
  rfl

/-- Running the stronger pass without its registration premise yields a stale
    answer. This is a counterexample to dropping that premise. -/
theorem unregistered_reuse_changes_execution :
    run 2 3 (Zkc.Compiler.FreshAllocation.compile importedFacts importedCaller)
      importedNames empty outerWorld = {aliasedExpected with values := [25, 405]} := by
  let finalWorld := patch {inner with namespaceId := outerName} outerWorld
  change (⟨⟨1, [0]⟩, finalWorld, [25,
    runPlan finalWorld.values (query outerName demand)
      (.reuse (fact outerName innerFact) [addr outerName 1])],
    [.allocation (.initialized outerName)]⟩ : Zkc.Modules.FactorScopes.Result Nat) = _
  have final : finalWorld = aliasedWorld := aliased_world
  rw [final]
  rfl

theorem registered_imported_execution :
    run 2 3 (Zkc.Compiler.FreshAllocation.compile importedFacts importedCaller)
      importedNames reconciledPool outerWorld =
      {nestedExpected with events := [.allocation (.initialized innerName)]} := by
  rw [Zkc.Compiler.FreshAllocation.compile_correct 2 3 importedCaller importedFacts importedNames
    reconciledPool outerWorld reconciled_good reconciled_registered imported_facts_sound]
  let finalWorld := patch {inner with namespaceId := innerName} outerWorld
  change (⟨⟨2, [1, 0]⟩, finalWorld,
    [runQuery finalWorld.values (query outerName demand),
      runQuery finalWorld.values (query innerName demand)], [.allocation (.initialized innerName)]⟩ :
      Zkc.Modules.FactorScopes.Result Nat) = _
  have final : finalWorld = nestedWorld := by
    dsimp only [finalWorld]
    rw [← outer_world, nested_world]
  rw [final]
  rfl

def reservedRequests (_ : Nat) : Request Nat := {outer with namespaceId := outerName}
def reservedCaller : Zkc.Compiler.FactorProgram.Source :=
  .call 0 (.demand (query outerName demand) .stop) .stop
def reservedCode := Zkc.Compiler.FactorProgram.compile
  (fun id => (contract (reservedRequests id)).post) [] [] reservedCaller

/-- Reserved-name installation inside a caller supplies the fact used by the
    binding join, starting from the explicitly empty analysis context. -/
theorem caller_installs_then_reuses :
    Zkc.Compiler.FactorProgram.run (fun id => execute 2 (reservedRequests id)) reservedCode initial =
      ⟨outerWorld, [23], [.initialized outerName]⟩ := by
  have legal : Zkc.Compiler.FactorProgram.Legal (fun id => contract (reservedRequests id))
      (fun id => execute 2 (reservedRequests id)) [] reservedCaller initial :=
    ⟨trivial, ⟨by decide, trivial⟩⟩
  unfold reservedCode
  rw [Zkc.Compiler.FactorBinding.caller_from_before 2 reservedRequests reservedCaller initial [] []
    (by simp [Valid]) (by simp [Known]) legal]
  change (⟨patch {outer with namespaceId := outerName} initial, [23], [.initialized outerName]⟩ :
    Zkc.Compiler.FactorProgram.Result Nat Event) = _
  rw [outer_world]

/-- Full-namespace instantiation installs a base function at every local key;
    the finite captured coordinates and the single materialized view are explicit. -/
def instantiatedWorld : World Nat where
  values := {
    base := fun k => if (Nat.unpair k.origin).1 = 0 then linear 10 else fun _ => 0
    view := fun h => match Nat.unpair h with
      | (0, 0) => fun tail => 20 + tail[0]?.getD 0
      | _ => fun _ => 0
    challenge := fun i => match Nat.unpair i with
      | (0, 0) => 2
      | (0, 1) => 3
      | _ => 0 }
  known := [0, 1]

def prepared : Prepared Nat := ⟨instantiatedWorld, fact outerName outerFact, [0, 1]⟩

theorem instantiated_world :
    link outerName {outer.localWorld with
      values := Zkc.Source.FactorInputs.install outer.localWorld.values outer.source outer.handle} initial =
      instantiatedWorld := by
  change World.mk _ _ = World.mk _ _
  rw [World.mk.injEq, State.mk.injEq]
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · funext h
    change (if (Nat.unpair h).1 = 0 then
      if (Nat.unpair h).2 = 0 then (fun tail => 20 + tail[0]?.getD 0) else fun _ => 0
      else fun _ => 0) = (match Nat.unpair h with
        | (0, 0) => fun tail => 20 + tail[0]?.getD 0
        | _ => fun _ => 0)
    cases Nat.unpair h with
    | mk instanceId localId => cases instanceId <;> cases localId <;> rfl
  · funext i
    change (if (Nat.unpair i).1 = 0 then [2, 3][(Nat.unpair i).2]?.getD 0 else 0) =
      (match Nat.unpair i with | (0, 0) => 2 | (0, 1) => 3 | _ => 0)
    cases Nat.unpair i with
    | mk instanceId localId =>
      cases instanceId with
      | zero => cases localId with
        | zero => rfl
        | succ localId => cases localId <;> rfl
      | succ instanceId => rfl

theorem instantiation_accepted :
    instantiate outerName outer.localWorld initial outer.source outer.handle = some prepared := by
  change some (⟨link outerName {outer.localWorld with
      values := Zkc.Source.FactorInputs.install outer.localWorld.values outer.source outer.handle} initial,
    fact outerName outerFact, [0, 1]⟩ : Prepared Nat) = some prepared
  rw [instantiated_world]
  rfl

def instantiatedCaller : Zkc.Compiler.FactorProgram.Source :=
  .demand (query outerName demand) .stop
def instantiatedCode := Zkc.Compiler.FactorProgram.compile
  (fun id => (contract (reservedRequests id)).post) [prepared.exported] prepared.available instantiatedCaller

/-- The returned prepared instance supplies the binding join's premises; its
    complete caller result and runtime readiness are both retained. -/
theorem caller_uses_instantiated_binding :
    Zkc.Compiler.FactorProgram.run (fun id => execute 2 (reservedRequests id))
      instantiatedCode prepared.world = ⟨instantiatedWorld, [23], []⟩ ∧
    Zkc.Compiler.FactorProgram.Enabled (fun id => contract (reservedRequests id))
      (fun id => execute 2 (reservedRequests id)) instantiatedCode prepared.world := by
  have joined := Zkc.Compiler.FactorBinding.instantiated_caller outerName outer.localWorld initial
    outer.source outer.handle prepared instantiation_accepted
    (fun id => contract (reservedRequests id)) (fun id => execute 2 (reservedRequests id))
    (fun id => execute_satisfies 2 (reservedRequests id)) instantiatedCaller ⟨by decide, trivial⟩
  refine ⟨joined.1.trans ?_, joined.2⟩
  have value : runQuery instantiatedWorld.values (query outerName demand) = 23 := by
    change (if (Nat.unpair 4).1 = 0 then linear 10 else fun _ => 0) [2, 3] = 23
    rw [show Nat.unpair 4 = (0, 2) from Nat.unpair_pair 0 2]
    rfl
  change (⟨instantiatedWorld, [runQuery instantiatedWorld.values (query outerName demand)], []⟩ :
    Zkc.Compiler.FactorProgram.Result Nat Event) = _
  rw [value]

end Tests.ScopedAllocation

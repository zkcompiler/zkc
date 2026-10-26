module

public import ZkcExamples.Construction.GkrDomainHelpers
public import ZkcExamples.Structured.Generated.Constructed.GkrValidator
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainRounds
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol
namespace View
abbrev output := Generated.Constructed.GkrValidator.bodyStep1Body
abbrev left := Generated.Constructed.GkrValidator.bodyStep3BodyStep1Body
abbrev right := Generated.Constructed.GkrValidator.bodyStep3BodyStep3Body
abbrev coefficient := Generated.Constructed.GkrValidator.bodyStep3BodyStep10Body
end View
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Env := Domain.Environment (uniformCarriers F G)
abbrev Hist := Domain.History (uniformCarriers F G)

def pointValues (point : List F) (suffix : Hist (F := F) (G := G)) : Env (F := F) (G := G) :=
  [.data (.vector "bls12-381.fr" point), .transcript context.suite suffix]
def roundValues (point : List F) (claim : F) (suffix : Hist (F := F) (G := G)) : Env (F := F) (G := G) :=
  [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim), .transcript context.suite suffix]

def PointReturns (source : List F × Hist (F := F) (G := G)) (actual : Env (F := F) (G := G)) : Prop :=
  ∃ point suffix, source = (point, history suffix) ∧ actual = pointValues point suffix
def RoundReturns (source : (List F × F) × Hist (F := F) (G := G)) (actual : Env (F := F) (G := G)) : Prop :=
  ∃ point claim suffix, source = ((point, claim), history suffix) ∧ actual = roundValues point claim suffix

abbrev yieldValues (yielded : List Nat) (declared : List ValueSort) (final : Env (F := F) (G := G)) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G)) :=
  match Domain.read final yielded with
  | none => .halt .refused
  | some next => if Domain.sortsMatch declared next then .done next else .halt .refused

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem sourceView_ite {A : Type} (ctx : Context) (condition : Prop) [Decidable condition]
    (left right : PIR.Process (Actions F G) A) (suffix : Hist (F := F) (G := G)) :
    SourceProcess.sourceView ctx (if condition then left else right) suffix =
      if condition then SourceProcess.sourceView ctx left suffix else SourceProcess.sourceView ctx right suffix := by
  split <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem interpret_ite {A : Type} (condition : Prop) [Decidable condition]
    (left right : PIR.Process (Domain.effects (uniformCarriers F G)) A) :
    (if condition then left else right).interpret operations =
      if condition then left.interpret operations else right.interpret operations := by
  split <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem guard_decide (condition : Prop) [Decidable condition]
    (env : Env (F := F) (G := G)) :
    (match some (Domain.Value.data (Domain.Payload.boolean (decide condition)) : Domain.Value (uniformCarriers F G)) with
     | some (.data (.boolean true)) => (PIR.Process.done env : PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G)))
     | some (.data (.boolean false)) => PIR.Process.halt .reject
     | _ => PIR.Process.halt .refused) =
      (if condition then .done env else .halt .reject) := by
  by_cases condition <;> simp_all

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Interpretation commutes with the existing finite loop and its exact yield
checks. No instruction evaluator is introduced. -/
theorem iterate_interpret (body : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G)))
    (outer : Env (F := F) (G := G)) (yielded : List Nat) (declared : List ValueSort)
    (indices : List Nat) (initial : Env (F := F) (G := G)) :
    (Domain.iterate body outer yielded declared indices initial).interpret operations =
      Finite.fold (fun carried index =>
        ((body (outer ++ .data (.index index) :: carried)).bind (yieldValues yielded declared)).interpret operations)
        indices initial := by
  rw [Original.iterate_eq_fold, Finite.interpret_fold]
  unfold ZkcExamples.Construction.GkrDomainRounds.yieldValues
  congr 1
  funext carried index
  congr 1
  congr 1
  funext final
  cases Domain.read final yielded <;> rfl

/-- Callback certificates compose at every index and every related state,
including the empty iteration list, through the existing loop implementation. -/
def iterate_binding {A : Type}
    (relation : (A × Hist (F := F) (G := G)) → Env (F := F) (G := G) → Prop)
    (step : A → Nat → PIR.Process (Actions F G) A)
    (body : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G)))
    (outer : Env (F := F) (G := G)) (yielded : List Nat) (declared : List ValueSort)
    (callback : ∀ source carried index, relation source carried →
      Original.Simulation relation (fun _ _ => True)
        (SourceProcess.sourceView context (step source.1 index) source.2)
        (((body (outer ++ .data (.index index) :: carried)).bind
          (yieldValues yielded declared)).interpret operations))
    (indices : List Nat) (initial : A) (suffix : Hist (F := F) (G := G))
    (carried : Env (F := F) (G := G)) (related : relation (initial, history suffix) carried) :
    Original.Simulation relation (fun _ _ => True)
      (SourceProcess.sourceView context (Finite.fold step indices initial) (history suffix))
      ((Domain.iterate body outer yielded declared indices carried).interpret operations) := by
  rw [sourceView_finite, iterate_interpret]
  exact Original.Simulation.finite _ _ callback (by intros; trivial) indices
    (initial, history suffix) carried related

def AppendReturns {A : Type}
    (relation : (A × Hist (F := F) (G := G)) → Env (F := F) (G := G) → Prop)
    (outer : Env (F := F) (G := G)) (source : A × Hist (F := F) (G := G))
    (actual : Env (F := F) (G := G)) : Prop :=
  ∃ carried, relation source carried ∧ actual = outer ++ carried

/-- A complete bounded View loop, preserving the immutable captures and exact
carried ABI. Its refusal branch is connected independently of honest bounds. -/
def loop_binding {A : Type}
    (relation : (A × Hist (F := F) (G := G)) → Env (F := F) (G := G) → Prop)
    (step : A → Nat → PIR.Process (Actions F G) A)
    (body : Env (F := F) (G := G) → PIR.Process (Domain.effects (uniformCarriers F G)) (Env (F := F) (G := G)))
    (outer : Env (F := F) (G := G)) (yielded : List Nat) (declared : List ValueSort)
    (callback : ∀ source carried index, relation source carried →
      Original.Simulation relation (fun _ _ => True)
        (SourceProcess.sourceView context (step source.1 index) source.2)
        (((body (outer ++ .data (.index index) :: carried)).bind
          (yieldValues yielded declared)).interpret operations))
    (sorts : ∀ source carried, relation source carried → Domain.sortsMatch declared carried = true)
    (bound countRef : Nat) (initialRefs : List Nat) (initial : A)
    (suffix : Hist (F := F) (G := G)) (carried : Env (F := F) (G := G))
    (foundCount : outer[countRef]? = some (.data (.index bound)))
    (foundInitial : Domain.read outer initialRefs = some carried)
    (related : relation (initial, history suffix) carried) :
    Original.Simulation (AppendReturns relation outer) (fun _ _ => True)
      (SourceProcess.sourceView context
        (if bound ≤ 4 then Finite.fold step (List.range bound) initial else .halt .refused) (history suffix))
      ((Domain.View.loop 4 yielded countRef initialRefs declared body outer).interpret operations) := by
  simp only [Domain.View.loop, foundCount, foundInitial, sorts _ _ related, and_true]
  by_cases bounded : bound ≤ 4
  · simp only [bounded, ite_true, PIR.Process.interpret_bind]
    have law := iterate_binding relation step body outer yielded declared callback
      (List.range bound) initial suffix carried related
    simpa only [PIR.Process.bind_done] using
      law.bind (sourceNext := fun source => .done source)
        (targetNext := fun next => (Domain.View.append declared outer next).interpret operations)
        (by intros; trivial) (fun source next reached => by
          simp only [Domain.View.append, sorts _ _ reached, ite_true, PIR.Process.interpret]
          exact .done ⟨next, reached, rfl⟩)
  · simp only [bounded, ite_false, PIR.Process.interpret, SourceProcess.sourceView]
    exact .halt .refused

theorem entry_metadata : GkrSourceData.snapshot.entry =
    "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" := rfl
theorem suite_metadata : artifact.policy.suite = "merlin3.bls12-381.fr64be/0" := rfl

theorem left_size : protocolSiteDecimal "label_6c656674".utf8ByteSize = "14" := by kernel_rfl
theorem right_size : protocolSiteDecimal "label_7269676874".utf8ByteSize = "16" := by kernel_rfl

/-- A reached field query has one reply carrier. Its key and accumulated
history are checked separately, before the arbitrary reply continuation. -/
def query_binding {A B : Type} {relation : A → B → Prop}
    {live : PIR.Process (Domain.effects (uniformCarriers F G)) A → Env (F := F) (G := G) → Prop}
    {sourceHistory targetHistory : Hist (F := F) (G := G)}
    {sourceEntry targetEntry : String} {sourceSite targetSite : List String}
    {left : F → PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {right : F → PIR.Process (Domain.effects (uniformCarriers F G)) B}
    (sameHistory : sourceHistory = targetHistory) (sameEntry : sourceEntry = targetEntry)
    (sameSite : sourceSite = targetSite)
    (next : ∀ reply, Original.Simulation relation live (left reply) (right reply)) :
    Original.Simulation relation live
      (.call (.query sourceHistory ⟨sourceEntry, sourceSite, some (.draw "bls12-381.fr")⟩) left)
      (.call (.query targetHistory ⟨targetEntry, targetSite, some (.draw "bls12-381.fr")⟩) right) := by
  subst targetHistory
  subst targetEntry
  subst targetSite
  exact .call _ next


end ZkcExamples.Construction.GkrDomainRounds

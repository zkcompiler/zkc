import Zkc.Modules.FactorExecution
import Zkc.Semantics.Preparation
import Zkc.Polynomial.Bilinear.Installation

set_option autoImplicit false

namespace Zkc.Polynomial.Bilinear.Execution
open PIR

open Zkc.Modules.Factor

abbrev Cache := Zkc.Modules.Preparation.Cache Zkc.Source.TablePreparation.Key (List Nat)
abbrev State := Zkc.Modules.FactorState.World Nat × Cache
abbrev Input := Zkc.Polynomial.Bilinear.Installation.Input
abbrev Namespace := Zkc.Modules.FactorBinding.Namespace

/-- Reserved-name installation or an ordinary contracted call. Allocation remains
    a separate operation; this construction does not reset an allocation registry. -/
inductive Call where
  | prepare (input : Input) (name : Namespace) (capacity : Nat)
  | external (id : Nat)

variable {E : Type}
abbrev Visible (E : Type) := Sum Zkc.Modules.Installation.Event E
abbrev Event (E : Type) := Preparation.Event (Visible E)

def mapReturned {F : Type} (f : E → F) (r : Zkc.Modules.FactorState.Returned Nat E) : Zkc.Modules.FactorState.Returned Nat F :=
  ⟨r.success,r.world,r.events.map f⟩

/-- Mathematical reference for Zkc.Modules.FactorState's existing call/inference theorem. This has
    no materialization cost claim; both measured modes below really prepare. -/
def reference (external : Nat → Zkc.Modules.FactorState.Implementation Nat E) : Call → Zkc.Modules.FactorState.Implementation Nat (Visible E)
  | .prepare i n cap => fun s => mapReturned Sum.inl (Zkc.Modules.Installation.execute cap (i.request n) s)
  | .external id => fun s => mapReturned Sum.inr (external id s)

def spec (external : Nat → Zkc.Modules.FactorState.Spec Nat) : Call → Zkc.Modules.FactorState.Spec Nat
  | .prepare i n _ => Zkc.Modules.Installation.contract (i.request n)
  | .external id => external id

theorem reference_satisfies (contracts : Nat → Zkc.Modules.FactorState.Spec Nat)
    (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (contracts id) (external id)) (c : Call) :
    Zkc.Modules.FactorState.Satisfies (spec contracts c) (reference external c) := by
  cases c with
  | prepare i n cap => exact Zkc.Modules.Installation.execute_satisfies cap (i.request n)
  | external id => exact laws id

structure Called (E : Type) where
  returned : Zkc.Modules.FactorState.Returned Nat (Visible E)
  cache : Cache
  work : Nat
  saved : Nat
  overhead : Nat

/-- The same admitted snapshot and immutable table code used in the bilinear preparation client.
    Preparation occurs only after successful reserved-name installation. -/
def call (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (c : Call) (s : State) : Called E :=
  match c with
  | .external id => ⟨reference external (.external id) s.1,s.2,0,0,0⟩
  | .prepare i n cap =>
    let out := Zkc.Modules.Installation.execute cap (i.request n) s.1
    if out.success then
      let a := Zkc.Modules.Preparation.acquire Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode s.2 i.prepKey
      ⟨mapReturned Sum.inl {out with world := Zkc.Polynomial.Bilinear.Installation.tableWorld i n a.value s.1},
        a.cache,a.work,a.saved,a.overhead⟩
    else ⟨mapReturned Sum.inl out,s.2,0,0,0⟩

theorem call_reference (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (c : Call) (s : State) (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2) :
    (call mode external c s).returned = reference external c s.1 := by
  cases c with
  | external id => rfl
  | prepare i n cap =>
    cases h : (Zkc.Modules.Installation.execute cap (i.request n) s.1).success with
    | false => simp [call,reference,h]
    | true =>
      have value := (Zkc.Modules.Preparation.acquire_law Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode s.2 i.prepKey valid).1
      have world := Zkc.Modules.Allocation.execute_success_world cap (i.request n) s.1 h
      simp only [call,h,↓reduceIte]
      rw [value,Zkc.Polynomial.Bilinear.Installation.table_world_eq,← world]
      simp [reference,mapReturned,h]

theorem call_cache_valid (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (c : Call) (s : State) (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2) :
    Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider (call mode external c s).cache := by
  cases c with
  | external id => exact valid
  | prepare i n cap =>
    cases h : (Zkc.Modules.Installation.execute cap (i.request n) s.1).success with
    | false => simpa [call,h] using valid
    | true => simpa only [call,h,↓reduceIte] using
        (Zkc.Modules.Preparation.acquire_law Zkc.Source.TablePreparation.provider Zkc.Source.TablePreparation.prices mode s.2 i.prepKey valid).2.1

/-- Cache validity is independent of mutations to the logical world. A fact about
    that world's live view still needs the outcome-sensitive Zkc.Modules.FactorState frame theorem. -/
def Rel (s : State) (t : Zkc.Modules.FactorState.World Nat) : Prop :=
  s.1 = t ∧ Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2

def handler (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (calls : Nat → Call) : Handler (Zkc.Modules.FactorExecution.signature Nat) State (Event E)
  | .demand q p, s => ⟨.returned (runPlan s.1.values q p),s,[]⟩
  | .external id, s =>
    let out := call mode external (calls id) s
    ⟨.returned out.returned.success,(out.returned.world,out.cache),
      out.returned.events.map Preparation.Event.visible ++
      [.charge out.work out.saved out.overhead]⟩

theorem handlers_related (mode : Zkc.Modules.Preparation.Mode)
    (external : Nat → Zkc.Modules.FactorState.Implementation Nat E) (calls : Nat → Call) :
    HandlerRelated Rel Preparation.view (fun e => [e])
      (handler mode external calls) (Zkc.Modules.FactorExecution.handler (fun id => reference external (calls id))) := by
  intro op s t h
  rcases h with ⟨rfl,valid⟩
  cases op with
  | demand q p => exact ⟨rfl,⟨rfl,valid⟩,rfl⟩
  | external id =>
    have same := call_reference mode external (calls id) s valid
    have hc := call_cache_valid mode external (calls id) s valid
    refine ⟨?_,⟨?_,hc⟩,?_⟩
    · change Outcome.returned (call mode external (calls id) s).returned.success = _
      rw [same]; rfl
    · change (call mode external (calls id) s).returned.world = _
      rw [same]; rfl
    · change observeEvents Preparation.view
        ((call mode external (calls id) s).returned.events.map Preparation.Event.visible ++
          [.charge _ _ _]) = _
      simp [observeEvents,List.flatMap_map,Preparation.view,same,Zkc.Modules.FactorExecution.handler,Zkc.Modules.FactorExecution.returned]

theorem run_reference {A : Type} (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (calls : Nat → Call) (prog : Proc (Zkc.Modules.FactorExecution.signature Nat) A)
    (s : State) (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2) :
    Related Rel Preparation.view (fun e => [e])
      (prog.run (handler mode external calls) s)
      (prog.run (Zkc.Modules.FactorExecution.handler (fun id => reference external (calls id))) s.1) :=
  run_related _ _ _ _ _ (handlers_related mode external calls) prog s s.1 ⟨rfl,valid⟩

/-- Same logical world, independent valid caches. Costs are kept in events but
    erased by the selected protocol observer. -/
def SameWorld (s t : State) : Prop :=
  s.1 = t.1 ∧ Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2 ∧ Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider t.2

theorem executions_from_reference {A : Type}
    (a b : Execution State (Event E) A) (r : Execution (Zkc.Modules.FactorState.World Nat) (Visible E) A)
    (ha : Related Rel Preparation.view (fun e => [e]) a r)
    (hb : Related Rel Preparation.view (fun e => [e]) b r) :
    Related SameWorld Preparation.view Preparation.view a b :=
  ⟨ha.outcome.trans hb.outcome.symm,
   ⟨ha.state.1.trans hb.state.1.symm,ha.state.2,hb.state.2⟩,
   ha.events.trans hb.events.symm⟩

end Zkc.Polynomial.Bilinear.Execution

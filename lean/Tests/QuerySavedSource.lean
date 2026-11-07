module

public import Zkc.Realization.QuerySavedSource
public import Tests.VirtualStorageInstallation
public import Tests.QuerySourceContinuation
public import Tests.QuerySourceExecution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySavedSource
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData VirtualStorageInstallation
open Zkc.Realization.QuerySavedSource

def frame : QueryContinuation.Frame := ⟨7, 3, 0, 0, [0]⟩

def parent : Parent layout references result.state.entries [record] frame :=
  ⟨location 9, 2, 2, 0, [1], captures, by kernel_rfl, installed⟩

def savedRecord : model.Value (QueryContinuation.layout "saved" 1).type :=
  (7, 3, 0, 0, 0, ())

theorem encoded : QueryContinuation.Encodes "saved" 1 frame savedRecord :=
  ⟨(0, ()), rfl, rfl⟩

def child : OracleRead := QuerySourceContinuation.child (anchor 0) 0 1
def next (answer : model.Value child.kind.answer) :
    PIR.Process (oracleReadInterface model.toCarriers)
      (Values (Component model.Value) [checked.declaration.kind.answer]) :=
  .done (.cons (some answer) .nil)

/-- A real source installation and its first returned child establish the
saved frame relation through common rules; no frame/source equality is assumed. -/
def saved : Saved "saved" 1 [savedRecord] 0 QuerySourceContinuation.arenas parent child next := by
  apply save [] encoded
  exact QuerySourceContinuation.afterFirst (anchor 0) 0

/-- The physical load restores the installed parent and ordered answers. Its
answer is the second real reply, and its events follow the first reply's log. -/
theorem restored_execution (program : Program) (context : Context)
    (suffix : Domain.Environment model.toCarriers) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (QueryContinuation.layout "saved" 1).type, rfl, [savedRecord]⟩,
        .data (.index 0)] ++ suffix
    Nonempty (Zkc.Realization.QuerySourceContinuation.Produced QuerySourceExecution.calls
      QuerySourceExecution.operations parent.body 0 0 QuerySourceContinuation.arenas
      (.done (.cons (some (20 : Nat)) .nil)) [0, 1] 22 2 [4, 5]) ∧
    ∃ record, QueryContinuation.Encodes "saved" 1 frame record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(QueryContinuation.layout "saved" 1).type, rfl, record⟩] ++
          frame.values.map (fun value ↦ Domain.Value.data (.index value))))
        (Domain.evaluate model program context
          (QueryContinuation.loadInstructions "saved" 1 environment.length 0 1) environment)) := by
  dsimp only
  exact saved.load_produced QuerySourceExecution.first
    (.step (P := QuerySourceExecution.calls) (child, 11) .done 1
      ⟨.returned (20 : Nat), 22, [5]⟩ _ _ (.refl _ _))
    (answerSlot := 1) rfl _ 0 1 rfl program context

/-- A later actual construction and extra frame/answer cells preserve this
suspension. Neither the source body nor its capture association is reproved. -/
def retained :
    Saved "saved" 1 ([savedRecord] ++ [savedRecord]) 0 QuerySourceContinuation.arenas
      (parent.transport
        (OracleExecution.operation_extension model [checked] (base none) (location 10)
          result.state.self id (.virtual checked.declaration.signature 0 [1])
          (ProtocolValue.embedComponents captures.present) result.state).fresh
        (List.prefix_refl _) (fun _ _ _ _ found ↦ found)) child next :=
  saved.transport
    (OracleExecution.operation_extension model [checked] (base none) (location 10)
      result.state.self id (.virtual checked.declaration.signature 0 [1])
      (ProtocolValue.embedComponents captures.present) result.state).fresh
    (List.prefix_refl _) (List.prefix_append _ _) (fun _ ↦ List.prefix_refl _)
    (fun _ _ _ _ found ↦ found)

/-- Equal-typed frame fields cannot exchange the outer and parent instances. -/
theorem parent_swap_rejected :
    ¬ QueryContinuation.Stored "saved" 1 [savedRecord] 0
      {frame with outerInstance := 0, parentInstance := 3} := by
  intro wrong
  have same := congrArg QueryContinuation.Frame.parentInstance (saved.decoded wrong)
  contradiction

/-- Replacing the parent's same-typed captured handle is impossible even when
the chosen continuation's final result would ignore that earlier child. -/
theorem capture_swap_rejected (other : Parent layout references result.state.entries [record] frame)
    (swapped : other.captures = .cons (anchor 10) .nil) : False := by
  have same := parent.captures_unique other
    (ClearStorage.references_unambiguous parentLayout words [parentRecord])
  rw [swapped] at same
  have handles := congrArg (fun values ↦ values.get .here) same
  have different : anchor 0 ≠ anchor 10 := by decide +kernel
  exact different handles

#print axioms saved
#print axioms restored_execution
#print axioms retained
#print axioms parent_swap_rejected
#print axioms capture_swap_rejected
end Tests.QuerySavedSource

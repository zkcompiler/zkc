module

public import ZkcSecurity.Families.Sumcheck.TableComponentNominal
public import ZkcSecurity.Families.Sumcheck.TableComponentHistory

@[expose] public section

/-! The nominal table-loop state and evaluator, independent of source adapters. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Execution
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {F G : Type} [Field F] [DecidableEq F]

structure State (F G : Type) where
  point : List F
  scalar : F
  history : Domain.History (uniformCarriers F G)

def advance (field : String) (sites : Nominal.Schedule field) (index : Nat)
    (state : State F G) (low high challenge : F) : State F G :=
  ⟨state.point ++ [challenge], (1 - challenge) * low + challenge * high,
    finalHistory field (sites.low index) (sites.high index)
      (sites.query index) (sites.delivery index) state.history low high challenge⟩

noncomputable def run (field : String) (sites : Nominal.Schedule field) :
    List Nat → State F G → PIR.Process (Nominal.signature F field) (State F G)
  | [], state => .done state
  | index :: rest, state =>
      .call (.receive (sites.low index)) fun low =>
      .call (.receive (sites.high index)) fun high =>
      if state.scalar = low + high then
        .call (.query (sites.query index) (sites.request index)) fun challenge =>
        .call (.deliver (sites.delivery index) challenge) fun _ =>
          run field sites rest (advance field sites index state low high challenge)
      else .halt .reject

end ZkcSecurity.Families.Sumcheck.TableComponent.Execution

module

public import Zkc.Realization.QuerySourceExecution
public import Tests.QuerySourceContinuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySourceExecution
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.QuerySourceContinuation OracleProcessData

abbrev effects := OracleProcess.Effect (oracleReadInterface model.toCarriers) Nat Nat

abbrev calls : PIR.Interaction effects where
  Role := Unit
  Phase := Nat
  owner := fun _ ↦ ()
  enabled := fun _ _ ↦ True
  advance := fun count _ _ ↦ count + 1

def operations (request : OracleRead) (state : Nat) :
    PIR.Process effects (PIR.Execution Nat Nat (model.Value request.kind.answer)) :=
  .call (request, state) .done

abbrev source := QuerySourceContinuation.source (anchor 0) 0
abbrev request (ordinal : Nat) := QuerySourceContinuation.child (anchor 0) 0 ordinal
abbrev remainder : PIR.Process (oracleReadInterface model.toCarriers)
    (Values (Component model.Value) [.index]) :=
  .call (request 1) (fun reply ↦ .done (.cons (some reply) .nil))

/-- The first actual external result, including poststate and events, advances
the checked source even though its returned value is not used by the body. -/
def first : Produced calls operations source 0 0 QuerySourceContinuation.arenas
    remainder [0] 11 1 [4] := by
  have start := Produced.initial (interaction := calls) (operations := operations)
    (source := source) (initialState := 0) (initialPhase := 0) QuerySourceContinuation.arenas
  rw [source, QuerySourceContinuation.source_body] at start
  exact start.resume
    (.step (P := calls) (request 0, 0) .done 0 ⟨.returned (10 : Nat), 11, [4]⟩ _ _ (.refl _ _)) rfl

def second : Produced calls operations source 0 0 QuerySourceContinuation.arenas
    (.done (.cons (some (20 : Nat)) .nil)) [0, 1] 22 2 [4, 5] :=
  first.resume
    (.step (P := calls) (request 1, 11) .done 1 ⟨.returned (20 : Nat), 22, [5]⟩ _ _ (.refl _ _)) rfl

theorem complete_execution :
    PIR.Reaches calls (OracleProcess.present operations source 0) 0
      (.done ⟨.returned (.cons (some (20 : Nat)) .nil), 22, [4, 5]⟩) 2 :=
  second.completed

/-- A stopped second child retains both event segments and its poststate.
It does not add a second saved answer or masquerade as a successful reply. -/
theorem second_stopped (reason : PIR.Stop) :
    PIR.Reaches calls (OracleProcess.present operations source 0) 0
      (.done ⟨.stopped reason, 22, [4, 5]⟩) 2 :=
  first.stopped
    (.step (P := calls) (request 1, 11) .done 1 ⟨.stopped reason, 22, [5]⟩ _ _ (.refl _ _))

def fixed : (request : OracleRead) → Nat →
    PIR.Process effects (PIR.Execution Nat Nat (model.Value request.kind.answer))
  | ⟨.table .index _, _, _, _, _⟩, state => .done ⟨.returned (10 : Nat), state + 1, [1]⟩
  | _, state => .done ⟨.stopped .refused, state + 1, [1]⟩

def wrongArenas : (kind : OracleKind) → List (model.Value kind.answer)
  | .table .index _ => ([99, 20] : List Nat)
  | _ => []

/-- An unproduced value can satisfy the weaker typed cursor relation when
the source ignores that value. This counterexample explains why it is not an
execution invariant by itself. -/
def unproduced_cursor : Associated wrongArenas source remainder [0] := by
  have start := QuerySourceContinuation.initial wrongArenas source
  rw [source, QuerySourceContinuation.source_body] at start
  exact start.resume (reply := (99 : Nat)) rfl

/-- Even equality of the residual open computation does not repair that
weaker cursor: the ignored answer has disappeared from the computation. -/
theorem same_residual_execution :
    PIR.Reaches calls (OracleProcess.present fixed source 0) 0
      (OracleProcess.prependEvents [1] (OracleProcess.present fixed remainder 1)) 0 := by
  rw [source, QuerySourceContinuation.source_body]
  exact .refl _ _

/-- The progress derivation rejects the same case because its first saved
value must come from the actual first child execution, which returns ten. -/
theorem unproduced_answer_rejected :
    IsEmpty (Produced calls fixed source 0 0 wrongArenas remainder [0] 1 0 [1]) := by
  constructor
  intro produced
  obtain ⟨operation, next, reply, sourceEq, residualEq, executed, stored⟩ := produced.one rfl
  rw [source, QuerySourceContinuation.source_body] at sourceEq
  obtain ⟨sameOperation, sameNext⟩ := PIR.Process.call.inj sourceEq
  cases sameOperation
  have value : reply = (10 : Nat) := by
    change PIR.Reaches calls (.done (⟨.returned 10, 1, [1]⟩ : PIR.Execution Nat Nat Nat)) 0
      (.done ⟨.returned reply, 1, [1]⟩) 0 at executed
    cases executed
    rfl
  rw [value] at stored
  change some (99 : Nat) = some 10 at stored
  cases stored

#print axioms first
#print axioms complete_execution
#print axioms second_stopped
#print axioms same_residual_execution
#print axioms unproduced_answer_rejected
end Tests.QuerySourceExecution

import Zkc.Compiler.Arithmetic.Dag
import Zkc.Compiler.FactorOptimization
import Zkc.Modules.Installation

/-! Behavioral and syntax-size controls for two compiler repairs.

A literal DAG root still rejects unavailable dead inputs. External-call chains
have linear syntax when their actual analysis transfers agree, even with distinct
summaries. Complete executions retain returned Booleans and events. These bounds
do not cover expansion of a live DAG root or differing analysis transfers.
-/

set_option autoImplicit false

namespace Tests.CompilerComplexity

open Zkc.Compiler.Arithmetic.Dag

def deadDag (depth : Nat) : DAG :=
  .lit 0 :: (List.replicate depth (.add 0 0) ++ [.input 7])

def literalSubject : Subject := ⟨"dead-input-control", 9, .lit 0⟩
def deadCertificate (depth : Nat) : Certificate :=
  ⟨"dead-input-control", 9, deadDag depth⟩

theorem dead_dag_size (depth : Nat) : (deadDag depth).length = depth + 2 := by
  simp only [deadDag, List.length_cons, List.length_append, List.length_replicate, List.length_nil]

/-- Thirty-two doubling nodes are dead, but the final raw input is still checked. -/
theorem available_dead_input_accepted :
    check literalSubject (deadCertificate 32) (fun k => if k = 7 then some 3 else none) = true := by
  decide +kernel

theorem unavailable_dead_input_rejected :
    check literalSubject (deadCertificate 32) (fun _ => none) = false := by
  decide +kernel

theorem accepted_dead_dag_execution :
    (runDAG (fun _ => 3) (deadDag 32)).head? = some 0 := rfl

open Zkc.Source Zkc.Source.FactorQueries Zkc.Modules.Factor Zkc.Modules.FactorState
open Zkc.Compiler.FactorOptimization

/-- Count syntax constructors independently of the rewriting implementation. -/
def nodes {vocabulary : Language} {context : List vocabulary.Ty} {result : vocabulary.Ty} :
    Program vocabulary context result → Nat
  | .ret _ | .stop _ => 1
  | .letOp _ _ next => 1 + nodes next
  | .branch _ yes no => 1 + nodes yes + nodes no
  | .iterate _ _ body next => 1 + nodes body + nodes next

def callChain {context : List Ty} : Nat → Program language context .boolean
  | 0 => .stop .abort
  | depth + 1 => .letOp (.external depth) .nil (callChain depth)

/-- The success summary frames everything; the failure summary promises no frame.
    They nevertheless produce the same facts and availability from empty lists. -/
def emptySummaries (_ : Nat) (success : Bool) : Summary :=
  if success then Zkc.Modules.Installation.failureSummary else ⟨none, [], [], []⟩

theorem summaries_differ : (emptySummaries 0 true).writes ≠ (emptySummaries 0 false).writes := by
  decide

theorem original_chain_size (depth : Nat) (context : List Ty) :
    nodes (callChain (context := context) depth) = depth + 1 := by
  induction depth generalizing context with
  | zero => rfl
  | succ depth ih => simp [callChain, nodes, ih, Nat.add_comm]

/-- An all-length bound, rather than a timing check or a recurrence copied from the pass. -/
theorem rewritten_chain_size (depth : Nat) (context : List Ty) :
    nodes (rewrite emptySummaries [] [] (callChain (context := context) depth)) = depth + 1 := by
  induction depth generalizing context with
  | zero => rfl
  | succ depth ih =>
      simp [callChain, rewrite, emptySummaries, Zkc.Modules.Installation.failureSummary,
        nextFacts, nextKnown, survivors, keep, keptKnown, nodes, Nat.add_comm]
      exact ih (.boolean :: context)

theorem eight_calls_have_nine_nodes :
    nodes (rewrite emptySummaries [] [] (callChain (context := []) 8)) = 9 :=
  rewritten_chain_size 8 []

def returningCall : Program language [] .boolean :=
  .letOp (.external 0) .nil (.ret .here)

def returningImplementation (success : Bool) (name : Nat) : Implementation Nat Nat :=
  fun state => ⟨success, state, [name]⟩

theorem returning_laws (success : Bool) :
    Laws (fun _ => True) emptySummaries (returningImplementation success) where
  summary name state _ := by
    cases success with
    | false =>
        exact ⟨trivial, by simp [Valid, emptySummaries, returningImplementation],
          by simp [Known, keptKnown, emptySummaries, returningImplementation], by simp [Known, emptySummaries, returningImplementation]⟩
    | true => exact Zkc.Modules.Installation.failure_justifies state
  preserves _ _ _ := trivial

def initial : World Nat := ⟨⟨fun _ _ => 11, fun _ _ => 12, fun _ => 13⟩, []⟩

theorem shared_call_keeps_result_and_events (success : Bool) :
    ((rewrite emptySummaries [] [] returningCall).denote plannedMeaning Values.nil.get).run
      (handler (returningImplementation success)) initial =
      ⟨.returned success, initial, [0]⟩ := by
  rw [execution (fun _ => True) _ _ (returning_laws success) returningCall _ initial [] []
    (by simp [Valid]) (by simp [Known]) trivial]
  rfl

def oneFact : Fact := ⟨⟨10, [0]⟩, 2, [], 1⟩

def unequalFacts (_ : Nat) (success : Bool) : Summary :=
  ⟨none, if success then [oneFact] else [], [], []⟩

def unequalAvailability (_ : Nat) (success : Bool) : Summary :=
  ⟨none, [], [], if success then [7] else []⟩

/-- Either difference requires the existing outcome-sensitive branch. -/
theorem different_fact_transfer_branches :
    nodes (rewrite unequalFacts [] [] returningCall) = 4 := by decide

theorem different_availability_transfer_branches :
    nodes (rewrite unequalAvailability [] [] returningCall) = 4 := by decide

def availableInitial : World Nat := {initial with known := [7]}

theorem availability_laws (success : Bool) :
    Laws (fun state => 7 ∈ state.known) unequalAvailability (returningImplementation success) where
  summary _ _ known := by
    refine ⟨trivial, ?_, ?_, ?_⟩
    · simp [Valid, unequalAvailability]
    · simp [Known, keptKnown, unequalAvailability]
    · cases success <;> simp [Known, unequalAvailability, returningImplementation, known]
  preserves _ _ known := known

/-- Both call outcomes also execute correctly when the compiler must keep a branch. -/
theorem branched_call_keeps_result_and_events (success : Bool) :
    ((rewrite unequalAvailability [] [] returningCall).denote plannedMeaning Values.nil.get).run
      (handler (returningImplementation success)) availableInitial =
      ⟨.returned success, availableInitial, [0]⟩ := by
  rw [execution (fun state => 7 ∈ state.known) _ _ (availability_laws success)
    returningCall _ availableInitial [] [] (by simp [Valid]) (by simp [Known]) (by decide)]
  rfl

end Tests.CompilerComplexity

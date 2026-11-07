module

public import Zkc.Realization.QuerySourceContext
public import Tests.QuerySavedSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySourceContext
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.QuerySavedSource OracleProcessData VirtualStorageInstallation

abbrev parent := QuerySavedSource.parent

/-- The context uses the actual installation suffix from the source virtual
construction, including the captured base table. -/
def context : SourceContext parent 1 where
  older := before.entries
  located := by
    change OracleStore.Located result.state.entries
      (VirtualStorage.table checked (location 9) 2 0 [1] captures) before.entries
    rw [poststate]
    exact .head _ _
  reachable := before_reachable
  smaller := by rw [poststate]; simp

theorem recovered : Nonempty (SourceContext parent 1) :=
  parent.sourceContext result_reachable

/-- An intervening real source construction retains exactly the same child
operations, including the older registry and enclosing source path. -/
theorem later_operations {S E : Type} (query : OracleRead) (state : S × Nat) :
    (context.transport
      (OracleExecution.operation_extension model [checked] (base none) (location 10)
        result.state.self id (.virtual checked.declaration.signature 0 [1])
        (ProtocolValue.embedComponents captures.present) result.state).fresh
      (List.prefix_refl _) (fun _ _ _ _ found ↦ found)).operations
      (E := E) (location 20) [] query state =
        context.operations (location 20) [] query state :=
  context.transport_operations _ _ _ _ _ _ _

abbrev calls : PIR.Interaction (OracleProcess.Interface model Nat Nat) where
  Role := Unit
  Phase := Nat
  owner := fun _ ↦ ()
  enabled := fun _ _ ↦ True
  advance := fun count _ _ ↦ count + 1

abbrev root := parent.request (location 20) []
abbrev child (ordinal : Nat) := QuerySourceContinuation.child (anchor 0) 0 ordinal
abbrev expanded (ordinal : Nat) := root.expand (child ordinal)

/-- Both actual child requests reach their provider leaf with the original
source-relative expansion. Its reply adds one query and the provider log. -/
theorem child_return (ordinal provider after count phase answer event : Nat) :
    PIR.Reaches calls (context.operations (location 20) [] (child ordinal) (provider, count)) phase
      (.done ⟨.returned answer, (after, count + 1),
        [.query (expanded ordinal), .provider event]⟩) (phase + 1) := by
  change PIR.Reaches calls
    (.call (I := OracleProcess.Interface model Nat Nat) (.inr (expanded ordinal), provider)
      (fun reply ↦ .done (⟨reply.outcome, (reply.state, count + 1),
        .query (expanded ordinal) :: reply.events.map OracleEvent.provider⟩ :
          PIR.Execution (Nat × Nat) (OracleEvent Nat) Nat))) phase _ (phase + 1)
  exact .step (P := calls) (.inr (expanded ordinal), provider) _ phase
    ⟨.returned answer, after, [event]⟩ _ _ (.refl _ _)

/-- One original virtual query and its two repeated child occurrences cost
three logical queries and two provider calls. Its first answer remains a real
access even though the final value depends only on the second answer. -/
theorem complete_parent :
    PIR.Reaches calls (OracleProcess.answer model 1 result.state.entries root (0, 0)) 0
      (.done ⟨.returned (20 : Nat), (22, 3),
        [.query root, .query (expanded 0), .provider 4,
          .query (expanded 1), .provider 5]⟩) 2 := by
  have start := Zkc.Realization.QuerySourceContinuation.Produced.initial
    (interaction := calls) (operations := context.operations (location 20) [])
    (source := parent.body) (initialState := (0, 1)) (initialPhase := 0)
    QuerySourceContinuation.arenas
  have source : parent.body = QuerySourceContinuation.source (anchor 0) 0 := by kernel_rfl
  rw [source, QuerySourceContinuation.source_body] at start
  have first := start.resume (slot := 0) (child_return 0 0 11 1 0 10 4) rfl
  have second := first.resume (slot := 1) (child_return 1 11 22 2 1 20 5) rfl
  rw [← QuerySourceContinuation.source_body, ← source] at second
  exact context.completed (location 20) [] (by decide) (by decide) (by decide)
    calls (0, 0) (22, 3) 0 2 QuerySourceContinuation.arenas [0, 1] (20 : Nat) _ second

/-- The original query is still charged when its body stops after the first
child. Its event precedes the reached child and provider events. -/
theorem stopped_parent (reason : PIR.Stop) :
    PIR.Reaches calls (OracleProcess.answer model 1 result.state.entries root (0, 0)) 0
      (.done ⟨.stopped reason, (11, 2),
        [.query root, .query (expanded 0), .provider 4]⟩) 1 := by
  apply context.reached (location 20) [] (by decide) (by decide) (by decide)
    calls (0, 0) 0 1 ⟨.stopped reason, (11, 2), [.query (expanded 0), .provider 4]⟩
  have source : parent.body = QuerySourceContinuation.source (anchor 0) 0 := by kernel_rfl
  rw [source, QuerySourceContinuation.source_body]
  apply OracleProcess.present_stopped (I := oracleReadInterface model.toCarriers)
  change PIR.Reaches calls
    (.call (I := OracleProcess.Interface model Nat Nat) (.inr (expanded 0), 0)
      (fun reply ↦ .done (⟨reply.outcome, (reply.state, 2),
        .query (expanded 0) :: reply.events.map OracleEvent.provider⟩ :
          PIR.Execution (Nat × Nat) (OracleEvent Nat) Nat))) 0 _ 1
  exact .step (P := calls) (.inr (expanded 0), 0) _ 0
    ⟨.stopped reason, 11, [4]⟩ _ _ (.refl _ _)

#print axioms complete_parent
#print axioms stopped_parent
#print axioms recovered
#print axioms later_operations
end Tests.QuerySourceContext

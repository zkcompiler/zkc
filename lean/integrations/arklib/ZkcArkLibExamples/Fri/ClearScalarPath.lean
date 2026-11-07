module

public import ZkcArkLibExamples.Fri.ClearAccess
public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.PathReading

@[expose] public section

/-! The eight sequential scalar requests are charged as eight logical
accesses. A single tree governs their replies on every fixed table, even
after early exposure of a later node by the prover. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ClearScalarPath
open Zkc.Source Zkc.Construction ZkcExamples.Structured ZkcSecurity.Examples
open ZkcSecurity.FiatShamir QueryTree QueryTreeSource OracleComp OracleSpec
open TranscriptCharge (History Table)

private theorem drawSite : FriScalarLoop.site FriScalarLoop.drawSites.draw = Placement.querySite FriScalarQueries.edge := by kernel_rfl
private theorem deliverySite : FriScalarLoop.site FriScalarLoop.drawSites.delivery = Placement.messageSite FriScalarQueries.edge := by kernel_rfl

/-- The original receiver service call at every path prefix asks this
history. The following send records the same value under its delivery
origin. Each index retains its preceding history, including repetitions. -/
theorem sourceStep (handle : Nat) (root : History) (node : Node (Fin 32) 8) (value : Fin 32) :
    let key := encode ClearAccess.segment (root, node)
    let ordinal := (nodePrefix node).length
    let state : Original.State _ := ⟨FriScalarQueries.frames ordinal, key.1⟩
    let after := {state with history := key.1 ++ [.challenge key.2]}
    Original.service (FriScalarQueries.routing .validator handle) state (FriScalarLoop.site FriScalarLoop.drawSites.draw)
      FriScalarLoop.contract (.sampleIndex 32) handle = Original.queryRequest state key.2 (.sampleIndex 32) ∧
    Original.send (FriScalarQueries.routing .validator handle) after .index (FriScalarLoop.site FriScalarLoop.drawSites.delivery)
      FriScalarQueries.context.producer value.val =
        .call (.observe (.message (ClearAccess.segment.deliveryAt ordinal) (.index value.val))) (fun _ ↦
          .done ((), {after with history := key.1 ++ [.challenge key.2, .message
            (ClearAccess.segment.deliveryAt ordinal) (.index value.val)]})) := by
  intro key ordinal state after
  rw [drawSite, deliverySite]
  constructor
  · exact FriScalarQueries.sourceQuery handle root node
  · have routed := (FriScalarQueries.sourceDelivery handle ordinal).2
    have mode : (FriScalarQueries.routing .validator handle).mode = .validator := rfl
    have validator : (FriScalarQueries.routing .validator handle).context.validator = FriScalarQueries.context.validator := rfl
    have frames : after.frames = FriScalarQueries.frames ordinal := rfl
    simp only [Original.send, mode, validator, frames, routed, Domain.Payload.ofValue, Structured.Ty.isHandle,
      ↓reduceDIte, Original.record]
    simp [after, List.append_assoc]

abbrev queries (root : History) := Composition.readPath ClearAccess.segment ClearAccess.request root 8 id

/-- Full trace and reply of the scalar segment in the macro experiment.
The primitive queries are still eight distinct occurrences in the log. -/
theorem reading (root : History) (table : Table) :
    let game := Composition.fullTranslate ClearAccess.segment (queries root)
    evalWithAnswerFn (QueryImpl.ofFn table) game = List.ofFn (ObservedQueries.positions (table (.inl (.inl root)))) ∧
      (tableQueryLog game table).map Sigma.fst = List.replicate 8 (.inl (.inl root)) := by
  intro game
  refine ⟨?_, Composition.readPath_log ClearAccess.segment ClearAccess.request root table 8 id⟩
  exact (Composition.full_table _ _ _).trans
    ((Composition.readPath_table ClearAccess.segment ClearAccess.request root table 8 id).trans
      (ObservedQueries.path_eq_positions _))

/-- If a prover exposes this root first, the subsequent verifier segment
still contributes eight entries and returns the path in that same tree. -/
theorem afterProver {A : Type} (prover : ClearAccess.Program A) (root : A → History) (table : Table) :
    let before := Composition.fullTranslate ClearAccess.segment prover
    let fixed := evalWithAnswerFn (QueryImpl.ofFn table) before
    let game := Composition.fullTranslate ClearAccess.segment (prover >>= fun result ↦ queries (root result))
    evalWithAnswerFn (QueryImpl.ofFn table) game = List.ofFn
        (ObservedQueries.positions (table (.inl (.inl (root fixed))))) ∧
      (tableQueryLog game table).map Sigma.fst =
        (tableQueryLog before table).map Sigma.fst ++ List.replicate 8 (.inl (.inl (root fixed))) := by
  intro before fixed game
  dsimp only [game]
  rw [Composition.fullTranslate_bind, evalWithAnswerFn_bind, tableQueryLog_bind, List.map_append]
  exact ⟨(reading (root fixed) table).1, congrArg (_ ++ ·) (reading (root fixed) table).2⟩

end ZkcSecurity.ArkLib.Fri.ClearScalarPath

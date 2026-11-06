import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Cache
import TestsSecurity.QueryTreeSource

/-! Mixed nominal fields, a different scalar bound, a block request, a fallback scalar key,
suffix-first access, repeats, private draws and separately querying verifier controls. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace TestsSecurity.QueryTreeSourceComposition
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir
open QueryTreeSource QueryTree OracleComp OracleSpec
open QueryTreeSource.Composition
open TestsSecurity.QueryTreeSource
noncomputable section
attribute [local instance] Composition.rawSampler Composition.otherSampler
  Composition.primitiveSampler Composition.macroSampler
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
local instance (p : Prop) : Decidable p := Classical.propDecidable p
abbrev fullSpec := ofFn (Typed.ByLast (@Domain.Raw carriers))

def nominalKey (request : Request) : Domain.History carriers :=
  [.challenge (context.query "heterogeneous" request)]

theorem field_not_scalar (field : String) :
    ¬ ScalarCell (bound := 2) (nominalKey (.draw field)) := by
  rw [show nominalKey (.draw field) =
    ([] : Domain.History carriers) ++ [.challenge (context.query "heterogeneous" (.draw field))]
      from rfl, scalarCell_iff]
  change ¬ some (Request.draw field) = some (Request.sampleIndex 2)
  simp [Request.draw, Request.sampleIndex]

theorem other_bound_not_scalar : ¬ ScalarCell (bound := 2) (nominalKey (.sampleIndex 3)) := by
  rw [show nominalKey (.sampleIndex 3) = ([] : Domain.History carriers) ++
    [.challenge (context.query "heterogeneous" (.sampleIndex 3))] from rfl, scalarCell_iff]
  change ¬ some (Request.sampleIndex 3) = some (Request.sampleIndex 2)
  simp [Request.sampleIndex]

theorem block_not_scalar : ¬ ScalarCell (bound := 2) (nominalKey (.sampleIndices 2 3)) := by
  rw [show nominalKey (.sampleIndices 2 3) = ([] : Domain.History carriers) ++
    [.challenge (context.query "heterogeneous" (.sampleIndices 2 3))] from rfl, scalarCell_iff]
  change ¬ some (Request.sampleIndices 2 3) = some (Request.sampleIndex 2)
  simp [Request.sampleIndices, Request.sampleIndex]

/-- Two nominal fields share the test host carrier but retain different dependent cells. -/
theorem different_fields :
    nominalKey (.draw "first.field") ≠ nominalKey (.draw "second.field") := by
  intro same
  have requests := congrArg (fun history : Domain.History carriers ↦
    history.map (fun event ↦ match event with
      | .challenge origin => origin.request
      | _ => none)) same
  change [some (Request.draw "first.field")] = [some (Request.draw "second.field")] at requests
  simp [Request.draw] at requests

theorem field_route (field : String) :
    (fullRenaming (bound := 2) (height := 3) segment).cell (nominalKey (.draw field)) =
      some (.inr ⟨nominalKey (.draw field), field_not_scalar field⟩) :=
  fullRenaming_other (height := 3) segment
    ⟨nominalKey (.draw field), field_not_scalar field⟩

theorem other_bound_route :
    (fullRenaming (bound := 2) (height := 3) segment).cell (nominalKey (.sampleIndex 3)) =
      some (.inr ⟨nominalKey (.sampleIndex 3), other_bound_not_scalar⟩) :=
  fullRenaming_other (height := 3) segment
    ⟨nominalKey (.sampleIndex 3), other_bound_not_scalar⟩

theorem block_route :
    (fullRenaming (bound := 2) (height := 3) segment).cell (nominalKey (.sampleIndices 2 3)) =
      some (.inr ⟨nominalKey (.sampleIndices 2 3), block_not_scalar⟩) :=
  fullRenaming_other (height := 3) segment
    ⟨nominalKey (.sampleIndices 2 3), block_not_scalar⟩

theorem suffix_route (history : Domain.History carriers) :
    (fullRenaming (bound := 2) (height := 3) segment).cell
      (oracleKey (key history (suffixNode 1 0)).val) =
      some (.inl (.inl history, .inl (suffixNode 1 0))) := by
  rw [fullRenaming_scalar, located_key]

theorem fallback_route :
    (fullRenaming (bound := 2) (height := 3) segment).cell (oracleKey outside.val) =
      some (.inl (.inr outside, .inr ())) := by
  rw [fullRenaming_scalar, outside_preserved]

def mixed (history : Domain.History carriers) : OracleComp fullSpec Unit := do
  let _ ← fullSpec.query (oracleKey (key history (suffixNode 1 0)).val)
  let _ ← fullSpec.query (nominalKey (.draw "first.field"))
  let _ ← fullSpec.query (nominalKey (.draw "second.field"))
  let _ ← fullSpec.query (nominalKey (.sampleIndex 3))
  let _ ← fullSpec.query (nominalKey (.sampleIndices 2 3))
  let _ ← fullSpec.query (oracleKey outside.val)
  let _ ← fullSpec.query (oracleKey (key history (suffixNode 1 0)).val)
  let _ ← fullSpec.query (oracleKey (key history rootNode).val)
  pure ()

theorem mixed_full_logs (history : Domain.History carriers) :
    let observed := (simulateQ loggingOracle (mixed history)).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (fullTranslate (bound := 2) (height := 3) segment observed)).run' ∅ :=
  full_logged segment _

theorem mixed_budget (history : Domain.History carriers) :
    IsTotalQueryBound (mixed history) 8 := by
  simp [mixed, ← bind_pure_comp, isTotalQueryBound_query_bind_iff]
  trivial

theorem mixed_macro_budget (history : Domain.History carriers) :
    IsTotalQueryBound (fullTranslate (bound := 2) (height := 3) segment (mixed history)) 8 :=
  full_budget segment _ _ (mixed_budget history)

def mixedPrivate (history : Domain.History carriers) : OracleComp (unifSpec + fullSpec) Unit := do
  let coin : Fin 2 ← (unifSpec + fullSpec).query (.inl 1)
  let selected := if coin = 0 then history else [.challenge (context.query "private" (.draw "F"))]
  simulateQ (fun input ↦ liftM ((unifSpec + fullSpec).query (.inr input))) (mixed selected)

theorem mixed_private_full_logs (history : Domain.History carriers) :
    let observed := logPrivate (mixedPrivate history)
    (simulateQ (unifSpec.passthrough + randomOracle) observed).run' ∅ =ᵈ
      (do let fixed ← Composition.privatePrograms observed
          (simulateQ randomOracle (fullTranslate (bound := 2) (height := 3)
            segment fixed)).run' ∅) := full_interleaved_logged segment _

def separateVerifier (history : Domain.History carriers) (_ : Unit) : OracleComp fullSpec Unit := do
  let _ ← fullSpec.query (nominalKey (.draw "verifier.field"))
  let _ ← fullSpec.query (oracleKey (key history rootNode).val)
  pure ()

theorem separate_verifier_shared_cache (history : Domain.History carriers) :
    (simulateQ randomOracle (mixed history >>= separateVerifier history)).run' ∅ =ᵈ
      (simulateQ randomOracle
        (fullTranslate (bound := 2) (height := 3) segment (mixed history) >>=
          fun result ↦ fullTranslate segment (separateVerifier history result))).run' ∅ :=
  full_withVerifier_exact segment _ _

theorem prover_and_verifier_budget (history : Domain.History carriers) :
    IsTotalQueryBound (fullTranslate (bound := 2) (height := 3) segment
      (mixed history >>= separateVerifier history)) 10 := by
  exact full_withVerifier_budget segment _ _ 8 2 (mixed_budget history)
    (fun _ ↦ by
      simp [separateVerifier, ← bind_pure_comp, isTotalQueryBound_query_bind_iff]
      trivial)

/-- The complete typed oracle's cached scalar request cannot be used as an always-fresh
ScalarDrawLaw. This is a kernel-checked obstruction at the existing semantic interface. -/
theorem cached_source_cannot_be_fresh (cache : fullSpec.QueryCache)
    (value : fullSpec.Range (nominalKey (.sampleIndex 2)))
    (hit : cache (nominalKey (.sampleIndex 2)) = some value) :
    ¬ (randomOracle (nominalKey (.sampleIndex 2))).run' cache =ᵈ
      ($ᵗ fullSpec.Range (nominalKey (.sampleIndex 2))) := by
  apply cached_not_fresh cache _ value hit
  change 1 < Nat.card (Fin 2)
  simp

/-- Every other dependent answer survives a scalar root allocation in the shared cache. -/
theorem other_cache_retained (cache : (ofFn (fullRange carriers 2 3)).QueryCache)
    (root : Root carriers 2) (tree : Coordinate 2 3 → Fin 2)
    (other : OtherKey carriers 2) :
    (cache.cacheQuery (.inl root) tree) (.inr other) = cache (.inr other) :=
  scalar_cache_preserves_other cache root tree other

/-- A verifier occurrence is logged after a prover root allocation, without resampling. -/
theorem verifier_log_after_prover (history : Domain.History carriers)
    (tree : Coordinate 2 3 → Fin 2) :
    ((randomOracle.withLogging (.inl (.inl history))).run).run
      ((∅ : (ofFn (fullRange carriers 2 3)).QueryCache).cacheQuery (.inl (.inl history)) tree) =
      pure ((tree, [⟨.inl (.inl history), tree⟩]),
        (∅ : (ofFn (fullRange carriers 2 3)).QueryCache).cacheQuery (.inl (.inl history)) tree) :=
  verifier_cached_logged _ history tree (QueryCache.cacheQuery_self _ _ _)

end
end TestsSecurity.QueryTreeSourceComposition

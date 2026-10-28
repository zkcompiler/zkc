module

public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionRouteCoverageSupport

@[expose] public section

/-! Physical-frame witnesses used only to establish source presence and full
nominal return readback. No target success or helper result equation is assumed. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRouteCoverage
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionComputation

/-- The full source-owned output row, including all absent/private components. -/
def ReadReturns (model : DomainModel) (role : Nat) (scopes : List (List Nat))
    (outputs : List Original.Location) {types : List Ty}
    (values : Values (Component model.Value) types) : Prop :=
  ∃ frame : Domain.Environment model.toCarriers,
    Original.ValuesHolds frame outputs (maskValues role scopes values)

theorem data_of_encode {model : DomainModel} {ty : Ty} {value : model.Value ty}
    {physical : Domain.Value model.toCarriers} (encoded : Domain.Value.encode ty value = some physical) :
    ty.isService = false := by
  unfold Domain.Value.encode Domain.Payload.ofValue at encoded
  split at encoded
  · assumption
  · simp at encoded

theorem CoordinatePrefix.realize {scope : Scope} {input output : Layout scope}
    {target : ConnectionCertificate.Block} (certificate : CoordinatePrefix input output target)
    {model : DomainModel} {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history input environment) :
    ∃ frame, Holds model binders history output frame := by
  induction certificate generalizing environment with
  | empty => exact ⟨environment, related⟩
  | indicesEmpty tail ih => exact ih related.indicesEmpty
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    exact ih (related.indicesAppend coordinates index).2

theorem CoordinatePrefix.realizeRetained {scope : Scope} {input output : Layout scope}
    {target : ConnectionCertificate.Block} (certificate : CoordinatePrefix input output target)
    {model : DomainModel} {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history input environment) :
    ∃ frame, Holds model binders history output frame ∧ ArtifactBinding.Captures environment frame := by
  induction certificate generalizing environment with
  | empty => exact ⟨environment, related, by simp [ArtifactBinding.Captures]⟩
  | indicesEmpty tail ih =>
    obtain ⟨frame, related, retained⟩ := ih related.indicesEmpty
    exact ⟨frame, related, ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) retained⟩
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    obtain ⟨frame, related, retained⟩ := ih (related.indicesAppend coordinates index).2
    exact ⟨frame, related, ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) retained⟩

theorem frames_cons {model : DomainModel} {scope : Scope} {slot : Slot}
    (frames : ScopedFrames scope) (binders : Binders model scope) (value : Slot.Value model slot) :
    (frames.rename (target := slot :: scope) .there).eval model (.cons value binders) =
      frames.eval model binders :=
  ScopedFrames.eval_rename (target := slot :: scope) .there binders (.cons value binders) (fun _ => rfl) frames

/-- Coverage needs a physical witness of presence, not a transcript execution.
The suite and complete physical prefix still come from the finite layout. -/
theorem observed_frame {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history layout environment)
    (suite : String) : Holds model binders history (observedLayout layout suite)
      (environment ++ [.transcript suite history]) :=
  (related.retireHistory history).append (.cons rfl .nil)

theorem query_frame {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers} (related : Holds model binders history layout environment)
    (field suite : String) (value : model.Value (.field field)) :
    Holds model (.cons value binders) history (queryLayout layout field suite)
      (environment ++ [.data (.field field value), .transcript suite history]) := by
  exact ((related.retireHistory history).rename .there (fun _ => rfl)).append
    (.cons ⟨value, rfl, rfl⟩ (.cons rfl .nil))

end Zkc.Construction.ConnectionRouteCoverage

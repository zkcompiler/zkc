module

public import Zkc.Construction.ConnectionCoordinates
public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! Finite coordinate preparation between an action and its observation.
Compiler exports may build the ordered coordinate vector after receiving or
sending a value. These steps preserve the source state and every existing
physical cell, with all actual checkpoints retained by the simulation.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFrame
open Zkc.Source Zkc.Source.Structured NormalForm

/-- A finite structural certificate, with no semantic proof callback. The
output frame is fixed by the actual coordinate instructions. -/
inductive CoordinatePrefix {scope : Scope} : Layout scope → Layout scope →
    ((model : DomainModel) → Domain.View.Block model.toCarriers) → Type 1 where
  | empty (layout : Layout scope) : CoordinatePrefix layout layout (fun _ => Domain.View.empty)
  | indicesEmpty {input output : Layout scope}
      {rest : (model : DomainModel) → Domain.View.Block model.toCarriers}
      (tail : CoordinatePrefix (input ++ [.coordinates []]) output rest) :
      CoordinatePrefix input output (fun model => Domain.View.sequence
        (Domain.View.indicesEmpty [.indices]) (rest model))
  | indicesAppend {input output : Layout scope}
      {rest : (model : DomainModel) → Domain.View.Block model.toCarriers}
      (terms : List (Term [] scope .index)) (term : Term [] scope .index)
      (coordinateRef indexRef : Nat)
      (coordinates : input[coordinateRef]? = some (.coordinates terms))
      (index : input[indexRef]? = some (.data (.present term)))
      (tail : CoordinatePrefix (input ++ [.coordinates (terms ++ [term])]) output rest) :
      CoordinatePrefix input output (fun model => Domain.View.sequence
        (Domain.View.indicesAppend coordinateRef indexRef [.indices]) (rest model))

/-- Splice coordinate preparation into an existing target suffix. This keeps
exactly the compiler's checkpoints, including when the prefix is empty. -/
def CoordinatePrefix.prepend {scope : Scope} {input output : Layout scope}
    {target : (model : DomainModel) → Domain.View.Block model.toCarriers}
    (certificate : CoordinatePrefix input output target)
    (suffix : (model : DomainModel) → Domain.View.Block model.toCarriers) :
    (model : DomainModel) → Domain.View.Block model.toCarriers :=
  match certificate with
  | .empty _ => suffix
  | .indicesEmpty tail => fun model => Domain.View.sequence
      (Domain.View.indicesEmpty [.indices]) (tail.prepend suffix model)
  | .indicesAppend _ _ coordinateRef indexRef _ _ tail => fun model => Domain.View.sequence
      (Domain.View.indicesAppend coordinateRef indexRef [.indices]) (tail.prepend suffix model)

theorem CoordinatePrefix.prepend_eq {scope : Scope} {input output : Layout scope}
    {target : (model : DomainModel) → Domain.View.Block model.toCarriers}
    (certificate : CoordinatePrefix input output target)
    (suffix : (model : DomainModel) → Domain.View.Block model.toCarriers)
    (model : DomainModel) (environment : Domain.Environment model.toCarriers) :
    certificate.prepend suffix model environment = (target model environment).bind (suffix model) := by
  induction certificate generalizing environment with
  | empty => rfl
  | indicesEmpty tail ih =>
    simp only [prepend, Domain.View.sequence, Domain.View.indicesEmpty,
      Domain.View.append, Domain.sortsMatch, PIR.Process.bind, PIR.Process.bind_assoc, ih]
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    simp only [prepend, Domain.View.sequence, PIR.Process.bind, PIR.Process.bind_assoc, ih]

/-- A coordinate prefix can precede any source/target continuation. The source
has not advanced, and the caller receives the checked final frame. The live
condition covers every physical checkpoint, rather than deleting the prefix. -/
@[no_expose] noncomputable def CoordinatePrefix.simulation
    {scope : Scope} {input output : Layout scope}
    {target : (model : DomainModel) → Domain.View.Block model.toCarriers}
    (certificate : CoordinatePrefix input output target)
    (model : DomainModel) (binders : Binders model scope) (history : Domain.History model.toCarriers)
    (captured environment : Domain.Environment model.toCarriers)
    (related : Holds model binders history input environment)
    (retained : ArtifactBinding.Captures captured environment)
    {A B : Type} (source : PIR.Process (Domain.effects model.toCarriers) A)
    (next : Domain.Environment model.toCarriers → PIR.Process (Domain.effects model.toCarriers) B)
    (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects model.toCarriers) A → Domain.Environment model.toCarriers → Prop)
    (checkpoints : ∀ frame, ArtifactBinding.Captures captured frame → live source frame)
    (suffix : ∀ frame, Holds model binders history output frame → ArtifactBinding.Captures captured frame →
      Original.Simulation returns live source (next frame)) :
    Original.Simulation returns live source ((target model environment).bind next) := by
  induction certificate generalizing environment with
  | empty => exact suffix environment related retained
  | indicesEmpty tail ih =>
    have kept := ArtifactBinding.captures_trans retained
      (ArtifactBinding.captures_append environment [.indices []])
    apply Original.Simulation.checkpoint environment (checkpoints _ retained)
    simp only [Domain.View.indicesEmpty, Domain.View.append, Domain.sortsMatch,
      List.map_cons, List.map_nil, Domain.Value.sort, beq_self_eq_true, ↓reduceIte, PIR.Process.bind]
    exact .checkpoint _ (checkpoints _ kept) (ih _ related.indicesEmpty kept suffix)
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    obtain ⟨step, extended⟩ := related.indicesAppend coordinates index
    have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
      [.indices ((terms ++ [term]).map fun value => value.eval (LawResults.empty model) binders)])
    apply Original.Simulation.checkpoint environment (checkpoints _ retained)
    rw [step]
    exact .checkpoint _ (checkpoints _ kept) (ih _ extended kept suffix)

end Zkc.Construction.ConnectionFrame

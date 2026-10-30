module

public import Zkc.Obligations.Assembly
public import ZkcSecurity.Bindings.Sumcheck.OriginalRawSoundness

public section

/-! The raw-table root is a component in its own right. Its input No side
includes malformed shapes, unlike the inner dimension-indexed family. This
boundary does not impose an honest-input policy on adversarial statements.
-/

namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck TableComponent

variable {F G : Type} [Field F] [DecidableEq F]

@[expose] def Correct (raw : List F) (claim : F) (count : Nat) : Prop :=
  raw.length < indexLimit ∧ raw.length = 2 ^ count ∧ claim = raw.sum

structure RootStatement (F : Type) where
  table : List F
  claim : F
  rounds : Nat

@[expose] def rootRelation : ClaimRelation (RootStatement F) Unit :=
  .exact fun statement _ => Correct statement.table statement.claim statement.rounds

@[expose] def acceptanceRelation : ClaimRelation (Option Bool) Unit :=
  .exact fun value _ => value = some true

structure RootInvocation (F G : Type) where
  statement : RootStatement F
  schedule : Nominal.Schedule "bls12-381.fr"
  construction : ConstructionState (F := F) (G := G)

@[expose] noncomputable def rootComponent (maximum : Nat) :
    ComponentInterface (NominalField.signature F "bls12-381.fr")
      (Domain.Event (uniformCarriers F G)) (RootInvocation F G) (Result (F := F) (G := G)) where
  Parameters := Unit
  Input := RootStatement F
  InputWitness := Unit
  Output := Option Bool
  OutputWitness := Unit
  input := rootRelation
  output := acceptanceRelation
  body runtime := root maximum runtime.schedule runtime.statement.table runtime.statement.claim
    runtime.statement.rounds runtime.construction
  Scope _ _ _ := True
  inputView _ runtime _ := some runtime.statement
  outputView _ _ _ result := some (acceptance result)

noncomputable def root_soundness
    {charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal}
    [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)]
    (sampling : (Nominal.queriesWithFrame (G := G) "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).ConditionalBound
      (Nominal.layoutWithFrame "bls12-381.fr"
        (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).representation 1 1 charge)
    (maximum : Nat) :
    SoundnessContract (rootComponent (F := F) (G := G) maximum)
      (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge) := by
  intro _ runtime history _ wrong
  have inputNo : ¬ Correct runtime.statement.table runtime.statement.claim runtime.statement.rounds := by
    have no := ReadbackHolds.some.mp wrong
    exact fun correct => no ⟨(), correct⟩
  have rejected := root_rejected sampling maximum runtime.schedule runtime.statement.table
    runtime.statement.claim runtime.statement.rounds runtime.construction history
    (fun bounded shape equal => inputNo ⟨bounded, shape, equal⟩)
  exact rejected.consequence fun _ result refused =>
    ⟨acceptance result, rfl, by rintro ⟨_, accepted⟩; exact refused accepted⟩

/-- Captured construction frames survive every returned execution, independently
of whether the input sum is true, false or outside the inner family's shape. -/
theorem root_returns (interaction : PIR.Interaction (NominalField.signature F "bls12-381.fr"))
    (phase : interaction.Phase) (maximum : Nat) (runtime : RootInvocation F G) :
    PIR.Boundary.Returns interaction
      (fun result _ => result.2.frames = runtime.construction.frames)
      ((rootComponent maximum).body runtime) phase := by
  change PIR.Boundary.Returns _ _ (root maximum _ _ _ _ _) _
  unfold root
  split
  · apply PIR.Boundary.returns_bind interaction _ _ (fun _ _ => True) _ phase
      (PIR.Boundary.returns_true interaction _ _)
    intro _ reached _
    apply PIR.Boundary.returns_bind interaction _ _ (fun _ _ => True) _ reached
      (PIR.Boundary.returns_true interaction _ _)
    intro _ _ _
    rfl
  · trivial

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw

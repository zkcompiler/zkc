module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheck

@[expose] public section

/-! The selected ideal challenge is uniform in the actual octic carrier.
Nominal message decoding and occurrence histories use the existing Domain
interface unchanged. The coefficient field's characteristic is not the sample
space cardinality. Native byte sampling is outside this source-model client. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity randomService)
open ZkcSecurity.Domains.KoalaBear (Octic q)
open ZkcSecurity.Families.Sumcheck

abbrev finite (identity : String) : Fintype (model.Field identity) := by
  change Fintype (ZkcSecurity.Domains.KoalaBearModel.carrier
    (ZkcSecurity.Domains.KoalaBearModel.resolve identity))
  cases ZkcSecurity.Domains.KoalaBearModel.resolve identity <;>
    dsimp [ZkcSecurity.Domains.KoalaBearModel.carrier] <;> infer_instance

abbrev sampleable (identity : String) : SampleableType (model.Field identity) := by
  letI := finite identity
  letI := model.fieldRing identity
  exact SampleableType.ofFintype _

abbrev rawSampleable : (event : Domain.Event model.toCarriers) → SampleableType (Domain.Raw event)
  | .challenge origin => by
    cases origin with
    | mk entry event request =>
      cases request with
      | none => exact inferInstanceAs (SampleableType Unit)
      | some request =>
        cases request with
        | mk method parameters sort =>
          cases sort
          case field identity => exact sampleable identity
          all_goals exact inferInstanceAs (SampleableType Unit)
  | .message .. | .publicBinding .. => inferInstanceAs (SampleableType Unit)

local instance : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event) := rawSampleable
local instance : SampleableType Octic := sampleable octicIdentity

def context : Zkc.Construction.Context :=
  .fiatShamir KoalaBearSumcheckSource.program.snapshot.entry
    KoalaBearSumcheckSource.program.payload.entry.roles 0 1 3 randomService
    (some (.draw octicIdentity)) "merlin3.koala-bear.ext8-binomial3.rejection31le/0"
    [((KoalaBearSumcheckSource.site "label_6368616c6c656e6765"), (KoalaBearSumcheckSource.site "label_64656c6976657279_0"))]

def absorb := Domain.interface (carriers := model.toCarriers) context

variable {Frame : Type}

def queries : QueryInterface (program (Frame := Frame)) absorb where
  event _ _ _ := .challenge (context.query (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") (.draw octicIdentity))
  decode _ _ _ raw := some raw
  challenge _ _ _ raw := raw
  absorbed _ _ _ := rfl
  decoded _ _ _ _ _ same := (Option.some.inj same).symm

/-- The exact decoder pushforward, at every reached history and with arbitrary
attacker endpoints fixed before the draw. -/
theorem sampling : queries.ConditionalBound (representation (Frame := Frame)) 1 1
    (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal)) := by
  intro n
  have uniform := (queries (Frame := Frame)).conditional_of_uniform representation 1 1
    (fun _ _ _ _ => rfl) (n := n)
  simpa only [max_self, Nat.cast_one, ZkcSecurity.Domains.KoalaBear.card_octic] using uniform

def octic_soundness (n : Nat) :
    Zkc.Obligations.SoundnessContract
      (Contract.component (representation (Frame := Frame)) n 1 actual) absorb
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => 1 / ((q ^ 8 : Nat) : ENNReal))) :=
  soundness absorb queries _ sampling n

theorem challenge_cardinality : Fintype.card Octic = q ^ 8 :=
  ZkcSecurity.Domains.KoalaBear.card_octic

/-- A base-field denominator is a different bound, even though both fields
have characteristic q. It cannot be substituted as the selected exact charge. -/
theorem wrong_denominator : (1 : ENNReal) / ((q ^ 8 : Nat) : ENNReal) ≠ 1 / (q : ENNReal) := by
  norm_num [q]

end ZkcSecurity.Examples.Components.KoalaBearSumcheck

module

public import ZkcSecurity.Claims.Subject
public import ZkcSecurity.Claims.Model

@[expose] public section

/-! Fixed soundness meanings over actual admitted compiled artifacts. Scalar
bounds need no reduction export. Charged requests additionally require the
certificate and validator cost at exactly their declared charges. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] {art : Artifacts} {endpoint : Semantics}

structure ChargeSchedule (subject : Subject F G art endpoint) where
  entries : List (Site subject.compiled.context × Bound)
  nonempty : entries ≠ []
  unique : (entries.map (fun entry => entry.1.label)).Nodup
  nativeUnique : (entries.map (fun entry => entry.1.native)).Nodup

noncomputable def ChargeSchedule.maximum {subject : Subject F G art endpoint}
    (schedule : ChargeSchedule subject) (queries : Nat) : ENNReal :=
  (schedule.entries.map (fun entry => entry.2.value queries)).foldr max 0

/-- The version-zero model charges malformed/unmapped oracle keys at the
maximum declared price. At a selected occurrence it uses that site's price.
This also gives uniform-charge families their original all-key bounds. -/
noncomputable def ChargeSchedule.charge {subject : Subject F G art endpoint}
    (schedule : ChargeSchedule subject) (queries : Nat) (_history : History F G) (event : Event F G) : ENNReal :=
  match schedule.entries.find? (fun entry => entry.1.event == event) with
  | some entry => entry.2.value queries
  | none => schedule.maximum queries

private theorem member_le_maximum (values : List ENNReal) (value : ENNReal) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact le_max_left _ _
    · exact (ih member).trans (le_max_right _ _)

omit [SampleableType F] in
theorem ChargeSchedule.charge_le_maximum {subject : Subject F G art endpoint}
    (schedule : ChargeSchedule subject) (queries : Nat) (history : History F G) (event : Event F G) :
    schedule.charge queries history event ≤ schedule.maximum queries := by
  unfold charge
  split
  next entry selected =>
    apply member_le_maximum
    exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some selected, rfl⟩
  next => exact le_rfl

/-- This export states the reduction at precisely the requested prices. A cost
proof for smaller family prices cannot fill `costBound`. -/
structure ChargedExport (subject : Subject F G art endpoint) (schedule : ChargeSchedule subject)
    (queries : Nat) (validatorCost : ENNReal) where
  certificate : Typed.ChargedCertificate (interface (G := G) subject.compiled.context id)
    (· = some true) (schedule.charge queries)
  handle : Nat
  doomed : ∀ statement, subject.falseStatement statement → ∀ initial,
    certificate.doomed initial (subject.compiled.original statement handle)
  costBound : ∀ statement initial, Typed.ChargedCostBound (interface (G := G) subject.compiled.context id)
    (schedule.charge queries) (subject.compiled.original statement handle) initial validatorCost

namespace Subject

abbrev verify (subject : Subject F G art endpoint) := subject.compiled.verifier ((Regime.exact F).challenge (G := G))

abbrev validate (subject : Subject F G art .executableBytes) :=
  (subject.lowering : LoweringEvidence art subject.compiled F G).validate ((Regime.exact F).challenge (G := G))

end Subject

def FixedIdeal (subject : Subject F G art .idealMeaning) (model : Model) (error : Nat → ENNReal) : Prop :=
  ∀ statement, subject.falseStatement statement → ∀ initial
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (Proof F G)) (queries : Nat),
    model.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let result ← (simulateQ randomOracle (prover >>= subject.verify statement initial)).run' ∅}[
      Zkc.Transcript.Accepted (· = some true) result.1] ≤ error queries

def AdaptiveIdeal (subject : Subject F G art .idealMeaning) (model : Model) (error : Nat → ENNReal) : Prop :=
  ∀ (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (art.Statement F G × Proof F G)) (queries : Nat),
    model.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun result => (claimed.1, result)) <$> subject.verify claimed.1
        ((policyCodec art.publics model.application).encode claimed.1) claimed.2)).run' ∅}[
      subject.falseStatement result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1] ≤ error queries

def FixedBytes (subject : Subject F G art .executableBytes) (model : Model) (error : Nat → ENNReal) : Prop :=
  ∀ codec budget binding statement, subject.falseStatement statement → ∀ initial
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (List UInt8)) (queries : Nat),
    model.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let accepted ← (simulateQ randomOracle
      (prover >>= subject.validate codec budget binding statement initial)).run' ∅}[accepted = true] ≤ error queries

def AdaptiveBytes (subject : Subject F G art .executableBytes) (model : Model) (error : Nat → ENNReal) : Prop :=
  ∀ codec budget binding (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (art.Statement F G × List UInt8)) (queries : Nat),
    model.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun accepted => (claimed.1, accepted)) <$> subject.validate codec budget binding claimed.1
        ((policyCodec art.publics model.application).encode claimed.1) claimed.2)).run' ∅}[
      subject.falseStatement result.1 ∧ result.2 = true] ≤ error queries

def Ordinary (subject : Subject F G art endpoint) (model : Model) (error : Nat → ENNReal) : Prop :=
  match endpoint, model.form with
  | .idealMeaning, .fixed => FixedIdeal subject model error
  | .idealMeaning, .adaptive => AdaptiveIdeal subject model error
  | .executableBytes, .fixed => FixedBytes subject model error
  | .executableBytes, .adaptive => AdaptiveBytes subject model error

/-- Weighted ordinary bounds retain the full endpoint budget strength, using
exactly the requested prices. The natural model symbol may parameterize them. -/
def WeightedFixedIdeal (subject : Subject F G art .idealMeaning) (model : Model)
    (schedule : ChargeSchedule subject) : Prop :=
  ∀ queries, model.queries.allows queries → ∀ statement, subject.falseStatement statement → ∀ initial
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (Proof F G)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let result ← (simulateQ randomOracle (prover >>= subject.verify statement initial)).run' ∅}[
      Zkc.Transcript.Accepted (· = some true) result.1] ≤ cost + model.validatorCost.value queries

def WeightedAdaptiveIdeal (subject : Subject F G art .idealMeaning) (model : Model)
    (schedule : ChargeSchedule subject) : Prop :=
  ∀ queries, model.queries.allows queries →
    ∀ (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (art.Statement F G × Proof F G)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun result => (claimed.1, result)) <$> subject.verify claimed.1
        ((policyCodec art.publics model.application).encode claimed.1) claimed.2)).run' ∅}[
      subject.falseStatement result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1] ≤
        cost + model.validatorCost.value queries

def WeightedFixedBytes (subject : Subject F G art .executableBytes) (model : Model)
    (schedule : ChargeSchedule subject) : Prop :=
  ∀ queries, model.queries.allows queries → ∀ codec budget binding statement,
    subject.falseStatement statement → ∀ initial
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (List UInt8)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let accepted ← (simulateQ randomOracle
      (prover >>= subject.validate codec budget binding statement initial)).run' ∅}[accepted = true] ≤
        cost + model.validatorCost.value queries

def WeightedAdaptiveBytes (subject : Subject F G art .executableBytes) (model : Model)
    (schedule : ChargeSchedule subject) : Prop :=
  ∀ queries, model.queries.allows queries → ∀ codec budget binding
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) (art.Statement F G × List UInt8)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun accepted => (claimed.1, accepted)) <$> subject.validate codec budget binding claimed.1
        ((policyCodec art.publics model.application).encode claimed.1) claimed.2)).run' ∅}[
      subject.falseStatement result.1 ∧ result.2 = true] ≤ cost + model.validatorCost.value queries

def WeightedOrdinary (subject : Subject F G art endpoint) (model : Model) (schedule : ChargeSchedule subject) : Prop :=
  match endpoint, model.form with
  | .idealMeaning, .fixed => WeightedFixedIdeal subject model schedule
  | .idealMeaning, .adaptive => WeightedAdaptiveIdeal subject model schedule
  | .executableBytes, .fixed => WeightedFixedBytes subject model schedule
  | .executableBytes, .adaptive => WeightedAdaptiveBytes subject model schedule

inductive SoundnessQuantity (subject : Subject F G art endpoint) where
  | scalar (error : Bound)
  | charged (schedule : ChargeSchedule subject)

structure SoundnessRequest (subject : Subject F G art endpoint) where
  model : Model
  quantity : SoundnessQuantity subject

/-- The definitional request meaning. Neither a family, a false predicate nor a
cost function is an argument supplied by evidence. -/
noncomputable def SoundnessRequest.meaning {subject : Subject F G art endpoint}
    (request : SoundnessRequest subject) : Prop :=
  match request.quantity with
  | .scalar error => Ordinary subject request.model error.value
  | .charged schedule =>
      WeightedOrdinary subject request.model schedule ∧
      ∀ queries, request.model.queries.allows queries →
        Nonempty (ChargedExport subject schedule queries (request.model.validatorCost.value queries))

end
end ZkcSecurity.Claims

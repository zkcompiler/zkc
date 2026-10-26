module

public import ZkcSecurity.Claims.DomainSoundness
public import ZkcSecurity.FiatShamir.DomainAdaptive
public import ZkcSecurity.FiatShamir.DomainBinding
public import ZkcSecurity.Obligations.Derivation

@[expose] public section
noncomputable section

/-! Shared assembly of actual compiled validator soundness. Source adapters
supply the exact participant bridge and mathematical rejection derivation;
this library installs the same charged certificate and adaptive ROM experiment.
No source-specific statement constructor, site path or validator is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Claims.CompiledSoundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open OracleComp OracleSpec

variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
  {subject : Claims.Domain.Subject model art}

/-- Equal declared prices preserve the actual site classifier, including the
maximum declared price for unknown adversary keys. -/
theorem charge_constant (schedule : Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (value : ENNReal)
    (allPrices : ∀ entry ∈ schedule.entries, entry.2.value queries = value) :
    schedule.charge queries = fun _ _ => value := by
  have folded : ∀ entries : List (Claims.Domain.ChargeSite subject.compiled × Claims.Bound),
      entries ≠ [] → (∀ entry ∈ entries, entry.2.value queries = value) →
      (entries.map (fun entry => entry.2.value queries)).foldr max 0 = value := by
    intro entries
    induction entries with
    | nil => simp
    | cons first rest ih =>
      intro nonempty prices
      cases rest with
      | nil => simp [prices first (by simp)]
      | cons second tail =>
        have tailEq := ih (by simp) (fun entry member => prices entry (List.mem_cons_of_mem _ member))
        change max (first.2.value queries)
          (((second :: tail).map (fun entry => entry.2.value queries)).foldr max 0) = value
        rw [prices first (by simp), tailEq, max_self]
  have maximum : schedule.maximum queries = value := folded schedule.entries schedule.nonempty allPrices
  funext history event
  unfold Claims.Domain.ChargeSchedule.charge
  cases event <;> try exact maximum
  rename_i origin
  dsimp only
  cases found : schedule.entries.find? (fun entry => entry.1.matches origin) with
  | none => exact maximum
  | some entry => exact allPrices entry (List.mem_of_find?_eq_some found)

/-- Assign one declared price to every source-selected actual charge site.
Site discovery and its source labels remain owned by the generated Subject. -/
def uniformSchedule (subject : Claims.Domain.Subject model art) (price : Claims.Bound)
    (nonempty : subject.sites ≠ [])
    (unique : (subject.sites.map (·.label)).Nodup)
    (nativeUnique : (subject.sites.map (·.native)).Nodup) : Claims.Domain.ChargeSchedule subject where
  entries := subject.sites.map (fun site => (site, price))
  nonempty := by simpa using nonempty
  unique := by simpa only [List.map_map, Function.comp_def] using unique
  nativeUnique := by simpa only [List.map_map, Function.comp_def] using nativeUnique

theorem uniformSchedule_prices (price : Claims.Bound) (nonempty unique nativeUnique)
    (queries : Nat) :
    ∀ entry ∈ (uniformSchedule subject price nonempty unique nativeUnique).entries,
      entry.2.value queries = price.value queries := by
  intro entry member
  obtain ⟨site, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Exact source connection, independent of truth, shape and query budget. -/
structure Installation (subject : Claims.Domain.Subject model art) where
  signature : PIR.Signature
  absorb : Typed.Interface signature (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw
  inputs : art.Statement model → Domain.Environment model.toCarriers
  encoded : ∀ statement, Domain.encodeValues statement = some (inputs statement)
  presented : art.Statement model → Domain.History model.toCarriers → PIR.Process signature (Domain.Result model.toCarriers)
  bridge : ∀ statement initial, DomainReduction.Bridge absorb (fun _ _ => True) initial
    (Domain.participant model subject.compiled.imported.program subject.compiled.selection.context art.participant
      (inputs statement ++ [.transcript subject.compiled.selection.context.suite initial]))
    (presented statement initial)

/-- All-data public ABIs have one shared nominal encoder. A root supplies
its presentation and exact bridge, without duplicating environment assembly. -/
def Installation.typed
    (signature : PIR.Signature)
    (absorb : Typed.Interface signature (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw)
    (data : art.publics.all Domain.dataType = true)
    (presented : art.Statement model → Domain.History model.toCarriers → PIR.Process signature (Domain.Result model.toCarriers))
    (bridge : ∀ statement initial, DomainReduction.Bridge absorb (fun _ _ => True) initial
      (Domain.participant model subject.compiled.imported.program subject.compiled.selection.context art.participant
        ((Domain.encodeValues statement).getD [] ++ [.transcript subject.compiled.selection.context.suite initial]))
      (presented statement initial)) : Installation subject where
  signature := signature
  absorb := absorb
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := Domain.encodeValues_getD statement data
  presented := presented
  bridge := bridge

variable (installation : Installation subject)
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- One certificate construction for all installed components and sequences. -/
noncomputable def assembled (value cost : ENNReal)
    (rejects : ∀ statement, subject.FalseStatement statement → ∀ initial,
      Zkc.Obligations.Derivation installation.absorb (boundedEscape (fun _ _ => value))
        (fun _ result => subject.compiled.acceptance result ≠ some true)
        initial (installation.presented statement initial))
    (costs : ∀ statement initial, Typed.ChargedCostBound installation.absorb (fun _ _ => value)
      (installation.presented statement initial) initial cost)
    (schedule : Claims.Domain.ChargeSchedule subject) (queries : Nat)
    (prices : ∀ entry ∈ schedule.entries, entry.2.value queries = value) :
    Claims.Domain.ChargedExport subject schedule queries cost where
  signature := installation.signature
  absorb := installation.absorb
  inputs := installation.inputs
  encoded := installation.encoded
  presented := installation.presented
  bridge := installation.bridge
  certificate := (reduction installation.absorb
    (fun _ result => subject.compiled.acceptance result ≠ some true)
    (schedule.charge queries)).toCertificate _ (fun _ _ post => post)
  doomed := by
    intro statement falseStatement initial
    rw [charge_constant schedule queries value prices]
    exact derived_doomed (rejects statement falseStatement initial)
  costBound := by
    intro statement initial
    rw [charge_constant schedule queries value prices]
    exact costs statement initial

noncomputable abbrev binding (subject : Claims.Domain.Subject model art) (application : String) :
    BindingCodec (art.Statement model) (Domain.Event model.toCarriers) :=
  DomainReduction.policyCodec subject.compiled application

/-- Full acceptance includes the absence of unread proof values. -/
noncomputable def probability (subject : Claims.Domain.Subject model art) (application : String)
    [DecidableEq (Domain.Event model.toCarriers)]
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (art.Statement model × Domain.Proof model.toCarriers)) : ENNReal :=
  Pr{let result ← (simulateQ randomOracle
    (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
      subject.compiled.verifier model (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
        ((binding subject application).encode claimed.1) claimed.2)).run' ∅}[
    subject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2]

variable [DecidableEq (Domain.Event model.toCarriers)]

/-- The same actual cache serves all queries before adaptive statement choice
and the subsequent compiled validator execution. -/
theorem adaptive_charged {schedule : Claims.Domain.ChargeSchedule subject} {queries : Nat} {cost : ENNReal}
    (exported : Claims.Domain.ChargedExport subject schedule queries cost)
    (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (art.Statement model × Domain.Proof model.toCarriers))
    (proverCost : ENNReal)
    (bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ proverCost) :
    probability subject application prover ≤ proverCost + cost := by
  exact DomainReduction.Compiled.adaptive_soundness_charged subject.compiled
    (binding subject application).encode exported.inputs
    (fun statement => exported.presented statement ((binding subject application).encode statement))
    exported.encoded (fun statement => exported.bridge statement _)
    (DomainReduction.policyCodec_determined subject.compiled _)
    subject.FalseStatement (exported.certificate.toReduction exported.absorb)
    (fun _ _ post => post) (fun statement falseStatement => exported.doomed statement falseStatement _)
    cost (fun statement => exported.costBound statement _) prover proverCost bounded

/-- Total query budgets count every visit, including repeated cached keys. -/
theorem adaptive {schedule : Claims.Domain.ChargeSchedule subject} {queries : Nat} {cost : ENNReal}
    (exported : Claims.Domain.ChargedExport subject schedule queries cost)
    (value : ENNReal) (prices : ∀ entry ∈ schedule.entries, entry.2.value queries = value)
    (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (art.Statement model × Domain.Proof model.toCarriers))
    (bounded : IsTotalQueryBound prover queries) :
    probability subject application prover ≤ (queries : ENNReal) * value + cost := by
  have priced : ∀ history event, schedule.charge queries history event ≤ value := by
    rw [charge_constant schedule queries value prices]
    exact fun _ _ => le_rfl
  exact adaptive_charged exported application prover _
    (Typed.worstCaseCostBound_of_isTotalQueryBound (Typed.keyCharge (schedule.charge queries))
      (fun key => Typed.keyCharge_le priced key) prover queries bounded)

/-- A uniform per-event field price gives the advertised scalar query bound. -/
theorem adaptive_fraction {schedule : Claims.Domain.ChargeSchedule subject} {queries : Nat}
    (divisor : ENNReal) (budget : Nat)
    (exported : Claims.Domain.ChargedExport subject schedule queries (budget • (1 / divisor)))
    (prices : ∀ entry ∈ schedule.entries, entry.2.value queries = 1 / divisor)
    (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (art.Statement model × Domain.Proof model.toCarriers))
    (bounded : IsTotalQueryBound prover queries) :
    probability subject application prover ≤ ((queries : ENNReal) + budget) / divisor := by
  have result := adaptive exported (1 / divisor) prices application prover bounded
  simpa only [nsmul_eq_mul, div_eq_mul_inv, one_mul, add_mul] using result

end ZkcSecurity.Claims.CompiledSoundness

namespace ZkcSecurity.Claims.CompiledSoundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.FiatShamir
open OracleComp OracleSpec
variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
  {subject : Claims.Domain.Subject model art}
  (capabilities : Claims.Domain.Capabilities model art.original)
local instance : DecidableEq (Domain.Event model.toCarriers) := Classical.decEq _

/-- Canonical scalar specialization of one installed all-statement export. -/
theorem scalar_meaning (schedule : Claims.Domain.ChargeSchedule subject) (divisor : ENNReal)
    (budget : Nat)
    (exports : ∀ queries, @Claims.Domain.ChargedExport model art subject schedule queries (budget • (1 / divisor)) capabilities.samples)
    (prices : ∀ queries entry, entry ∈ schedule.entries → entry.2.value queries = 1 / divisor)
    (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness capabilities subject selected
      (fun queries => ((queries : ENNReal) + budget) / divisor) := by
  classical
  let _ := capabilities.samples
  simp only [Claims.Domain.Soundness, adaptiveForm]
  intro prover queries _ bounded
  have result := adaptive (exports queries) (1 / divisor) (prices queries) selected.application prover bounded
  simpa only [probability, binding, nsmul_eq_mul, div_eq_mul_inv, one_mul, add_mul] using result

/-- Canonical charged meaning retains the exact reduction witness as well as
weighted soundness of the full compiled experiment. -/
theorem charged_meaning (schedule : Claims.Domain.ChargeSchedule subject) (cost : ENNReal)
    (exports : ∀ queries, @Claims.Domain.ChargedExport model art subject schedule queries cost capabilities.samples)
    (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (validatorCost : ∀ queries, selected.validatorCost.value queries = cost) :
    Claims.Domain.SoundnessArguments.meaning capabilities
      (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments subject) := by
  classical
  let _ := capabilities.samples
  unfold Claims.Domain.SoundnessArguments.meaning
  constructor
  · simp only [Claims.Domain.WeightedSoundness, adaptiveForm]
    intro queries _ prover proverCost bounded
    rw [validatorCost queries]
    exact adaptive_charged (exports queries) selected.application prover proverCost bounded
  · intro queries _
    rw [validatorCost queries]
    exact ⟨exports queries⟩
end ZkcSecurity.Claims.CompiledSoundness

module

public import ZkcSecurity.Claims.DomainSoundness
public import ZkcSecurity.Bindings.Transcript.DomainAdaptive
public import ZkcSecurity.Bindings.Transcript.DomainBinding
public import ZkcSecurity.ProgramLogic.Derivation

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

/-- A uniform method needs a nonempty declaration to identify the maximum
with its selected price. The general schedule schema admits no entries. -/
theorem maximum_constant (schedule : Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (value : ENNReal) (nonempty : schedule.entries ≠ [])
    (allPrices : ∀ entry ∈ schedule.entries, entry.2.value queries = value) :
    schedule.maximum queries = value := by
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
  exact folded schedule.entries nonempty allPrices

/-- Uniform pricing preserves the complete native origin classifier. -/
theorem charge_constant (schedule : Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (value : ENNReal) (nonempty : schedule.entries ≠ [])
    (allPrices : ∀ entry ∈ schedule.entries, entry.2.value queries = value) :
    schedule.charge queries = fun _ _ => value := by
  have maximum := maximum_constant schedule queries value nonempty allPrices
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
    (unique : (subject.sites.map (·.label)).Nodup)
    (nativeUnique : (subject.sites.map (·.native)).Nodup) : Claims.Domain.ChargeSchedule subject where
  entries := subject.sites.map (fun site => (site, price))
  unique := by simpa only [List.map_map, Function.comp_def] using unique
  nativeUnique := by simpa only [List.map_map, Function.comp_def] using nativeUnique

theorem uniformSchedule_prices (price : Claims.Bound) (unique nativeUnique)
    (queries : Nat) :
    ∀ entry ∈ (uniformSchedule subject price unique nativeUnique).entries,
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
      (Domain.inputFrame subject.compiled.selection.context (inputs statement) initial))
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
        (Domain.inputFrame subject.compiled.selection.context ((Domain.encodeValues statement).getD []) initial))
      (presented statement initial)) : Installation subject where
  signature := signature
  absorb := absorb
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := Domain.encodeValues_getD statement data
  presented := presented
  bridge := bridge

variable (installation : Installation subject)
variable [∀ event, SampleableType (@Domain.Raw model.toCarriers event)]

/-- Assemble a certificate at the exact supplied schedule. No distribution,
price or syntactic query count is inferred by this consumer. -/
noncomputable def assembled (schedule : Claims.Domain.ChargeSchedule subject)
    (queries : Nat) (cost : ENNReal)
    (rejects : ∀ statement, subject.FalseStatement statement → ∀ initial,
      Zkc.Obligations.Derivation installation.absorb (boundedEscape (schedule.charge queries))
        (fun _ result => subject.compiled.acceptance result ≠ some true)
        initial (installation.presented statement initial))
    (costs : ∀ statement initial, Typed.ChargedCostBound installation.absorb (schedule.charge queries)
      (installation.presented statement initial) initial cost) :
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
  doomed statement falseStatement initial := derived_doomed (rejects statement falseStatement initial)
  costBound := costs

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

/-- Total query budgets count every visit, including repeated cached keys.
The maximum comes from the checked schedule and can depend on the query bound. -/
theorem adaptive {schedule : Claims.Domain.ChargeSchedule subject} {queries : Nat} {cost : ENNReal}
    (exported : Claims.Domain.ChargedExport subject schedule queries cost)
    (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers) (art.Statement model × Domain.Proof model.toCarriers))
    (bounded : IsTotalQueryBound prover queries) :
    probability subject application prover ≤ (queries : ENNReal) * schedule.maximum queries + cost := by
  exact adaptive_charged exported application prover _
    (Typed.worstCaseCostBound_of_isTotalQueryBound (Typed.keyCharge (schedule.charge queries))
      (fun key => Typed.keyCharge_le (schedule.charge_le_maximum queries) key) prover queries bounded)

end ZkcSecurity.Claims.CompiledSoundness

namespace ZkcSecurity.Claims.CompiledSoundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.FiatShamir
open OracleComp OracleSpec
variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
  {subject : Claims.Domain.Subject model art}
  (capabilities : Claims.Domain.Capabilities model art.original)
local instance : DecidableEq (Domain.Event model.toCarriers) := Classical.decEq _

/-- Scalar output requires a checked conversion from the schedule maximum
and the query-dependent validator cost to the selected error function. -/
theorem scalar_meaning (schedule : Claims.Domain.ChargeSchedule subject)
    (cost error : Nat → ENNReal)
    (exports : ∀ queries, @Claims.Domain.ChargedExport model art subject schedule queries (cost queries) capabilities.samples)
    (bound : ∀ (queries : Nat), (queries : ENNReal) * schedule.maximum queries + cost queries ≤ error queries)
    (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness capabilities subject selected error := by
  classical
  let _ := capabilities.samples
  simp only [Claims.Domain.Soundness, adaptiveForm]
  intro prover queries _ bounded
  exact (adaptive (exports queries) selected.application prover bounded).trans (bound queries)

/-- Canonical charged meaning retains the exact reduction witness as well as
weighted soundness of the full compiled experiment. -/
theorem charged_meaning (schedule : Claims.Domain.ChargeSchedule subject) (cost : Nat → ENNReal)
    (exports : ∀ queries, @Claims.Domain.ChargedExport model art subject schedule queries (cost queries) capabilities.samples)
    (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (validatorCost : ∀ queries, selected.validatorCost.value queries = cost queries) :
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

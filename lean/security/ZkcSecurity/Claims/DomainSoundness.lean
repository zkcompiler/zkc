module

public import ZkcSecurity.Claims.DomainModel
public import ZkcSecurity.FiatShamir.HonestCompiled
public import ZkcSecurity.FiatShamir.DomainBinding
public import ZkcSecurity.FiatShamir.DomainReduction

@[expose] public section

/-! Compiled-ideal soundness over the actual dependent verifier. Adaptive
statements are chosen after oracle queries and bound with the typed public
codec. Charged quantities retain the requested prices and require an existing
typed reduction at exactly those prices. Knowledge and bytes are unsupported. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.Domain
open Zkc.Claims Zkc.Source.Structured Zkc.Construction
open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}

/-- Match the complete nominal origin, including each dynamic coordinate.
Malformed or foreign keys do not match a selected occurrence. -/
def ChargeSite.matches {compiled : ZkcSecurity.Endpoint.Domain.Compiled art}
    (site : ChargeSite compiled) (origin : Origin) : Bool :=
  let template := site.occurrence.template
  let context := compiled.selection.context
  match template.origin context with
  | none => false
  | some base =>
    let suffix := origin.event.drop base.event.length
    let coordinates := if template.repeats = 0 then some [] else
      match suffix with
      | "indices" :: values => values.mapM fun value =>
          Zkc.Source.Format.canonicalDecimal value value.utf8ByteSize
      | _ => none
    match coordinates with
    | none => false
    | some coordinates =>
      Zkc.Construction.Domain.queryOrigin context site.occurrence.suite
        site.occurrence.field template coordinates == some origin

structure ChargeSchedule (subject : Subject model art) where
  entries : List (ChargeSite subject.compiled × Bound)
  unique : (entries.map (fun entry => entry.1.label)).Nodup
  nativeUnique : (entries.map (fun entry => entry.1.native)).Nodup

noncomputable def ChargeSchedule.maximum {subject : Subject model art}
    (schedule : ChargeSchedule subject) (queries : Nat) : ENNReal :=
  (schedule.entries.map (fun entry => entry.2.value queries)).foldr max 0

/-- Empty schedules declare zero cost; rejection still requires a certificate. -/
def ChargeSchedule.empty (subject : Subject model art) : ChargeSchedule subject :=
  ⟨[], by simp, by simp⟩

/-- Unmapped and malformed keys pay the maximum declared price. The complete
key is retained by the oracle; classification selects only its charge. -/
noncomputable def ChargeSchedule.charge {subject : Subject model art}
    (schedule : ChargeSchedule subject) (queries : Nat)
    (_history : Zkc.Construction.Domain.History model.toCarriers)
    (event : Zkc.Construction.Domain.Event model.toCarriers) : ENNReal :=
  match event with
  | .challenge origin =>
    match schedule.entries.find? (fun entry => entry.1.matches origin) with
    | some entry => entry.2.value queries
    | none => schedule.maximum queries
  | _ => schedule.maximum queries

theorem ChargeSchedule.empty_charge (subject : Subject model art) (queries : Nat) :
    (ChargeSchedule.empty subject).charge queries = fun _ _ => 0 := by
  funext history event
  cases event <;> rfl

theorem ChargeSchedule.charge_le_maximum {subject : Subject model art}
    (schedule : ChargeSchedule subject) (queries : Nat)
    (history : Zkc.Construction.Domain.History model.toCarriers)
    (event : Zkc.Construction.Domain.Event model.toCarriers) :
    schedule.charge queries history event ≤ schedule.maximum queries := by
  have memberBound : ∀ entry ∈ schedule.entries,
      entry.2.value queries ≤ schedule.maximum queries := by
    have folded : ∀ (values : List ENNReal) value, value ∈ values → value ≤ values.foldr max 0 := by
      intro values
      induction values with
      | nil => simp
      | cons head rest ih =>
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact le_max_left _ _
        · exact (ih value member).trans (le_max_right _ _)
    intro entry member
    exact folded _ _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
  cases event <;> try exact le_rfl
  rename_i origin
  change (match schedule.entries.find? (fun entry => entry.1.matches origin) with
    | some entry => entry.2.value queries
    | none => schedule.maximum queries) ≤ schedule.maximum queries
  cases found : schedule.entries.find? (fun entry => entry.1.matches origin) with
  | none => exact le_rfl
  | some entry => exact memberBound entry (List.mem_of_find?_eq_some found)

/-- A fixed endpoint reduction obligation. Witness processes/interfaces cannot
change the actual verifier, retained target, complete acceptance, or charges:
the checked bridge relates them to that exact compiled execution. -/
structure ChargedExport (subject : Subject model art) (schedule : ChargeSchedule subject)
    (queries : Nat) (validatorCost : ENNReal)
    [∀ event : Zkc.Construction.Domain.Event model.toCarriers,
      SampleableType (Zkc.Construction.Domain.Raw event)] where
  signature : PIR.Signature
  absorb : Typed.Interface signature (Zkc.Construction.Domain.Event model.toCarriers)
    (Zkc.Construction.Domain.Payload model.toCarriers) Zkc.Construction.Domain.Raw
  inputs : art.Statement model → Zkc.Construction.Domain.Environment model.toCarriers
  encoded : ∀ statement, Zkc.Construction.Domain.encodeValues statement = some (inputs statement)
  presented : art.Statement model → Zkc.Construction.Domain.History model.toCarriers →
    PIR.Process signature (Zkc.Construction.Domain.Result model.toCarriers)
  bridge : ∀ statement initial, DomainReduction.Bridge absorb (fun _ _ => True) initial
    (Zkc.Construction.Domain.participant model subject.compiled.imported.program
      subject.compiled.selection.context art.participant
      (Domain.inputFrame subject.compiled.selection.context (inputs statement) initial))
    (presented statement initial)
  certificate : Typed.ChargedCertificate absorb
    (fun result => subject.compiled.acceptance result = some true) (schedule.charge queries)
  doomed : ∀ statement, subject.FalseStatement statement → ∀ initial,
    certificate.doomed initial (presented statement initial)
  costBound : ∀ statement initial, Typed.ChargedCostBound absorb (schedule.charge queries)
    (presented statement initial) initial validatorCost

noncomputable def FixedSoundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (error : Nat → ENNReal) : Prop := by
  classical
  letI := capabilities.samples
  exact ∀ statement, subject.FalseStatement statement → ∀ initial
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (Zkc.Construction.Domain.Proof model.toCarriers)) (queries : Nat),
    selected.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let result ← (simulateQ randomOracle
      (prover >>= subject.compiled.verifier model
        (Typed.ask (R := Typed.ByLast Zkc.Construction.Domain.Raw))
        statement initial)).run' ∅}[ZkcSecurity.Endpoint.Domain.CompleteAccepted result] ≤ error queries

noncomputable def AdaptiveSoundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (error : Nat → ENNReal) : Prop := by
  classical
  letI := capabilities.samples
  exact ∀ (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (art.Statement model × Zkc.Construction.Domain.Proof model.toCarriers)) (queries : Nat),
    selected.queries.allows queries → IsTotalQueryBound prover queries →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun result => (claimed.1, result)) <$> subject.compiled.verifier model
        (Typed.ask (R := Typed.ByLast Zkc.Construction.Domain.Raw)) claimed.1
        ((DomainReduction.policyCodec subject.compiled selected.application).encode claimed.1)
        claimed.2)).run' ∅}[
      subject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤ error queries

noncomputable def Soundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (error : Nat → ENNReal) : Prop :=
  match selected.form with
  | .fixed => FixedSoundness capabilities subject selected error
  | .adaptive => AdaptiveSoundness capabilities subject selected error

noncomputable def WeightedFixedSoundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (schedule : ChargeSchedule subject) : Prop := by
  classical
  letI := capabilities.samples
  exact ∀ queries, selected.queries.allows queries → ∀ statement,
    subject.FalseStatement statement → ∀ initial
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (Zkc.Construction.Domain.Proof model.toCarriers)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let result ← (simulateQ randomOracle
      (prover >>= subject.compiled.verifier model
        (Typed.ask (R := Typed.ByLast Zkc.Construction.Domain.Raw))
        statement initial)).run' ∅}[ZkcSecurity.Endpoint.Domain.CompleteAccepted result] ≤
          cost + selected.validatorCost.value queries

noncomputable def WeightedAdaptiveSoundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (schedule : ChargeSchedule subject) : Prop := by
  classical
  letI := capabilities.samples
  exact ∀ queries, selected.queries.allows queries →
    ∀ (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (art.Statement model × Zkc.Construction.Domain.Proof model.toCarriers)) (cost : ENNReal),
    WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost →
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
      (fun result => (claimed.1, result)) <$> subject.compiled.verifier model
        (Typed.ask (R := Typed.ByLast Zkc.Construction.Domain.Raw)) claimed.1
        ((DomainReduction.policyCodec subject.compiled selected.application).encode claimed.1)
        claimed.2)).run' ∅}[
      subject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        cost + selected.validatorCost.value queries

noncomputable def WeightedSoundness (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (schedule : ChargeSchedule subject) : Prop :=
  match selected.form with
  | .fixed => WeightedFixedSoundness capabilities subject selected schedule
  | .adaptive => WeightedAdaptiveSoundness capabilities subject selected schedule

inductive SoundnessQuantity (subject : Subject model art) where
  | scalar (error : Bound)
  | charged (schedule : ChargeSchedule subject)

structure SoundnessArguments (subject : Subject model art) where
  selected : Model
  quantity : SoundnessQuantity subject

noncomputable def SoundnessArguments.meaning (capabilities : Capabilities model art.original)
    {subject : Subject model art} (arguments : SoundnessArguments subject) : Prop := by
  letI := capabilities.samples
  exact match arguments.quantity with
    | .scalar error => Soundness capabilities subject arguments.selected error.value
    | .charged schedule =>
      WeightedSoundness capabilities subject arguments.selected schedule ∧
        ∀ queries, arguments.selected.queries.allows queries →
          Nonempty (ChargedExport subject schedule queries (arguments.selected.validatorCost.value queries))

/-- Resolve source labels independently of numerical expressions. This static
selection can be checked without unfolding a carrier's finite enumeration or
the program and correspondence proofs stored in each retained occurrence. -/
def selectChargeSites (subject : Subject model art) (charges : List (String × Wire.Expr)) :
    Except ResolutionError (List (ChargeSite subject.compiled × Wire.Expr)) :=
  charges.mapM fun (name, expression) =>
    match subject.sites.filter (fun site => site.label == name) with
    | [site] => .ok (site, expression)
    | _ => .error (.siteMismatch name)

def chargeSchedule (capabilities : Capabilities model art.original)
    (subject : Subject model art) (selected : Model) (charges : List (String × Wire.Expr)) :
    Except ResolutionError (Except Incomplete (ChargeSchedule subject)) := do
  let sites ← selectChargeSites subject charges
  return do
    let entries ← sites.mapM fun (site, expression) => do
      return (site, ← Bound.elaborateWith capabilities.cardinality selected.budgetSymbol expression)
    if unique : (entries.map (fun entry => entry.1.label)).Nodup then
      if nativeUnique : (entries.map (fun entry => entry.1.native)).Nodup then
        return ⟨entries, unique, nativeUnique⟩
      else .error ⟨["distinct construction occurrences"]⟩
    else .error ⟨["distinct charge sites"]⟩

def soundnessArguments (capabilities : Capabilities model art.original)
    (registry : ModelRegistry) (request : Wire.Request) (subject : Subject model art) :
    Except ResolutionError (Except Incomplete (SoundnessArguments subject)) := do
  subject.check request
  checkCapabilities request
  let parameters ← (soundnessParameters capabilities.cardinality).decode request.parameters
  checkDefaultRelation subject.compiled.imported.program.payload.definitions
    subject.target.formula.definition.helper
  let selected ← resolveModel registry request.model
  match parameters with
  | .error missing => return .error missing
  | .ok parameters =>
    match requireExactSoundness subject.targetReference parameters with
    | .error missing => return .error missing
    | .ok () => pure ()
  match selected with
  | .error missing => return .error missing
  | .ok selected =>
    match request.quantity with
    | .scalar expression =>
      if !request.capabilities.isEmpty then return .error ⟨["charged capability requires a charge schedule"]⟩
      return do return ⟨selected, .scalar (← Bound.elaborateWith capabilities.cardinality selected.budgetSymbol expression)⟩
    | .charged charges =>
      return (← chargeSchedule capabilities subject selected charges).map fun schedule => ⟨selected, .charged schedule⟩
    | _ => throw (.schema "dependent soundness requires an error or charge quantity")

noncomputable def soundnessProperty (capabilities : Capabilities model art.original)
    (registry : ModelRegistry) : PropertyExport (Subject model art) where
  Arguments subject := Except Incomplete (SoundnessArguments subject)
  elaborate := soundnessArguments capabilities registry
  meaning _ arguments := arguments.map (SoundnessArguments.meaning capabilities)
  requiredLinks subject _ := subject.stageLinks

end ZkcSecurity.Claims.Domain

module

public import ZkcSecurity.FiatShamir.HonestCompiled
public import ZkcSecurity.FiatShamir.HonestSampling
public import ZkcSecurity.FiatShamir.HonestSamplingTransport
public import Zkc.Construction.DomainTransport

@[expose] public section

/-! The actual constructed pair with request-fixed private field sampling.
Only admitted participant ports grant local capabilities. Service roots are
not random values or public oracle keys. The ideal service is stateless and
draws afresh on each reached operation; native entropy is a separate boundary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.FiatShamir.SampledCompiled
open Zkc.Source Zkc.Construction OracleComp OracleSpec

abbrev Spec (carriers : Structured.Carriers) := HonestSampling.Spec (@Domain.Raw carriers)

def oracle {carriers : Structured.Carriers} : Domain.Oracle (OracleComp (Spec carriers)) carriers Unit :=
  fun history event state => liftM (HonestCompiled.oracle history event state)

/-- Capability selection is fixed by the exact pair, before any proof. A
copied port name cannot grant another root, owner or nominal result domain. -/
def allowed (context : Context) (producer validator : List ServicePort)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin) : Bool :=
  let (role, ports) := match mode with
    | .producer => (context.role context.producer, producer)
    | .validator => (context.role context.validator, validator)
  ports.contains port && port.owner == role && origin.entry == context.entry &&
    origin.event[0]? == some "query" &&
    origin.event[3]? == some ("input_" ++ decimal port.root) &&
    origin.event[4]? == some port.contract && origin.event[5]? == some port.owner &&
    match origin.request with
    | some ⟨"draw", [], .field field⟩ => port.contract == "random." ++ field ++ "/0"
    | _ => false

/-- Each reached request forwards a fresh uniform sample. The complete service
state is preserved; a root alias cannot reset an enclosing runtime's state. -/
def privateServices {carriers : Structured.Carriers} {S : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (context : Context) (producer validator : List ServicePort) :
    Domain.LocalServices ProbComp carriers S :=
  fun mode port origin state =>
    if allowed context producer validator mode port origin then do
      let reply ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))
      pure (.returned reply, state)
    else pure (.stopped .refused, state)

/-- Lift private sampling into the combined interface without adding ROM queries. -/
def services {carriers : Structured.Carriers} {S : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (context : Context) (producer validator : List ServicePort) :
    Domain.LocalServices (OracleComp (Spec carriers)) carriers S :=
  fun mode port origin state => liftM (privateServices context producer validator mode port origin state)

def computation (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers) :
    OracleComp (Spec model.toCarriers) (Domain.PairExecution model.toCarriers Unit) :=
  Domain.executePair model program context producer validator producerInputs validatorInputs oracle ()
    (services context producer.servicePorts validator.servicePorts)

theorem unauthorized_refuses {carriers : Structured.Carriers} {S : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (context : Context) (producer validator : List ServicePort)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin) (state : S)
    (refused : allowed context producer validator mode port origin = false) :
    services (carriers := carriers) context producer validator mode port origin state =
      pure (.stopped .refused, state) := by
  simp [services, privateServices, refused]

theorem authorized_samples {carriers : Structured.Carriers} {S : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (context : Context) (producer validator : List ServicePort)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin) (state : S)
    (admitted : allowed context producer validator mode port origin = true) :
    services (carriers := carriers) context producer validator mode port origin state =
      (do
        let reply ← (liftM ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))) :
          OracleComp (Spec carriers) _)
        pure (.returned reply, state)) := by
  simp [services, privateServices, admitted]

def tableOracle {carriers : Structured.Carriers} (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Domain.Oracle ProbComp carriers Unit := fun history event state =>
  pure (HonestCompiled.tableOracle answers history event state)

theorem simulate_oracle {carriers : Structured.Carriers}
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (history : Domain.History carriers) (event : Domain.Event carriers) (state : Unit) :
    simulateQ (unifFwdAnswerImpl answers) (oracle history event state) =
      tableOracle answers history event state := by
  unfold oracle unifFwdAnswerImpl
  rw [QueryImpl.passthrough_add, QueryImpl.liftTarget_self]
  rw [QueryImpl.simulateQ_add_liftM_right (QueryImpl.id' unifSpec) (answers.liftTarget ProbComp)
    (HonestCompiled.oracle history event state), simulateQ_liftTarget]
  change pure (evalWithAnswerFn answers (HonestCompiled.oracle history event state)) = _
  rw [HonestCompiled.eval_oracle]
  rfl

theorem simulate_services {carriers : Structured.Carriers} {S : Type}
    [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (context : Context) (producer validator : List ServicePort)
    (mode : Domain.Mode) (port : ServicePort) (origin : Origin) (state : S) :
    simulateQ (unifFwdAnswerImpl answers)
      (services context producer validator mode port origin state) =
      privateServices context producer validator mode port origin state := by
  unfold services unifFwdAnswerImpl
  rw [QueryImpl.passthrough_add, QueryImpl.liftTarget_self]
  rw [QueryImpl.simulateQ_add_liftM_left (QueryImpl.id' unifSpec) (answers.liftTarget ProbComp)
    (privateServices context producer validator mode port origin state), simulateQ_id']


theorem simulate_computation (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) :
    simulateQ (unifFwdAnswerImpl answers)
      (computation model program context producer validator producerInputs validatorInputs) =
      Domain.executePair model program context producer validator producerInputs validatorInputs
        (tableOracle answers) () (privateServices context producer.servicePorts validator.servicePorts) := by
  simp only [computation, HonestSampling.simulate_executePair, simulate_oracle]
  congr 1
  funext mode port origin state
  exact simulate_services answers context producer.servicePorts validator.servicePorts mode port origin state

/-- With no installed local ports the full computation is the old computation,
including its failures and both post-states, lifted into the extended interface. -/
theorem computation_no_services (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (noProducer : producer.servicePorts = []) (noValidator : validator.servicePorts = []) :
    computation model program context producer validator producerInputs validatorInputs =
      liftM (HonestCompiled.computation model program context producer validator producerInputs validatorInputs) := by
  unfold computation HonestCompiled.computation
  rw [Domain.executePair_lift]
  congr 1
  funext mode port origin state
  cases mode <;> simp [services, privateServices, allowed, noProducer, noValidator, Domain.refuseLocal]

end ZkcSecurity.FiatShamir.SampledCompiled

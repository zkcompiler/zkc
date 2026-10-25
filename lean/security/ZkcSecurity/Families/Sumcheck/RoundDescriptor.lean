module

public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackLoop
public import ZkcSecurity.Families.Sumcheck.CompiledValidator

@[expose] public section

/-! Small structural data for the installed table-round schema. Recognition is
only a proposal: clients also check the full generated block equations. No
helper name, protocol name, or source-specific instruction offset is installed
here. The two action counts and the relative slots belong to this family. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.RoundDescriptor
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open TableComponent

structure Loop where
  index : Nat
  capture : Nat
  site : String
  maximum : Nat
  yielded : List Nat
  operands : List Nat
  results : List ValueSort
  deriving DecidableEq, Repr

def Loop.instruction (loop : Loop) (artifact : Participant) : Zkc.Construction.Instruction :=
  artifact.instructions[loop.index]?.getD ⟨.unsupported "missing-loop", [], [], []⟩

/-- Capture size is computed from all inputs and all preceding results,
including private values that the round itself never reads. -/
def Loop.Matches (loop : Loop) (artifact : Participant) : Prop :=
  loop.index < artifact.instructions.length ∧
  loop.capture = (artifact.instructions.take loop.index).foldl
    (fun size instruction => size + instruction.results.length) artifact.inputs.length ∧
  (loop.instruction artifact).operation = .loop loop.site loop.maximum loop.yielded ∧
  (loop.instruction artifact).operands = loop.operands ∧
  (loop.instruction artifact).results = loop.results

instance (loop : Loop) (artifact : Participant) : Decidable (loop.Matches artifact) :=
  inferInstanceAs (Decidable (loop.index < artifact.instructions.length ∧
    loop.capture = (artifact.instructions.take loop.index).foldl
      (fun size instruction => size + instruction.results.length) artifact.inputs.length ∧
    (loop.instruction artifact).operation = .loop loop.site loop.maximum loop.yielded ∧
    (loop.instruction artifact).operands = loop.operands ∧
    (loop.instruction artifact).results = loop.results))

structure Pattern where
  plan : ReadbackRound.Plan
  suite : String

def occurrences (plan : ReadbackRound.Plan) : List Template :=
  [plan.lowTemplate, plan.highTemplate, plan.queryTemplate, plan.deliveryTemplate]

def templatesAt (body : List Zkc.Construction.Instruction) (indices : List Nat) : Option (List Template) :=
  indices.mapM fun index => do
    match (← body[index]?).operation with
    | .observe _ template | .challenge _ _ template => some template
    | _ => none

/-- Extract only the installed 17/23-action table family. The exact operations,
operands, sorts, checkpoints and evaluation order are checked separately by
equality to the existing family blocks, rather than a second interpreter. -/
def pattern? (producer validator : List Zkc.Construction.Instruction) : Option Pattern := do
  if producer.length != 17 || validator.length != 23 ||
      !(producer ++ validator).all (·.body.isEmpty) then none else pure ()
  let .call sums := (← producer[0]?).operation | none
  let .send low lowSchema receiver := (← producer[1]?).operation | none
  let .observe suite lowTemplate := (← producer[4]?).operation | none
  let .send high highSchema receiver' := (← producer[5]?).operation | none
  let .observe suite' highTemplate := (← producer[8]?).operation | none
  let .challenge querySuite field queryTemplate := (← producer[11]?).operation | none
  let .observe deliverySuite deliveryTemplate := (← producer[14]?).operation | none
  let .call first := (← producer[15]?).operation | none
  let .call append := (← producer[16]?).operation | none
  let .receive vlow vlowSchema sender (.field vfield) := (← validator[0]?).operation | none
  let .receive vhigh vhighSchema sender' (.field vfield') := (← validator[4]?).operation | none
  let .observe vlowSuite vlowTemplate := (← validator[3]?).operation | none
  let .observe vhighSuite vhighTemplate := (← validator[7]?).operation | none
  let .challenge vquerySuite vqueryField vqueryTemplate := (← validator[13]?).operation | none
  let .observe vdeliverySuite vdeliveryTemplate := (← validator[16]?).operation | none
  let .call vappend := (← validator[17]?).operation | none
  if !(low == lowSchema && low == vlow && low == vlowSchema &&
      high == highSchema && high == vhigh && high == vhighSchema &&
      receiver == receiver' && sender == sender' &&
      suite == suite' && suite == querySuite && suite == deliverySuite &&
      suite == vlowSuite && suite == vhighSuite && suite == vquerySuite && suite == vdeliverySuite &&
      field == vfield && field == vfield' && field == vqueryField && append == vappend &&
      lowTemplate == vlowTemplate && highTemplate == vhighTemplate &&
      queryTemplate == vqueryTemplate && deliveryTemplate == vdeliveryTemplate) then none else
  some ⟨{
    lowSite := low
    highSite := high
    producer := sender
    lowTemplate := lowTemplate
    highTemplate := highTemplate
    queryTemplate := queryTemplate
    deliveryTemplate := deliveryTemplate
    appendHelper := append
    field := field
    validator := receiver
    sumsHelper := sums
    firstHelper := first }, suite⟩

/-- A family round has exactly one enclosing repeat. Application coordinates
are retained in the template; the loop site must name that same repeat. -/
def repeatSite? (template : Template) : Option String :=
  match template.steps.filter (·.kind == "repeat") with
  | [step] => some (template.qualify step.site)
  | _ => none

structure Descriptor where
  producer : Loop
  validator : Loop
  deriving DecidableEq, Repr

def Descriptor.pattern? (descriptor : Descriptor) (producer validator : Participant) : Option Pattern :=
  RoundDescriptor.pattern? (descriptor.producer.instruction producer).body
    (descriptor.validator.instruction validator).body

/-- In addition to the full block equations, check both exact loop headers and
the installed yield ABI. In particular, changing a loop site is not hidden by
the operational View.loop, whose semantic arguments omit that site string. -/
def Descriptor.Matches (descriptor : Descriptor) (producer validator : Participant) : Prop :=
  descriptor.producer.Matches producer ∧ descriptor.validator.Matches validator ∧
  descriptor.producer.maximum = descriptor.validator.maximum ∧
  descriptor.producer.site = descriptor.validator.site ∧
  descriptor.producer.yielded = [21, 22, 23, 24, 20].map (descriptor.producer.capture + ·) ∧
  descriptor.validator.yielded = [21, 26, 20].map (descriptor.validator.capture + ·) ∧
  match descriptor.pattern? producer validator with
  | none => False
  | some pattern =>
      repeatSite? pattern.plan.queryTemplate = some descriptor.producer.site ∧
      descriptor.producer.results = [.data (.vector pattern.plan.field), .data .index,
        .data .index, .data (.vector pattern.plan.field), .transcript pattern.suite] ∧
      descriptor.validator.results = [.data (.vector pattern.plan.field),
        .data (.field pattern.plan.field), .transcript pattern.suite] ∧
      descriptor.producer.operands.length = 6 ∧ descriptor.validator.operands.length = 4

instance (descriptor : Descriptor) (producer validator : Participant) :
    Decidable (descriptor.Matches producer validator) := by
  unfold Descriptor.Matches
  split <;> infer_instance

/-- The four static bases are read from actual templates at the request's
context. Their validity is a concrete kernel obligation, never an assumption
that equal carrier types imply equal source occurrences. -/
structure OriginBases where
  low : Origin
  high : Origin
  query : Origin
  delivery : Origin
  deriving DecidableEq, Repr

def originBases (plan : ReadbackRound.Plan) (context : Context) : OriginBases :=
  let origin (template : Template) := (template.origin context).getD ⟨"", [], none⟩
  ⟨origin plan.lowTemplate, origin plan.highTemplate, origin plan.queryTemplate,
    origin plan.deliveryTemplate⟩

def templateValid (context : Context) (template : Template) : Prop :=
  template.entry = context.entry ∧ template.repeats = 1 ∧
    template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true

instance (context : Context) (template : Template) : Decidable (templateValid context template) :=
  inferInstanceAs (Decidable (template.entry = context.entry ∧ template.repeats = 1 ∧
    template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true))

def OriginBases.Valid (bases : OriginBases) (plan : ReadbackRound.Plan) (context : Context) : Prop :=
  templateValid context plan.lowTemplate ∧ templateValid context plan.highTemplate ∧
  templateValid context plan.queryTemplate ∧ templateValid context plan.deliveryTemplate ∧
  plan.lowTemplate.origin context = some bases.low ∧
  plan.highTemplate.origin context = some bases.high ∧
  plan.queryTemplate.origin context = some bases.query ∧
  plan.deliveryTemplate.origin context = some bases.delivery ∧
  bases.low.request = none ∧ bases.high.request = none ∧ bases.delivery.request = none ∧
  bases.query.request = some (.draw plan.field) ∧
  context.contract = "random." ++ plan.field ++ "/0" ∧
  context.request = some (.draw plan.field)

instance (bases : OriginBases) (plan : ReadbackRound.Plan) (context : Context) :
    Decidable (bases.Valid plan context) := by
  unfold OriginBases.Valid
  infer_instance

theorem template_at (context : Context) (template : Template) (base : Origin)
    (valid : templateValid context template) (found : template.origin context = some base)
    (index : Nat) :
    Domain.templateOrigin context template [index] = some (Domain.atCoordinates base [index]) := by
  simp [Domain.templateOrigin, valid.1, valid.2.1, valid.2.2, found]

@[simp] theorem request_at (origin : Origin) (index : Nat) :
    (Domain.atCoordinates origin [index]).request = origin.request := rfl

def OriginBases.sites {bases : OriginBases} {plan : ReadbackRound.Plan} {context : Context}
    (valid : bases.Valid plan context) (index : Nat) : ReadbackRound.Sites plan context index := by
  rcases valid with ⟨lv, hv, qv, dv, lf, hf, qf, df, lr, hr, dr, qr, contract, request⟩
  refine ⟨Domain.atCoordinates bases.low [index], Domain.atCoordinates bases.high [index],
    Domain.atCoordinates bases.query [index], Domain.atCoordinates bases.delivery [index],
    template_at _ _ _ lv lf index, template_at _ _ _ hv hf index, ?_,
    template_at _ _ _ dv df index, lr, hr, dr, qr⟩
  simp [Domain.queryOrigin, contract, request, template_at _ _ _ qv qf index, qr]

def OriginBases.schedule {bases : OriginBases} {plan : ReadbackRound.Plan} {context : Context}
    (valid : bases.Valid plan context) : TableComponent.Nominal.Schedule plan.field where
  low index := (OriginBases.sites valid index).low
  high index := (OriginBases.sites valid index).high
  query index := (OriginBases.sites valid index).query
  delivery index := (OriginBases.sites valid index).delivery
  request index := (OriginBases.sites valid index).request

/-- All source-occurrence wiring is shared. The only remaining premise is the
mathematical law of the actual retained append helper. -/
theorem OriginBases.connection {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    {bases : OriginBases} {plan : ReadbackRound.Plan} {context : Context}
    (valid : bases.Valid plan context) (program : Structured.Program)
    (append : ∀ point challenge,
      Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector plan.field)]
        [.data (.vector plan.field point), .data (.field plan.field challenge)] =
          .returned [.data (.vector plan.field (point ++ [challenge]))]) :
    CompiledValidator.RoundConnection (F := F) (G := G) plan.field program context plan.toPlan
      (OriginBases.schedule valid) where
  lowFound index := (OriginBases.sites valid index).lowFound
  highFound index := (OriginBases.sites valid index).highFound
  queryFound index := (OriginBases.sites valid index).queryFound
  deliveryFound index := (OriginBases.sites valid index).deliveryFound
  lowMessage index := (OriginBases.sites valid index).lowMessage
  highMessage index := (OriginBases.sites valid index).highMessage
  deliveryMessage index := (OriginBases.sites valid index).deliveryMessage
  append := append

end ZkcSecurity.Families.Sumcheck.RoundDescriptor

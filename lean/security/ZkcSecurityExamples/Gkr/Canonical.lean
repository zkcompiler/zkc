module

public import ZkcExamples.Construction.Generated.GkrPair
public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurity.Bindings.Gkr.RootEncoding
public import ZkcSecurity.Bindings.Gkr.Relations
public import ZkcExamples.Structured.GkrSourceViews
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.PairValidator
public import ZkcSecurity.Bindings.Subjects.ABI
public import ZkcSecurity.Bindings.Subjects.ChargeSites
public meta import ZkcTools.StructuredSource.NamedValues

@[expose] public section

/-! The actual GKR pair and its source-selected, registered circuit meaning.
Artifact selection and relation registration precede all proof evidence. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000

noncomputable section
namespace ZkcSecurity.Realizations.Gkr.Canonical
open Zkc.Source Zkc.Source.Structured Zkc.Construction

abbrev original := ZkcExamples.Structured.GkrSourceData.snapshot
abbrev imported := ZkcExamples.Structured.GkrSourceViews.imported
abbrev artifacts := ZkcExamples.Construction.Generated.GkrPair.artifacts

def selected : AuthoredPair.Selection original :=
  (AuthoredPair.select original artifacts "circuit_outputs").toOption.get (by decide +kernel)

def subject (model : DomainModel) :
    ZkcSecurity.Claims.HonestPair.Subject model original imported selected := by
  bind_authored_subject "circuit_outputs" with_registry (Relations.registry model)
    connections ZkcExamples.Structured.Generated.Connections.Gkr.producer, ZkcExamples.Structured.Generated.Connections.Gkr.validator
    exports "sha256:d7e4dd28461c16c9d8d294768991358538b733e3e8214b44dc606ee46af4031f",
      "sha256:ee9b21fe16f97b7a083f8c3c0ebde8cf3c2fdab80c47e61849715bdfc4af1d0e",
      "sha256:70bb6aa114cdee5f89f786f0f9fa95ff19c876d143707dcf592e7d1014769ee7"

/- Complete raw views share the retained source schema for every carrier,
including optional components and preparation data. Labels carry no authority. -/
named_values InputView [inputs, outputs, add, mul, layers, selector, width, handle] :=
  imported.program.payload.entry.inputs

named_values StatementView [inputs, outputs, add, mul, layers, selector, width] :=
  selected.policy.publicInputs.filterMap (imported.program.payload.entry.inputs[·]?)

named_values OutputView [accepted] := imported.program.payload.entry.outputs

named_values_bridge InputInvocation (model : DomainModel) : Source.Invocation (model.Field scalarDomain) :=
  InputView model.Value with [inputs, outputs, add, mul, layers, selector, width, handle]

named_values_bridge StatementInvocation (model : DomainModel) : Source.Invocation (model.Field scalarDomain) :=
  StatementView model.Value with [inputs, outputs, add, mul, layers, selector, width] (handle : Nat)

named_values_projection publicData (model : DomainModel) :=
  InputView (TypedABI.Slot Domain.dataType model.Value) => StatementView model.Value
  with [inputs, outputs, add, mul, layers, selector, width]

def sourceInputs (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).Inputs :=
  InputView.pack (InputView.map (fun _ => some) (InputInvocation.toView model runtime))

/-- The retained output selectors read the independent registered predicate.
No evidence-selected circuit or representation is an argument of this law. -/
theorem relation_exact (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).Relation (sourceInputs model runtime) ↔ runtime.Correct := by
  exact ((subject model).relation_iff_of_read _ _ (by rfl)).trans (by rfl)

theorem input_clause_exact (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).inputClause (sourceInputs model runtime) ⟨0, by change 0 < 2; decide⟩ rfl ↔
      runtime.Admitted := by
  exact (((subject model).inputMeanings ⟨0, by change 0 < 2; decide⟩ rfl).holds_iff_of_read {}
    ((subject model).boundary (sourceInputs model runtime))
    ((subject model).assignments (sourceInputs model runtime)) _ (by rfl)).trans (by rfl)

theorem honest_admitted (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain))
    (honest : (subject model).HonestInput (sourceInputs model runtime)) : runtime.Admitted :=
  (input_clause_exact model runtime).mp (honest.2.1 ⟨0, by change 0 < 2; decide⟩ rfl)

/-- The four source-selected challenge occurrences, fixed before soundness
evidence. Missing or ambiguous occurrences make construction fail. -/
def validatorSites (model : DomainModel) :
    List (ZkcSecurity.Claims.Domain.ChargeSite (subject model).validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel (subject model).validatorCompiled
      "output").toOption.get (by kernel_rfl),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel (subject model).validatorCompiled
      "left.challenge").toOption.get (by kernel_rfl),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel (subject model).validatorCompiled
      "right.challenge").toOption.get (by kernel_rfl),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel (subject model).validatorCompiled
      "line_challenge").toOption.get (by kernel_rfl)]

def validatorSubject (model : DomainModel) := (subject model).validatorSubject (validatorSites model)

def statement (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).validatorArtifacts.Statement model :=
  StatementView.pack (StatementInvocation.toView model runtime)

/-- Readback is total on every typed statement, including malformed tables.
The separate service handle never enters the fixed circuit predicate. -/
def invocation (model : DomainModel)
    (values : (subject model).validatorArtifacts.Statement model) (handle : Nat) :
    Source.Invocation (model.Field scalarDomain) :=
  StatementInvocation.fromView model (StatementView.unpack values) handle

theorem statement_invocation (model : DomainModel)
    (values : (subject model).validatorArtifacts.Statement model) (handle : Nat) :
    statement model (invocation model values handle) = values := by
  exact (congrArg StatementView.pack
    (StatementInvocation.toView_fromView model (StatementView.unpack values) handle)).trans
      (StatementView.pack_unpack values)

theorem invocation_statement (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain)) :
    invocation model (statement model runtime) runtime.handle = runtime := by
  exact (congrArg (fun view => StatementInvocation.fromView model view runtime.handle)
    (StatementView.unpack_pack (StatementInvocation.toView model runtime))).trans
      (StatementInvocation.fromView_toView model runtime)

/-- Soundness reads the actual validator inputs, independently of any honest
producer or honest-input policy. All target selectors are published inputs. -/
theorem holds_exact (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain))
    (witness : (validatorSubject model).Witness) :
    (validatorSubject model).Holds (statement model runtime) witness ↔ runtime.Correct := by
  exact ((validatorSubject model).holds_iff_of_read _ witness _ (by rfl)).trans (by rfl)

theorem false_statement_exact (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain)) :
    (validatorSubject model).FalseStatement (statement model runtime) ↔ ¬ runtime.Correct := by
  constructor
  · intro wrong correct
    exact wrong ⟨fun _ _ => none, (holds_exact model runtime _).mpr correct⟩
  · rintro wrong ⟨witness, correct⟩
    exact wrong ((holds_exact model runtime witness).mp correct)

/-- The fixed target law covers all typed validator statements, including
malformed raw tables and every adversarial witness. -/
theorem holds_all (model : DomainModel)
    (values : (subject model).validatorArtifacts.Statement model) (handle : Nat)
    (witness : (validatorSubject model).Witness) :
    (validatorSubject model).Holds values witness ↔ (invocation model values handle).Correct := by
  simpa only [statement_invocation] using holds_exact model (invocation model values handle) witness

end ZkcSecurity.Realizations.Gkr.Canonical

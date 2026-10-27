module

public import ZkcSecurity.Realizations.Gkr.CanonicalPair
public import ZkcSecurity.Realizations.Gkr.RootEncoding
public import ZkcSecurity.Realizations.Gkr.Relations
public import ZkcExamples.Structured.GkrSourceViews
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.PairValidator
public import ZkcSecurity.Claims.SubjectABI
public import ZkcSecurity.Claims.SourceChargeSites

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
abbrev artifacts := CanonicalPair.artifacts

def selected : AuthoredPair.Selection original :=
  (AuthoredPair.select original artifacts "circuit_outputs").toOption.get (by decide +kernel)

def subject (model : DomainModel) :
    ZkcSecurity.Claims.HonestPair.Subject model original imported selected := by
  bind_authored_subject "circuit_outputs" with_registry (Relations.registry model)
    exports "sha256:624ace13f9ec65913feab37af7f567746f268585252e9c3bb0708e61e84a70dd",
      "sha256:f829be33b7fbf7688a97068f3e195f109cc8021bc40f90719a27510f630d25fc",
      "sha256:fd0bdc7ff8c6e5279e5e0d89df36aa36b3a9180f4ac027c2afb3cd7b9de6bd4b"

def sourceInputs (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).Inputs :=
  .cons (some runtime.inputs) (.cons (some runtime.outputs) (.cons (some runtime.add)
    (.cons (some runtime.mul) (.cons (some runtime.layers) (.cons (some runtime.selector)
      (.cons (some runtime.width) (.cons (some runtime.handle) .nil)))))))

/-- The retained output selectors read the independent registered predicate.
No evidence-selected circuit or representation is an argument of this law. -/
theorem relation_exact (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).Relation (sourceInputs model runtime) ↔ runtime.Correct := by
  change (∃ arguments : Values model.Value (Relations.outputInputs scalarDomain),
    some (.cons runtime.inputs (.cons runtime.add (.cons runtime.mul (.cons runtime.layers
      (.cons runtime.selector (.cons runtime.width (.cons runtime.outputs .nil))))))) = some arguments ∧
      Relations.outputMeaning model scalarDomain arguments) ↔ _
  constructor
  · rintro ⟨arguments, same, correct⟩
    cases Option.some.inj same
    exact correct
  · intro correct
    exact ⟨_, rfl, correct⟩

theorem input_clause_exact (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain)) :
    (subject model).inputClause (sourceInputs model runtime) ⟨0, by change 0 < 2; decide⟩ rfl ↔
      runtime.Admitted := by
  change (∃ arguments : Values model.Value (Relations.shapeInputs scalarDomain),
    some (.cons runtime.inputs (.cons runtime.outputs (.cons runtime.add (.cons runtime.mul
      (.cons runtime.layers (.cons runtime.selector (.cons runtime.width .nil))))))) = some arguments ∧
      Relations.shapeMeaning model scalarDomain 4 4 arguments) ↔ _
  constructor
  · rintro ⟨arguments, same, admitted⟩
    cases Option.some.inj same
    exact admitted
  · intro admitted
    exact ⟨_, rfl, admitted⟩

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
  .cons runtime.inputs (.cons runtime.outputs (.cons runtime.add (.cons runtime.mul
    (.cons runtime.layers (.cons runtime.selector (.cons runtime.width .nil))))))

/-- Every typed public statement supplies exactly the actual validator's
seven public inputs. Its service handle is separate from target truth. -/
def invocation (model : DomainModel)
    (values : (subject model).validatorArtifacts.Statement model) (handle : Nat) :
    Source.Invocation (model.Field scalarDomain) where
  inputs := values.get .here
  outputs := values.get (.there .here)
  add := values.get (.there (.there .here))
  mul := values.get (.there (.there (.there .here)))
  layers := values.get (.there (.there (.there (.there .here))))
  selector := values.get (.there (.there (.there (.there (.there .here)))))
  width := values.get (.there (.there (.there (.there (.there (.there .here))))))
  handle := handle

theorem statement_invocation (model : DomainModel)
    (values : (subject model).validatorArtifacts.Statement model) (handle : Nat) :
    statement model (invocation model values handle) = values := by
  cases values with | cons inputs rest =>
    cases rest with | cons outputs rest =>
      cases rest with | cons add rest =>
        cases rest with | cons mul rest =>
          cases rest with | cons layers rest =>
            cases rest with | cons selector rest =>
              cases rest with | cons width rest =>
                cases rest
                rfl

theorem invocation_statement (model : DomainModel)
    (runtime : Source.Invocation (model.Field scalarDomain)) :
    invocation model (statement model runtime) runtime.handle = runtime := by
  cases runtime
  rfl

/-- Soundness reads the actual validator inputs, independently of any honest
producer or honest-input policy. All target selectors are published inputs. -/
theorem holds_exact (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain))
    (witness : (validatorSubject model).Witness) :
    (validatorSubject model).Holds (statement model runtime) witness ↔ runtime.Correct := by
  apply ((validatorSubject model).holds_iff_of_read _ witness
    (.cons runtime.inputs (.cons runtime.add (.cons runtime.mul (.cons runtime.layers
      (.cons runtime.selector (.cons runtime.width (.cons runtime.outputs .nil))))))) (by rfl)).trans
  rfl

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

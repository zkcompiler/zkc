module

public import Zkc.Construction.DomainCorrespondence
public import Zkc.Construction.DomainProducer
public import Zkc.Specification

@[expose] public section

/-! Consumers of one exact nominal constructed Process binding.
All transport uses equality of the complete open Process. No handler, return
projection or structural artifact-admission check weakens that equation. -/
set_option autoImplicit false
namespace Zkc.Construction.Domain.Binding
open Zkc.Source
variable {carriers : Structured.Carriers}

abbrev Meaning (carriers : Structured.Carriers) :=
  Environment carriers → PIR.Process (effects carriers) (Result carriers)

/-- Both independent consumers receive the same full Process equation. -/
theorem both {actual view : Meaning carriers} (same : ∀ inputs, actual inputs = view inputs)
    (first second : PIR.Process (effects carriers) (Result carriers) → Prop)
    (inputs : Environment carriers) (one : first (view inputs)) (two : second (view inputs)) :
    first (actual inputs) ∧ second (actual inputs) := by
  rw [same]
  exact ⟨one, two⟩

/-- Reuse the existing admitted-source certificate; this adds no admission rule. -/
theorem certificate {original : Structured.Snapshot} (imported : Structured.Imported original)
    (model : Structured.DomainModel) (context : Context) (artifact : Participant)
    (view : Meaning model.toCarriers)
    (same : ∀ inputs, Domain.participant model imported.program context artifact inputs = view inputs) :
    Zkc.Verification.Certificate imported
      (fun program => Domain.participant model program context artifact)
      (fun actual => ∀ inputs, actual inputs = view inputs) := ⟨same⟩

/-- Rewrite an actual producer without discarding its result, state or prefix. -/
theorem produce_eq {m : Type → Type} [Monad m] {S : Type}
    (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (artifact : Participant) (view : Meaning model.toCarriers)
    (same : ∀ inputs, Domain.participant model program context artifact inputs = view inputs)
    (inputs : Environment model.toCarriers) (oracle : Oracle m model.toCarriers S) (initial : S) :
    produce model program context artifact inputs oracle initial =
      run .producer oracle (view inputs) ⟨inputs, [], initial⟩ := by
  unfold produce
  rw [same]

theorem validate_eq {m : Type → Type} [Monad m] {S : Type}
    (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (artifact : Participant) (view : Meaning model.toCarriers)
    (same : ∀ inputs, Domain.participant model program context artifact inputs = view inputs)
    (inputs : Environment model.toCarriers) (proof : Proof model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S) :
    validate model program context artifact inputs proof oracle initial =
      run .validator oracle (view inputs) ⟨inputs, proof, initial⟩ := by
  unfold validate
  rw [same]

/-- The actual compiled pair uses both exact views and the producer's actual
oracle poststate and complete proof. A stopped producer still prevents validation. -/
theorem executePair_eq {m : Type → Type} [Monad m] {S : Type}
    (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (producer validator : Participant) (producerView validatorView : Meaning model.toCarriers)
    (producerSame : ∀ inputs,
      Domain.participant model program context producer inputs = producerView inputs)
    (validatorSame : ∀ inputs,
      Domain.participant model program context validator inputs = validatorView inputs)
    (producerInputs validatorInputs : Environment model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S) :
    executePair model program context producer validator producerInputs validatorInputs oracle initial =
      (do
        let produced ← run .producer oracle (producerView producerInputs) ⟨producerInputs, [], initial⟩
        match produced.outcome with
        | .stopped _ => pure ⟨produced, none⟩
        | .returned _ =>
            let validated ← run .validator oracle (validatorView validatorInputs)
              ⟨validatorInputs, produced.state.proof, produced.state.oracle⟩
            pure ⟨produced, some validated⟩) := by
  simp only [executePair, produce_eq model program context producer producerView producerSame,
    validate_eq model program context validator validatorView validatorSame]
  kernel_rfl

/-- A helper law must identify its outcome on the EXACT program and signature,
including failures. Merely matching its name never supplies this premise. -/
theorem helper_eq (model : Structured.DomainModel) (program : Structured.Program)
    (name : String) (references : List Nat) (declared : List ValueSort)
    (meaning : Environment model.toCarriers → PIR.Outcome (Environment model.toCarriers))
    (law : ∀ arguments, callHelper model program name declared arguments = meaning arguments)
    (env : Environment model.toCarriers) :
    View.helper model program name references declared env =
      (match read env references with
      | none => .halt .refused
      | some arguments =>
          match meaning arguments with
          | .returned results => View.append declared env results
          | .stopped reason => .halt reason) := by
  simp only [View.helper, law]
  kernel_rfl

/-- A known actual closure retains every stopped outcome and failed encoding.
The lookup indexes the complete helper, not just a same-named replacement. -/
theorem callHelper_of_lookup (model : Structured.DomainModel) (program : Structured.Program)
    (entry : Structured.HelperDefinition model.Value Structured.closedInterface)
    (found : (helperTable model program).find? (fun item => item.helper.name == entry.helper.name) =
      some entry)
    (arguments : Values model.Value entry.helper.inputs) (encoded : Environment model.toCarriers)
    (encoding : encodeValues arguments = some encoded) :
    callHelper model program entry.helper.name (entry.helper.outputs.map ValueSort.data) encoded =
      (match closedOutcome (entry.invoke arguments) with
      | .stopped reason => .stopped reason
      | .returned results =>
          match encodeValues results with
          | some values => .returned values
          | none => .stopped .refused) := by
  simp only [callHelper, found, ↓reduceIte, decodeValues_encodeValues encoding]
  kernel_rfl

/-- A successful typed invoke law on the actual closed helper table provides
its own exact signature check. Both nominal ABI encodings remain explicit. -/
theorem callHelper_of_invoke_return (model : Structured.DomainModel) (program : Structured.Program)
    (helper : Structured.Helper) (arguments : Values model.Value helper.inputs)
    (results : Values model.Value helper.outputs)
    (law : Structured.invoke (helperTable model program) helper arguments = .done results)
    (encodedArguments encodedResults : Environment model.toCarriers)
    (argumentsEncoding : encodeValues arguments = some encodedArguments)
    (resultsEncoding : encodeValues results = some encodedResults) :
    callHelper model program helper.name (helper.outputs.map ValueSort.data) encodedArguments =
      .returned encodedResults := by
  cases found : (helperTable model program).find? (fun entry => entry.helper.name == helper.name) with
  | none => simp [Structured.invoke, found] at law
  | some entry =>
      by_cases signature : entry.helper = helper
      · subst helper
        simp only [Structured.invoke, found, ↓reduceDIte] at law
        rw [callHelper_of_lookup model program entry found arguments encodedArguments argumentsEncoding,
          law]
        simp only [closedOutcome, resultsEncoding]
      · simp [Structured.invoke, found, signature] at law

/-- Exact uniform interpretation of the SAME ordered definition prefix. -/
theorem helperTable_ringModel {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (program : Structured.Program) :
    helperTable (Structured.ringModel F G) program =
      program.payload.definitions.foldl
        (Structured.Evaluation.extendMeanings (F := F) (G := G) Structured.SiteObservations.closed) [] := by
  have extend : Structured.Evaluation.extendMeanings (F := F) (G := G)
      Structured.SiteObservations.closed =
      Structured.Evaluation.extendMeaningsOn (Structured.ringModel F G)
        Structured.SiteObservations.closed :=
    funext fun table => funext fun definition =>
      Structured.Evaluation.extendMeanings_eq_extendMeaningsOn _ table definition
  simp only [helperTable, ← extend]

end Zkc.Construction.Domain.Binding

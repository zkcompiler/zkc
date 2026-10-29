module

public import Zkc.Construction.DomainBinding
public import Zkc.Source.Structured.ReferenceLaws

@[expose] public section

/-! Install a checked mathematical reference at the actual constructed helper.
The linked source identifies the declaration independently of its outcome, so
a refusal is preserved just as a return is. Full nominal ABI encoding remains
explicit; this theorem never substitutes a reference implementation by name.
-/
set_option autoImplicit false
namespace Zkc.Construction.Domain.Binding
open Zkc.Source Zkc.Source.Structured

variable (model : DomainModel) (program : Structured.Program) (helper : Helper)

theorem callHelper_of_reference
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (arguments : Values model.Value helper.inputs)
    (encoded : Environment model.toCarriers)
    (associated : BodyIn program.payload.definitions helper law.body)
    (premises : law.Requires (helperTable model program) arguments)
    (encoding : encodeValues arguments = some encoded) :
    callHelper model program helper.name (helper.outputs.map ValueSort.data) encoded =
      (match law.reference arguments with
      | .stopped reason => .stopped reason
      | .returned values => match encodeValues values with
        | some results => .returned results
        | none => .stopped .refused) := by
  have present : helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
    obtain ⟨definition, member, signature, _⟩ := associated
    exact List.mem_map.mpr ⟨definition, member, signature⟩
  obtain ⟨entry, found, signature⟩ := Evaluation.linked_lookupOn model SiteObservations.closed
    program.payload.linked helper present
  have equation := law.invoke program.payload.definitions program.payload.linked associated arguments premises
  subst helper
  have invocation : entry.invoke arguments = primitiveOutcome (law.reference arguments) := by
    simpa only [Structured.invoke, found, ↓reduceDIte] using equation
  rw [callHelper_of_lookup model program entry found arguments encoded encoding, invocation]
  cases law.reference arguments <;> rfl

end Zkc.Construction.Domain.Binding

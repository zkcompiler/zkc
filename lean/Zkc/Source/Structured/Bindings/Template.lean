module

public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.DomainLaws

@[expose] public section

/-! Installed templates produce ordinary normal forms at dependent types.
The model, helper table and immutable protocol capture remain parameters of
the existing interpreter. Neither nominal names nor template selection is a
certificate. The checked body/normalization equation carries that authority. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Bindings
open NormalForm

/-- A template is indexed by the actual checked definition and normalizer
signature. Wrong nominal domains, helpers or captures change these indices. -/
structure Template (definition : CheckedProtocol) (sig : Signature) (role roster : Nat) where
  form : Form sig.laws sig.callees (optionalPattern definition.inputs).scope definition.outputs
  normalized : normalize sig definition.body role roster (optionalPattern definition.inputs) = .ok form
  matched : form.CallsMatch

namespace Template
variable {definition : CheckedProtocol} {sig : Signature} {role roster : Nat}

def view (template : Template definition sig role roster) (model : DomainModel)
    (tables : Tables model) (protocols : ProtocolTable model.Value (Interface model))
    (results : LawResults model sig.laws) (processes : CalleeProcesses model sig.callees)
    (context : ProtocolContext) (input : Values (Component model.Value) definition.inputs) :=
  (template.form.denote model tables results context (runsAt model tables protocols context role)
    processes (optionalBinders model
      (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input))).bind
    fun out => .done (maskValues (context.roles role) (context.mapScopes definition.outputScopes) out)

/-- Whole-process binding, universally quantified over typed answers and stops.
Laws refer to these very helper tables and this captured protocol prefix. -/
theorem binding (template : Template definition sig role roster) (model : DomainModel)
    (tables : Tables model) (protocols : ProtocolTable model.Value (Interface model))
    (results : LawResults model sig.laws) (processes : CalleeProcesses model sig.callees)
    (context : ProtocolContext) (distinct : RosterDistinct context role roster)
    (input : Values (Component model.Value) definition.inputs)
    (laws : LawsHold tables results
      (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input))
    (callees : CalleesHold protocols processes
      (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input)) :
    definition.denoteWithOn model (.silent _) (participantActionsOn model.toCarriers)
      tables protocols .silent context (context.roles role) input =
      template.view model tables protocols results processes context input := by
  unfold CheckedProtocol.denoteWithOn view
  apply bind_congr_left
  have same := normalize_sound (model := model) (tables := tables) (protocols := protocols)
    (context := context) sig definition.body role roster (optionalPattern definition.inputs)
    template.form template.normalized template.matched distinct results processes
    (optionalBinders model (maskValues (context.roles role) (context.mapScopes definition.inputScopes) input))
  simp only [optional_environment] at same
  exact same laws callees

end Template
end Zkc.Source.Structured.Bindings

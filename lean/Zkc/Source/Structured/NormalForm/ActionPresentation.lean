module

public import Zkc.Source.Structured.NormalForm.Actions
public import Zkc.Source.Structured.NormalForm.Soundness

@[expose] public section

/-! The ordinary symbolic presentation and the generic residual action presentation
denote the same existing Region. This bridge retains every premise of the symbolic
normalizer's soundness theorem, including exact helper keys and input-pinned laws. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.NormalForm

theorem normalizeActions_form {model : DomainModel} {tables : Tables model}
    {protocols : ProtocolTable model.Value (Interface model)} {context : ProtocolContext}
    (sig : Signature) {inputs outputs : List Ty}
    (body : Region protocolDialect inputs outputs) (role roster : Nat)
    (pattern : InputPattern inputs) (form : Form sig.laws sig.callees pattern.scope outputs)
    (normalized : normalize sig body role roster pattern = .ok form)
    (matched : form.CallsMatch) (distinct : RosterDistinct context role roster)
    (results : LawResults model sig.laws) (processes : CalleeProcesses model sig.callees)
    (binders : Binders model pattern.scope)
    (lawsHold : LawsHold tables results (pattern.environment model binders))
    (calleesHold : CalleesHold protocols processes (pattern.environment model binders)) :
    (normalizeActions (meaningAt model tables protocols context role) body
      (pattern.environment model binders).get).process =
        form.denote model tables results context (runsAt model tables protocols context role)
          processes binders := by
  rw [normalizeActions_process]
  exact normalize_sound sig body role roster pattern form normalized matched distinct
    results processes binders lawsHold calleesHold

end Zkc.Source.Structured.NormalForm

module

public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Source.Structured.InputVisibility

@[expose] public section

/-! A checked occurrence normal form for any admitted root. Input visibility,
helper membership, callee operands and complete output layout come from the
source. The only interpretation is the existing NormalForm.denoteOn. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.NormalizedRoot
open Zkc.Source Zkc.Source.Structured NormalForm

def pattern (program : Program) (role : Nat) : InputPattern program.payload.entry.inputs :=
  InputVisibility.rolePattern role program.payload.entry.inputs program.payload.entry.inputScopes

structure CheckedOn (program : Program) (role : Nat) (signature : Signature)
    (inputPattern : InputPattern program.payload.entry.inputs) where
  form : Form signature.laws signature.callees inputPattern.scope program.payload.entry.outputs
  normalized : normalize signature program.payload.entry.body role program.payload.entry.roles.length
    inputPattern = .ok form
  matched : form.CallsMatch
  visible : InputVisibility.patternVisible role inputPattern program.payload.entry.inputScopes = true
  distinct : RosterDistinct {} role program.payload.entry.roles.length

abbrev Checked (program : Program) (role : Nat) (signature : Signature) :=
  CheckedOn program role signature (pattern program role)

variable {program : Program} {role : Nat} {signature : Signature}
  {inputPattern : InputPattern program.payload.entry.inputs}
  (checked : CheckedOn program role signature inputPattern) (model : DomainModel)

/-- Fill a checked pattern while leaving hidden coordinates absent. The default
role pattern keeps visible inputs optional, including malformed or unavailable
adversarial rows; an explicit present pattern also serves honest clients. -/
def inputsOn (inputPattern : InputPattern program.payload.entry.inputs)
    (args : Binders model inputPattern.scope) :=
  inputPattern.fill model args (Values.absent model.Value _)

def inputs (args : Binders model (pattern program role).scope) :=
  inputsOn model (pattern program role) args

/-- The existing normal-form denotation, including every root return mask.
Property proposers may expose this tree; its equation below is the authority. -/
def process (args : Binders model inputPattern.scope)
    (results : LawResults model signature.laws)
    (callees : CalleeProcesses model signature.callees (Occurrence.signature model.toCarriers)) :=
  (checked.form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload) results {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
      (Occurrence.table model program.payload) {} role) callees args).bind fun returned =>
        .done (maskValues role program.payload.entry.outputScopes returned)

theorem equation (args : Binders model inputPattern.scope)
    (results : LawResults model signature.laws)
    (callees : CalleeProcesses model signature.callees (Occurrence.signature model.toCarriers))
    (laws : LawsHold (Occurrence.helpers model program.payload) results
      (inputPattern.environment model args))
    (calls : CalleesHold (Occurrence.table model program.payload) callees
      (inputPattern.environment model args)) :
    Occurrence.participant model program role (inputsOn model inputPattern args) =
      (checked.form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload) results {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
          (Occurrence.table model program.payload) {} role) callees args).bind fun returned =>
            .done (maskValues role program.payload.entry.outputScopes returned) :=
  normalize_program_occurrence program signature role _ checked.form checked.normalized checked.matched
    checked.distinct results callees (inputsOn model inputPattern args) args
    (InputVisibility.mask_fill model role _ _ checked.visible args _) laws calls

/-- A kernel-checked presentation of the existing normalized process. This is
proof output, never a premise authorizing a new source or a registered law. -/
structure Composed (args : Binders model inputPattern.scope)
    (results : LawResults model signature.laws)
    (callees : CalleeProcesses model signature.callees (Occurrence.signature model.toCarriers)) where
  presented : PIR.Process (Occurrence.signature model.toCarriers)
    (Values (Component model.Value) program.payload.entry.outputs)
  equation : process checked model args results callees = presented

end Zkc.Source.Structured.NormalizedRoot

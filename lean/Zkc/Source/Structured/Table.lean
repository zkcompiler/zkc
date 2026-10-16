module

public import Zkc.Source.Structured.Operations

@[expose] public section

/-! Named semantic closures independent of the chosen values and effects.
Lookup checks the complete ordered signature after finding the name. A closure
may stop or interact; successful resolution does not assert successful execution.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

abbrev HelperFunction (Value : Ty → Type) (interface : PIR.Signature) (helper : Helper) :=
  RegionFunction Value interface (helper.inputs, helper.outputs)

structure HelperDefinition (Value : Ty → Type) (interface : PIR.Signature) where
  helper : Helper
  invoke : HelperFunction Value interface helper

abbrev HelperTable (Value : Ty → Type) (interface : PIR.Signature) :=
  List (HelperDefinition Value interface)

def invoke {Value : Ty → Type} {interface : PIR.Signature}
    (table : HelperTable Value interface) (helper : Helper) : HelperFunction Value interface helper :=
  match table.find? (fun entry => entry.helper.name == helper.name) with
  | none => fun _ => .halt .refused
  | some entry =>
    if h : entry.helper = helper then h ▸ entry.invoke
    else fun _ => .halt .refused

theorem invoke_cons_same {Value : Ty → Type} {interface : PIR.Signature}
    (table : HelperTable Value interface) (entry : HelperDefinition Value interface) :
    invoke (entry :: table) entry.helper = entry.invoke := by
  simp [invoke]

theorem invoke_cons_other {Value : Ty → Type} {interface : PIR.Signature}
    (table : HelperTable Value interface) (entry : HelperDefinition Value interface)
    (helper : Helper) (different : entry.helper.name ≠ helper.name) :
    invoke (entry :: table) helper = invoke table helper := by
  simp [invoke, different]

theorem invoke_cons_mismatch {Value : Ty → Type} {interface : PIR.Signature}
    (table : HelperTable Value interface) (entry : HelperDefinition Value interface)
    (helper : Helper) (sameName : entry.helper.name = helper.name)
    (different : entry.helper ≠ helper) :
    invoke (entry :: table) helper = fun _ => .halt .refused := by
  simp [invoke, sameName, different]

end Zkc.Source.Structured

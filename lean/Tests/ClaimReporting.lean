import Zkc.Claims.Receipt

/-! Probability-free, kernel-emitted controls for the assurance-report reader.
These prove only a registered test property, never a protocol security claim. -/

set_option autoImplicit false
namespace Tests.ClaimReporting
open Zkc.Claims

def request0Data : Wire.Request where
  subject := ⟨"test-unit", "test::Entry", .interactive, []⟩
  property := ⟨"user.reporting_control", 0⟩
  model := ⟨⟨"models.reporting_control", 0⟩, []⟩
  target := .retained "test" 0 "control"
  accept := ⟨true, 0, 0, []⟩
  quantity := .scalar (.natural 0)

def importedData : Wire.Request :=
  { request0Data with target :=
      .importedLanguage "test" ⟨⟨"languages.reporting_control", 3⟩, [(some "parameter", .natural 7)]⟩ }

def property : PropertyExport Unit where
  Arguments _ := Unit
  elaborate _ _ := .ok ()
  meaning _ _ := .ok True

def registry : Registry (PropertyExport Unit) :=
  ⟨[⟨⟨"user.reporting_control", 0⟩, "zkc.property.reporting-control/0", some property⟩]⟩

def resolved : Resolved registry (fun _ => request0Data.subject) () request0Data where
  subjectMatched := rfl
  entry := ⟨⟨"user.reporting_control", 0⟩, "zkc.property.reporting-control/0", some property⟩
  registered := rfl
  property := property
  defined := rfl
  arguments := ()
  elaborated := rfl

def evaluated : Evaluated resolved := ⟨True, rfl⟩

theorem discharge : True := True.intro

def wrongType : Nat := 0

def provenance : Provenance :=
  ⟨.theorem, "Tests.ClaimReporting.discharge", ⟨"methods.reporting_control", 0⟩, [], []⟩

def clean : Receipt evaluated := Receipt.ofTheorem discharge provenance

/-- A generic wrapper changes attribution, not the registered meaning. -/
def invoke {α : Sort _} (proof : α) : α := proof

def genericDirect : Receipt evaluated := Receipt.ofTheorem (invoke discharge) provenance

def explicitFalse (_hypothesis : False) : Receipt evaluated := clean

def implicitFalse {_hypothesis : False} : Receipt evaluated := clean

def inhabitedFalse [Inhabited False] : Receipt evaluated := clean

def liftedFalse (_hypothesis : PLift False) : Receipt evaluated := clean

def forgedDischarger : Receipt evaluated :=
  Receipt.ofTheorem discharge { provenance with discharger := "False.elim" }

def forgedDependency : Receipt evaluated :=
  Receipt.ofTheorem discharge { provenance with dependencies := ["False.elim"] }

def forgedRoute : Receipt evaluated :=
  ⟨discharge, { provenance.withSource with root := .endpoint }, List.mem_cons_self, fun _ => none⟩


def linkedProperty : PropertyExport Unit :=
  { property with requiredLinks := fun _ _ => [⟨"reporting.required", "reporting context", True, .infrastructure⟩] }

def linkedRegistry : Registry (PropertyExport Unit) :=
  ⟨[⟨⟨"user.reporting_control", 0⟩, "zkc.property.reporting-control/0", some linkedProperty⟩]⟩

def linkedResolved : Resolved linkedRegistry (fun _ => request0Data.subject) () request0Data where
  subjectMatched := rfl
  entry := ⟨⟨"user.reporting_control", 0⟩, "zkc.property.reporting-control/0", some linkedProperty⟩
  registered := rfl
  property := linkedProperty
  defined := rfl
  arguments := ()
  elaborated := rfl

def linkedEvaluated : Evaluated linkedResolved := ⟨True, rfl⟩

def omittedLink : Receipt linkedEvaluated := Receipt.ofTheorem discharge provenance

def provedLink : Receipt linkedEvaluated :=
  Receipt.ofTheorem discharge provenance (fun ⟨index, bounded⟩ => by
    have equal : index = 0 := Nat.lt_one_iff.mp bounded
    subst index
    exact some ⟨True.intro⟩)

end Tests.ClaimReporting

import Zkc.Source.Structured.NormalForm.Observation
import Zkc.Source.KernelRfl

/-! Bounded reads use the actual partial normalizer path. Present, absent and
out-of-bounds inputs retain distinct outcomes; no return-only premise is used. -/
set_option autoImplicit false
namespace Tests.StructuredPartialCalculation
open Zkc.Source Zkc.Source.Structured NormalForm

def body (domain : String) : Region protocolDialect [.vector domain, .index] [.field domain] :=
  .letOp (.calculate (.boundedAt domain) rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

def presentPattern (domain : String) : InputPattern [.vector domain, .index] :=
  .cons .present (.cons .present .nil)

def presentForm (domain : String) : Form [] [] (presentPattern domain).scope [.field domain] :=
  .compute (.boundedAt domain) rfl (.cons (.var .here) (.cons (.var (.there .here)) .nil))
    (.done (.cons (.present (.result .here .here)) .nil))

example (domain : String) : normalize {} (body domain) 0 1 (presentPattern domain) =
    .ok (presentForm domain) := by kernel_rfl

def optionalPattern (domain : String) : InputPattern [.vector domain, .index] :=
  .cons .optional (.cons .optional .nil)

def optionalForm (domain : String) : Form [] [] (optionalPattern domain).scope [.field domain] :=
  (normalize {} (body domain) 0 1 (optionalPattern domain)).toOption.getD (.halt .abort)

example (domain : String) : normalize {} (body domain) 0 1 (optionalPattern domain) =
    .ok (optionalForm domain) := by kernel_rfl
example (domain : String) : (optionalForm domain).CallsMatch := by kernel_rfl

theorem source_exact (model : DomainModel) (domain : String)
    (tables : Tables model (Occurrence.signature model.toCarriers))
    (container : Option (List (model.Field domain))) (index : Option Nat) :
    (body domain).denote (participantMeaningWithOn model (.silent _) Occurrence.actions
        tables 0 [] {} Occurrence.iterations)
      (optionalPattern domain |>.environment model (.cons container (.cons index .nil))).get =
      (optionalForm domain).denoteOn model Occurrence.actions tables (LawResults.empty model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations tables [] {} 0)
        (noCallees model (Occurrence.signature model.toCarriers)) (.cons container (.cons index .nil)) :=
  normalize_occurrence_sound {} (body domain) 0 1 (optionalPattern domain) (optionalForm domain)
    (by kernel_rfl) (by kernel_rfl) (RosterDistinct.root 0 1) (LawResults.empty model)
    (noCallees model (Occurrence.signature model.toCarriers)) _ (LawsHold.empty _ _) (noCallees_hold _ _)

example (model : DomainModel) (domain : String) (index : Option Nat) :
    (optionalForm domain).denoteOn model Occurrence.actions ⟨[], []⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[], []⟩ [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) (.cons none (.cons index .nil)) = .done (.cons none .nil) := by
  kernel_rfl

example (model : DomainModel) (domain : String) (container : List (model.Field domain)) :
    (optionalForm domain).denoteOn model Occurrence.actions ⟨[], []⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[], []⟩ [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) (.cons (some container) (.cons none .nil)) = .done (.cons none .nil) := by
  kernel_rfl

example (model : DomainModel) (domain : String) :
    (presentForm domain).denoteOn model Occurrence.actions ⟨[], []⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[], []⟩ [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) (.cons [] (.cons 0 .nil)) = .halt .refused := by
  kernel_rfl

example (model : DomainModel) (domain : String) (value : model.Field domain) :
    (presentForm domain).denoteOn model Occurrence.actions ⟨[], []⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[], []⟩ [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) (.cons [value] (.cons 0 .nil)) = .done (.cons (some value) .nil) := by
  kernel_rfl

example (model : DomainModel) (domain : String) (value : model.Field domain) :
    (presentForm domain).denoteOn model Occurrence.actions ⟨[], []⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[], []⟩ [] {} 0)
      (noCallees model (Occurrence.signature model.toCarriers)) (.cons [value] (.cons 1 .nil)) = .halt .refused := by
  kernel_rfl

end Tests.StructuredPartialCalculation

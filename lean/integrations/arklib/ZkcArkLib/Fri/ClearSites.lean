module

public import ZkcArkLib.Fri.TranscriptTrace

@[expose] public section

/-! The realized word, field challenges and terminal coefficients of the
retained clear profile. The original routing is independently discovered
from the admitted unit. The native descriptor supplies the realized message. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ClearSites
open Zkc.Construction Zkc.Executable.Descriptor
open ZkcExamples.Structured
open ZkcSecurity.Examples
open ZkcExamples.Structured.FriSource (extension)

def event (index : Fin 6) : Event :=
  FriClearDescriptor.events[index.val]'(by change index.val < 6; exact index.isLt)

def base (index : Fin 4) : Origin :=
  let template := (event ⟨index.val, by omega⟩).template
  (template.origin FriScalarQueries.context).get (by fin_cases index <;> decide +kernel)

def sites : ObservedLayers.Sites where
  round i := ⟨Domain.atCoordinates (base 0) [i], Domain.atCoordinates (base 1) [i],
    Domain.atCoordinates (base 2) [i]⟩
  terminal := base 3

theorem fields (i : Nat) : (sites.round i).draw.request = some (.draw extension) := by
  rw [show (sites.round i).draw = Domain.atCoordinates (base 1) [i] from rfl,
    OccurrenceResolution.atCoordinates_request]
  rfl

theorem formats :
    FriClearDescriptor.events.map (·.observation) =
      [.message ("vector:" ++ extension) "zkc.native-data/0", .draw,
       .message ("field:" ++ extension) ("zkcv.field." ++ extension ++ "/0"),
       .message ("vector:" ++ extension) "zkc.native-data/0", .index 32, .message "index" "zkcv.index/0"] := rfl

theorem valid_templates : FriClearDescriptor.events.all (·.template.validNamespaces) = true := by decide +kernel

theorem word_placement :
    (event 0).template.steps = (event 1).template.steps ∧
    (event 1).template.steps = (event 2).template.steps ∧
    (event 0).template.messageSite? = some "oracle_0_7_deliver" ∧
    (event 0).template.sentBy FriScalarQueries.policy.producer = true := by decide +kernel

theorem observed (i : Nat) :
    Domain.templateOrigin FriScalarQueries.context (event 0).template [i] = some (sites.round i).word ∧
    Domain.templateOrigin FriScalarQueries.context (event 1).template [i] = some (sites.round i).draw ∧
    Domain.templateOrigin FriScalarQueries.context (event 2).template [i] = some (sites.round i).delivery ∧
    Domain.templateOrigin FriScalarQueries.context (event 3).template [] = some sites.terminal := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 10000 in
/-- The same scalar pair appears in the compiled roster and the original service walk. -/
theorem scalar_pair :
    (event 4).template = FriScalarQueries.edge.draw ∧
    (event 5).template = FriScalarQueries.edge.message := by decide +kernel

set_option maxRecDepth 10000 in
theorem fold_pair :
    ∃ edge ∈ FriScalarQueries.publicRoutes.deliveries,
      (event 1).template = edge.draw ∧ (event 2).template = edge.message := by
  refine ⟨FriScalarQueries.publicRoutes.deliveries[0]'(by decide +kernel), ?_⟩
  exact ⟨List.getElem_mem _, by decide +kernel⟩

/-- Substituting a coordinate before entering the round, or dropping it in
the loop, fails even when the static event and its payload match. -/
theorem wrong_depth (i : Nat) :
    Domain.templateOrigin FriScalarQueries.context (event 0).template [] = none ∧
    Domain.templateOrigin FriScalarQueries.context (event 3).template [i] = none := by exact ⟨rfl, rfl⟩

end ZkcSecurity.ArkLib.Fri.ClearSites

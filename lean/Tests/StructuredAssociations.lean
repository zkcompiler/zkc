import Zkc.Source.Structured.BodyBindings

/-! Exact association controls independent of source admission. The fixtures
construct formed declarations; linking remains a separate invocation premise. -/
set_option autoImplicit false
namespace Tests.StructuredAssociations
open Zkc.Source Zkc.Source.Structured

private def formed {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, .math, inputs, outputs, body.erase, body, body.elaborate_erase⟩

private def valueBody (value : Bool) : Region dialect [] [.boolean] :=
  .letOp (.booleanConstant value) .nil .nil (.ret (.cons .here .nil))

private def helper : Helper := ⟨"value", .math, [], [.boolean]⟩
private def actual : CheckedDefinition := formed "value" (valueBody true)
private def unrelated : CheckedDefinition := formed "unrelated" (valueBody false)
private def wrongRaw : CheckedDefinition := formed "value" (valueBody false)
private def wrongKind : CheckedDefinition := { actual with kind := .local }
private def wrongInputs : CheckedDefinition :=
  formed "value" (.ret (.cons .here .nil) : Region dialect [.boolean] [.boolean])
private def wrongOutputs : CheckedDefinition :=
  formed "value" (.ret .nil : Region dialect [] [])

theorem original_association : BodyIn [actual, unrelated] helper (valueBody true) := by
  exact_body actual

/-- The same constructor finds the actual declaration after an independent one. -/
theorem permuted_association : BodyIn [unrelated, actual] helper (valueBody true) := by
  exact_body actual

theorem association_transport : BodyIn [unrelated, actual] helper (valueBody true) :=
  original_association.perm (List.Perm.swap _ _ [])

theorem same_name_wrong_raw_rejected : ¬ BodyIn [wrongRaw] helper (valueBody true) := by
  rintro ⟨definition, member, _, exactRaw⟩
  rcases List.mem_singleton.mp member with rfl
  have first := congrArg (fun raw => raw.operations.head?) exactRaw
  change some (Op.booleanConstant false) = some (.booleanConstant true) at first
  cases Option.some.inj first

theorem same_name_wrong_kind_rejected : ¬ BodyIn [wrongKind] helper (valueBody true) := by
  rintro ⟨definition, member, signature, _⟩
  rcases List.mem_singleton.mp member with rfl
  have kind := congrArg Helper.kind signature
  change HelperKind.local = .math at kind
  cases kind

theorem same_name_wrong_inputs_rejected : ¬ BodyIn [wrongInputs] helper (valueBody true) := by
  rintro ⟨definition, member, signature, _⟩
  rcases List.mem_singleton.mp member with rfl
  have inputs := congrArg Helper.inputs signature
  change [Ty.boolean] = [] at inputs
  cases inputs

theorem same_name_wrong_outputs_rejected : ¬ BodyIn [wrongOutputs] helper (valueBody true) := by
  rintro ⟨definition, member, signature, _⟩
  rcases List.mem_singleton.mp member with rfl
  have outputs := congrArg Helper.outputs signature
  change [] = [Ty.boolean] at outputs
  cases outputs

/-- A valid raw view and ABI are insufficient without membership. -/
theorem absent_rejected : ¬ BodyIn [unrelated] helper (valueBody true) := by
  rintro ⟨definition, member, signature, _⟩
  rcases List.mem_singleton.mp member with rfl
  have name := congrArg Helper.name signature
  change "unrelated" = "value" at name
  contradiction

/-- The tactic fails at the same boundaries, including the typed body context. -/
example : True := by
  fail_if_success
    have : BodyIn [wrongRaw] helper (valueBody true) := by exact_body wrongRaw
  fail_if_success
    have : BodyIn [wrongKind] helper (valueBody true) := by exact_body wrongKind
  fail_if_success
    have : BodyIn [wrongInputs] helper (valueBody true) := by exact_body wrongInputs
  fail_if_success
    have : BodyIn [wrongOutputs] helper (valueBody true) := by exact_body wrongOutputs
  fail_if_success
    have : BodyIn [unrelated] helper (valueBody true) := by exact_body actual
  fail_if_success
    have : BodyIn [actual, unrelated] helper (.ret .nil : Region dialect [] []) := original_association
  trivial

private theorem permuted_linked : DeclarationsLinked [] [unrelated, actual] := by
  simp [DeclarationsLinked, unrelated, actual, formed, valueBody,
    CheckedDefinition.helper, CheckedDefinition.helpers, Region.erase, Regions.erase,
    RawRegion.operations, RawRegions.operations, Op.helpers]

/-- Reuse the existing semantic transport after separately checking the new order. -/
theorem permuted_invocation (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] :
    invoke (closedMeanings (F := F) (G := G) [unrelated, actual]) helper .nil =
      .done (.cons true .nil) :=
  (permuted_association.invoke permuted_linked .nil).trans rfl

private def stopped : CheckedDefinition :=
  formed "stopped" (.stop .abort : Region dialect [] [])

/-- Exact association and successful linking retain a legitimate stop. -/
theorem associated_stop (F G : Type) [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] :
    invoke (closedMeanings (F := F) (G := G) [unrelated, stopped]) stopped.helper .nil =
      .halt .abort := by
  have association : BodyIn [unrelated, stopped] stopped.helper (.stop .abort) := by
    exact_body stopped
  have linked : DeclarationsLinked [] [unrelated, stopped] := by
    simp [DeclarationsLinked, unrelated, stopped, formed, valueBody,
      CheckedDefinition.helper, CheckedDefinition.helpers, Region.erase, Regions.erase,
      RawRegion.operations, RawRegions.operations, Op.helpers]
  exact (association.invoke linked .nil).trans rfl

/-- Automatic association searches the actual list, including reordered tables. -/
example : BodyIn [actual, unrelated] helper (valueBody true) := by bind_structured_bodies
example : BodyIn [unrelated, actual] helper (valueBody true) := by bind_structured_bodies

private structure Installed (definitions : List CheckedDefinition) : Prop where
  value : BodyIn definitions helper (valueBody true)
  stopped : BodyIn definitions stopped.helper (.stop .abort)

example : Installed [unrelated, stopped, actual] := by bind_structured_bodies

/-- Search refuses body, kind, signature, absence and arbitrary proposition gaps. -/
example : True := by
  fail_if_success
    have : BodyIn [wrongRaw] helper (valueBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongKind] helper (valueBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongInputs] helper (valueBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [wrongOutputs] helper (valueBody true) := by bind_structured_bodies
  fail_if_success
    have : BodyIn [unrelated] helper (valueBody true) := by bind_structured_bodies
  fail_if_success
    have : Installed [actual] := by bind_structured_bodies
  fail_if_success
    have : True := by bind_structured_bodies
  fail_if_success
    have : False := by bind_structured_bodies
  trivial

end Tests.StructuredAssociations

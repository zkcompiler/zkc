import Zkc.Source.Structured.ComponentLinking

/-! Optional denotation controls on linked typed bodies. These are Lean model
fixtures; no multi-role native admission or availability analysis is exercised. -/
set_option autoImplicit false
namespace Tests.StructuredComponents
open Zkc.Source Zkc.Source.Structured

private abbrev scalar : Ty := .field "bls12-381.fr"

private def formed {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, inputs, outputs, body.erase, body, body.elaborate_erase⟩

private def first (name : String) : CheckedDefinition :=
  formed name (.ret (.cons .here .nil) : Region dialect [scalar, scalar] [scalar])

private def relay (name target : String) : CheckedDefinition :=
  formed name (.letOp (.invoke ⟨target, [scalar, scalar], [scalar]⟩)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)) :
    Region dialect [scalar, scalar] [scalar])

private def constant : CheckedDefinition :=
  formed "constant" (.letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil
    (.ret (.cons .here .nil)) : Region dialect [scalar, scalar] [scalar])

private def separate : CheckedDefinition :=
  formed "separate" (.ret (.cons .here (.cons (.there .here) .nil)) :
    Region dialect [scalar, scalar] [scalar, scalar])

private def nested : Payload :=
  (linkPayload "main" [first "first", relay "relay" "first", constant,
    relay "main" "relay", separate]).toOption.get (by decide +kernel)

/-- Full-table equations compose without inspecting prefix positions. -/
theorem shared_first (payload : Payload) (helperName callerName : String)
    (helperMember : first helperName ∈ payload.definitions)
    (callerMember : relay callerName helperName ∈ payload.definitions)
    (F : Type) [CommRing F] [DecidableEq F] (x y : Option F) :
    invoke (payload.componentTables F).components (relay callerName helperName).helper
      (.cons x (.cons y .nil)) = .done (.cons x .nil) := by
  have helper : invoke (payload.componentTables F).components
      ⟨helperName, [scalar, scalar], [scalar]⟩ (.cons x (.cons y .nil)) =
        .done (.cons x .nil) :=
    payload.component_invoke_body (first helperName) helperMember _
  apply (payload.component_invoke_body (F := F) _ callerMember (.cons x (.cons y .nil))).trans
  change (invoke (payload.componentTables F).components
    ⟨helperName, [scalar, scalar], [scalar]⟩ (.cons x (.cons y .nil))).bind _ = _
  rw [helper]
  rfl

theorem nested_first (F : Type) [CommRing F] [DecidableEq F] (x y : Option F) :
    nested.component F (.cons x (.cons y .nil)) = .done (.cons x .nil) := rfl

theorem missing_unused (F : Type) [CommRing F] [DecidableEq F] (x : F) :
    nested.component F (.cons (some x) (.cons none .nil)) = .done (.cons (some x) .nil) := rfl

theorem missing_needed (F : Type) [CommRing F] [DecidableEq F] (y : F) :
    nested.component F (.cons none (.cons (some y) .nil)) = .done (.cons none .nil) := rfl

theorem constant_absent_inputs (F : Type) [CommRing F] [DecidableEq F] :
    invoke (nested.componentTables F).components constant.helper (.cons none (.cons none .nil)) =
      .done (.cons (some (7 : F)) .nil) := rfl

theorem separate_outputs (F : Type) [CommRing F] [DecidableEq F] (x y : Option F) :
    invoke (nested.componentTables F).components separate.helper (.cons x (.cons y .nil)) =
      .done (.cons x (.cons y .nil)) := rfl

theorem nested_all_present (F : Type) [CommRing F] [DecidableEq F] (x y : F) :
    nested.component F (.cons (some x) (.cons (some y) .nil)) =
      (nested.denote F (.cons x (.cons y .nil))).bind (fun results => .done results.present) :=
  nested.component_present (.cons x (.cons y .nil))

/-- Strict leaf lifting delegates arithmetic to the existing closed operation. -/
theorem present_add (F : Type) [CommRing F] [DecidableEq F] (x y : F) :
    componentOperation (⟨[], []⟩ : ComponentTables F) (.fieldAdd "bls12-381.fr")
      (.cons (some x) (.cons (some y) .nil)) .nil = .done (.cons (some (x + y)) .nil) := rfl

theorem absent_add (F : Type) [CommRing F] [DecidableEq F] (x : F) :
    componentOperation (⟨[], []⟩ : ComponentTables F) (.fieldAdd "bls12-381.fr")
      (.cons (some x) (.cons none .nil)) .nil = .done (.cons none .nil) := rfl

/-- Equal arms do not make the primitive select condition optional. -/
theorem select_needs_condition (F : Type) [CommRing F] [DecidableEq F] (x : F) :
    componentOperation (⟨[], []⟩ : ComponentTables F) (.select scalar)
      (.cons none (.cons (some x) (.cons (some x) .nil))) .nil =
        .done (.cons none .nil) := rfl

private def stopping : Payload :=
  (linkPayload "main" [formed "stop" (.stop .abort : Region dialect [] []),
    formed "main" (.letOp (.invoke ⟨"stop", [], []⟩) .nil .nil
      (.stop .refused) : Region dialect [] [])]).toOption.get (by decide +kernel)

/-- A zero-result named call still executes and stops before the continuation. -/
theorem zero_result_stop (F : Type) [CommRing F] [DecidableEq F] :
    stopping.component F .nil = .halt .abort := rfl

theorem stopping_adequacy (F : Type) [CommRing F] [DecidableEq F] :
    stopping.component F .nil = (stopping.denote F .nil).bind (fun results => .done results.present) :=
  stopping.component_present .nil

private def callbackRoot : CheckedDefinition := formed "main"
  (.bind (.ret (.cons .here .nil) : Region dialect [.boolean] [.boolean])
    (.letOp (.branch [] []) (.cons .here .nil)
      (.cons (.stop .abort)
        (.cons (.letOp (.invoke ⟨"callback", [], []⟩) .nil .nil (.ret .nil)) .nil))
      (.ret .nil)))

private def callbacks : Payload :=
  (linkPayload "main" [formed "callback" (.ret .nil : Region dialect [] []), callbackRoot]).toOption.get
    (by decide +kernel)

theorem nested_callback_stop (F : Type) [CommRing F] [DecidableEq F] :
    callbacks.component F (.cons (some true) .nil) = .halt .abort := rfl

theorem nested_callback_return (F : Type) [CommRing F] [DecidableEq F] :
    callbacks.component F (.cons (some false) .nil) = .done .nil := rfl

theorem nested_callback_adequacy (F : Type) [CommRing F] [DecidableEq F] (condition : Bool) :
    callbacks.component F (.cons (some condition) .nil) =
      (callbacks.denote F (.cons condition .nil)).bind (fun results => .done results.present) :=
  callbacks.component_present (.cons condition .nil)

/-- Distinguish callback interpretation even when the two tables deliberately
disagree. A call inside a closed callback uses the closed table. -/
theorem callback_uses_closed_table (F : Type) [CommRing F] [DecidableEq F] :
    let tables : ComponentTables F :=
      ⟨[⟨⟨"callback", [], []⟩, fun _ => .done .nil⟩],
        [⟨⟨"callback", [], []⟩, fun _ => .halt .abort⟩]⟩
    callbackRoot.body.component (meaning F tables.closed) (componentOperation tables)
      (Values.cons (some false) .nil).get = .done .nil := rfl

/-- Missing callback linkage is rejected even when another branch always stops. -/
theorem dormant_link_rejected : (linkPayload "main" [callbackRoot]).toOption.isNone = true := by
  decide +kernel

theorem dormant_component_resolves (F : Type) [CommRing F] [DecidableEq F] :
    ∃ entry : HelperDefinition (Component (scalarAssignment F)) closedInterface,
      ([formed "callback" (.ret .nil : Region dialect [] [])].foldl ComponentTables.extend
        (⟨[], []⟩ : ComponentTables F)).components.find?
          (fun entry => entry.helper.name == "callback") = some entry ∧
        entry.helper = ⟨"callback", [], []⟩ :=
  callbacks.component_reference_resolves
    [formed "callback" (.ret .nil : Region dialect [] [])] callbackRoot [] (by rfl)
    ⟨"callback", [], []⟩ (by decide +kernel)

theorem absent_guard (F : Type) [CommRing F] [DecidableEq F] :
    componentOperation (⟨[], []⟩ : ComponentTables F) .guard (.cons none .nil) .nil = .done .nil := rfl

theorem false_guard (F : Type) [CommRing F] [DecidableEq F] :
    componentOperation (⟨[], []⟩ : ComponentTables F) .guard (.cons (some false) .nil) .nil =
      .halt .reject := rfl

theorem invalid_read (F : Type) [CommRing F] [DecidableEq F] :
    componentOperation (⟨[], []⟩ : ComponentTables F) (.boundedAt "bls12-381.fr")
      (.cons (some ([] : List F)) (.cons (some 0) .nil)) .nil = .halt .refused := rfl

private def unusedIntermediate : Region dialect [scalar, scalar] [scalar] :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons (.there .here) .nil))

/-- MODEL COUNTEREXAMPLE: a missing required intermediate is invisible in the
returned component. A future formation judgment must independently reject the
corresponding unavailable intermediate. This is not native admission. -/
theorem unused_intermediate_returns (F : Type) [CommRing F] [DecidableEq F] (x : F) :
    unusedIntermediate.component (meaning F []) (componentOperation ⟨[], []⟩)
      (Values.cons (some x) (.cons none .nil)).get = .done (.cons (some x) .nil) := rfl

/-- A private Local boundary sketch: an owner must have all arguments before
entering the closed closure; nonowners receive absent results and do not run it.
This is not dispatch for Op.invoke, whose call-kind metadata is still missing. -/
private def localBoundary {Value : Ty → Type} {inputs outputs : List Ty}
    (owner : Bool) (closed : Values Value inputs → Closed (Values Value outputs))
    (args : Values (Component Value) inputs) : Closed (Values (Component Value) outputs) :=
  if owner then
    match RoleFamily.sequence args with
    | none => .halt .incomplete
    | some values => (closed values).bind (fun results => .done results.present)
  else .done (Values.absent Value outputs)

theorem local_owner_stop :
    localBoundary (Value := scalarAssignment Nat) true (inputs := []) (outputs := [])
      (fun _ => .halt .abort) .nil = .halt .abort := rfl

theorem local_nonowner_skip :
    localBoundary (Value := scalarAssignment Nat) false (inputs := []) (outputs := [])
      (fun _ => .halt .abort) .nil = .done .nil := rfl

theorem local_owner_requires_unused (x : Nat) :
    localBoundary (Value := scalarAssignment Nat) true (inputs := [scalar, scalar])
      (fun args => .done (.cons (args.get .here) .nil))
      (.cons (some x) (.cons none .nil)) = .halt .incomplete := rfl

end Tests.StructuredComponents

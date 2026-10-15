import Zkc.Source.Structured.Linking
import Zkc.Source.Structured.Frame
import Zkc.Source.RegionContracts

/-! Linker boundary controls and reusable conditional contracts. The fixtures
construct formed bodies directly to test invariants independently of lowering. -/
set_option autoImplicit false
namespace Tests.StructuredLinking
open Zkc.Source Zkc.Source.Structured

private def formed {inputs outputs : List Ty} (name : String)
    (body : Region dialect inputs outputs) : CheckedDefinition :=
  ⟨name, inputs, outputs, body.erase, body, body.elaborate_erase⟩

private def constant (name : String) (value : Bool) : CheckedDefinition :=
  formed name (.letOp (.booleanConstant value) .nil .nil (.ret (.cons .here .nil)) :
    Region dialect [] [.boolean])

private def call (name target : String) : CheckedDefinition :=
  formed name (.letOp (.invoke ⟨target, [], [.boolean]⟩) .nil .nil
    (.ret (.cons .here .nil)) : Region dialect [] [.boolean])

private def rejected (definitions : List CheckedDefinition) (code : String) : Bool :=
  match linkPayload "main" definitions with
  | .error actual => actual == code
  | .ok _ => false

theorem missing_rejected : rejected [call "main" "missing"] "structured-helper-link" = true := by
  decide +kernel

theorem forward_rejected : rejected [call "main" "helper", constant "helper" true]
    "structured-helper-link" = true := by decide +kernel

theorem duplicate_rejected : rejected [constant "same" true, constant "same" false,
    call "main" "same"] "structured-helper-link" = true := by decide +kernel

/-- The helper name exists, but its output signature does not match the call. -/
theorem signature_rejected : rejected [formed "helper" (.ret .nil : Region dialect [] []),
    call "main" "helper"] "structured-helper-link" = true := by decide +kernel

theorem duplicate_different_signature_rejected : rejected
    [constant "same" true, formed "same" (.ret .nil : Region dialect [] []),
      call "main" "same"] "structured-helper-link" = true := by decide +kernel

private def reorderedInputs : List CheckedDefinition := [
  formed "helper" (.ret (.cons (.there .here) (.cons .here .nil)) :
    Region dialect [.boolean, .index] [.index, .boolean]),
  formed "main" (.letOp (.invoke ⟨"helper", [.index, .boolean], [.index, .boolean]⟩)
    (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here (.cons (.there .here) .nil))) :
    Region dialect [.index, .boolean] [.index, .boolean])]

theorem input_order_rejected : rejected reorderedInputs "structured-helper-link" = true := by
  decide +kernel

private abbrev emptyStateFold : FoldSpec :=
  ⟨⟨"items", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩,
    [], [], "step", "predicate"⟩

private def foldRoot : CheckedDefinition := formed "main"
  (.letOp (.fold emptyStateFold) (.cons .here .nil) .nil (.ret .nil) :
    Region dialect [.vector "bls12-381.fr"] [])

private def foldStep : CheckedDefinition := formed "step"
  (.ret .nil : Region dialect [.field "bls12-381.fr", .vector "bls12-381.fr"] [])

private def foldPredicate : CheckedDefinition := formed "predicate"
  (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)) :
    Region dialect [.field "bls12-381.fr", .vector "bls12-381.fr"] [.boolean])

/-- Empty iteration at a later execution cannot excuse either missing callback. -/
theorem missing_step_rejected : rejected [foldPredicate, foldRoot]
    "structured-helper-link" = true := by decide +kernel

theorem missing_predicate_rejected : rejected [foldStep, foldRoot]
    "structured-helper-link" = true := by decide +kernel

private def dormant : CheckedDefinition := formed "main"
  (.letOp (.branch [] [.boolean]) (.cons .here .nil)
    (.cons (.letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil)))
      (.cons (.letOp (.invoke ⟨"missing", [], [.boolean]⟩) .nil .nil
        (.ret (.cons .here .nil))) .nil))
    (.ret (.cons .here .nil)) : Region dialect [.boolean] [.boolean])

theorem dormant_rejected : rejected [dormant] "structured-helper-link" = true := by
  decide +kernel

private def stoppedSuffix : CheckedDefinition := formed "main"
  (.bind (.stop .abort : Region dialect [] [])
    (.letOp (.invoke ⟨"missing", [], [.boolean]⟩) .nil .nil (.ret (.cons .here .nil))))

theorem stopped_suffix_rejected : rejected [stoppedSuffix] "structured-helper-link" = true := by
  decide +kernel

private def accepted : Payload :=
  (linkPayload "main" [constant "unused" false, constant "helper" true, call "main" "helper",
    constant "later" false]).toOption.get (by decide +kernel)

theorem linked : DeclarationsLinked [] accepted.definitions := accepted.linked

theorem unique_names : (accepted.definitions.map (·.name)).Nodup := accepted.linked.nodup

/-- A later declaration leaves the earlier helper's body and closure intact. -/
theorem helper_body (F : Type) [CommRing F] [DecidableEq F] :
    invoke (accepted.meanings F) (constant "helper" true).helper .nil =
      (constant "helper" true).body.denote
        (meaning F ([constant "unused" false].foldl extendMeanings [])) Values.nil.get :=
  accepted.invoke_declaration [constant "unused" false] (constant "helper" true)
    [call "main" "helper", constant "later" false] (by rfl) .nil

/-- Membership of the exact helper and caller suffices to compose their meanings
in any linked payload; the proof never inspects declaration positions or prefixes. -/
theorem constant_caller (payload : Payload) (helperName callerName : String) (value : Bool)
    (helperMember : constant helperName value ∈ payload.definitions)
    (callerMember : call callerName helperName ∈ payload.definitions)
    (F : Type) [CommRing F] [DecidableEq F] :
    invoke (payload.meanings F) (call callerName helperName).helper .nil =
      .done (.cons value .nil) := by
  have helper : invoke (payload.meanings F) ⟨helperName, [], [.boolean]⟩ .nil =
      .done (.cons value .nil) :=
    payload.invoke_body (constant helperName value) helperMember .nil
  exact (payload.invoke_body (call callerName helperName) callerMember .nil).trans
    ((Region.letOp_return (meaning F (payload.meanings F))
      (.invoke ⟨helperName, [], [.boolean]⟩) .nil .nil
      (.ret (.cons .here .nil)) Values.nil.get (.cons value .nil) helper).trans rfl)

private def permuted : Payload :=
  (linkPayload "main" [constant "later" false, constant "inserted" false,
    constant "helper" true, call "main" "helper", constant "unused" false]).toOption.get
    (by decide +kernel)

theorem caller_original (F : Type) [CommRing F] [DecidableEq F] :
    accepted.denote F .nil = .done (.cons true .nil) :=
  constant_caller accepted "helper" "main" true
    (List.get_find?_mem (xs := accepted.definitions)
      (p := fun definition => definition.name == "helper") (by decide +kernel))
    (List.get_find?_mem (xs := accepted.definitions)
      (p := fun definition => definition.name == "main") (by decide +kernel)) F

/-- The same composition theorem survives permuting the independent declarations
and inserting another unrelated declaration before the helper. -/
theorem caller_permuted (F : Type) [CommRing F] [DecidableEq F] :
    permuted.denote F .nil = .done (.cons true .nil) :=
  constant_caller permuted "helper" "main" true
    (List.get_find?_mem (xs := permuted.definitions)
      (p := fun definition => definition.name == "helper") (by decide +kernel))
    (List.get_find?_mem (xs := permuted.definitions)
      (p := fun definition => definition.name == "main") (by decide +kernel)) F

private def nested : Payload :=
  (linkPayload "main" [constant "seed" true, call "helper" "seed", constant "unused" false,
    call "main" "helper", constant "later" false]).toOption.get (by decide +kernel)

/-- A helper retains its own earlier dependency when later declarations exist. -/
theorem nested_helper (F : Type) [CommRing F] [DecidableEq F] :
    nested.denote F .nil = .done (.cons true .nil) := rfl

private def stopping : Payload :=
  (linkPayload "main" [formed "stop" (.stop .abort : Region dialect [] []),
    formed "main" (.letOp (.invoke ⟨"stop", [], []⟩) .nil .nil
      (.ret .nil) : Region dialect [] [])]).toOption.get (by decide +kernel)

/-- Successful linking does not imply termination, even with no outputs. -/
theorem linked_zero_result_stops (F : Type) [CommRing F] [DecidableEq F] :
    stopping.denote F .nil = .halt .abort := rfl

/-- Exact source shape is enough to expose a typed body, regardless of the
checker implementation used to obtain that body. -/
theorem body_recovery : (constant "helper" true).body =
    (.letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil))) :=
  (constant "helper" true).body_eq_of_raw _ (by rfl)

/-- Reuse a caller equation after adding unrelated declarations. The frame law
requires agreement only on the helper actually present in the formed body. -/
theorem unrelated_binding (F : Type) [CommRing F] [DecidableEq F] :
    (call "main" "helper").body.denote
      (meaning F (extendMeanings [] (constant "helper" true))) =
    (call "main" "helper").body.denote
      (meaning F (extendMeanings (extendMeanings [] (constant "helper" true))
        (constant "unrelated" false))) := by
  apply region_denote_table_congr
  intro helper member
  have same : helper = ⟨"helper", [], [.boolean]⟩ := by
    simpa [call, formed, Region.erase, Regions.erase, RawRegion.operations, RawRegions.operations, Op.helpers] using member
  subst helper
  exact (invoke_extend_other _ (constant "unrelated" false) _ (by decide +kernel)).symm

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev vector : Ty := .vector "bls12-381.fr"

private def readBody : Region dialect [vector, .index] [scalar] :=
  .letOp (.boundedAt "bls12-381.fr") (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons .here .nil))

/-- A mathematical read has a conditional contract on the exact vector/index
pair. No premise claims that every arbitrary index is safe. -/
theorem read_contract (F : Type) [CommRing F] [DecidableEq F] (table : Meanings F) :
    readBody.Contract (meaning F table)
      (fun env => env (.there .here) < (env .here).length)
      (fun env values => (env .here)[env (.there .here)]? = some (values.get .here)) := by
  intro env bound
  let result := (env .here)[env (.there .here)]
  have read : (env .here)[env (.there .here)]? = some result := List.getElem?_eq_getElem bound
  refine ⟨.cons result .nil, ?_, read⟩
  exact (Region.letOp_return (meaning F table) (.boundedAt "bls12-381.fr")
    (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil)) env (.cons result .nil)
    (boundedAt_exact table "bls12-381.fr" _ _ result read)).trans rfl

private def doubleResult : Region dialect [scalar, vector, .index] [scalar] :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons .here .nil))
    .nil (.ret (.cons .here .nil))

/-- A caller reuses the checked read contract and carries its exact-value fact
through a lexical continuation. The bound is assumed once at the call boundary. -/
theorem read_then_double (F : Type) [CommRing F] [DecidableEq F] (table : Meanings F) :
    (readBody.bind doubleResult).Contract (meaning F table)
      (fun env => env (.there .here) < (env .here).length)
      (fun env values => ∃ value, (env .here)[env (.there .here)]? = some value ∧
        values.get .here = value + value) := by
  apply Region.Contract.bind (meaning F table) readBody doubleResult
    (fun env => env (.there .here) < (env .here).length)
    (fun env values => (env .here)[env (.there .here)]? = some (values.get .here))
  · exact read_contract F table
  · intro env values _ read
    cases values with
    | cons value rest =>
      cases rest
      exact ⟨.cons (value + value) .nil, rfl, value, read, rfl⟩

/-- Omitting the read premise really permits a stop, even for this tiny body. -/
theorem invalid_read (F : Type) [CommRing F] [DecidableEq F] :
    readBody.denote (meaning F [])
      (Values.cons ([] : List F) (.cons 0 .nil)).get = .halt .refused := rfl

end Tests.StructuredLinking

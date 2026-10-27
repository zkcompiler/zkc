module

public import ZkcTools.StructuredSource.Bindings.Callbacks
public import ZkcExamples.Structured.SumcheckVerifierLaws

@[expose] public section

/-! Instantiation of the installed endpoint-round template. Candidate selection
compares the entire typed callback, never a source/protocol name. The emitted
equations still require the kernel to check that body and the complete Process.
No relation truth or honest wire reply is a template premise. -/

namespace Tests.Generators.SumcheckBindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation
open ZkcTools.StructuredSource.Bindings

/-- Explicit example-library selection. The full typed append body must match;
its name, signature or source hash does not establish its law. -/
def sumcheckCallbacksSource (program : Program) (output : Output) : Except String String := do
  let appendHelper := ZkcExamples.Structured.SumcheckHelperBodies.appendHelper
  let appendBody := ZkcExamples.Structured.SumcheckHelperBodies.appendBody
  let some appendIndex := program.payload.definitions.findIdx? (fun definition =>
    definition.helper == appendHelper && ZkcTools.StructuredSource.Bindings.helperRegionText definition.body == ZkcTools.StructuredSource.Bindings.helperRegionText appendBody)
    | throw "callback-append-template-body"
  let laws : List LawKey := [⟨appendHelper, .returns [], []⟩]
  let mut text := ""
  text := text ++ "open ZkcExamples.Structured\n" ++
    "theorem append_association : BodyIn payload.definitions SumcheckHelperBodies.appendHelper SumcheckHelperBodies.appendBody := by\n" ++
    "  exact ⟨payload.definitions.get ⟨" ++ toString appendIndex ++ ", by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩\n\n" ++
    "theorem append_plain (point : List F) (value : F) :\n" ++
    "    invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.appendHelper (.cons point (.cons value .nil)) =\n" ++
    "      .done (.cons (point ++ [value]) .nil) := by\n" ++
    "  rw [Zkc.Source.Structured.closed_invoke_plain payload]\n" ++
    "  rw [append_association.invoke payload.linked, SumcheckHelperLaws.append_body]\n  rfl\n\n" ++
    "def callbackKeys : List LawKey := " ++ listText (laws.map lawText) ++ "\n\n" ++
    "def callbackResults : LawResults (ringModel F G) callbackKeys where\n" ++
    "  result := Fin.cases (fun args => .cons ((args.get .here) ++ [args.get (.there .here)]) .nil) (fun entry => entry.elim0)\n\n" ++
    "theorem callbackLaws_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :\n" ++
    "    LawsHold (helpers payload).toOn (callbackResults (F := F) (G := G)) input := by\n" ++
    "  intro entry\n  fin_cases entry\n  intro args _ values returned\n" ++
    "  cases args with | cons point args =>\n    cases args with | cons value args =>\n      cases args\n" ++
    "      change some (.cons (point ++ [value]) .nil) = some values at returned\n" ++
    "      exact (append_plain point value).trans (congrArg PIR.Process.done (Option.some.inj returned))\n\n"
  callbacksSource program output {
    imports := ["ZkcExamples.Structured.SumcheckVerifierHelpers"]
    laws := laws
    declarations := text
    lawResult := fun _ position => if position == 0 then some "{0} ++ [{1}]" else none }


structure HelperTemplate where
  helper : Helper
  body : Region dialect helper.inputs helper.outputs
  field : String

def verifierTemplates : List HelperTemplate := [
  ⟨ZkcExamples.Structured.SumcheckHelperBodies.emptyHelper,
    ZkcExamples.Structured.SumcheckHelperBodies.emptyBody, "empty"⟩,
  ⟨ZkcExamples.Structured.SumcheckHelperBodies.appendHelper,
    ZkcExamples.Structured.SumcheckHelperBodies.appendBody, "append"⟩,
  ⟨ZkcExamples.Structured.MapFirstBodies.widthHelper,
    ZkcExamples.Structured.MapFirstBodies.widthBody, "width"⟩,
  ⟨ZkcExamples.Structured.MapFirstBodies.variablesHelper,
    ZkcExamples.Structured.MapFirstBodies.variablesBody, "«variables»"⟩,
  ⟨ZkcExamples.Structured.MapFirstBodies.valuesHelper,
    ZkcExamples.Structured.MapFirstBodies.valuesBody, "values"⟩]

def sumcheckSource (program : Program) (output : Output) : Except String String := do
  let mut text := "module\n\npublic import " ++ output.moduleName ++ "Callbacks\n" ++
    "public import ZkcExamples.Structured.SumcheckVerifierLaws\n\n@[expose] public section\n\n" ++
    "/-! Generated actual-source endpoint template bindings. -/\nnamespace " ++ output.moduleName ++ "Sumcheck\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "open ZkcExamples.Structured " ++ output.moduleName ++ " " ++ output.moduleName ++ "Callbacks\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nset_option smartUnfolding false\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  text := text ++ "theorem helper_bodies : SumcheckVerifierHelpers.Bodies payload.definitions where\n"
  for template in verifierTemplates do
    let some index := program.payload.definitions.findIdx? (fun definition =>
        definition.helper == template.helper && ZkcTools.StructuredSource.Bindings.helperRegionText definition.body == ZkcTools.StructuredSource.Bindings.helperRegionText template.body)
      | throw ("endpoint-template-helper-body:" ++ template.field)
    text := text ++ "  " ++ template.field ++ " := ⟨payload.definitions.get ⟨" ++ toString index ++
      ", by decide +kernel⟩, List.get_mem _ _, rfl, by kernel_rfl⟩\n"
  text := text ++ "\n"
  let mut found := false
  for (definition, index) in program.payload.protocols.zipIdx do
    if !output.protocols.isEmpty && !output.protocols.contains index then continue
    if !output.roles.isEmpty && !output.roles.contains 1 then continue
    for (callback, callbackIndex) in (callbacks definition.body).zipIdx do
      if regionText callback.body != regionText ZkcExamples.Structured.SumcheckVerifierBodies.roundBody then continue
      if repeatText callback.spec != repeatText (ZkcExamples.Structured.SumcheckVerifierBodies.repeatSpec callback.spec.maximum) then continue
      found := true
      let name := roleName index 1 ++ "Callback" ++ toString callbackIndex
      text := text ++ "theorem " ++ name ++ "_body_template : " ++ name ++
        "Body = SumcheckVerifierBodies.roundBody := by\n  kernel_rfl\n\n" ++
        "theorem " ++ name ++ "_template (ctx : ProtocolContext) (index : Option Nat)\n" ++
        "    (table : Option (List F)) (dimension width : Option Nat) (privatePoint point : Option (List F))\n" ++
        "    (claim : Option F) (service : Option Nat) :\n" ++
        "    " ++ name ++ "Process (G := G) ctx index table dimension width privatePoint point claim service =\n" ++
        "      (SumcheckVerifierLaws.roundPlain ctx service (point, claim)).bind\n" ++
        "        (fun result => .done (SumcheckVerifierLaws.embedV result)) := by\n" ++
        "  unfold " ++ name ++ "Process SumcheckVerifierLaws.roundPlain\n" ++
        "  simp only [PIR.Process.bind.eq_3]\n  congr 1\n  funext low\n  congr 1\n  funext high\n" ++
        "  cases claim with\n  | none => rfl\n  | some current =>\n" ++
        "    dsimp only\n    by_cases passed : current = low + high\n" ++
        "    · simp only [ite_eq_left passed]\n      cases service with\n      | none => rfl\n      | some handle =>\n" ++
        "        dsimp only\n        congr 1\n        funext challenge\n" ++
        "        congr 1\n        funext acknowledgement\n        cases point <;> rfl\n" ++
        "    · simp only [ite_eq_right passed, PIR.Process.bind.eq_2]\n\n" ++
        "theorem " ++ name ++ "_family_source (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)\n" ++
        "    (index : Option Nat) (table : Option (List F)) (dimension width : Option Nat)\n" ++
        "    (privatePoint point : Option (List F)) (claim : Option F) (service : Option Nat) :\n" ++
        "    " ++ name ++ "Body.denote (participantMeaningWith (.silent _) (participantActions F G)\n" ++
        "      (helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx)\n" ++
        "      (Values.cons index (.cons table (.cons dimension (.cons width (.cons privatePoint\n" ++
        "        (.cons point (.cons claim (.cons service .nil)))))))).get =\n" ++
        "      (SumcheckVerifierLaws.roundPlain ctx service (point, claim)).bind\n" ++
        "        (fun result => .done (SumcheckVerifierLaws.embedV result)) :=\n" ++
        "  (" ++ name ++ "_source ctx distinct _).trans (" ++ name ++
        "_template ctx index table dimension width privatePoint point claim service)\n\n" ++
        "theorem " ++ name ++ "_loop_family (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)\n" ++
        "    (start count : Nat) (service : Option Nat) (state : Option (List F) × Option F) :\n" ++
        "    Repeat.loop " ++ repeatText callback.spec ++ " ctx (ctx.roles 1) (SumcheckVerifierLaws.cap service)\n" ++
        "      ((Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx\n" ++
        "        (ctx.roles 1)).callback " ++ repeatText callback.spec ++ " " ++ name ++ "Body)\n" ++
        "      start count (SumcheckVerifierLaws.embedV state) =\n" ++
        "      (PIR.repeatN count (SumcheckVerifierLaws.roundPlain ctx service) state).bind\n" ++
        "        (fun result => .done (SumcheckVerifierLaws.embedV result)) := by\n" ++
        "  rw [" ++ name ++ "_body_template]\n" ++
        "  exact SumcheckVerifierLaws.loop_optional payload helper_bodies ctx (ctx.roles 1) rfl\n" ++
        "    (fun same => distinct 0 (by decide) (by decide) same) start count " ++ toString callback.spec.maximum ++
        " service state\n\n"
  unless found do throw "endpoint-template-no-complete-body-match"
  return text ++ "end " ++ output.moduleName ++ "Sumcheck\n"

end Tests.Generators.SumcheckBindings

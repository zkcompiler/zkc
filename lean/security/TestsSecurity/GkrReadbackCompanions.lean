import ZkcSecurityExamples.Gkr.HonestHelpersSource

/-! Focused controls for the actual producer helpers and a changed calling
composition. No canonical GKR root or protocol-security receipt is built here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace TestsSecurity.GkrReadbackCompanions
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Realizations.Gkr.HonestHelpers
open ReadbackGoals ReadbackCompanion

private abbrev model := ringModel Int Int

-- These declarations reuse the actual source bodies and complete signatures.
private def definition (helper : Helper) (body : Region dialect helper.inputs helper.outputs) :
    CheckedDefinition :=
  ⟨helper.name, helper.kind, helper.inputs, helper.outputs, body.erase, body,
    body.elaborate_erase⟩

private def stepDefinition := definition GkrSourceBodies.helper53Helper Step.body
private def callbackDefinition := definition GkrSourceBodies.helper54Helper Callback.body
private def alteredStep := definition GkrSourceBodies.helper53Helper (.stop .abort)

/-- The actual callback body is unchanged, but its actual dependency now stops. -/
theorem altered_dependency_stops :
    invoke (closedMeaningsOn model [alteredStep, callbackDefinition])
      GkrSourceBodies.helper54Helper
      (Callback.Inputs.pack { current := 7, index := 0, value := 11, source := [11], position := 0 }) =
      .halt .abort := by rfl

/-- A matching dependency name and ABI cannot install its old body law. -/
theorem altered_dependency_not_associated :
    ¬ BodyIn [alteredStep, callbackDefinition] GkrSourceBodies.helper53Helper Step.body := by
  rintro ⟨selected, member, signature, body⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases body
  · have mismatch : callbackDefinition.helper.name ≠ GkrSourceBodies.helper53Helper.name := by
      decide +kernel
    exact mismatch (congrArg Helper.name signature)

theorem altered_dependency_not_realized :
    ¬ (callbackLaw model).Realizes (helper := GkrSourceBodies.helper54Helper)
      (closedMeaningsOn model [alteredStep, callbackDefinition]) := by
  intro claimed
  have wrong := claimed (Callback.Inputs.pack
    { current := 7, index := 0, value := 11, source := [11], position := 0 })
  rw [altered_dependency_stops] at wrong
  contradiction

/-- Checked overflow and an allowed out-of-bounds read have different outcomes. -/
example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper57Helper
    (Element.Inputs.pack { source := [3, 5], position := 2 }) = .done (Element.encode model ⟨0⟩) :=
  element_equation [3, 5] 2 (by decide +kernel) (by decide +kernel)

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper70Helper
    (Element.Inputs.pack { source := [3, 5], position := indexLimit - 1 }) = .halt .refused :=
  element_after_overflow [3, 5] (indexLimit - 1) (by decide +kernel)

/-- An empty scan has no reached equality/increment, even at an invalid index. -/
example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper57Helper
    (Element.Inputs.pack { source := [], position := indexLimit }) = .done (Element.encode model ⟨0⟩) := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := Int) (G := Int)).element
    (Element.Inputs.pack { source := [], position := indexLimit })
  change _ = primitiveOutcome (Element.encodeOutcome model (elementReference model [] indexLimit)) at law
  simpa only [elementReference, scanReference, List.length_nil,
    show 0 < indexLimit by decide +kernel, ↓reduceIte,
    Zkc.Algorithms.ListReadback.scan_empty, Element.encodeOutcome, primitiveOutcome] using law

example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper57Helper
    (Element.Inputs.pack { source := [3], position := indexLimit }) = .halt .refused := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := Int) (G := Int)).element
    (Element.Inputs.pack { source := [3], position := indexLimit })
  change _ = primitiveOutcome (Element.encodeOutcome model (elementReference model [3] indexLimit)) at law
  simpa only [elementReference, scanReference, List.length_cons, List.length_nil,
    show 0 + 1 < indexLimit by decide +kernel, ↓reduceIte,
    Zkc.Algorithms.ListReadback.scan_refused indexLimit indexLimit (3 : Int) [] 0 0
      (by simp), Element.encodeOutcome, primitiveOutcome] using law

/-- Domain exhaustion is preserved before any callback or index check. -/
example (source : List Int) (exhausted : ¬ source.length < indexLimit) :
    invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper57Helper
      (Element.Inputs.pack { source, position := indexLimit }) = .halt .exhausted := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := Int) (G := Int)).element
    (Element.Inputs.pack { source, position := indexLimit })
  change _ = primitiveOutcome (Element.encodeOutcome model (elementReference model source indexLimit)) at law
  simpa only [elementReference, scanReference, exhausted, ↓reduceIte,
    Element.encodeOutcome, primitiveOutcome] using law

/-- The successor fails before shape admission, even on an exhausted source. -/
example (source : List Int) (_exhausted : ¬ source.length < indexLimit) :
    invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.helper70Helper
      (Element.Inputs.pack { source, position := indexLimit - 1 }) = .halt .refused :=
  element_after_overflow source (indexLimit - 1) (by decide +kernel)

/-- The full fold result includes the advanced cursor, not only the selection. -/
example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.scopedHelper82Helper
    (Scan.Inputs.pack { source := [11, 13], current := 7, index := 2, position := 3 }) =
      .done (Scan.encode model ⟨13, 4⟩) :=
  read_fold [11, 13] 3 2 7 (by decide +kernel) (by decide +kernel)

/-- The actual scan still checks later increments after selecting its value. -/
example : invoke (GkrSourceLaws.helpers (F := Int) (G := Int)) GkrSourceBodies.scopedHelper82Helper
    (Scan.Inputs.pack
      { source := [3, 5], current := 0, index := indexLimit - 2, position := indexLimit - 2 }) = .halt .refused := by
  simp only [GkrSourceLaws.helpers, closedMeanings_eq_closedMeaningsOn]
  have law := (readback_laws (F := Int) (G := Int)).scan
    (Scan.Inputs.pack
      { source := [3, 5], current := 0, index := indexLimit - 2, position := indexLimit - 2 })
  change _ = primitiveOutcome (Scan.encodeOutcome model
    (scanReference model [3, 5] 0 (indexLimit - 2) (indexLimit - 2))) at law
  simpa only [show scanReference model [3, 5] 0 (indexLimit - 2) (indexLimit - 2) =
    .stopped .refused from rfl, Scan.encodeOutcome, primitiveOutcome] using law

/-- A wrong cursor cannot discharge the complete generated correspondence. -/
theorem wrong_cursor_refused :
    ¬ Step.Goal model
      (fun current index value position => .returned ⟨if index = position then value else current, index⟩)
      (fun _ _ _ _ _ => True) := by
  intro wrong
  have changed := wrong [] 7 0 11 0 trivial
  have impossible : (1 : Nat) = 0 :=
    congrArg Step.Output.nextIndex (PIR.Process.done.inj changed)
  cases impossible

-- Changed source composition: reordered caller inputs, an extra Boolean
-- context input, an extra helper boundary, and successor readback through the actual
-- producer helper. The complete actual typed body fixes the generated goal.
private def variantHelper : Helper :=
  ⟨"successor-readback-with-context", .local,
    [.index, .boolean, .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩

private def variantBody : Region dialect variantHelper.inputs variantHelper.outputs :=
  .letOp (.mark "readback") .nil .nil <|
    .letOp (.invoke GkrSourceBodies.helper70Helper)
      (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
      .ret (.cons .here .nil)

helper_presentation Variant inputs [position, retained, source] outputs [value] := variantBody

private def variantLibrary := forward_reference% Variant.body using (afterLaw model)

private def variantReference (position : Nat) (_retained : Bool) (source : List Int) :
    PIR.Outcome (Variant.Output model) :=
  match afterReference model source position with
  | .returned result => .returned ⟨result.value⟩
  | .stopped reason => .stopped reason

theorem variant_companion : Variant.Goal model variantReference
    (fun table _ _ _ => (afterLaw model).Realizes (helper := GkrSourceBodies.helper70Helper) table) := by
  apply Variant.of_law model _ _ variantLibrary rfl
  · intro position retained source
    change After.encodeOutcome model (afterReference model source position) = _
    cases outcome : afterReference model source position <;>
      simp [variantReference, outcome, After.encodeOutcome, After.encode,
        Variant.encodeOutcome, Variant.encode]
  · intro table position retained source dependency; exact dependency _

private def variantDefinition := definition variantHelper variantBody

-- Reassemble only the source helpers of this readback slice. Each body comes
-- from the retained actual source; no independent ideal implementation is used.
private def definitions :=
  [definition GkrSourceBodies.helper46Helper Zero.body,
    definition GkrSourceBodies.scopedHelper74Helper ZeroWrapper.body,
    stepDefinition, callbackDefinition,
    definition GkrSourceBodies.scopedHelper82Helper Scan.body,
    definition GkrSourceBodies.helper56Helper ScanWrapper.body,
    definition GkrSourceBodies.helper57Helper Element.body,
    definition GkrSourceBodies.helper70Helper After.body]

set_option maxRecDepth 20000 in
private theorem linked : DeclarationsLinked [] (definitions ++ [variantDefinition]) := by
  decide +kernel

private theorem bodies : Bodies (definitions ++ [variantDefinition]) := by
  bind_structured_bodies

private def variantLaw := Variant.law model variantReference
  (fun table _ _ _ => (afterLaw model).Realizes (helper := GkrSourceBodies.helper70Helper) table)
  variant_companion

/-- The variant is installed against its own body and all actual dependencies. -/
theorem variant_actual (position : Nat) (retained : Bool) (source : List Int) :
    invoke (closedMeaningsOn model (definitions ++ [variantDefinition])) variantHelper
      (.cons position (.cons retained (.cons source .nil))) =
      primitiveOutcome (Variant.encodeOutcome model (variantReference position retained source)) := by
  apply variantLaw.invoke (helper := variantHelper) _ linked
  · exact BodyIn.of_mem (List.mem_append_right _ List.mem_cons_self) rfl rfl
  · exact (install model _ linked bodies).after

example : invoke (closedMeaningsOn model (definitions ++ [variantDefinition])) variantHelper
    (.cons 0 (.cons false (.cons [3, 5] .nil))) = .done (Variant.encode model ⟨5⟩) := by
  rw [variant_actual]
  rfl

example : invoke (closedMeaningsOn model (definitions ++ [variantDefinition])) variantHelper
    (.cons 2 (.cons true (.cons [3, 5] .nil))) = .done (Variant.encode model ⟨0⟩) := by
  rw [variant_actual]
  rfl

example : invoke (closedMeaningsOn model (definitions ++ [variantDefinition])) variantHelper
    (.cons (indexLimit - 1) (.cons true (.cons [] .nil))) = .halt .refused := by
  rw [variant_actual]
  rfl

/-- Optional producer consumers still use the complete present helper output. -/
example : invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
    GkrSourceBodies.helper57Helper
    (.cons (some [3, 5]) (.cons (some 2) .nil)) = .done (.cons (some 0) .nil) :=
  element_component (F := ℚ) (G := ℚ) [3, 5] 2 (by decide +kernel) (by decide +kernel)

#print axioms ReadbackGoals.Scan.equation
#print axioms ReadbackCompanion.scan
#print axioms ReadbackCompanion.install
#print axioms element_equation
#print axioms altered_dependency_not_associated
#print axioms altered_dependency_not_realized
#print axioms wrong_cursor_refused
#print axioms variant_actual
end TestsSecurity.GkrReadbackCompanions

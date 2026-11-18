import Zkc.Core.Transform.Annotated
import Zkc.Core.Admission.Admit
import Zkc.Tests.Core.Facts

namespace Zkc.Core.BodyAnalysis.AnnotatedFunctionTests
open FactsTests
open HeaderContracts (add less negate)

/-- The associativity of natural addition supplies the inequality required by subtraction. -/
private def association : Lemma field.Ty (LocalRaw field) :=
  ⟨[.nat, .nat, .nat], [], negate (less (add (add (.arg 0) (.arg 1)) (.arg 2))
    (add (.arg 0) (add (.arg 1) (.arg 2))))⟩

private theorem association_valid (M : Model field) {hs : List (FnHeader field)} (table : FnTable M hs) :
    association.Valid (HeaderContracts.Runs M table) (localReading M)
      (TypedValue (localSem M hs table) (ValidDyn M)) := by
  intro args typed premises
  change ArgumentsMatch (TypedValue (localSem M hs table) (ValidDyn M)) args [.nat, .nat, .nat] at typed
  cases typed with
  | cons h₁ xs =>
    cases xs with
    | cons h₂ xs =>
      cases xs with
      | cons h₃ xs =>
        cases xs
        rename_i x y z
        obtain ⟨τ, x⟩ := x
        obtain ⟨υ, y⟩ := y
        obtain ⟨ω, z⟩ := z
        obtain ⟨_, rfl⟩ := h₁
        obtain ⟨_, rfl⟩ := h₂
        obtain ⟨_, rfl⟩ := h₃
        let args : List (localSem M hs table).Dyn := [⟨.nat,x⟩,⟨.nat,y⟩,⟨.nat,z⟩]
        have a : (Expr.arg (Raw := LocalRaw field) 0).Denotes (HeaderContracts.Runs M table) args ⟨.nat,x⟩ := .arg rfl
        have b : (Expr.arg (Raw := LocalRaw field) 1).Denotes (HeaderContracts.Runs M table) args ⟨.nat,y⟩ := .arg rfl
        have c : (Expr.arg (Raw := LocalRaw field) 2).Denotes (HeaderContracts.Runs M table) args ⟨.nat,z⟩ := .arg rfl
        have left := HeaderContracts.add_denotes M table (HeaderContracts.add_denotes M table a b) c
        have right := HeaderContracts.add_denotes M table a (HeaderContracts.add_denotes M table b c)
        refine ⟨_, HeaderContracts.negate_denotes M table (HeaderContracts.less_denotes M table left right), ?_⟩
        change some (!decide (x + y + z < x + (y + z))) = some true
        simp [Nat.add_assoc]

private def header : FnHeader field := ⟨⟨9⟩,[.nat,.nat,.nat],[.nat],false,none,Summary.empty⟩

private def source : Region (LocalRaw field) Unit :=
  .mk [0,1,2] [.op ⟨1⟩ [3] plus [0,1], .op ⟨2⟩ [4] plus [3,2],
    .op ⟨3⟩ [5] plus [1,2], .op ⟨4⟩ [6] plus [0,5],
    .op ⟨5⟩ [7] minus [4,6]] [7]

private def fn : TypedFn field [] header :=
  (typeFn [] header source).toOption.get (by decide +kernel)
private def catalog : FunctionContracts ([] : List (FnHeader field)) :=
  (FunctionContracts.check []).toOption.get (by decide +kernel)
private def notes : Annotations (LocalRaw field) :=
  [(.instruction ⟨.root,4⟩ ⟨5⟩, .step 0 [0,1,2])]

example : (catalog.checkFunction fn).isOk = false := by decide +kernel

private theorem accepted : catalog.checkFunction fn [association] notes = .ok [] := by
  have checked : (catalog.checkFunction fn [association] notes).toOption = some [] := by decide +kernel
  cases h : catalog.checkFunction fn [association] notes <;> simp_all [Except.toOption]

private theorem evidence : catalog.AnnotationEvidence fn [association] notes := by
  constructor
  · intro M table _ l mem
    obtain rfl := List.mem_singleton.mp mem
    exact association_valid M table
  · intro M table _ ins _ _
    exact everyFact_of_noGiven _ rfl _ _ _

theorem associativeDifferenceAssured : fn.Assured [] :=
  catalog.checkAnnotated_assured fn evidence accepted

/-- Rebinding the third formal to the first actual still type-checks. The resulting
law does not justify the subtraction that uses the original third input. -/
example : (catalog.checkFunction fn [association]
    [(.instruction ⟨.root,4⟩ ⟨5⟩, .step 0 [0,1,0])]).isOk = false := by decide +kernel

/-- The source's safety was established by a producer. Its original unannotated walk
refuses the subtraction, while comparison with the annotated candidate succeeds. -/
theorem annotatedReplacement :
    fn.Assured [] ∧ fn.SameAs fn := by
  have compared : (catalog.compareFunctions fn fn [association] [] notes).toOption = some [] := by
    decide +kernel
  apply catalog.compareAnnotated_assured fn fn associativeDifferenceAssured.safe evidence
    (sourceNotes := [])
  cases h : catalog.compareFunctions fn fn [association] [] notes <;> simp_all [Except.toOption]

/-- The named program and the typed function retain the exact lexical binding. -/
private def annotated : TypedFn field [] header :=
  (typeFn [] header source notes).toOption.get (by decide +kernel)

private def written : NamedProgram field :=
  ⟨[.fn header.key header.ins header.outs header.canStop header.kernel header.summary source notes]⟩

private def elaborated : Typed field :=
  (elaborateFunctions written).toOption.get (by decide +kernel)

example : erase elaborated = written := by
  apply erase_elab
  rfl

private theorem storedEvidence : catalog.AnnotationEvidence annotated [association] annotated.notes :=
  catalog.evidenceOfLaws annotated rfl evidence.laws

example : (annotated.admitAnnotated catalog [association] storedEvidence).isOk = true := by decide +kernel

example : ((⟨fn, [], associativeDifferenceAssured⟩ : AssuredFn field [] header).stepAnnotated
    annotated catalog [association] storedEvidence).isOk = true := by decide +kernel

private def loopSite : AnnotationSite := .instruction .root ⟨1⟩

private def literalBool (b : Bool) : Expr (LocalRaw field) := .apply (.literal .bool [b.toNat]) .nil 0

private def loopWith (annotations : Annotations (LocalRaw field)) : Definition field :=
  .fn ⟨12⟩ [] [] false none Summary.empty (.mk [] [
    .loop ⟨1⟩ () (.fixed 2) [] [] (.mk [0] [] [])] []) annotations

private def namedVerdict (definition : Definition field) : Except (List (AdmissionRefusal field)) Unit :=
  (Zkc.Core.checkDefinition (V := field) ⟨[], []⟩ definition).map fun _ => ()

example : (namedVerdict (loopWith [(loopSite, .invariant [] [literalBool true])])).isOk = true := by
  decide +kernel

private def refusals (definition : Definition field) : List (AdmissionRefusal field) :=
  match namedVerdict definition with
  | .ok _ => []
  | .error rs => rs

private def loopPlace : Place := ⟨⟨12⟩, [], some ⟨1⟩, none⟩

example : refusals (loopWith [(loopSite, .fact [] (literalBool true))]) =
    [.definition (.fn ⟨.factEvidence, loopPlace, .annotationSite loopSite⟩)] := by decide +kernel

example : refusals (loopWith [(loopSite, .step 0 [])]) =
    [.definition (.fn ⟨.annotation, loopPlace, .annotationSite loopSite⟩)] := by decide +kernel

private def missingSite : AnnotationSite := .instruction ⟨.root,1⟩ ⟨7⟩

example : refusals (loopWith [(missingSite, .invariant [] [])]) =
    [.definition (.fn ⟨.annotation, ⟨⟨12⟩, [], some ⟨7⟩, none⟩, .annotationSite missingSite⟩)] := by decide +kernel

/-- A syntactically valid assertion needs to hold on entry to a real loop. -/
example : (refusals (loopWith [(loopSite, .invariant [] [literalBool false])])).head? =
    some (.definition (.fn ⟨.loopInvariant, loopPlace, .invariant loopSite 0 false⟩)) := by decide +kernel

#print axioms annotatedReplacement
#print axioms associativeDifferenceAssured
end Zkc.Core.BodyAnalysis.AnnotatedFunctionTests

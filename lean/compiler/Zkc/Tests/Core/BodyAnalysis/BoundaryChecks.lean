import Zkc.Core.Facts.Contracts.AnnotationLaws
import Zkc.Core.Facts.Body.ComparisonSound
import Zkc.Core.Facts.Contracts.RoleIndex

namespace Zkc.Core.BodyAnalysis.Checks

private def statement : Lemma Bool Unit := ⟨[false, true], [], .arg 0⟩
private def closedStatement : Lemma Bool Unit := ⟨[], [], .apply () .nil 0⟩
private def names := (Ctx.empty.insert 10 false).insert 20 true

example : Lemma.resolve? [statement] names 0 [10, 20] = some statement := rfl
example : Lemma.resolve? [statement] names 0 [20, 10] = none := rfl
example : Lemma.resolve? [statement] names 0 [10] = none := rfl
example : Lemma.resolve? [statement] names 0 [10, 30] = none := rfl
example : Lemma.resolve? [closedStatement] Ctx.empty 0 [] = some closedStatement := rfl
example : Lemma.resolve? [closedStatement] Ctx.empty 1 [] = none := rfl

/-- A value shared by two roles gives the loop-local index through an actual role operation. -/
example {V : Vocabulary} {hs : Headers V} (M : Model V) (fns : FnTable M hs.fns)
    (roles : RTable M hs.protocols) (n : Nat) (key : Key) (path : List Frame) :
    let sem := roleSem M 0 fns roles
    let ok : (roleDialect V hs 0).Count [0] ⟨.nat, [0, 1]⟩ := by simp
    sem.op key (roleIndexFromCount ok) path (.cons (hide M 0 ⟨.nat, [0, 1]⟩ n) .nil) =
      .done (.cons (sem.index [0] n) .nil) := by
  let ok : (roleDialect V hs 0).Count [0] ⟨.nat, [0, 1]⟩ := by simp
  have run := roleIndexFromCount_denote M fns roles ok (hide M 0 ⟨.nat, [0, 1]⟩ n) key path
  have counted : (roleSem M 0 fns roles).count ok (hide M 0 ⟨.nat, [0, 1]⟩ n) = n :=
    reveal_hide M (a := ⟨.nat, [0, 1]⟩) ok.2.1 n
  exact counted ▸ run

private def dialect : Dialect where
  Ty := Unit
  Op _ _ := Unit
  Who := Unit
  Condition _ _ := True
  Alternatives _ _ _ := True
  Count _ _ := True
  index _ := ()
  Attempt _ := True
  Gives _ _ := True
  collected _ _ := ()

private def repeated : Term dialect Ctx.empty [] :=
  .step ⟨7⟩ (.op () .nil) .nil (.ret .nil)

private def unrolled : Term dialect Ctx.empty [] :=
  .step ⟨10⟩ (.block 0 repeated) .nil
    (.step ⟨10⟩ (.block 1 repeated) .nil (.ret .nil))

private def selected : AnnotationSite := .instruction (StaticCursor.root.block ⟨10⟩ 0) ⟨7⟩
private def stepNotes : Annotations Unit := [(selected, .step 0 [])]

/-- The structural obligation is imposed at precisely the selected copy of the repeated body. -/
example (σ : Setting dialect Unit) (registered : σ.notes = stepNotes) :
    Term.AnnotationsDefined σ .root unrolled ↔
      StepsDefinedAt σ Ctx.empty selected := by
  simp [unrolled, repeated, Term.AnnotationsDefined, Instr.AnnotationsDefined,
    StepsDefinedAt, registered, selected, stepNotes, Annotations.at_, Instr.site,
    StaticCursor.root, StaticCursor.next, StaticCursor.block]

/-- Empty sibling blocks can share both the printed key and the unrolling number. -/
example : Annotations.at_ ([(.block .root ⟨10⟩ 0, .step 0 [])] : Annotations Unit)
    (.block StaticCursor.root.next ⟨10⟩ 0) = [] := rfl

example : Annotations.at_ ([(.block .root ⟨10⟩ 0, .step 0 [])] : Annotations Unit)
    (.block .root ⟨10⟩ 1) = [] := rfl

example (cfg : Config dialect Unit) (ids : Ctx Ident) (s : State Unit) (k : cfg.domain.State) :
    atEntry cfg stepNotes (.instruction (StaticCursor.root.next.block ⟨10⟩ 1) ⟨7⟩) ids s k =
      (s, k) := rfl

local instance : DecidableEq dialect.Ty := inferInstanceAs (DecidableEq Unit)

private def signature : AssertionTypes Unit Unit := ⟨fun _ ins => if ins.isEmpty then some [()] else none, fun _ => true⟩
private def closed : Lemma Unit Unit := ⟨[], [], .apply () .nil 0⟩

example : checkAnnotations signature [closed] unrolled stepNotes = true := rfl
example : checkAnnotations signature [] unrolled stepNotes = false := rfl
example : checkAnnotations signature [closed] unrolled [(selected, .step 0 [22])] = false := rfl
example : checkAnnotations signature [] unrolled [(selected, .invariant [] [])] = false := rfl
example : checkAnnotations signature [] unrolled
    [(.instruction .root ⟨999⟩, .fact [] (.apply () .nil 0))] = false := rfl
example : checkAnnotations signature [] unrolled [(selected, .fact [] (.apply () .nil 1))] = false := rfl

/-- A failure is returned before consulting the domain, even for a zero-premise step. -/
example (cfg : Config dialect Unit) (noLemmas : cfg.lemmas = []) (start : Values Unit) :
    analyseCheckedFrom {cfg with assertions := signature} stepNotes ⟨[], []⟩ .nil unrolled start = .error .annotations := by
  simp only [analyseCheckedFrom, noLemmas]
  rfl

private def unusedIllTyped : Lemma Unit Unit := ⟨[], [], .arg 0⟩

example : checkDefinition signature [unusedIllTyped] .nil unrolled [] ⟨[], []⟩ = .error .registry := rfl
example : checkDefinition signature [closed] .nil unrolled stepNotes ⟨[], []⟩ = .ok () := rfl
example (cfg : Config dialect Unit) :
    checkFacts {cfg with assertions := signature, lemmas := []} stepNotes ⟨[], []⟩ .nil unrolled =
      .error (.definition .annotations) := rfl
example (cfg : Config dialect Unit) (cmp : SkelRules dialect) :
    follows {cfg with assertions := signature, lemmas := []} cmp ⟨2⟩ [] stepNotes ⟨[], []⟩ .nil .nil
      unrolled unrolled = false := rfl
example (cfg : Config dialect Unit) (cmp : SkelRules dialect) :
    follows {cfg with assertions := signature, lemmas := []} cmp ⟨2⟩ stepNotes [] ⟨[], []⟩ .nil .nil
      unrolled unrolled = false := rfl
example : Concern.premise (Raw := Unit) (.block .root ⟨10⟩ 0) (.step 0 []) ≠
    .premise (.block StaticCursor.root.next ⟨10⟩ 0) (.step 0 []) := by
  intro eq
  have sites := (Concern.premise.inj eq).1
  cases sites

example : checkDefinition signature [] .nil unrolled []
    ⟨[], [⟨.apply () .nil 0, some (.arg 0)⟩]⟩ = .error .contract := rfl

#print axioms Lemma.resolve?_eq_some
#print axioms Lemma.valid_iff_typed
#print axioms finalIndex_sound
#print axioms roleIndexFromCount_denote
#print axioms roleIndexAt_denote

end Zkc.Core.BodyAnalysis.Checks

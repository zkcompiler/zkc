import Zkc.Source.Interpretation
import Zkc.Semantics.MonadInterpretation
import Zkc.Semantics.InterpretationAdmission
import Zkc.Source.PhaseAdmissionInterpretation

/-! Discriminating controls for expanded calls and staged source interpretation. -/

set_option autoImplicit false

namespace Tests.Interpretation

open PIR

abbrev abstractCall : Signature := ⟨Unit, fun _ => Nat⟩
abbrev concreteCalls : Signature := ⟨Nat, fun _ => Nat⟩

def expand : OperationInterpretation abstractCall concreteCalls := fun _ =>
  .call 1 (fun first => .call 2 (fun second => .done (first + second)))

def backend : Handler concreteCalls Nat Nat := fun op state =>
  ⟨if op == 2 then .stopped .abort else .returned state, state + 1, [op]⟩

def source : Proc abstractCall Nat := .call () (fun value => .done (value + 100))

example : (source.interpret expand).run backend 7 =
    ⟨.stopped .abort, 9, [1, 2]⟩ := rfl

example : source.run (fun op state => (expand op).run backend state) 7 =
    ⟨.stopped .abort, 9, [1, 2]⟩ := rfl

def pairBackend : Handler concreteCalls (Nat × Unit) Nat := fun op state =>
  let result := backend op state.1
  ⟨result.outcome, (result.state, state.2), result.events⟩

/-- A private layout change preserves the actual stopped post-state and both
events, not just the success reply type. -/
example : Related (fun s (t : Nat × Unit) => s = t.1)
    (fun e : Nat => [e]) (fun e : Nat => [e])
    (source.run (fun op state => (expand op).run backend state) 7)
    ((source.interpret expand).run pairBackend (7, ())) := by
  apply Proc.run_interpret_related expand _ pairBackend _ _ _ _ source 7 (7, ()) rfl
  intro op s t initial
  rcases t with ⟨t, u⟩
  cases op
  cases u
  change s = t at initial
  subst s
  exact ⟨rfl, rfl, rfl⟩

/-- An incorrectly collapsed call loses the earlier event and post-state. -/
example : (source.interpret expand).run backend 7 ≠
    source.run (fun _ state => backend 2 state) 7 := by
  intro same
  have states := congrArg Execution.state same
  change (9 : Nat) = 8 at states
  contradiction

example : (source.interpret expand).runM (m := Id) backend 7 =
    source.runM (m := Id) (fun op state => (expand op).runM backend state) 7 :=
  Proc.runM_interpret (m := Id) expand backend source 7

open Zkc.Source

abbrev vocabulary : Language := ⟨Unit, Unit, fun _ => [], fun _ => (), ()⟩

abbrev meaning : Interpretation vocabulary abstractCall where
  Value _ := Nat
  condition value := value != 0
  operation _ _ := .call () .done

def structured : Program vocabulary [()] () :=
  .branch .here
    (.iterate 3 .here (.letOp () .nil (.ret .here)) (.ret .here))
    (.stop .reject)

example (env : Environment meaning.Value [()]) :
    structured.denote (meaning.translate expand) env =
      (structured.denote meaning env).interpret expand :=
  Program.denote_translate meaning expand structured env

example : ((structured.denote (meaning.translate expand)
    (Values.cons 1 .nil).get).run backend 7).events = [1, 2] := rfl

abbrev upper : Interaction abstractCall :=
  ⟨Unit, Nat, fun _ => (), fun phase _ => phase = 0, fun _ _ _ => 1⟩

abbrev lower : Interaction concreteCalls :=
  ⟨Unit, Nat, fun _ => (), fun phase op => op = phase + 1, fun phase _ _ => phase + 1⟩

def admission : InterpretationAdmission upper lower expand where
  phases sourcePhase targetPhase := targetPhase = 2 * sourcePhase
  operation := by
    intro phase op enabled lowerPhase initial
    cases op
    subst phase
    change lowerPhase = 0 at initial
    subst lowerPhase
    exact ⟨⟨rfl, fun _ => ⟨rfl, fun _ => trivial⟩⟩, fun _ _ => rfl⟩

example : Conforms lower (source.interpret expand) 0 ∧
    Boundary.Returns lower (fun _ phase => ∃ upperPhase,
      upperPhase = 1 ∧ phase = 2 * upperPhase) (source.interpret expand) 0 :=
  admission.transport source (fun _ phase => phase = 1) 0 0
    ⟨rfl, fun _ => trivial⟩ (fun _ => rfl) rfl

example : Within 2 (source.interpret expand) :=
  Proc.within_interpret expand 2 (fun _ _ _ => trivial) source 1 (fun _ => trivial)

/-- Reply cardinality does not replace a uniform call bound. -/
example : ¬Within 1 (source.interpret expand) := by
  intro bounded
  exact bounded 0

/-- A legal entry with the wrong returning phase cannot be admitted. -/
example : ¬Boundary.Returns lower (fun _ phase => phase = 1) (expand ()) 0 := by
  intro returned
  have impossible : (2 : Nat) = 1 := returned 0 0
  contradiction

def policy : PhaseAdmission.Policy vocabulary Nat where
  step _ before := if before = 0 then some [1] else none

def summaryLaws : PhaseAdmission.Realizes policy meaning upper where
  relates := Eq
  operation := by
    intro op before exits accepted args phase initial
    subst phase
    cases op
    cases args
    by_cases enabled : before = 0
    · subst before
      simp [policy] at accepted
      subst exits
      exact ⟨⟨rfl, fun _ => trivial⟩, fun _ => ⟨1, by simp, rfl⟩⟩
    · simp [policy, enabled] at accepted

def lowerSummaryLaws : PhaseAdmission.Realizes policy (meaning.translate expand) lower :=
  summaryLaws.translate admission

def oneCall : Program vocabulary [] () := .letOp () .nil (.ret .here)

example : PhaseAdmission.check policy oneCall (.next .terminal) [0] = some [1] := by decide

example : PhaseAdmission.check policy oneCall .terminal [0] = none := rfl

example : Conforms lower (oneCall.denote (meaning.translate expand) Values.nil.get) 0 := by
  have checked := PhaseAdmission.check_sound policy (meaning.translate expand) lower
    lowerSummaryLaws oneCall (.next .terminal) [0] [1] (by decide) Values.nil.get 0
      ⟨0, by simp, 0, rfl, rfl⟩
  exact checked.1

end Tests.Interpretation

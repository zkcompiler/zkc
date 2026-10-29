import Zkc.Construction.ConnectionRouteCoverage

/-! Controls for reached-source coverage, independent of successful folding.
The absent splitPresent branch is deliberately uncovered. Physical relatedness
is essential, and arbitrary typed responses remain quantified. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRouteCoverageControls
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate ConnectionRouteCoverage

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "coverage"
  domains := []
  relations := []
  bindings := []
  definitions := []
  contracts := []
  catalogue := blsCatalogue

def routing : Original.Routing :=
  ⟨snapshot, .plain "coverage" ["P", "V"] 0 1, .validator, 0, [], [], [], []⟩

def missing (model : DomainModel) : PIR.Process (Occurrence.signature model.toCarriers) Nat :=
  .call (.action (.receive .index "missing" 0)) .done

example (model : DomainModel) : Original.fold routing (missing model) {} = .halt .refused := rfl

example (model : DomainModel) : ¬ Nonempty (Original.RouteCoverage routing [] [] (missing model)) := by
  rintro ⟨proof⟩
  have required := Original.RouteCoverage.action_required proof
  obtain ⟨_, origin, found⟩ := required
  have absent : routing.message [] "missing" 0 routing.self = none := rfl
  rw [absent] at found
  cases found

-- Simulation can certify two refusals while the original receive is unrouted.
example (model : DomainModel) : Original.Simulation (fun _ (_ : Unit) => True)
    (fun _ _ => True) (Original.fold routing (missing model) {}) (.halt .refused) :=
  .halt .refused

def optionalScope : Scope := [.component .index]
def subject : Subject optionalScope .index := .input .here
def layout : Layout optionalScope := [.data subject.comp]
def absent : Form [] [] optionalScope [] :=
  .receive .index "missing" 0 (.halt .exhausted)
def present : Form [] [] (.value .index :: optionalScope) [] := .halt .reject
def splitForm : Form [] [] optionalScope [] := .split subject.comp absent present

def splitAccepted : Derivation routing {} [] [] [] 1 [] [] none [] layout splitForm
    (fun _ _ => .halt .reject) :=
  .splitPresent subject 0 rfl rfl (.halt .reject)

example (model : DomainModel) (value : Nat) (history : Domain.History model.toCarriers) :
    Original.RouteCoverage routing [] [] (splitForm.denoteOn model Occurrence.actions ⟨[],[]⟩
      (LawResults.empty model) {} (runsAtOn model Occurrence.actions Occurrence.iterations
        ⟨[],[]⟩ [] {} 1) (noCallees model _) (.cons (some value) .nil)) :=
  (splitAccepted.covered model ⟨[],[]⟩ (fun entry => entry.elim0) []
    (noCallees model _) (fun inputs => noCallees_hold _ inputs)
    (.cons (some value) .nil) history [.data (.index value)] (.cons ⟨value,rfl,rfl⟩ .nil)).coverage

example (model : DomainModel) (history : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers) :
    ¬ Holds model (.cons none .nil) history layout environment := by
  intro related
  exact related.not_absent (reference := 0) rfl rfl

example (model : DomainModel) : ¬ Nonempty (Original.RouteCoverage routing [] []
    (splitForm.denoteOn model Occurrence.actions ⟨[],[]⟩ (LawResults.empty model) {}
      (runsAtOn model Occurrence.actions Occurrence.iterations ⟨[],[]⟩ [] {} 1)
      (noCallees model _) (.cons none .nil))) := by
  rintro ⟨proof⟩
  have required := Original.RouteCoverage.action_required proof
  obtain ⟨_, origin, found⟩ := required
  have absent : routing.message [] "missing" 0 routing.self = none := rfl
  change routing.message [] "missing" 0 routing.self = some origin at found
  rw [absent] at found
  cases found

-- Explicitly absent/literal branches may contain unreachable missing routes.
-- Their finite certificates establish which branch the source actually reaches.
def inactiveSplit : Form [] [] [] [] :=
  .split (.absent (ty := .index)) (.halt .reject) (.receive .index "missing" 0 (.halt .exhausted))
def inactiveAccepted : Derivation routing {} [] [] [] 1 [] [] none [] [] inactiveSplit
    (fun _ _ => .halt .reject) := .splitAbsent rfl (.halt .reject)
def inactiveCoverage (model : DomainModel) (history : Domain.History model.toCarriers) :=
  (inactiveAccepted.covered model ⟨[],[]⟩ (fun entry => entry.elim0) [] (noCallees model _)
    (fun inputs => noCallees_hold _ inputs) .nil history [] .nil).coverage

def literalSplit : Form [] [] [] [] :=
  .split (.present (.index 7)) (.receive .index "missing" 0 (.halt .exhausted)) (.halt .reject)
def literalAccepted : Derivation routing {} [] [] [] 1 [] [] none [] [] literalSplit
    (fun _ _ => .halt .reject) := .splitValue (.index 7) rfl (.halt .reject)
def literalCoverage (model : DomainModel) (history : Domain.History model.toCarriers) :=
  (literalAccepted.covered model ⟨[],[]⟩ (fun entry => entry.elim0) [] (noCallees model _)
    (fun inputs => noCallees_hold _ inputs) .nil history [] .nil).coverage

-- Every closed helper result and stop is retained; no protocol helper equality.
example (model : DomainModel) (reason : PIR.Stop) :
    Original.RouteCoverage (carriers := model.toCarriers) routing [] []
      ((PIR.Process.halt reason : PIR.Process closedInterface Nat).interpret
        (closedLift (I := Occurrence.signature model.toCarriers))) :=
  ConnectionActionCoverage.closed routing [] (.halt reason)

example (model : DomainModel) (source : PIR.Process closedInterface (Values model.Value [.index, .boolean])) :
    Original.RouteCoverage (carriers := model.toCarriers) routing [] []
      (source.interpret (closedLift (I := Occurrence.signature model.toCarriers))) :=
  ConnectionActionCoverage.closed routing [] source

-- Nested equal indices preserve the order of distinct source frames.
example (model : DomainModel) (outer inner : Nat) (reason : PIR.Stop) :
    Original.RouteCoverage (carriers := model.toCarriers) routing [] []
      (Occurrence.iterations.within "outer" outer
        (Occurrence.iterations.within "inner" inner (.halt reason : PIR.Process _ Unit))) :=
  Original.RouteCoverage.within "outer" outer
    (Original.RouteCoverage.within "inner" inner (.halt _ _ reason))

-- Inactive roles do not reach the callback, even if it is unrouted. Counts,
-- initial private values and capture values remain arbitrary.
example (model : DomainModel) (spec : RepeatSpec) (context : ProtocolContext) (role : Nat)
    (inactive : (spec.roles.map context.roles).contains role = false)
    (count : Option Nat) (state : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (callback : RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    Original.RouteCoverage routing [] []
      (denoteRepeatOn spec context role count state captures callback Occurrence.iterations "inactive") := by
  simp only [denoteRepeatOn, inactive, Bool.false_eq_true, ↓reduceIte]
  exact .done _ _

#print axioms Derivation.covered
#print axioms Certificate.routeCoverage
end Tests.ConnectionRouteCoverageControls

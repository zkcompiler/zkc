module

public import Zkc.Realization.QueryControllerPhase
public import Tests.QueryController

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryControllerPhase
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData QueryController

def header : Header := ⟨⟨9, 0, 0, 0, 0⟩, 0, 1, 1⟩
def stores : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence .index, rfl, ([10, 20] : List Nat)⟩]
def state : List Nat := List.range 9
def body := Phase.instructions 3
def yielded := Phase.output state 9

theorem recognized : (Phase.recognize 9 state body yielded).isSome = true := by decide +kernel

/-- The branch returns the complete carried state after replacing only its
phase. In particular the second answer remains selected. -/
theorem actual (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ header.encode stores <+: frame)
      (.done ({header with phase := 3}.encode stores))
      ((Domain.evaluate model program context body (header.encode stores)).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) :=
  (show Phase.Recognized body yielded from ⟨3, 9, state, rfl, rfl⟩).simulation
    model program context header stores (header.encode stores) rfl (by decide) rfl

theorem wrong_answer_refused :
    (Phase.recognize 9 state body [0, 1, 2, 3, 4, 5, 9, 0, 8]).isSome = false := by decide +kernel

theorem wrong_phase_operand_refused :
    (Phase.recognize 9 state body [0, 1, 2, 3, 4, 9, 6, 7, 8]).isSome = false := by decide +kernel

theorem lost_store_refused :
    (Phase.recognize 9 state body [0, 1, 2, 3, 4, 5, 9, 7]).isSome = false := by decide +kernel

/-- The generated Completed literal does not authorize a non-root return. -/
theorem nested_completion_refused :
    QueryController.leafHeader.continuation ≠ 0 := by decide

def baseHeader : Header := ⟨⟨7, 0, 0, 0, 0⟩, 0, 1, 0⟩
def baseStores : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence .index, rfl, ([10] : List Nat)⟩]
def rootBody := Root.instructions 9 3 "root"
def rootYielded := Phase.output state 11
abbrev baseSource := Tests.QuerySourceStack.innerContext.operations (E := Nat)
  Tests.QuerySourceStack.first.location Tests.QuerySourceStack.first.expansion
  (Tests.QuerySourceContext.child 0) (0, 0)

noncomputable def baseReturned : Returned (snapshot := OracleProcessData.snapshot)
    (domains := []) (math := OracleProcessData.math) (self := 1)
    QueryController.calls baseSource 0 (fun _ ↦ 0) QueryController.afterLeaf baseHeader where
  kind := OracleProcessData.kind
  answer := (10 : Nat)
  state := (11, 1)
  phase := 1
  events := [.query Tests.QuerySourceStack.leaf, .provider 4]
  kind_eq := rfl
  cell := rfl
  stack := .root
  reached := Tests.QueryNestedSource.leaf_return 0 0 0 11 0 0 10 4

def baseWork : Work (model := model) .base baseHeader QueryController.afterLeaf (fun _ _ ↦ []) where
  position := .returned []
  steps := 1
  replies := 1
  answers := 1
  saves := 0
  history := .respond (.advance (.nil _) (.base _)) (.base _)
  phase := rfl
  answerBound := by
    intro kind
    cases kind with | table row shape => cases row <;> simp [QueryController.afterLeaf]
  frameBound := fun _ _ ↦ Nat.le_refl _

/-- An actual base-provider execution, its allocation history and the emitted
root leaf compose in one application. The source reply, state and event remain
the same. This is the terminal arm, not a claim about the enclosing loops. -/
theorem source_finish (program : Program) (context : Context) :
    Nonempty (Work (model := model) .base {baseHeader with phase := 3}
      QueryController.afterLeaf (fun _ _ ↦ [])) ∧
    (∃ answer : model.Value .index,
      (QueryController.afterLeaf OracleProcessData.kind)[0]? = some answer ∧
      PIR.Reaches QueryController.calls baseSource 0
        (.done ⟨.returned answer, (11, 1), [.query Tests.QuerySourceStack.leaf, .provider 4]⟩) 1) ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ baseHeader.encode baseStores <+: frame)
      (.done ({baseHeader with phase := 3}.encode baseStores))
      ((Domain.evaluate model program context rootBody (baseHeader.encode baseStores)).bind fun final ↦
        match Domain.read final rootYielded with
        | some values => .done values
        | none => .halt .refused)) := by
  exact baseReturned.finish baseWork [] rfl
    (fun _ _ shape ↦ shape = .base) .base rfl rfl rfl
    ⟨9, 3, "root", state, rfl, rfl, rfl⟩ program context
    baseStores (baseHeader.encode baseStores) rfl rfl

/-- A non-root arm selection refuses before projecting Completed, even with
an otherwise well-formed state and a valid stored answer. -/
theorem nonroot_refused (program : Program) (context : Context) :
    let nested := {baseHeader with continuation := 1}
    Nonempty (Original.Simulation Eq (fun _ frame ↦ nested.encode baseStores <+: frame)
      (.halt .refused)
      ((Domain.evaluate model program context rootBody (nested.encode baseStores)).bind fun final ↦
        match Domain.read final rootYielded with
        | some values => .done values
        | none => .halt .refused)) := by
  exact (show Root.Recognized rootBody rootYielded from
    ⟨9, 3, "root", state, rfl, rfl, rfl⟩).simulation
      model program context {baseHeader with continuation := 1} baseStores _ rfl rfl

theorem root_guard_swapped :
    (Root.recognize 9 state (Root.instructions 9 5 "root") rootYielded).isSome = false := by
  decide +kernel

#print axioms actual
#print axioms wrong_answer_refused
#print axioms wrong_phase_operand_refused
#print axioms lost_store_refused
#print axioms source_finish
#print axioms nonroot_refused
#print axioms root_guard_swapped
end Tests.QueryControllerPhase

module

public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Scoped motion laws for total pure nodes in the canonical outcome process.
Invalid declarations and partial calculations cannot use these laws. Effectful
suffixes remain arbitrary Processes, so a later false result or failure cannot
remove a preceding action. These are transformation laws, not an instruction
interpreter or a replacement meaning for normalization's anchors. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source
variable {carriers : Structured.Carriers}

theorem read_append {env values : Domain.Environment carriers} {references : List Nat}
    (found : Domain.read env references = some values) (more : Domain.Environment carriers) :
    Domain.read (env ++ more) references = some values := by
  induction references generalizing values with
  | nil => exact found
  | cons reference rest ih =>
      simp only [Domain.read, List.mapM_cons] at found ⊢
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          have within := (List.getElem?_eq_some_iff.mp first).1
          rw [List.getElem?_append_left within, first]
          cases others : rest.mapM (env[·]?) with
          | none => simp [first, others] at found
          | some tail =>
              simp [first, others] at found
              subst values
              simp [show rest.mapM ((env ++ more)[·]?) = some tail from ih others]

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)

theorem step_calculate {calculation : Calculation} {references : List Nat}
    {env arguments results : Environment F G}
    (found : Domain.read env references = some arguments)
    (computed : Domain.calculate (Structured.ringModel F G) calculation arguments = .returned results)
    (sorted : results.map Domain.Value.sort = calculation.op.results.map ValueSort.data) :
    Domain.step (Structured.ringModel F G) program context
      ⟨.calculate calculation, references, calculation.op.results.map ValueSort.data, []⟩ env =
      .done (env ++ results) := by
  simp only [Domain.step, found, computed, Domain.sortsMatch, sorted, beq_self_eq_true, ite_true]

/-- At the explicit outcome boundary a successful pure node changes only the
SSA environment. Every action in the suffix remains in its original order. -/
theorem observation_calculate {calculation : Calculation} {references : List Nat}
    {env arguments results : Environment F G}
    (found : Domain.read env references = some arguments)
    (computed : Domain.calculate (Structured.ringModel F G) calculation arguments = .returned results)
    (sorted : results.map Domain.Value.sort = calculation.op.results.map ValueSort.data)
    (rest : List Instruction) (returned : List Nat) :
    observation program context
      (⟨.calculate calculation, references, calculation.op.results.map ValueSort.data, []⟩ :: rest)
      returned env = observation program context rest returned (env ++ results) := by
  unfold observation outcome
  rw [Domain.Correspondence.evaluate_cons, step_calculate program context found computed sorted]
  simp only [PIR.Process.bind, PIR.Process.interpret, Original.forgetCheckpoints]

/-- A total pure node can be removed when the final scope reads only its input
prefix. Correct operand sorts and metadata are structural scope facts. -/
theorem drop_dead_calculation (calculation : Calculation) (total : calculation.total = true)
    (references returned : List Nat) (env arguments selected : Environment F G)
    (found : Domain.read env references = some arguments)
    (data : calculation.op.arguments.all Domain.dataType = true)
    (sorted : arguments.map Domain.Value.sort = calculation.op.arguments.map ValueSort.data)
    (selectedEq : Domain.read env returned = some selected) :
    observation program context
      [⟨.calculate calculation, references, calculation.op.results.map ValueSort.data, []⟩] returned env =
      observation program context [] returned env := by
  obtain ⟨results, computed, resultsSorted⟩ := calculate_total calculation total arguments data sorted
  rw [observation_calculate program context found computed resultsSorted]
  simp only [observation, outcome, Domain.evaluate, PIR.Process.bind, readback,
    selectedEq, read_append selectedEq results]

/-- Two independent total calculations may exchange positions. The returned
scope swaps their physical slots back into the same semantic order. -/
theorem swap_calculations (first second : Calculation)
    (firstTotal : first.total = true) (secondTotal : second.total = true)
    (firstRefs secondRefs : List Nat) (env firstArgs secondArgs : Environment F G)
    (firstRead : Domain.read env firstRefs = some firstArgs)
    (secondRead : Domain.read env secondRefs = some secondArgs)
    (firstData : first.op.arguments.all Domain.dataType = true)
    (secondData : second.op.arguments.all Domain.dataType = true)
    (firstSorted : firstArgs.map Domain.Value.sort = first.op.arguments.map ValueSort.data)
    (secondSorted : secondArgs.map Domain.Value.sort = second.op.arguments.map ValueSort.data) :
    observation program context
      [⟨.calculate first, firstRefs, first.op.results.map ValueSort.data, []⟩,
       ⟨.calculate second, secondRefs, second.op.results.map ValueSort.data, []⟩]
      [env.length, env.length + 1] env =
    observation program context
      [⟨.calculate second, secondRefs, second.op.results.map ValueSort.data, []⟩,
       ⟨.calculate first, firstRefs, first.op.results.map ValueSort.data, []⟩]
      [env.length + 1, env.length] env := by
  obtain ⟨one, computedOne, sortedOne⟩ := calculate_total first firstTotal firstArgs firstData firstSorted
  obtain ⟨two, computedTwo, sortedTwo⟩ := calculate_total second secondTotal secondArgs secondData secondSorted
  have oneLength : one.length = 1 := by
    have lengths := congrArg List.length sortedOne
    have single : first.op.results.length = 1 := by cases first <;> rfl
    simpa [single] using lengths
  have twoLength : two.length = 1 := by
    have lengths := congrArg List.length sortedTwo
    have single : second.op.results.length = 1 := by cases second <;> rfl
    simpa [single] using lengths
  rcases one with _ | ⟨one, _ | ⟨_, _⟩⟩ <;> simp only [List.length_nil, List.length_cons] at oneLength
  all_goals try omega
  rcases two with _ | ⟨two, _ | ⟨_, _⟩⟩ <;> simp only [List.length_nil, List.length_cons] at twoLength
  all_goals try omega
  rw [observation_calculate program context firstRead computedOne sortedOne,
    observation_calculate program context (read_append secondRead [one]) computedTwo sortedTwo,
    observation_calculate program context secondRead computedTwo sortedTwo,
    observation_calculate program context (read_append firstRead [two]) computedOne sortedOne]
  simp [observation, outcome, Domain.evaluate, readback, Domain.read,
    PIR.Process.bind, List.append_assoc]

end Zkc.Executable.DomainVM

module

public import Zkc.Executable.Evaluation

@[expose] public section

/-! Soundness of the lowering rule.

For every executable validator that reads back as constructed instructions
(`Validator.read`), every deployment context, challenge function in every
lawful monad, helper table, decoder, budget, data input, initial transcript and
proof byte string, the executable meaning and the metered ideal meaning of the
reading produce the same outcome class and the same interaction with the
challenge function (`execute_metered`). The proof read by the ideal meaning is
the decoding of the message bytes at the receive types of the run, which the
data inputs fix (`Plan.types`). One premise relates the two meanings of helper
calls: the executable body of every helper the reading calls by name must
implement the helper of the table (`Prepared`); its work is what its unbounded
evaluation charges (`Validator.evaluateCall`).

A normal return, a budget stop and the other stop classes are distinct. For a
reading without loops and helper calls the charges are static: with a budget of
at least their total the metered meaning is the ideal meaning, and below it it
never returns (`execute_ideal`, `execute_short`, `validate_ideal`,
`validate_rejects`). For every reading, host validation is the ideal acceptance
of the metered meaning (`validate_metered`), which `Zkc.Executable.Pruning`
relates to the ideal meaning at every budget.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type}

section Invariant
variable {data : List (Value F G)} {R : Reading} {s : State F G} {env : List (Value F G)}

theorem Simulates.congr (sim : Simulates data R s env) {s' : State F G} (live : s'.live = s.live) :
    Simulates data R s' env where
  length := sim.length
  sorted := sim.sorted
  live := by rw [live]; exact sim.live
  inputs := sim.inputs

theorem Simulates.input_bound (sim : Simulates data R s env) {index : Nat} (lt : index < data.length) :
    index < env.length := by
  have := sim.inputs index lt
  rw [List.getElem?_eq_getElem lt] at this
  exact (List.getElem?_eq_some_iff.mp this).1

theorem Simulates.current_bound (sim : Simulates data R s env) : R.current < env.length :=
  (List.getElem?_eq_some_iff.mp sim.live).1

/-- Extend the environment by values of the given sorts. -/
theorem Simulates.extend (sim : Simulates data R s env) {values : List (Value F G)}
    {sorts : List ValueSort} (lengths : values.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort)
    {current : Nat} {s' : State F G} (live : (env ++ values)[current]? = some (.transcript s'.live)) :
    Simulates data ⟨R.sorts ++ sorts, current⟩ s' (env ++ values) where
  length := by simp [sim.length, lengths]
  sorted := sorted_extend sim.length sim.sorted sorted
  live := live
  inputs := by
    intro index lt
    rw [List.getElem?_append_left (sim.input_bound lt)]
    exact sim.inputs index lt

/-- Extend the environment, keeping the live transcript. -/
theorem Simulates.keep (sim : Simulates data R s env) {values : List (Value F G)}
    {sorts : List ValueSort} (lengths : values.length = sorts.length)
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort)
    {s' : State F G} (live : s'.live = s.live) :
    Simulates data ⟨R.sorts ++ sorts, R.current⟩ s' (env ++ values) :=
  sim.extend lengths sorted (by rw [List.getElem?_append_left sim.current_bound, live]; exact sim.live)

theorem Simulates.indices (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some .indices) :
    ∃ coordinates, env[index]? = some (.indices coordinates) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  cases value with
  | indices coordinates => exact ⟨coordinates, found⟩
  | data => cases sorted
  | index => cases sorted
  | vector => cases sorted
  | transcript => cases sorted

theorem Simulates.index (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some (.data .index)) :
    ∃ value, env[index]? = some (.index value) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  obtain ⟨decoded, encoded⟩ := sorted
  exact ⟨decoded, by rw [found, ← encoded]; rfl⟩

theorem Simulates.boolean (sim : Simulates data R s env) {index : Nat}
    (sortEq : R.sorts[index]? = some (.data .boolean)) :
    ∃ value, env[index]? = some (.data (.boolean value)) := by
  obtain ⟨value, found, sorted⟩ := sim.value sortEq
  obtain ⟨decoded, encoded⟩ := sorted
  exact ⟨decoded, by rw [found, ← encoded]; rfl⟩

theorem State.bind_eq {s : State F G} {top : Frame F G} {rest : List (Frame F G)}
    (frames : s.frames = top :: rest) (names : List String) (values : List (Value F G)) :
    s.bind names values = { s with frames := ⟨top.id, names.zip values ++ top.env⟩ :: rest } := by
  simp [State.bind, frames]

theorem read_bounds {env : List (Value F G)} :
    ∀ {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      ∀ reference ∈ references, reference < env.length
  | [], _, _ => by simp
  | reference :: references, values, found => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              intro target member
              rcases List.mem_cons.mp member with rfl | member
              · exact (List.getElem?_eq_some_iff.mp first).1
              · exact read_bounds others target member

theorem sorted_read {env : List (Value F G)} {sorts : List ValueSort}
    (sorted : ∀ (index : Nat) (value : Value F G) (sort : ValueSort),
      env[index]? = some value → sorts[index]? = some sort → HasSort value sort) :
    ∀ {references : List Nat} {values : List (Value F G)} {expected : List ValueSort},
      references.mapM (fun reference => env[reference]?) = some values →
      references.map (sorts[·]?) = expected.map some →
      ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
        expected[index]? = some sort → HasSort value sort
  | [], values, expected, found, sortsEq => by
      change some [] = some values at found
      cases found
      simp
  | reference :: references, values, expected, found, sortsEq => by
      simp only [List.mapM_cons] at found
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              cases expected with
              | nil => simp at sortsEq
              | cons head tail =>
                  simp only [List.map_cons, List.cons.injEq] at sortsEq
                  intro index v sort vFound sortFound
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at vFound sortFound
                      subst vFound sortFound
                      exact sorted reference value head first sortsEq.1
                  | succ index =>
                      simp only [List.getElem?_cons_succ] at vFound sortFound
                      exact sorted_read sorted others sortsEq.2 index v sort vFound sortFound

theorem read_extend {env : List (Value F G)} (more : List (Value F G)) :
    ∀ {references : List Nat} {values : List (Value F G)},
      references.mapM (fun reference => env[reference]?) = some values →
      references.mapM (fun reference => (env ++ more)[reference]?) = some values
  | [], _, found => found
  | reference :: references, values, found => by
      simp only [List.mapM_cons] at found ⊢
      cases first : env[reference]? with
      | none => simp [first] at found
      | some value =>
          have bound : reference < env.length := (List.getElem?_eq_some_iff.mp first).1
          rw [List.getElem?_append_left bound, first]
          cases others : references.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              simp [read_extend more others]

theorem read_range' (env : List (Value F G)) :
    ∀ (values : List (Value F G)),
      (List.range' env.length values.length).mapM (fun reference => (env ++ values)[reference]?) =
        some values
  | [] => rfl
  | value :: values => by
      simp only [List.length_cons, List.range'_succ, List.mapM_cons]
      have tail := read_range' (env ++ [value]) values
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.singleton_append] at tail
      rw [tail]
      simp

theorem map_filterMap_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), (xs.filterMap f).length = xs.length → xs.map f = (xs.filterMap f).map some
  | [], _ => rfl
  | x :: xs, lengths => by
      cases fx : f x with
      | none =>
          simp only [List.filterMap_cons, fx, List.length_cons] at lengths
          have := List.length_filterMap_le f xs
          omega
      | some y =>
          simp only [List.filterMap_cons, fx, List.length_cons, Nat.add_right_cancel_iff] at lengths
          simp [fx, map_filterMap_length f xs lengths]

theorem transcriptPosition_sort {sorts : List ValueSort} {position : Nat}
    (found : transcriptPosition sorts = some position) :
    ∃ suite, sorts[position]? = some (.transcript suite) := by
  have entry := List.of_findIdx?_eq_some found
  cases sortEq : sorts[position]? with
  | none => simp [sortEq] at entry
  | some sort =>
      rw [sortEq] at entry
      cases sort with
      | transcript suite => exact ⟨suite, rfl⟩
      | data => simp at entry
      | indices => simp at entry

theorem custody_at {sorts : List ValueSort} {current : Nat} {references : List Nat}
    (kept : custody sorts current references = true) {reference : Nat} (member : reference ∈ references)
    {suite : String} (sortEq : sorts[reference]? = some (.transcript suite)) : reference = current := by
  simp only [custody, List.all_eq_true] at kept
  have := kept reference member
  simp only [sortEq, beq_iff_eq] at this
  exact this

theorem position_read {references : List Nat} {sorts sorts' : List ValueSort}
    (sortsEq : references.map (sorts[·]?) = sorts'.map some) {position : Nat} {sort : ValueSort}
    (found : sorts'[position]? = some sort) :
    ∃ reference, references[position]? = some reference ∧ sorts[reference]? = some sort := by
  have lengths : references.length = sorts'.length := by simpa using congrArg List.length sortsEq
  have bound : position < references.length := by
    rw [lengths]; exact (List.getElem?_eq_some_iff.mp found).1
  refine ⟨references[position], List.getElem?_eq_getElem bound, ?_⟩
  have := congrArg (·[position]?) sortsEq
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound, found, Option.map_some] at this
  simpa using this

theorem value_at {env : List (Value F G)} {references : List Nat} {values : List (Value F G)}
    (found : references.mapM (fun reference => env[reference]?) = some values)
    {position reference : Nat} (entry : references[position]? = some reference) :
    values[position]? = env[reference]? := by
  induction references generalizing values position with
  | nil => simp at entry
  | cons head tail ih =>
      simp only [List.mapM_cons] at found
      cases first : env[head]? with
      | none => simp [first] at found
      | some value =>
          cases others : tail.mapM (fun reference => env[reference]?) with
          | none => simp [first, others] at found
          | some rest =>
              simp [first, others] at found
              subst found
              cases position with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at entry
                  subst entry
                  simp [first]
              | succ position =>
                  simp only [List.getElem?_cons_succ] at entry ⊢
                  exact ih others entry

end Invariant

section Field
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The work a helper call charges: what its body charges on the arguments. -/
def helperCost (vocabulary : Vocabulary) (validator : Validator) (symbol : String)
    (arguments : List (Value F G)) : Nat :=
  (validator.evaluateCall vocabulary symbol arguments).cost

/-- The executable body of the local function `symbol` implements the helper of
the same name in `table`: on arguments of its declared input sorts, its
unbounded evaluation hands back exactly the values the helper returns, at the
function's declared result sorts, or stops in the class the helper stops in. -/
def Prepared (vocabulary : Vocabulary) (validator : Validator)
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (symbol : String) : Prop :=
  ∀ callee, validator.function? symbol = some callee →
    ∀ arguments : List (Value F G), callee.inputs.length = arguments.length →
      (∀ (index : Nat) (value : Value F G) (sort : ValueSort), arguments[index]? = some value →
        (callee.inputs.map (·.2.sort))[index]? = some sort → HasSort value sort) →
      match evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip arguments),
          callHelper table symbol arguments with
      | .values results _, .returned results' =>
          results = results' ∧ results.length = callee.results.length ∧
            ∀ (index : Nat) (value : Value F G) (sort : ValueSort), results[index]? = some value →
              (callee.results.map (·.sort))[index]? = some sort → HasSort value sort
      | .stopped cause _, .stopped reason => cause.outcome = reason
      | _, _ => False

section Metered
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

theorem meteredK_append {R : Type} :
    ∀ (first second : List Code) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (next : List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)),
      meteredK context challenge table cost budget (first ++ second) env proof used next =
        meteredK context challenge table cost budget first env proof used fun env' unread used' =>
          meteredK context challenge table cost budget second env' unread used' next
  | [], second, env, proof, used, next => rfl
  | code :: first, second, env, proof, used, next => by
      simp only [List.cons_append, meteredK]
      congr 1
      funext env' unread used'
      exact meteredK_append first second env' unread used' next


/-- With static charges that fit within the budget, the metered meaning is the
ideal meaning. -/
theorem meteredK_static {R : Type} :
    ∀ (code : List Code) {total : Nat}, Code.static code = some total →
      ∀ (env : List (Value F G)) (proof : Proof F G) (used : Nat)
        (next : List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G)),
        used + total ≤ budget →
        meteredK context challenge table cost budget code env proof used next =
          idealK context challenge table (Code.instructions code) env proof fun env' unread =>
            next env' unread (used + total)
  | [], total, static, env, proof, used, next, _ => by
      simp only [Code.static, Option.some.injEq] at static
      subst static
      simp [meteredK, Code.instructions, idealK]
  | .charge count :: rest, total, static, env, proof, used, next, fits => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [meteredK, meteredStep, Code.instructions, show used + count ≤ budget by omega, ite_true]
          rw [meteredK_static rest restStatic _ _ _ _ (by omega)]
          simp [Nat.add_assoc]
  | .step instruction charged :: rest, total, static, env, proof, used, next, fits => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [meteredK, meteredStep, Code.instructions, idealK,
            show used + charged ≤ budget by omega, ite_true]
          congr 1
          funext env' unread
          rw [meteredK_static rest restStatic _ _ _ _ (by omega)]
          simp [Nat.add_assoc]
  | .helper _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static
  | .loop _ _ _ _ _ _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static

theorem metered_eq_ideal {L : Lowered} {total : Nat} (static : L.total? = some total)
    (sufficient : total ≤ budget) (env : List (Value F G)) (proof : Proof F G) :
    metered context challenge table cost budget L env proof =
      ideal context challenge table L.returned (Code.instructions L.code) env proof := by
  unfold Lowered.total? at static
  cases codeStatic : Code.static L.code with
  | none => simp [codeStatic] at static
  | some charges =>
      simp only [codeStatic, Option.map_some, Option.some.injEq] at static
      unfold metered ideal
      rw [meteredK_static context challenge table cost budget L.code codeStatic env proof 0 _ (by omega)]
      congr 1
      funext final unread
      have fits : charges + 1 ≤ budget := by omega
      simp [fits]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Loop iterations whose body returns only stops or results of its
continuation do the same. -/
theorem iterateM_constant [LawfulMonad m] {R β : Type} (observer : PIR.Outcome R × Proof F G → β)
    (constant : β) (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant)
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (bodyConstant : ∀ start proof
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> body start proof next = (fun _ => constant) <$> body start proof next)
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> iterateM body env yielded items carried proof next =
        (fun _ => constant) <$> iterateM body env yielded items carried proof next
  | [], carried, proof, next, continues => continues carried proof
  | index :: rest, carried, proof, next, continues => by
      simp only [iterateM]
      apply bodyConstant
      intro final unread
      split
      · exact iterateM_constant observer constant onStops body bodyConstant env yielded rest _ _ next
          continues
      · simp [onStops]

set_option linter.unusedSectionVars false in
mutual
/-- The ideal meaning returns only stops or results of its continuation: a
function of the result that is constant on stops and on every continuation
result is constant. -/
theorem idealK_constant [LawfulMonad m] {R β : Type} (observer : PIR.Outcome R × Proof F G → β)
    (constant : β) (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> idealK context challenge table instructions env proof next =
        (fun _ => constant) <$> idealK context challenge table instructions env proof next
  | [], env, proof, next, continues => by simpa only [idealK] using continues env proof
  | instruction :: rest, env, proof, next, continues => by
      simp only [idealK]
      exact idealStep_constant observer constant onStops instruction env proof _
        (fun env' unread => idealK_constant observer constant onStops rest env' unread next continues)

theorem idealStep_constant [LawfulMonad m] {R β : Type} (observer : PIR.Outcome R × Proof F G → β)
    (constant : β) (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      (∀ env unread, observer <$> next env unread = (fun _ => constant) <$> next env unread) →
      observer <$> idealStep context challenge table instruction env proof next =
        (fun _ => constant) <$> idealStep context challenge table instruction env proof next
  | ⟨operation, operands, results, body⟩, env, proof, next, continues => by
      have stopped : ∀ (stop : PIR.Stop) (unread : Proof F G),
          observer <$> (pure (.stopped stop, unread) : m (PIR.Outcome R × Proof F G)) =
            (fun _ => constant) <$> (pure (.stopped stop, unread) : m (PIR.Outcome R × Proof F G)) := by
        intro stop unread
        simp [onStops]
      cases operation with
      | loop site maximum yielded =>
          cases operands with
          | nil => exact stopped _ _
          | cons count initial =>
              simp only [idealStep]
              split
              · split
                · exact iterateM_constant observer constant onStops _
                    (fun start unread continuation bodyContinues =>
                      idealK_constant observer constant onStops body start unread continuation
                        bodyContinues) env yielded _ _ proof _ (fun final unread => continues _ _)
                · exact stopped _ _
              · exact stopped _ _
      | _ =>
          unfold idealStep
          repeat' split
          all_goals first
            | exact stopped _ _
            | exact continues _ _
            | (simp only [map_bind]
               congr 1
               funext answer
               exact continues _ _)
            | simp_all
end

/-- Static charges that exceed the budget before the return: the metered
meaning returns only stops, and so does every function of its result that is
constant on stops. -/
theorem meteredK_static_constant [LawfulMonad m] {β : Type}
    (observer : PIR.Outcome (List (Value F G)) × Proof F G → β) (constant : β)
    (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) :
    ∀ (code : List Code) {total : Nat}, Code.static code = some total →
      ∀ (env : List (Value F G)) (proof : Proof F G) (used : Nat)
        (next : List (Value F G) → Proof F G → Nat → m (PIR.Outcome (List (Value F G)) × Proof F G)),
        (∀ env' unread used', used' = used + total →
          observer <$> next env' unread used' = (fun _ => constant) <$> next env' unread used') →
        observer <$> meteredK context challenge table cost budget code env proof used next =
          (fun _ => constant) <$> meteredK context challenge table cost budget code env proof used next
  | [], total, static, env, proof, used, next, continues => by
      simp only [Code.static, Option.some.injEq] at static
      subst static
      simpa [meteredK] using continues env proof used (by simp)
  | .charge count :: rest, total, static, env, proof, used, next, continues => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [meteredK, meteredStep]
          split
          · exact meteredK_static_constant observer constant onStops rest restStatic _ _ _ _
              (fun env' unread used' same => continues env' unread used' (by omega))
          · simp [onStops]
  | .step instruction charged :: rest, total, static, env, proof, used, next, continues => by
      simp only [Code.static] at static
      cases restStatic : Code.static rest with
      | none => simp [restStatic] at static
      | some restTotal =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [meteredK, meteredStep]
          split
          · exact idealStep_constant context challenge table observer constant onStops instruction env proof _
              (fun env' unread => meteredK_static_constant observer constant onStops rest restStatic _ _ _ _
                (fun env'' unread' used' same => continues env'' unread' used' (by omega)))
          · simp [onStops]
  | .helper _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static
  | .loop _ _ _ _ _ _ :: _, _, static, _, _, _, _, _ => by simp [Code.static] at static

/-- Below the total charge of a reading with static charges, the metered
meaning never returns. -/
theorem metered_constant [LawfulMonad m] {β : Type} {L : Lowered} {total : Nat}
    (static : L.total? = some total) (short : budget < total)
    (observer : PIR.Outcome (List (Value F G)) × Proof F G → β) (constant : β)
    (onStops : ∀ stop proof, observer (.stopped stop, proof) = constant) (env : List (Value F G))
    (proof : Proof F G) :
    observer <$> metered context challenge table cost budget L env proof =
      (fun _ => constant) <$> metered context challenge table cost budget L env proof := by
  unfold Lowered.total? at static
  cases codeStatic : Code.static L.code with
  | none => simp [codeStatic] at static
  | some charges =>
      simp only [codeStatic, Option.map_some, Option.some.injEq] at static
      unfold metered
      apply meteredK_static_constant context challenge table cost budget observer constant onStops L.code
        codeStatic
      intro env' unread used' same
      have exceeds : ¬ used' + 1 ≤ budget := by omega
      simp [exceeds, onStops]

end Metered


section Simulation
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

/-- A transparent local body simulates its reading: the constructed
instructions with their charges, ending in the return's charge, after which the
continuations are related at the returned references. -/
theorem localK_metered (data : List (Value F G)) (call : String × String) :
    ∀ (steps : List Step) (scope : List (String × Nat)) (R : Reading) (codes : List Code)
      (returned : List Nat) (R' : Reading),
      readBody vocabulary validator steps scope R = .ok (codes, returned, R') →
      ∀ (named : Env F G) (s : State F G) (env : List (Value F G)) (proof : Proof F G)
        (exit : List (Value F G) → State F G → m (Run F G))
        (k : List (Value F G) → Proof F G → Nat → m (PIR.Outcome (List (Value F G)) × Proof F G)),
        s.used ≤ budget → Simulates data R s env → EnvAgrees env named scope →
        (∀ (s' : State F G) (more results : List (Value F G)), s'.used ≤ budget →
          Simulates data R' s' (env ++ more) → s'.frames = s.frames → s'.proof = s.proof →
          read (env ++ more) returned = some results →
          Run.observe <$> exit results s' = idealObservation <$> k (env ++ more) proof s'.used) →
        Run.observe <$> localK vocabulary validator context challenge budget call true none steps named s exit =
          idealObservation <$> meteredK context challenge table cost budget codes env proof s.used k := by
  intro steps
  induction steps with
  | nil => intro scope R codes returned R' reading; simp [readBody] at reading
  | cons step rest ih =>
    intro scope R codes returned R' reading named s env proof exit k within sim agrees exits
    cases step with
    | ret values =>
        cases rest with
        | nil =>
            simp only [readBody] at reading
            split at reading
            · rename_i references referencesRead
              cases reading
              obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
              obtain ⟨results, resultsEq⟩ := mapM_getElem?_some env bounds
              simp only [localK, localStep, meteredK, meteredStep]
              by_cases tick : s.used < budget
              · have fits : s.used + 1 ≤ budget := by omega
                simp only [tick, ite_true, lookups, resultsEq, fits]
                have related := exits s.charge [] results (by simp [State.charge]; omega)
                  (by simpa using sim.congr (s' := s.charge) rfl) rfl rfl (by simpa [Construction.read] using resultsEq)
                simpa [State.charge] using related
              · have short : ¬ s.used + 1 ≤ budget := by omega
                simp [tick, short]
            · cases reading
        | cons _ _ => simp [readBody, Step.name] at reading
    | operation site binding parameters inputs outputs =>
        simp only [readBody] at reading
        split at reading
        · rename_i resolved resolvedEq
          split at reading
          · rename_i operands operandsRead
            split at reading
            · rename_i operation results advances operationRead
              split at reading
              · rename_i lengths
                split at reading
                · rename_i codes' returned' R'' bodyRead
                  cases reading
                  obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees operandsRead
                  obtain ⟨arguments, argumentsEq⟩ := mapM_getElem?_some env bounds
                  simp only [localK, localStep, meteredK, meteredStep]
                  by_cases tick : s.used < budget
                  · have fits : s.used + 1 ≤ budget := by omega
                    simp only [tick, ite_true, fits, resolvedEq, lookups, argumentsEq]
                    have current := sim.current_bound
                    -- Continue after an operation that appends `values` of sorts `sorts'`.
                    have continues : ∀ (values : List (Value F G)) (s₁ : State F G),
                        outputs.length = values.length → values.length = results.length →
                        (∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
                          results[index]? = some sort → HasSort value sort) →
                        (env ++ values)[if advances then R.sorts.length + results.length - 1 else R.current]? =
                          some (.transcript s₁.live) →
                        s₁.used = s.used + 1 → s₁.frames = s.frames → s₁.proof = s.proof →
                        Run.observe <$> localK vocabulary validator context challenge budget call true none rest
                            (outputs.zip values ++ named) s₁ exit =
                          idealObservation <$> meteredK context challenge table cost budget codes' (env ++ values)
                            proof (s.used + 1) k := by
                      intro values s₁ outputsLength valuesLength valuesSorted live used frames proofs
                      rw [← used]
                      apply ih _ _ _ _ _ bodyRead
                      · omega
                      · exact sim.extend valuesLength valuesSorted live
                      · have := agrees.pushAll outputs values outputsLength
                        rwa [valuesLength, sim.length] at this
                      · intro s' more results' within' sim' frames' proofs' resultsRead
                        have related := exits s' (values ++ more) results' within' (by simpa using sim')
                          (frames'.trans frames) (proofs'.trans proofs) (by simpa using resultsRead)
                        simpa using related
                    cases resolved with
                    | indicesEmpty =>
                        cases operands with
                        | cons => simp [readOperation] at operationRead
                        | nil =>
                            simp only [readOperation, Except.ok.injEq, Prod.mk.injEq] at operationRead
                            obtain ⟨rfl, rfl, rfl⟩ := operationRead
                            change some [] = some arguments at argumentsEq
                            cases argumentsEq
                            simp only [Resolved.apply, idealStep, pure_bind]
                            simp only [List.length_singleton] at lengths
                            simp only [lengths]
                            refine continues [.indices []] _ (by simpa using lengths) rfl
                              (by intro index v sort found sortFound
                                  match index, found, sortFound with
                                  | 0, found, sortFound =>
                                      simp at found sortFound; subst found sortFound; trivial)
                              ?_ ?_ ?_ ?_
                            · simpa [List.getElem?_append_left current] using sim.live
                            all_goals simp [State.charge]
                    | indicesAppend =>
                        rcases operands with _ | ⟨coordinates, _ | ⟨index, _ | ⟨extra, more⟩⟩⟩
                        all_goals try (simp [readOperation] at operationRead; done)
                        simp only [readOperation] at operationRead
                        split at operationRead
                        · rename_i conditions
                          obtain ⟨coordinatesSort, indexSort⟩ := conditions
                          simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          obtain ⟨coordinateValues, coordinatesFound⟩ := sim.indices coordinatesSort
                          obtain ⟨indexValue, indexFound⟩ := sim.index indexSort
                          simp only [List.mapM_cons, coordinatesFound, indexFound] at argumentsEq
                          simp only [List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                            Option.bind_some, Option.some.injEq] at argumentsEq
                          subst argumentsEq
                          simp only [Resolved.apply, idealStep, pure_bind, indicesAt, indexAt,
                            coordinatesFound, indexFound, Option.toList_some]
                          simp only [List.length_singleton] at lengths
                          simp only [lengths]
                          refine continues [.indices (coordinateValues ++ [indexValue])] _ (by simpa using lengths) rfl
                            (by intro index v sort found sortFound
                                match index, found, sortFound with
                                | 0, found, sortFound =>
                                    simp at found sortFound; subst found sortFound; trivial)
                            ?_ ?_ ?_ ?_
                          · simpa [List.getElem?_append_left current] using sim.live
                          all_goals simp [State.charge]
                        · cases operationRead
                    | observe suite leaf template =>
                        rcases operands with _ | ⟨state, _ | ⟨value, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩⟩
                        all_goals try (simp [readOperation] at operationRead; done)
                        simp only [readOperation] at operationRead
                        split at operationRead
                        · rename_i conditions
                          obtain ⟨stateEq, stateSort, valueSort, coordinatesSort⟩ := conditions
                          simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          subst stateEq
                          obtain ⟨observed, valueFound, valueSorted⟩ := sim.value valueSort
                          obtain ⟨coordinateValues, coordinatesFound⟩ := sim.indices coordinatesSort
                          simp only [List.mapM_cons, sim.live, valueFound, coordinatesFound] at argumentsEq
                          simp only [List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                            Option.bind_some, Option.some.injEq] at argumentsEq
                          subst argumentsEq
                          simp only [idealStep, transcriptAt, sim.live]
                          cases origin : template.origin context with
                          | none =>
                              cases observed <;> simp [Resolved.apply, origin]
                          | some occurrence =>
                              cases observed with
                              | data payload =>
                                  have payloadSort := sorted_payload valueSorted rfl
                                  simp only [Resolved.apply, origin, payloadSort, and_self, ite_true,
                                    pure_bind, dataAt, valueFound]
                                  simp only [List.length_singleton] at lengths
                                  simp only [lengths]
                                  refine continues [.transcript (s.live ++ [.message occurrence payload])] _
                                    (by simpa using lengths) rfl
                                    (by intro index v sort found sortFound
                                        match index, found, sortFound with
                                        | 0, found, sortFound =>
                                            simp at found sortFound; subst found sortFound; trivial)
                                    ?_ ?_ ?_ ?_
                                  · simp [← sim.length]
                                  all_goals simp [State.charge]
                              | _ => simp [Resolved.apply, dataAt, valueFound]
                        · cases operationRead
                    | challenge suite field template =>
                        rcases operands with _ | ⟨state, _ | ⟨coordinates, _ | ⟨extra, more⟩⟩⟩
                        all_goals try (simp [readOperation] at operationRead; done)
                        simp only [readOperation] at operationRead
                        split at operationRead
                        · rename_i conditions
                          obtain ⟨stateEq, stateSort, coordinatesSort⟩ := conditions
                          simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          subst stateEq
                          obtain ⟨coordinateValues, coordinatesFound⟩ := sim.indices coordinatesSort
                          simp only [List.mapM_cons, sim.live, coordinatesFound] at argumentsEq
                          simp only [List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
                            Option.bind_some, Option.some.injEq] at argumentsEq
                          subst argumentsEq
                          simp only [idealStep, transcriptAt, sim.live]
                          cases origin : template.origin context with
                          | none => simp [Resolved.apply, origin]
                          | some occurrence =>
                              simp only [Resolved.apply, origin, ite_true, bind_map_left, map_bind]
                              congr 1
                              funext answer
                              simp only [List.length_cons, List.length_nil] at lengths
                              simp only [lengths]
                              refine continues [.data (.field field answer),
                                  .transcript (s.live ++ [.challenge occurrence])] _
                                (by simpa using lengths) rfl
                                (by intro index v sort found sortFound
                                    match index, found, sortFound with
                                    | 0, found, sortFound =>
                                        simp at found sortFound; subst found sortFound
                                        exact ⟨answer, rfl⟩
                                    | 1, found, sortFound =>
                                        simp at found sortFound; subst found sortFound; trivial)
                                ?_ ?_ ?_ ?_
                              · simp [← sim.length]
                              all_goals simp [State.charge]
                        · cases operationRead
                    | calculate calculation =>
                        rw [readOperation_calculate] at operationRead
                        split at operationRead
                        · simp only [Except.ok.injEq, Prod.mk.injEq] at operationRead
                          obtain ⟨rfl, rfl, rfl⟩ := operationRead
                          have readEq : Construction.read env operands = some arguments := argumentsEq
                          simp only [Resolved.apply, idealStep, readEq, pure_bind]
                          cases computed : Zkc.Construction.calculate calculation arguments with
                          | stopped reason => simp
                          | returned values =>
                              have valuesLength := calculate_length calculation computed
                              simp only [List.length_map] at lengths
                              have outputsLength : outputs.length = values.length := by
                                rw [lengths, valuesLength]
                              simp only [outputsLength, ite_true]
                              refine continues values _ outputsLength (by simp [valuesLength])
                                (calculate_sorted computed) ?_ ?_ ?_ ?_
                              · simpa [List.getElem?_append_left current] using sim.live
                              all_goals simp [State.charge]
                        · cases operationRead
                    | compute operation => simp [readOperation] at operationRead
                  · have short : ¬ s.used + 1 ≤ budget := by omega
                    simp [tick, short]
                · cases reading
              · cases reading
            · cases reading
          · cases reading
        · cases reading
    | constant site output value =>
        simp only [readBody] at reading
        split at reading
        · rename_i codes' returned' R'' bodyRead
          cases reading
          simp only [localK, localStep, meteredK, meteredStep]
          by_cases tick : s.used < budget
          · have fits : s.used + 1 ≤ budget := by omega
            simp only [tick, ite_true, fits, idealStep, Construction.read, List.mapM_nil, Option.pure_def,
              Calculation.op, Structured.Op.arguments, decodeValues, Calculation.evaluate,
              Zkc.Construction.calculate]
            change Run.observe <$> _ = idealObservation <$> meteredK context challenge table cost budget codes'
              (env ++ [.data (.boolean value)]) proof (s.used + 1) k
            apply ih _ _ _ _ _ bodyRead
            · simp [State.charge]; omega
            · exact sim.keep (values := [.data (.boolean value)]) (sorts := [.data .boolean]) rfl
                (by intro index v sort found sortFound
                    match index, found, sortFound with
                    | 0, found, sortFound => simp at found sortFound; subst found sortFound; exact ⟨value, rfl⟩)
                rfl
            · simpa [sim.length] using agrees.push output (.data (.boolean value))
            · intro s' more results within' sim' frames' proofs' resultsRead
              have related := exits s' ([.data (.boolean value)] ++ more) results within' (by simpa using sim')
                (by simpa [State.charge] using frames') (by simpa [State.charge] using proofs')
                (by simpa using resultsRead)
              simpa using related
          · have short : ¬ s.used + 1 ≤ budget := by omega
            simp [tick, short]
        · cases reading
    | cond site condition captures yes no outputs =>
        unfold readBody at reading
        split at reading
        · cases reading
        · rename_i heq; simp at heq
        · rename_i heq; simp at heq
        · rename_i heq; simp at heq
        · rename_i site' condition' stopSite rest' heq
          simp only [List.cons.injEq, Step.cond.injEq] at heq
          obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := heq
          split at reading
          · rename_i reference referenceRead
            split at reading
            · rename_i boolean
              split at reading
              · rename_i codes' returned' R'' bodyRead
                cases reading
                obtain ⟨bound, same⟩ := lookupName_eq agrees referenceRead
                obtain ⟨taken, takenFound⟩ := sim.boolean boolean
                rw [takenFound] at same
                simp only [localK, localStep, meteredK, meteredStep]
                by_cases tick : s.used < budget
                · by_cases second : s.used + 1 < budget
                  · have fits : s.used + 2 ≤ budget := by omega
                    cases taken with
                    | true =>
                        simp only [tick, ite_true, same, fits, idealStep, takenFound]
                        simp only [lookupAll, List.mapM_nil, Option.pure_def,
                          State.charge, second, ite_true, List.zip_nil_left, List.nil_append,
                          List.length_nil]
                        rw [show s.used + 2 = s.used + 1 + 1 by omega]
                        apply ih _ _ _ _ _ bodyRead
                        · simp; omega
                        · exact sim.congr rfl
                        · exact agrees
                        · intro s' more results within' sim' frames' proofs' resultsRead
                          exact exits s' more results within' sim' frames' proofs' resultsRead
                    | false =>
                        simp [tick, same, fits, idealStep, takenFound, lookupAll,
                          State.charge, second, stopReason?]
                  · have short : ¬ s.used + 2 ≤ budget := by omega
                    cases taken <;>
                      simp [tick, same, short, lookupAll, State.charge, second]
                · have short : ¬ s.used + 2 ≤ budget := by omega
                  simp [tick, short]
              · cases reading
            · cases reading
          · cases reading
        · cases reading
    | iterate => simp [readBody, Step.name] at reading
    | stop => simp [readBody, Step.name] at reading
    | yield => simp [readBody, Step.name] at reading
    | unsupported => simp [readBody, Step.name] at reading


omit [LawfulMonad m] in
/-- How the continuations after a participant body are related. A loop body
yields its carried values to `exit`, which first charges the yield, and must
agree with `k`; the participant's body returns, after which `k` charges the
return and reads the returned references. -/
def Ends (data : List (Value F G)) (ending : Ending) (R' : Reading) (env : List (Value F G))
    (rest : List (Frame F G)) (after : List PhysicalType)
    (exit : List (Value F G) → State F G → m (Run F G))
    (k : List (Value F G) → Proof F G → Nat → m (PIR.Outcome (List (Value F G)) × Proof F G)) : Prop :=
  match ending with
  | .yielded references =>
      ∀ (s : State F G) (more results : List (Value F G)) (top : Frame F G),
        s.used ≤ budget → Simulates data R' s (env ++ more) → s.frames = top :: rest →
        Construction.read (env ++ more) references = some results →
        Run.observe <$> (if s.used < budget then exit results s.charge else pure (s.stop .limit none none)) =
          idealObservation <$> k (env ++ more) (decodeProof decode after s.proof) s.used
  | .returned references =>
      rest = [] ∧ after = [] ∧ ∀ final unread used, k final unread used =
        pure (if used + 1 ≤ budget then finish references final else .stopped .exhausted, unread)

omit [LawfulMonad m] [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Ends.extend {data : List (Value F G)} {ending : Ending} {R' : Reading} {env : List (Value F G)}
    {rest : List (Frame F G)} {after : List PhysicalType}
    {exit : List (Value F G) → State F G → m (Run F G)}
    {k : List (Value F G) → Proof F G → Nat → m (PIR.Outcome (List (Value F G)) × Proof F G)}
    (ends : Ends decode budget data ending R' env rest after exit k) (more : List (Value F G)) :
    Ends decode budget data ending R' (env ++ more) rest after exit k := by
  cases ending with
  | yielded references =>
      intro s more' results top within sim frames found
      simpa using ends s (more ++ more') results top within (by simpa using sim) frames (by simpa using found)
  | returned references => exact ends

/-- A participant body simulates its reading at every budget. -/
theorem runK_metered (data : List (Value F G)) (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) :
    ∀ (actions : List Action) (scope : List (String × Nat)) (R : Reading) (codes : List Code)
      (plan : List Plan) (ending : Ending) (R' : Reading),
      readActions vocabulary validator helpers data.length actions scope R = .ok (codes, plan, ending, R') →
      ∀ (s : State F G) (env : List (Value F G)) (top : Frame F G) (rest : List (Frame F G))
        (after : List PhysicalType) (exit : List (Value F G) → State F G → m (Run F G))
        (k : List (Value F G) → Proof F G → Nat → m (PIR.Outcome (List (Value F G)) × Proof F G)),
        s.used ≤ budget → Simulates data R s env → s.frames = top :: rest → FrameAgrees env top scope →
        Ends decode budget data ending R' env rest after exit k →
        Run.observe <$> runK vocabulary validator context challenge decode budget actions s exit =
          idealObservation <$> meteredK context challenge table (helperCost vocabulary validator) budget codes env
            (decodeProof decode (Plan.types data plan ++ after) s.proof) s.used k
  | [], scope, R, codes, plan, ending, R', reading => by simp [readActions] at reading
  | [.yield values], scope, R, codes, plan, ending, R', reading => by
      simp only [readActions] at reading
      split at reading
      · rename_i references referencesRead
        cases reading
        intro s env top rest after exit k within sim frames agrees ends
        obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
        obtain ⟨results, resultsEq⟩ := mapM_getElem?_some env bounds
        have related := ends s [] results top within (by simpa using sim) frames
          (by simpa [Construction.read] using resultsEq)
        simp only [List.append_nil] at related
        simp only [runK, runStep, meteredK, Plan.types, List.nil_append, frames, lookups, resultsEq]
        exact related
      · cases reading
  | [.ret values], scope, R, codes, plan, ending, R', reading => by
      simp only [readActions] at reading
      split at reading
      · rename_i references referencesRead
        split at reading
        · rename_i checked
          cases reading
          intro s env top rest after exit k within sim frames agrees ends
          obtain ⟨restNil, afterNil, finishes⟩ := ends
          subst restNil afterNil
          obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees referencesRead
          obtain ⟨results, resultsEq⟩ := mapM_getElem?_some env bounds
          have custody := custody_of_read sim resultsEq checked
          simp only [runK, runStep, meteredK, Plan.types, List.append_nil, frames, lookups, resultsEq,
            finishes]
          by_cases tick : s.used < budget
          · have fits : s.used + 1 ≤ budget := by omega
            simp only [tick, fits, ite_true, custody, finish, Construction.read, resultsEq]
            cases unread : s.proof <;>
              simp [State.charge, State.done, Run.observe, idealObservation, observation, Result.outcome,
                decodeProof, unread]
          · have short : ¬ s.used + 1 ≤ budget := by omega
            simp [tick, short]
        · cases reading
      · cases reading
  | .receive site schema peer output type :: rest, scope, R, codes, plan, ending, R', reading => by
      simp only [readActions] at reading
      split at reading
      · rename_i ty sortEq
        split at reading
        · split at reading
          · rename_i codes' plan' ending' R'' restRead
            cases reading
            intro s env top rest' after exit k within sim frames agrees ends
            simp only [runK, runStep, meteredK, meteredStep, Plan.types, List.cons_append]
            by_cases tick : s.used < budget
            · have fits : s.used + 1 ≤ budget := by omega
              simp only [tick, fits, ite_true]
              cases frame : readFrame s.proof with
              | none =>
                  simp only [decodeProof, frame, idealStep]
                  cases scalarType ty <;> simp
              | some pair =>
                  obtain ⟨payload, unread⟩ := pair
                  cases decoded : decode type payload with
                  | none =>
                      simp only [decodeProof, frame, decoded, idealStep]
                      cases scalarType ty <;> simp
                  | some value =>
                      by_cases typed : type.sort = .data (payloadType value)
                      · have same : ty = payloadType value := by
                          rw [sortEq] at typed
                          exact ValueSort.data.inj typed
                        simp only [typed, ite_true, decodeProof, frame, decoded, idealStep, same,
                          payloadType_scalar, Payload.ty]
                        rw [State.bind_eq (by exact frames)]
                        apply runK_metered data helpers prepared rest _ _ _ _ _ _ restRead
                        · simp only; omega
                        · refine sim.keep (values := [.data value]) (sorts := [.data ty]) rfl ?_ rfl
                          intro index v sort found sortFound
                          match index, found, sortFound with
                          | 0, found, sortFound =>
                              simp at found sortFound
                              subst found sortFound
                              rw [same]
                              exact payload_sorted value
                        · rfl
                        · simpa [sim.length] using agrees.push output (.data value)
                        · exact ends.extend decode budget [.data value]
                      · have different : ty ≠ payloadType value := by
                          intro same
                          exact typed (by rw [sortEq, same])
                        simp only [typed, ite_false, decodeProof, frame, decoded, idealStep]
                        cases scalar : scalarType ty with
                        | none => simp
                        | some common =>
                            have mismatch : ¬ value.ty = common := by
                              intro same
                              exact different (scalarType_payload (same ▸ scalar))
                            simp [mismatch]
            · have short : ¬ s.used + 1 ≤ budget := by omega
              simp [tick, short]
          · cases reading
        · cases reading
      · cases reading
  | .call site function arguments outputs :: rest, scope, R, codes, plan, ending, R', reading => by
      simp only [readActions] at reading
      split at reading
      · rename_i callee operands calleeEq operandsRead
        split at reading
        · rename_i conditions
          obtain ⟨arity, formalSorts⟩ := conditions
          intro s env top rest' after exit k within sim frames agrees ends
          obtain ⟨lookups, bounds⟩ := lookupAll_eq agrees operandsRead
          obtain ⟨values, valuesEq⟩ := mapM_getElem?_some env bounds
          have valuesLength : operands.length = values.length := length_of_mapM_some valuesEq
          have current := sim.current_bound
          split at reading
          · -- A helper call.
            rename_i isHelper
            split at reading
            · rename_i helperConditions
              obtain ⟨free, outputsLength, resultsData⟩ := helperConditions
              split at reading
              · rename_i codes' plan' ending' R'' restRead
                cases reading
                simp only [runK, runStep, frames, calleeEq, lookups, valuesEq, meteredK, meteredStep]
                by_cases tick : s.used < budget
                · have fits : s.used + 1 ≤ budget := by omega
                  have arityValues : callee.inputs.length = values.length := by omega
                  simp only [tick, fits, ite_true, arityValues]
                  rw [localK_evaluates vocabulary validator context challenge budget _ true none callee.body _ _ _
                    free (by simp; omega)]
                  have readEq : Construction.read env operands = some values := valuesEq
                  simp only [readEq]
                  have costEq : helperCost vocabulary validator function values =
                      (evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip values)).cost := by
                    simp [helperCost, Validator.evaluateCall, calleeEq, arityValues]
                  rw [costEq]
                  have sortedArguments := sorted_read sim.sorted valuesEq
                    (expected := callee.inputs.map (·.2.sort)) (by rw [← formalSorts]; simp)
                  have prep := prepared function (by simpa using isHelper) callee calleeEq values arityValues
                    sortedArguments
                  revert prep
                  cases evaluated : evalSteps vocabulary validator callee.body ((callee.inputs.map (·.1)).zip values) with
                  | values results cost =>
                      cases called : callHelper table function values with
                      | returned results' =>
                          intro prep
                          obtain ⟨same, resultsLength, resultsSorted⟩ := prep
                          subst same
                          simp only [cutoff, Evaluated.cost]
                          by_cases enough : s.used + 1 + cost ≤ budget
                          · simp only [enough, ite_true, idealStep, readEq, called]
                            have declared : results.length = (callee.results.map (·.sort)).length := by
                              simpa using resultsLength
                            have lengths : outputs.length = results.length := by
                              rw [outputsLength]; simpa using resultsLength.symm
                            simp only [declared, ite_true, lengths]
                            have related := runK_metered data helpers prepared rest _ _ _ _ _ _ restRead
                              { s with
                                used := s.used + 1 + cost
                                frames := ⟨top.id, outputs.zip results ++ top.env⟩ :: rest'
                                events := s.events ++ [.enter (.call site function)] ++
                                  [.leave (.call site function) .returned] }
                              (env ++ results) _ rest' after exit k (by simp; omega)
                              (sim.keep (by rw [← declared]) (by simpa using resultsSorted) rfl) rfl
                              (by
                                have pushed := agrees.pushAll outputs results lengths
                                rwa [sim.length, declared] at pushed)
                              (ends.extend decode budget results)
                            simpa using related
                          · simp [enough]
                      | stopped reason => intro prep; exact prep.elim
                  | stopped cause cost =>
                      cases called : callHelper table function values with
                      | returned results' => intro prep; exact prep.elim
                      | stopped reason =>
                          intro prep
                          simp only at prep
                          simp only [cutoff, Evaluated.cost]
                          by_cases enough : s.used + 1 + cost ≤ budget
                          · simp only [enough, ite_true, idealStep, readEq, called, prep]
                            simp [idealObservation, observation]
                          · simp [enough]
                · have short : ¬ s.used + 1 ≤ budget := by omega
                  simp [tick, short]
              · cases reading
            · cases reading
          · -- A transparent call.
            split at reading
            · rename_i body returned R₁ bodyRead
              split at reading
              · rename_i returnedConditions
                obtain ⟨outputsLength, returnedSorts⟩ := returnedConditions
                split at reading
                · rename_i codes' plan' ending' R'' restRead
                  cases reading
                  simp only [runK, runStep, frames, calleeEq, lookups, valuesEq, meteredK, meteredStep,
                    List.cons_append]
                  rw [meteredK_append]
                  by_cases tick : s.used < budget
                  · have fits : s.used + 1 ≤ budget := by omega
                    simp only [tick, fits, ite_true, show callee.inputs.length = values.length by omega]
                    apply localK_metered vocabulary validator context challenge table
                      (helperCost vocabulary validator) budget data (site, function) callee.body
                      _ _ _ _ _ bodyRead
                    · simp; omega
                    · exact sim.congr rfl
                    · exact EnvAgrees.enter _ bounds valuesEq
                    · intro s' more results within' sim' frames' proofs' resultsRead
                      have resultsBounds := read_bounds resultsRead
                      simp only [frames']
                      have lengths : outputs.length = results.length := by
                        rw [outputsLength]; exact length_of_mapM_some resultsRead
                      simp only [lengths, ite_true]
                      have related := runK_metered data helpers prepared rest _ _ _ _ _ _ restRead
                        { s' with
                          frames := ⟨top.id, outputs.zip results ++ top.env⟩ :: rest'
                          events := s'.events ++ [.leave (.call site function) .returned] }
                        (env ++ more) _ rest' after exit k within' (sim'.congr rfl) rfl
                        (EnvAgrees.leave (agrees.extend more) outputsLength resultsBounds resultsRead)
                        (ends.extend decode budget more)
                      rw [related]
                      simp [proofs']
                  · have short : ¬ s.used + 1 ≤ budget := by omega
                    simp [tick, short]
                · cases reading
              · cases reading
            · cases reading
        · cases reading
      · cases reading
      · cases reading
  | .loop site count maximum induction carried captures body outputs :: rest, scope, R, codes, plan,
      ending, R', reading => by
      simp only [readActions] at reading
      split at reading
      · rename_i counter initial captured counterRead initialRead capturedRead
        split at reading
        · rename_i conditions
          split at reading
          · rename_i inner innerPlan yielded R₁ innerRead
            split at reading
            · rename_i yieldConditions
              split at reading
              · rename_i codes' plan' ending' R'' restRead
                cases reading
                intro s env top rest' after exit k within sim frames agrees ends
                obtain ⟨counterLt, counterSort, sortsLength, carriedLength, outputsLength, initialCustody, -,
                  -⟩ := conditions
                obtain ⟨yieldedSorts, yieldedCustody, untouched⟩ := yieldConditions
                generalize sortsDef : List.filterMap (fun x => R.sorts[x]?) initial = sorts at *
                have initialSorts : initial.map (R.sorts[·]?) = sorts.map some := by
                  rw [← sortsDef]; exact map_filterMap_length _ initial (sortsDef ▸ sortsLength)
                obtain ⟨counterBound, counterSame⟩ := lookupName_eq agrees counterRead
                obtain ⟨bound, boundFound⟩ := sim.index counterSort
                obtain ⟨initialLookups, initialBounds⟩ := lookupAll_eq agrees initialRead
                obtain ⟨initialValues, initialEq⟩ := mapM_getElem?_some env initialBounds
                obtain ⟨capturedLookups, capturedBounds⟩ := lookupAll_eq agrees capturedRead
                obtain ⟨capturedValues, capturedEq⟩ := mapM_getElem?_some env capturedBounds
                have dataCount : data[counter]? = some (.index bound) := by
                  rw [← sim.inputs counter counterLt]; exact boundFound
                rw [boundFound] at counterSame
                have current := sim.current_bound
                have initialLength : initialValues.length = sorts.length := by
                  rw [← length_of_mapM_some initialEq, sortsLength]
                have readInitial : Construction.read env initial = some initialValues := initialEq
                simp only [runK, runStep, frames, counterSame, initialLookups, initialEq, capturedLookups,
                  capturedEq, meteredK, meteredStep, indexAt, boundFound, readInitial, Plan.types, dataCount,
                  List.append_assoc]
                by_cases maxOk : bound ≤ maximum
                · by_cases tick : s.used < budget
                  · have fits : s.used + 1 ≤ budget := by omega
                    simp only [maxOk, tick, fits, ite_true]
                    -- The carried values the next iteration starts from hold the live transcript.
                    let LiveCarried : List (Value F G) → History F G → Prop := fun values live =>
                      match transcriptPosition sorts with
                      | some position => values[position]? = some (.transcript live)
                      | none => env[R.current]? = some (.transcript live)
                    have iterate : ∀ (indices : List Nat) (values : List (Value F G)) (s' : State F G),
                        s'.used ≤ budget → s'.frames = top :: rest' → values.length = sorts.length →
                        (∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
                          sorts[index]? = some sort → HasSort value sort) →
                        LiveCarried values s'.live →
                        Run.observe <$> loopK (fun s exit => runK vocabulary validator context challenge decode
                            budget body s exit) site induction (carried.map (·.1)) (captures.zip capturedValues)
                            indices values s' (fun final s'' => runK vocabulary validator context challenge
                              decode budget rest (s''.bind outputs final) exit) =
                          idealObservation <$> meteredIterate budget (fun start unread used continuation =>
                              meteredK context challenge table (helperCost vocabulary validator) budget inner start
                                unread used continuation) env yielded indices values
                            (decodeProof decode ((List.replicate indices.length (Plan.types data innerPlan)).flatten ++
                              (Plan.types data plan' ++ after)) s'.proof) s'.used
                            (fun final unread used' => meteredK context challenge table
                              (helperCost vocabulary validator) budget codes' (env ++ final) unread used' k) := by
                      intro indices
                      induction indices with
                      | nil =>
                          intro values s' within' frames' valuesLength valuesSorted live'
                          simp only [loopK, meteredIterate, List.length_nil, List.replicate_zero,
                            List.flatten_nil, List.nil_append]
                          rw [State.bind_eq frames']
                          apply runK_metered data helpers prepared rest _ _ _ _ _ _ restRead
                          · simpa using within'
                          · refine sim.extend valuesLength valuesSorted ?_
                            simp only [LiveCarried] at live'
                            split at live'
                            · rename_i position positionEq
                              rw [positionEq]
                              simp only
                              rw [List.getElem?_append_right (by rw [sim.length]; omega)]
                              simpa [sim.length] using live'
                            · rename_i positionEq
                              rw [positionEq]
                              simp only
                              rw [List.getElem?_append_left current]
                              exact live'
                          · rfl
                          · have pushed := agrees.pushAll outputs values
                              (by rw [outputsLength, valuesLength, sortsLength])
                            rwa [sim.length, valuesLength] at pushed
                          · exact ends.extend decode budget values
                      | cons index indices ih =>
                          intro values s' within' frames' valuesLength valuesSorted live'
                          simp only [loopK, meteredIterate]
                          have proofSplit : (List.replicate (indices.length + 1) (Plan.types data innerPlan)).flatten ++
                              (Plan.types data plan' ++ after) = Plan.types data innerPlan ++
                                ((List.replicate indices.length (Plan.types data innerPlan)).flatten ++
                                  (Plan.types data plan' ++ after)) := by
                            simp [List.replicate_succ, List.flatten_cons, List.append_assoc]
                          rw [List.length_cons, proofSplit]
                          apply runK_metered data helpers prepared body _ _ _ _ _ _ innerRead
                          · simpa using within'
                          · refine sim.extend (values := .index index :: values) (sorts := .data .index :: sorts)
                              (by simp [valuesLength]) ?_ ?_
                            · intro position v sort found sortFound
                              cases position with
                              | zero =>
                                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found sortFound
                                  subst found sortFound
                                  exact ⟨index, rfl⟩
                              | succ position =>
                                  simp only [List.getElem?_cons_succ] at found sortFound
                                  exact valuesSorted position v sort found sortFound
                            · simp only [LiveCarried] at live'
                              split at live'
                              · rename_i position positionEq
                                rw [positionEq]
                                simp only
                                rw [List.getElem?_append_right (by rw [sim.length]; omega)]
                                have shift : R.sorts.length + 1 + position - env.length = position + 1 := by
                                  rw [sim.length]; omega
                                rw [shift]
                                simpa using live'
                              · rename_i positionEq
                                rw [positionEq]
                                simp only
                                rw [List.getElem?_append_left current]
                                exact live'
                          · rfl
                          · -- The loop frame names the index, the carried values and the captures.
                            have keys : (induction, R.sorts.length) ::
                                ((carried.map (·.1)).zip (List.range' (R.sorts.length + 1) initial.length) ++
                                  captures.zip captured) =
                                (induction :: (carried.map (·.1) ++ captures)).zip
                                  (R.sorts.length :: (List.range' (R.sorts.length + 1) initial.length ++ captured)) := by
                              rw [List.zip_cons_cons, List.zip_append (by simp [carriedLength])]
                            have frameEnv : (induction, Value.index index) ::
                                ((carried.map (·.1)).zip values ++ captures.zip capturedValues) =
                                (induction :: (carried.map (·.1) ++ captures)).zip
                                  (.index index :: (values ++ capturedValues)) := by
                              rw [List.zip_cons_cons, List.zip_append (by simp [carriedLength, valuesLength,
                                initialLength.symm, length_of_mapM_some initialEq])]
                            change EnvAgrees _ ((induction, Value.index index) ::
                              ((carried.map (·.1)).zip values ++ captures.zip capturedValues))
                              ((induction, R.sorts.length) ::
                                ((carried.map (·.1)).zip (List.range' (R.sorts.length + 1) initial.length) ++
                                  captures.zip captured))
                            rw [frameEnv, keys]
                            apply EnvAgrees.enter
                            · intro reference member
                              simp only [List.mem_cons, List.mem_append, List.mem_range'] at member
                              simp only [List.length_append, List.length_cons, sim.length]
                              rcases member with rfl | ⟨offset, offsetLt, rfl⟩ | member
                              · omega
                              · omega
                              · have := capturedBounds reference member; rw [sim.length] at this; omega
                            · simp only [List.mapM_cons]
                              have readValues := read_range' (env ++ [.index index]) values
                              simp only [List.length_append, List.length_cons, List.length_nil,
                                List.append_assoc, List.singleton_append] at readValues
                              rw [sim.length] at readValues
                              have readCaptured := read_extend (.index index :: values) capturedEq
                              have head : (env ++ Value.index index :: values)[R.sorts.length]? =
                                  some (.index index) := by
                                rw [← sim.length, List.getElem?_append_right (le_refl _)]
                                simp
                              rw [head, show initial.length = values.length by
                                rw [valuesLength, ← initialLength, length_of_mapM_some initialEq]]
                              rw [List.mapM_append, readValues, readCaptured]
                              rfl
                          · intro s₃ more results loopTop within₃ sim₃ frames₃ resultsRead
                            have resultsLength : results.length = sorts.length := by
                              rw [← length_of_mapM_some resultsRead]
                              simpa using congrArg List.length yieldedSorts
                            by_cases tick₃ : s₃.used < budget
                            · have fits₃ : s₃.used + 1 ≤ budget := by omega
                              simp only [tick₃, ite_true, State.charge, frames₃, fits₃, resultsRead]
                              have namesLength : results.length = (carried.map (·.1)).length := by
                                simp [resultsLength, ← initialLength, carriedLength, length_of_mapM_some initialEq]
                              simp only [namesLength, ite_true]
                              have related := ih results
                                { s₃ with
                                  used := s₃.used + 1
                                  frames := s'.frames
                                  events := s₃.events ++ [.leave (.loop site index) .returned] }
                                fits₃ frames' resultsLength (sorted_read sim₃.sorted resultsRead yieldedSorts) ?_
                              · simpa using related
                              · simp only [LiveCarried]
                                split
                                · rename_i position positionEq
                                  obtain ⟨suite, suiteFound⟩ := transcriptPosition_sort positionEq
                                  obtain ⟨reference, referenceAt, referenceSort⟩ :=
                                    position_read yieldedSorts suiteFound
                                  have isCurrent := custody_at yieldedCustody
                                    (List.mem_of_getElem? referenceAt) referenceSort
                                  rw [value_at resultsRead referenceAt, isCurrent]
                                  exact sim₃.live
                                · rename_i positionEq
                                  have same := untouched positionEq
                                  have live₃ := sim₃.live
                                  rw [same, List.getElem?_append_left
                                    (by simp; omega)] at live₃
                                  rw [List.getElem?_append_left current] at live₃
                                  exact live₃
                            · have short : ¬ s₃.used + 1 ≤ budget := by omega
                              simp [tick₃, short]
                    have initialSorted := sorted_read sim.sorted initialEq initialSorts
                    have start := iterate (List.range bound) initialValues s.charge
                      (by simp [State.charge]; omega) (by simp [State.charge, frames]) initialLength
                      initialSorted ?_
                    · simpa [List.length_range, State.charge] using start
                    · simp only [LiveCarried]
                      split
                      · rename_i position positionEq
                        obtain ⟨suite, suiteFound⟩ := transcriptPosition_sort positionEq
                        obtain ⟨reference, referenceAt, referenceSort⟩ := position_read initialSorts suiteFound
                        have isCurrent := custody_at initialCustody (List.mem_of_getElem? referenceAt)
                          referenceSort
                        rw [value_at initialEq referenceAt, isCurrent]
                        exact sim.live
                      · exact sim.live
                  · have short : ¬ s.used + 1 ≤ budget := by omega
                    simp [maxOk, tick, short]
                · simp [maxOk]
              · cases reading
            · cases reading
          · cases reading
          · cases reading
        · cases reading
      · cases reading
      · cases reading
      · cases reading
  | .yield _ :: _ :: _, scope, R, codes, plan, ending, R', reading => by simp [readActions] at reading
  | .ret _ :: _ :: _, scope, R, codes, plan, ending, R', reading => by simp [readActions] at reading
  | .unsupported _ :: _, scope, R, codes, plan, ending, R', reading => by simp [readActions] at reading


omit [LawfulMonad m] [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem admits_sorts {data : List (Value F G)} (admitted : validator.admits data = true) :
    ∃ suite, ∃ sorts : List ValueSort, validator.inputs.map (·.2.sort) = sorts ++ [.transcript suite] ∧
      sorts.map some = data.map dataSort? := by
  unfold Validator.admits at admitted
  simp only [Bool.and_eq_true, beq_iff_eq] at admitted
  obtain ⟨dropped, last⟩ := admitted
  cases lastEq : validator.inputs.getLast? with
  | none => simp [lastEq] at last
  | some pair =>
      obtain ⟨name, type⟩ := pair
      simp only [lastEq] at last
      cases sortEq : type.sort with
      | transcript suite =>
          have mapped : (validator.inputs.map (·.2.sort)).getLast? = some (.transcript suite) := by
            simp [List.getLast?_map, lastEq, sortEq]
          obtain ⟨front, frontEq⟩ := List.getLast?_eq_some_iff.mp mapped
          refine ⟨suite, front, frontEq, ?_⟩
          rw [frontEq] at dropped
          simpa using dropped
      | data => simp [sortEq] at last
      | indices => simp [sortEq] at last

/-- The participant's body simulates its reading from the initial state. -/
theorem execute_metered (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) (data : List (Value F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data history bytes =
      idealObservation <$> metered context challenge table (helperCost vocabulary validator) budget L
        (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes) := by
  unfold Validator.read at reading
  dsimp only at reading
  simp only [readActionList_eq] at reading
  split_ifs at reading with conditions
  split at reading
  · rename_i code plan returned R' bodyRead
    cases reading
    obtain ⟨suite, sorts, sortsEq, dataSorts⟩ := admits_sorts validator admitted
    have inputsLength : validator.inputs.length = data.length + 1 := by
      have := congrArg List.length sortsEq
      have lengths := congrArg List.length dataSorts
      simp only [List.length_map, List.length_append, List.length_singleton] at this lengths
      omega
    have dataLength : (validator.inputs.map (·.2.sort)).length - 1 = data.length := by
      simp [inputsLength]
    rw [dataLength] at bodyRead
    have simulates : Simulates data ⟨validator.inputs.map (·.2.sort), data.length⟩
        (initial validator data history bytes) (data ++ [.transcript history]) := by
      refine ⟨by simp [inputsLength], ?_, ?_, ?_⟩
      · intro index value sort found sortFound
        simp only [sortsEq] at sortFound
        rcases Nat.lt_or_ge index data.length with lt | ge
        · rw [List.getElem?_append_left lt] at found
          have sortsLength : sorts.length = data.length := by
            simpa using congrArg List.length dataSorts
          rw [List.getElem?_append_left (by omega)] at sortFound
          have reported : dataSort? value = some sort := by
            have := congrArg (·[index]?) dataSorts
            simp only [List.getElem?_map, sortFound, found, Option.map_some] at this
            exact (Option.some.inj this).symm
          exact dataSort_sorted reported
        · have sortsLength : sorts.length = data.length := by
            simpa using congrArg List.length dataSorts
          rw [List.getElem?_append_right ge] at found
          rw [List.getElem?_append_right (by omega), sortsLength] at sortFound
          cases offset : index - data.length with
          | zero =>
              simp [offset] at found sortFound
              subst found sortFound
              trivial
          | succ k => simp [offset] at found
      · simp [initial]
      · intro index lt
        rw [List.getElem?_append_left lt]
    have agrees : FrameAgrees (data ++ [.transcript history])
        ⟨.participant, (validator.inputs.map (·.1)).zip (data ++ [.transcript history])⟩
        ((validator.inputs.map (·.1)).zip (List.range (validator.inputs.map (·.2.sort)).length)) := by
      intro name reference found
      have lengths : (validator.inputs.map (·.1)).length = (data ++ [Value.transcript history]).length := by
        simp [inputsLength]
      have := lookup_zip_range' (outputs := validator.inputs.map (·.1))
        (results := data ++ [Value.transcript history]) [] lengths name reference
      simp only [List.length_nil, List.nil_append, Nat.zero_add] at this
      rw [List.length_map, List.range_eq_range'] at found
      exact this (by simpa [inputsLength] using found)
    have related := runK_metered vocabulary validator context challenge table decode budget data helpers prepared
      validator.body _ _ code plan (.returned returned) R' bodyRead (initial validator data history bytes)
      (data ++ [.transcript history]) _ [] [] (fun _ s => pure (s.stop .contract none none))
      (fun final unread used => pure (if used + 1 ≤ budget then finish returned final else .stopped .exhausted,
        unread))
      (by simp [initial]) simulates rfl agrees ⟨rfl, rfl, fun _ _ _ => rfl⟩
    unfold execute metered
    simp only [admitted, ite_true]
    simpa [initial] using related
  all_goals cases reading

/-- With static charges and a budget of at least their total, the executable
has the ideal meaning's observation and challenge interaction. -/
theorem execute_ideal (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) {total : Nat} (static : L.total? = some total)
    (sufficient : total ≤ budget) (data : List (Value F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data history bytes =
      idealObservation <$> ideal context challenge table L.returned (Code.instructions L.code)
        (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes) := by
  rw [execute_metered vocabulary validator context challenge table decode budget helpers prepared reading data
    history bytes admitted, metered_eq_ideal context challenge table _ budget static sufficient]

/-- With static charges and a budget below their total, every observation the
executable can make is a stop. -/
theorem execute_short {β : Type} (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) {total : Nat} (static : L.total? = some total)
    (short : budget < total) (data : List (Value F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true)
    (observer : PIR.Outcome (List (Value F G)) × Bool → β) (constant : β)
    (onStops : ∀ stop, observer (.stopped stop, true) = constant) :
    (fun result => observer result.observe) <$>
        execute vocabulary validator context challenge decode budget data history bytes =
      (fun _ => constant) <$> execute vocabulary validator context challenge decode budget data history bytes := by
  have same := execute_metered vocabulary validator context challenge table decode budget helpers prepared
    reading data history bytes admitted
  have never := metered_constant context challenge table (helperCost vocabulary validator) budget static short
    (fun result => observer (idealObservation result)) constant
    (fun stop proof => by simpa [idealObservation, observation] using onStops stop)
    (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes)
  calc (fun result => observer result.observe) <$>
        execute vocabulary validator context challenge decode budget data history bytes
      = observer <$> (Run.observe <$>
          execute vocabulary validator context challenge decode budget data history bytes) := by
        rw [Functor.map_map]
    _ = observer <$> (idealObservation <$> metered context challenge table (helperCost vocabulary validator)
          budget L (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes)) := by
        rw [same]
    _ = (fun _ => constant) <$> (idealObservation <$> metered context challenge table
          (helperCost vocabulary validator) budget L (data ++ [.transcript history])
          (decodeProof decode (Plan.types data L.plan) bytes)) := by
        rw [Functor.map_map, Functor.map_map]
        exact never
    _ = (fun _ => constant) <$> execute vocabulary validator context challenge decode budget data history bytes := by
        rw [← same, Functor.map_map]

end Simulation

/-- The selected Boolean of a returned outcome is true. -/
def Decision (acceptance : Nat) : PIR.Outcome (List (Value F G)) → Bool
  | .returned values => selectedTrue values acceptance
  | .stopped _ => false

/-- Host acceptance of an observation: the whole proof was read and the
selected Boolean is true. -/
def Accepts (acceptance : Nat) (observed : PIR.Outcome (List (Value F G)) × Bool) : Bool :=
  observed.2 && Decision acceptance observed.1

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Run.accepts_observe (run : Run F G) (acceptance : Nat) :
    run.accepts acceptance = Accepts acceptance run.observe := by
  rcases run with ⟨result, _, _, _, unread, _, _⟩
  cases result with
  | returned values => rfl
  | stopped cause site call =>
      simp [Run.accepts, Accepts, Decision, Run.observe, observation, Result.outcome]

section Validation
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

/-- Host validation with the expected framing header is the ideal acceptance of
the metered meaning on the decoded proof, at every budget. -/
theorem validate_metered (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) (binding : List UInt8) (acceptance : Nat)
    (data : List (Value F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) (header : bytes.take 40 = magic ++ binding) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun result => Accepts acceptance (idealObservation result)) <$>
        metered context challenge table (helperCost vocabulary validator) budget L
          (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) (bytes.drop 40)) := by
  unfold validate
  simp only [header, ↓reduceIte]
  have same := execute_metered vocabulary validator context challenge table decode budget helpers prepared
    reading data history (bytes.drop 40) admitted
  calc (fun result => result.accepts acceptance) <$>
        execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
      = Accepts acceptance <$> (Run.observe <$>
          execute vocabulary validator context challenge decode budget data history (bytes.drop 40)) := by
        rw [Functor.map_map]
        congr 1
        funext result
        exact Run.accepts_observe result acceptance
    _ = _ := by rw [same, Functor.map_map]

/-- With static charges, the expected framing header and a budget of at least
their total, host validation is the ideal acceptance of the decoded proof. -/
theorem validate_ideal (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) {total : Nat} (static : L.total? = some total)
    (sufficient : total ≤ budget) (binding : List UInt8) (acceptance : Nat) (data : List (Value F G))
    (history : History F G) (bytes : List UInt8) (admitted : validator.admits data = true)
    (header : bytes.take 40 = magic ++ binding) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun result => Accepts acceptance (idealObservation result)) <$>
        ideal context challenge table L.returned (Code.instructions L.code)
          (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) (bytes.drop 40)) := by
  rw [validate_metered vocabulary validator context challenge table decode budget helpers prepared reading
    binding acceptance data history bytes admitted header,
    metered_eq_ideal context challenge table _ budget static sufficient]

/-- With static charges, host validation below their total or with another
framing header rejects on every path. -/
theorem validate_rejects (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) {total : Nat} (static : L.total? = some total)
    (binding : List UInt8) (acceptance : Nat) (data : List (Value F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true)
    (short : budget < total ∨ bytes.take 40 ≠ magic ++ binding) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun _ => false) <$>
        validate vocabulary validator context challenge decode budget binding acceptance data history bytes := by
  unfold validate
  by_cases header : bytes.take 40 = magic ++ binding
  · have below : budget < total := short.resolve_right (not_not.mpr header)
    simp only [header, ↓reduceIte]
    have never := execute_short vocabulary validator context challenge table decode budget helpers prepared
      reading static below data history (bytes.drop 40) admitted (Accepts acceptance) false
      (fun stop => by simp [Accepts, Decision])
    calc (fun result => result.accepts acceptance) <$>
          execute vocabulary validator context challenge decode budget data history (bytes.drop 40)
        = (fun result => Accepts acceptance result.observe) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40) := by
          congr 1
          funext result
          exact Run.accepts_observe result acceptance
      _ = (fun _ => false) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40) := never
      _ = (fun _ => false) <$> ((fun result => result.accepts acceptance) <$>
            execute vocabulary validator context challenge decode budget data history (bytes.drop 40)) := by
          rw [Functor.map_map]
  · simp [header]

end Validation

/-- What the per-compile rule establishes syntactically when it accepts: the
reading, the agreeing interface, and that the reading is the constructed
validator itself or has its normal form. `checkLowering_sound` turns the
latter into equal ideal meanings. -/
theorem checkLowering_spec {vocabulary : Vocabulary} {participant : Participant}
    {validator : Validator} {L : Lowered}
    (accepted : checkLowering vocabulary participant validator = .ok L) :
    validator.read vocabulary (Instruction.helpers participant.instructions) = .ok L ∧
      ((Code.instructions L.code = participant.instructions ∧ L.returned = participant.returned) ∨
        ∃ normalized, checkNormalized participant.inputs participant.instructions participant.returned
          (Code.instructions L.code) L.returned = .ok normalized) ∧
      validator.inputs.map (·.2.sort) = participant.inputs ∧
      validator.results.map (·.sort) = participant.outputs ∧ validator.symbol = participant.symbol ∧
      validator.entry = participant.policy.entry ∧ validator.role = participant.policy.validator := by
  unfold checkLowering at accepted
  simp only [Instruction.helperList_eq, Code.instructionList_eq] at accepted
  cases reading : validator.read vocabulary (Instruction.helpers participant.instructions) with
  | error refusal => simp [reading] at accepted; cases accepted
  | ok lowered =>
      simp only [reading] at accepted
      by_cases symbol : validator.symbol = participant.symbol <;>
      by_cases entry : validator.entry = participant.policy.entry <;>
      by_cases role : validator.role = participant.policy.validator <;>
      by_cases inputs : validator.inputs.map (·.2.sort) = participant.inputs <;>
      by_cases outputs : validator.results.map (·.sort) = participant.outputs <;>
      by_cases exact : Code.instructions lowered.code = participant.instructions ∧
        lowered.returned = participant.returned <;>
      cases normalized : checkNormalized participant.inputs participant.instructions participant.returned
        (Code.instructions lowered.code) lowered.returned <;>
      simp_all [bind, Except.bind, pure, Except.pure]

end Field

end Zkc.Executable

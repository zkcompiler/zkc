module

public import Zkc.Executable.Completeness

@[expose] public section

/-! Charges by evaluation, loops and loop invariants.

A reading's charge is computed from the reading itself. For code without loops,
`Code.charges` adds the instructions each item charges, taking a bound for what
each helper's body charges; `FitsK.of_charges` turns that sum into the charge
bound `FitsK` of the code, given only where the ideal meaning passes on
(`Passes` with every answer and stops allowed). A loop charges its entry and
then, per iteration, its body and its yield: `FitsK.loop_invariant` bounds a
loop of a runtime count `n` at most its static maximum by the sum of iteration
charges (`chargeSum`), from a family-supplied invariant on the carried values
and the unread proof (`LoopInvariant`); `chargeSum_uniform` is the corollary
`n · (body + 1)` under a uniform body bound.

Completeness follows one honest run. `Passes` reads the ideal meaning in the
predicate-transformer monad `Always`, with the challenge answers a relation
admits and a postcondition for stops. With every answer and stops allowed it is
`Continues`, which the charge bound uses; with the answers of a deterministic
challenge function and no stop allowed, it is the run of the ideal meaning in
`Id`, which passes on (`idealK_oracle`). A family therefore states once, in
`Passes`, what one iteration does on every proof and every answer, and both
uses follow. `iterateM_invariant` composes iterations of an honest run.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-! ## Answers and passing -/

/-- The challenge answers a relation admits, as the challenge function of
`Always`. -/
def answers (admitted : History F G → F → Prop) : History F G → Always F :=
  fun history post => ∀ answer, admitted history answer → post answer

/-- The answers of a deterministic challenge function. -/
def oracleAnswers (oracle : History F G → F) : History F G → F → Prop :=
  fun history answer => answer = oracle history

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem everyAnswer_eq : (everyAnswer : History F G → Always F) = answers fun _ _ => True := by
  funext history post
  simp [everyAnswer, answers]

section Passing
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Every run of the instructions, under the answers `admitted` allows, either
stops with a result `stopped` holds of, or passes on to an environment and
unread proof `holds` holds of. -/
def Passes (admitted : History F G → F → Prop) (stopped : PIR.Outcome Unit × Proof F G → Prop)
    (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
    (holds : List (Value F G) → Proof F G → Prop) : Prop :=
  idealK (m := Always) (R := Unit) context (answers admitted) table instructions env proof
    (fun env' unread _ => holds env' unread) stopped

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Loop iterations of a monotone body are monotone. -/
theorem iterateM_mono {R : Type}
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → Always (PIR.Outcome R × Proof F G)) → Always (PIR.Outcome R × Proof F G))
    (bodyMono : ∀ start proof (next next' : List (Value F G) → Proof F G → Always (PIR.Outcome R × Proof F G))
      (post post' : PIR.Outcome R × Proof F G → Prop),
      (∀ final unread, next final unread post → next' final unread post') → (∀ result, post result → post' result) →
      body start proof next post → body start proof next' post')
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → Always (PIR.Outcome R × Proof F G))
      (post post' : PIR.Outcome R × Proof F G → Prop),
      (∀ final unread, next final unread post → next' final unread post') → (∀ result, post result → post' result) →
      iterateM body env yielded items carried proof next post → iterateM body env yielded items carried proof next' post'
  | [], _, _, _, _, _, _, continues, _, holds => continues _ _ holds
  | index :: rest, carried, proof, next, next', post, post', continues, stops, holds => by
      simp only [iterateM] at holds ⊢
      refine bodyMono _ _ _ _ post post' ?_ stops holds
      intro final unread found
      cases readEq : read final yielded with
      | none =>
          simp only [readEq] at found ⊢
          exact stops _ found
      | some carried' =>
          simp only [readEq] at found ⊢
          exact iterateM_mono body bodyMono env yielded rest carried' unread next next' post post' continues stops found

variable (challenge : History F G → Always F)
  (challengeMono : ∀ history (post post' : F → Prop), (∀ answer, post answer → post' answer) →
    challenge history post → challenge history post')

include challengeMono

set_option linter.unusedSectionVars false in
mutual
/-- The ideal meaning read in `Always` is monotone in its continuation and its
postcondition. -/
theorem idealK_mono {R : Type} :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → Always (PIR.Outcome R × Proof F G))
      (post post' : PIR.Outcome R × Proof F G → Prop),
      (∀ env' unread, next env' unread post → next' env' unread post') → (∀ result, post result → post' result) →
      idealK context challenge table instructions env proof next post →
        idealK context challenge table instructions env proof next' post'
  | [], env, proof, _, _, _, _, continues, _, holds => continues env proof holds
  | instruction :: rest, env, proof, next, next', post, post', continues, stops, holds => by
      simp only [idealK] at holds ⊢
      exact idealStep_mono instruction env proof _ _ post post'
        (fun env' unread found => idealK_mono rest env' unread next next' post post' continues stops found) stops holds

theorem idealStep_mono {R : Type} :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next next' : List (Value F G) → Proof F G → Always (PIR.Outcome R × Proof F G))
      (post post' : PIR.Outcome R × Proof F G → Prop),
      (∀ env' unread, next env' unread post → next' env' unread post') → (∀ result, post result → post' result) →
      idealStep context challenge table instruction env proof next post →
        idealStep context challenge table instruction env proof next' post'
  | ⟨operation, operands, results, body⟩, env, proof, next, next', post, post', continues, stops, holds => by
      cases operation with
      | loop site maximum yielded =>
          cases operands with
          | nil => exact stops _ holds
          | cons count initial =>
              simp only [idealStep] at holds ⊢
              cases countEq : indexAt env count with
              | none => simp only [countEq] at holds ⊢; exact stops _ holds
              | some bound =>
                  cases initialEq : read env initial with
                  | none => simp only [countEq, initialEq] at holds ⊢; exact stops _ holds
                  | some carried =>
                      simp only [countEq, initialEq] at holds ⊢
                      by_cases bounded : bound ≤ maximum
                      · simp only [bounded, ite_true] at holds ⊢
                        exact iterateM_mono _
                          (fun start unread k k' q q' kk qq h => idealK_mono body start unread k k' q q' kk qq h)
                          env yielded _ _ proof _ _ post post' (fun final unread found => continues _ _ found) stops
                          holds
                      · simp only [bounded, ite_false] at holds ⊢
                        exact stops _ holds
      | receive site schema peer ty =>
          rcases operands with _ | ⟨_, _⟩
          · simp only [idealStep] at holds ⊢
            cases scalar : scalarType ty with
            | none => simp only [scalar] at holds ⊢; exact stops _ holds
            | some common =>
                cases proof with
                | nil => simp only [scalar] at holds ⊢; exact stops _ holds
                | cons payload rest =>
                    simp only [scalar] at holds ⊢
                    by_cases typed : payload.ty = common
                    · simp only [typed, ite_true] at holds ⊢
                      exact continues _ _ holds
                    · simp only [typed, ite_false] at holds ⊢
                      exact stops _ holds
          · exact stops _ holds
      | indicesEmpty =>
          rcases operands with _ | ⟨_, _⟩
          · exact continues _ _ holds
          · exact stops _ holds
      | indicesAppend =>
          rcases operands with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals first | exact continues _ _ holds | exact stops _ holds
      | observe suite template =>
          rcases operands with _ | ⟨state, _ | ⟨value, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
          all_goals try exact stops _ holds
          simp only [idealStep] at holds ⊢
          cases stateEq : transcriptAt env state with
          | none => simp only [stateEq] at holds ⊢; exact stops _ holds
          | some history =>
              cases originEq : template.origin context with
              | none => simp only [stateEq, originEq] at holds ⊢; exact stops _ holds
              | some origin =>
                  cases valueEq : dataAt env value with
                  | none => simp only [stateEq, originEq, valueEq] at holds ⊢; exact stops _ holds
                  | some payload =>
                      simp only [stateEq, originEq, valueEq] at holds ⊢
                      exact continues _ _ holds
      | challenge suite field template =>
          rcases operands with _ | ⟨state, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals try exact stops _ holds
          simp only [idealStep] at holds ⊢
          cases stateEq : transcriptAt env state with
          | none => simp only [stateEq] at holds ⊢; exact stops _ holds
          | some history =>
              cases originEq : template.origin context with
              | none => simp only [stateEq, originEq] at holds ⊢; exact stops _ holds
              | some origin =>
                  simp only [stateEq, originEq] at holds ⊢
                  exact challengeMono _ _ _ (fun answer found => continues _ _ found) holds
      | calculate calculation =>
          simp only [idealStep] at holds ⊢
          cases argumentsEq : Construction.read env operands with
          | none => simp only [argumentsEq] at holds ⊢; exact stops _ holds
          | some arguments =>
              simp only [argumentsEq] at holds ⊢
              cases computed : Zkc.Construction.calculate calculation arguments with
              | stopped reason => simp only [computed] at holds ⊢; exact stops _ holds
              | returned values => simp only [computed] at holds ⊢; exact continues _ _ holds
      | call name =>
          simp only [idealStep] at holds ⊢
          cases argumentsEq : Construction.read env operands with
          | none => simp only [argumentsEq] at holds ⊢; exact stops _ holds
          | some arguments =>
              simp only [argumentsEq] at holds ⊢
              cases called : callHelper table name arguments with
              | stopped reason => simp only [called] at holds ⊢; exact stops _ holds
              | returned values =>
                  simp only [called] at holds ⊢
                  by_cases lengths : values.length = results.length
                  · simp only [lengths, ite_true] at holds ⊢
                    exact continues _ _ holds
                  · simp only [lengths, ite_false] at holds ⊢
                    exact stops _ holds
      | guard site =>
          rcases operands with _ | ⟨condition, _ | ⟨_, _⟩⟩
          all_goals try exact stops _ holds
          simp only [idealStep] at holds ⊢
          cases found : env[condition]? with
          | none => simp only [found] at holds ⊢; exact stops _ holds
          | some value =>
              rcases value with ⟨(_ | _) | _ | _⟩ | _ | _ | _ | _
              all_goals simp only [found] at holds ⊢
              all_goals first | exact continues _ _ holds | exact stops _ holds
      | send => exact stops _ holds
      | unsupported => exact stops _ holds
end

omit challengeMono

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem answers_mono (admitted : History F G → F → Prop) :
    ∀ history (post post' : F → Prop), (∀ answer, post answer → post' answer) →
      answers admitted history post → answers admitted history post' :=
  fun _ _ _ weaker holds answer allowed => weaker answer (holds answer allowed)

/-- One instruction passes on, as `Passes` reads a list. -/
def PassesStep (admitted : History F G → F → Prop) (stopped : PIR.Outcome Unit × Proof F G → Prop)
    (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
    (holds : List (Value F G) → Proof F G → Prop) : Prop :=
  idealStep (m := Always) (R := Unit) context (answers admitted) table instruction env proof
    (fun env' unread _ => holds env' unread) stopped

variable {admitted : History F G → F → Prop} {stopped : PIR.Outcome Unit × Proof F G → Prop}

theorem Passes.nil {env : List (Value F G)} {proof : Proof F G} {holds : List (Value F G) → Proof F G → Prop}
    (finished : holds env proof) : Passes context table admitted stopped [] env proof holds :=
  finished

theorem Passes.cons {instruction : Instruction} {rest : List Instruction} {env : List (Value F G)}
    {proof : Proof F G} {holds : List (Value F G) → Proof F G → Prop}
    (first : PassesStep context table admitted stopped instruction env proof fun env' unread =>
      Passes context table admitted stopped rest env' unread holds) :
    Passes context table admitted stopped (instruction :: rest) env proof holds := by
  unfold Passes
  simp only [idealK]
  exact idealStep_mono context table (answers admitted) (answers_mono admitted) instruction env proof
    (fun env' unread _ => Passes context table admitted stopped rest env' unread holds) _ stopped stopped
    (fun env' unread found => found) (fun _ found => found) first

theorem Passes.mono {instructions : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds holds' : List (Value F G) → Proof F G → Prop} {stopped' : PIR.Outcome Unit × Proof F G → Prop}
    (weaker : ∀ env' unread, holds env' unread → holds' env' unread)
    (stopsWeaker : ∀ result, stopped result → stopped' result)
    (passes : Passes context table admitted stopped instructions env proof holds) :
    Passes context table admitted stopped' instructions env proof holds' :=
  idealK_mono context table (answers admitted) (answers_mono admitted) instructions env proof _ _ stopped stopped'
    (fun env' unread found => weaker env' unread found) stopsWeaker passes

/-! ### One instruction at a time -/

variable {results : List ValueSort} {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
  {holds : List (Value F G) → Proof F G → Prop}

theorem PassesStep.receive {site schema peer : String} {ty : Structured.Ty} {common : Common.Native.Ty}
    (scalar : scalarType ty = some common)
    (missing : ∀ payload rest, proof = payload :: rest → payload.ty ≠ common → stopped (.stopped .refused, proof))
    (empty : proof = [] → stopped (.stopped .refused, proof))
    (next : ∀ payload rest, proof = payload :: rest → payload.ty = common →
      holds (env ++ [.data payload]) rest) :
    PassesStep context table admitted stopped ⟨.receive site schema peer ty, [], results, body⟩ env proof holds := by
  unfold PassesStep
  simp only [idealStep, scalar]
  cases proof with
  | nil => exact empty rfl
  | cons payload rest =>
      simp only
      by_cases typed : payload.ty = common
      · simp only [typed, ite_true]
        exact next payload rest rfl typed
      · simp only [typed, ite_false]
        exact missing payload rest rfl typed

theorem PassesStep.indicesEmpty (next : holds (env ++ [.indices []]) proof) :
    PassesStep context table admitted stopped ⟨.indicesEmpty, [], results, body⟩ env proof holds :=
  next

theorem PassesStep.indicesAppend {coordinates index : Nat}
    (next : ∀ appended, holds (env ++ [.indices appended]) proof) :
    PassesStep context table admitted stopped ⟨.indicesAppend, [coordinates, index], results, body⟩ env proof holds :=
  next _

theorem PassesStep.observe {suite : String} {template : Template} {state value coordinates : Nat}
    {history : History F G} {origin : Origin} {payload : Payload F G}
    (stateEq : transcriptAt env state = some history) (originEq : template.origin context = some origin)
    (valueEq : dataAt env value = some payload)
    (next : holds (env ++ [.transcript (history ++ [.message origin payload])]) proof) :
    PassesStep context table admitted stopped ⟨.observe suite template, [state, value, coordinates], results, body⟩
      env proof holds := by
  unfold PassesStep
  simp only [idealStep, stateEq, originEq, valueEq]
  exact next

theorem PassesStep.draw {suite field : String} {template : Template} {state coordinates : Nat}
    {history : History F G} {origin : Origin}
    (stateEq : transcriptAt env state = some history) (originEq : template.origin context = some origin)
    (next : ∀ answer, admitted (history ++ [.challenge origin]) answer →
      holds (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])]) proof) :
    PassesStep context table admitted stopped ⟨.challenge suite field template, [state, coordinates], results, body⟩
      env proof holds := by
  unfold PassesStep
  simp only [idealStep, stateEq, originEq]
  exact next

theorem PassesStep.calculate {calculation : Calculation} {operands : List Nat} {arguments values : List (Value F G)}
    (found : Construction.read env operands = some arguments)
    (computed : Zkc.Construction.calculate calculation arguments = .returned values)
    (next : holds (env ++ values) proof) :
    PassesStep context table admitted stopped ⟨.calculate calculation, operands, results, body⟩ env proof holds := by
  unfold PassesStep
  simp only [idealStep, found, computed]
  exact next

theorem PassesStep.call {name : String} {operands : List Nat} {arguments values : List (Value F G)}
    (found : Construction.read env operands = some arguments) (called : callHelper table name arguments = .returned values)
    (lengths : values.length = results.length) (next : holds (env ++ values) proof) :
    PassesStep context table admitted stopped ⟨.call name, operands, results, body⟩ env proof holds := by
  unfold PassesStep
  simp only [idealStep, found, called, lengths, ite_true]
  exact next

theorem PassesStep.guard {site : String} {condition : Nat} {decision : Bool}
    (found : env[condition]? = some (.data (.boolean decision)))
    (rejected : decision = false → stopped (.stopped .reject, proof)) (next : decision = true → holds env proof) :
    PassesStep context table admitted stopped ⟨.guard site, [condition], results, body⟩ env proof holds := by
  unfold PassesStep
  simp only [idealStep, found]
  cases decision with
  | true => exact next rfl
  | false => exact rejected rfl

/-! ### Every answer -/

theorem continues_of_passes {instruction : Instruction}
    (passes : PassesStep context table (fun _ _ => True) (fun _ => True) instruction env proof holds) :
    Continues context table instruction env proof holds := by
  unfold Continues
  rw [everyAnswer_eq]
  exact passes

end Passing

/-! ## Honest runs -/

section Oracle
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (oracle : History F G → F)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Iterations that never stop under a deterministic challenge function pass on
in `Id` to what they pass on to in `Always`. -/
theorem iterateM_oracle
    (bodyAlways : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)) → Always (PIR.Outcome Unit × Proof F G))
    (bodyId : (R : Type) → List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)) → Id (PIR.Outcome R × Proof F G))
    (bodyOracle : ∀ start proof (next : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)),
      bodyAlways start proof next (fun _ => False) →
        ∃ final unread, next final unread (fun _ => False) ∧
          ∀ (R : Type) (next' : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
            bodyId R start proof next' = next' final unread)
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)),
      iterateM bodyAlways env yielded items carried proof next (fun _ => False) →
        ∃ final unread, next final unread (fun _ => False) ∧
          ∀ (R : Type) (next' : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
            iterateM (bodyId R) env yielded items carried proof next' = next' final unread
  | [], carried, proof, next, holds => ⟨carried, proof, holds, fun _ _ => rfl⟩
  | index :: rest, carried, proof, next, holds => by
      simp only [iterateM] at holds
      obtain ⟨final, unread, found, run⟩ := bodyOracle _ _ _ holds
      cases readEq : read final yielded with
      | none =>
          simp only [readEq] at found
          exact found.elim
      | some carried' =>
          simp only [readEq] at found
          obtain ⟨final', unread', found', run'⟩ := iterateM_oracle bodyAlways bodyId bodyOracle env yielded rest
            carried' unread next found
          refine ⟨final', unread', found', fun R next' => ?_⟩
          simp only [iterateM, run, readEq]
          exact run' R next'

set_option linter.unusedSectionVars false in
mutual
/-- A reading that never stops under the answers of a deterministic challenge
function passes on, in `Id`, to an environment and unread proof its
continuation holds of. -/
theorem idealK_oracle :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)),
      idealK context (answers (oracleAnswers oracle)) table instructions env proof next (fun _ => False) →
        ∃ final unread, next final unread (fun _ => False) ∧
          ∀ (R : Type) (next' : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
            idealK (m := Id) context oracle table instructions env proof next' = next' final unread
  | [], env, proof, next, holds => ⟨env, proof, holds, fun _ _ => rfl⟩
  | instruction :: rest, env, proof, next, holds => by
      simp only [idealK] at holds
      obtain ⟨env₁, unread₁, found, run⟩ := idealStep_oracle instruction env proof _ holds
      obtain ⟨final, unread, found', run'⟩ := idealK_oracle rest env₁ unread₁ next found
      refine ⟨final, unread, found', fun R next' => ?_⟩
      simp only [idealK]
      rw [run R (fun env' unread' => idealK (m := Id) context oracle table rest env' unread' next')]
      exact run' R next'

theorem idealStep_oracle :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (next : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)),
      idealStep context (answers (oracleAnswers oracle)) table instruction env proof next (fun _ => False) →
        ∃ final unread, next final unread (fun _ => False) ∧
          ∀ (R : Type) (next' : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
            idealStep (m := Id) context oracle table instruction env proof next' = next' final unread
  | ⟨operation, operands, results, body⟩, env, proof, next, holds => by
      cases operation with
      | loop site maximum yielded =>
          cases operands with
          | nil => exact holds.elim
          | cons count initial =>
              simp only [idealStep] at holds
              cases countEq : indexAt env count with
              | none => simp only [countEq] at holds; exact holds.elim
              | some bound =>
                  cases initialEq : read env initial with
                  | none => simp only [countEq, initialEq] at holds; exact holds.elim
                  | some carried =>
                      simp only [countEq, initialEq] at holds
                      by_cases bounded : bound ≤ maximum
                      · simp only [bounded, ite_true] at holds
                        obtain ⟨final, unread, found, run⟩ := iterateM_oracle _
                          (fun R start unread continuation =>
                            idealK (m := Id) context oracle table body start unread continuation)
                          (fun start unread continuation bodyHolds => idealK_oracle body start unread continuation
                            bodyHolds) env yielded _ _ proof _ holds
                        refine ⟨env ++ final, unread, found, fun R next' => ?_⟩
                        simp only [idealStep, countEq, initialEq, bounded, ite_true]
                        exact run R _
                      · simp only [bounded, ite_false] at holds
                        exact holds.elim
      | receive site schema peer ty =>
          rcases operands with _ | ⟨_, _⟩
          · simp only [idealStep] at holds
            cases scalar : scalarType ty with
            | none => simp only [scalar] at holds; exact holds.elim
            | some common =>
                cases proof with
                | nil => simp only [scalar] at holds; exact holds.elim
                | cons payload rest =>
                    simp only [scalar] at holds
                    by_cases typed : payload.ty = common
                    · simp only [typed, ite_true] at holds
                      exact ⟨_, _, holds, fun R next' => by simp only [idealStep, scalar, typed, ite_true]⟩
                    · simp only [typed, ite_false] at holds
                      exact holds.elim
          · exact holds.elim
      | indicesEmpty =>
          rcases operands with _ | ⟨_, _⟩
          · exact ⟨_, _, holds, fun R next' => rfl⟩
          · exact holds.elim
      | indicesAppend =>
          rcases operands with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals first | exact holds.elim | exact ⟨_, _, holds, fun R next' => rfl⟩
      | observe suite template =>
          rcases operands with _ | ⟨state, _ | ⟨value, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
          all_goals try exact holds.elim
          simp only [idealStep] at holds
          cases stateEq : transcriptAt env state with
          | none => simp only [stateEq] at holds; exact holds.elim
          | some history =>
              cases originEq : template.origin context with
              | none => simp only [stateEq, originEq] at holds; exact holds.elim
              | some origin =>
                  cases valueEq : dataAt env value with
                  | none => simp only [stateEq, originEq, valueEq] at holds; exact holds.elim
                  | some payload =>
                      simp only [stateEq, originEq, valueEq] at holds
                      exact ⟨_, _, holds, fun R next' => by simp only [idealStep, stateEq, originEq, valueEq]⟩
      | challenge suite field template =>
          rcases operands with _ | ⟨state, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals try exact holds.elim
          simp only [idealStep] at holds
          cases stateEq : transcriptAt env state with
          | none => simp only [stateEq] at holds; exact holds.elim
          | some history =>
              cases originEq : template.origin context with
              | none => simp only [stateEq, originEq] at holds; exact holds.elim
              | some origin =>
                  simp only [stateEq, originEq] at holds
                  have chosen := holds _ rfl
                  exact ⟨_, _, chosen, fun R next' => by simp only [idealStep, stateEq, originEq]; rfl⟩
      | calculate calculation =>
          simp only [idealStep] at holds
          cases argumentsEq : Construction.read env operands with
          | none => simp only [argumentsEq] at holds; exact holds.elim
          | some arguments =>
              simp only [argumentsEq] at holds
              cases computed : Zkc.Construction.calculate calculation arguments with
              | stopped reason => simp only [computed] at holds; exact holds.elim
              | returned values =>
                  simp only [computed] at holds
                  exact ⟨_, _, holds, fun R next' => by simp only [idealStep, argumentsEq, computed]⟩
      | call name =>
          simp only [idealStep] at holds
          cases argumentsEq : Construction.read env operands with
          | none => simp only [argumentsEq] at holds; exact holds.elim
          | some arguments =>
              simp only [argumentsEq] at holds
              cases called : callHelper table name arguments with
              | stopped reason => simp only [called] at holds; exact holds.elim
              | returned values =>
                  simp only [called] at holds
                  by_cases lengths : values.length = results.length
                  · simp only [lengths, ite_true] at holds
                    exact ⟨_, _, holds, fun R next' => by
                      simp only [idealStep, argumentsEq, called, lengths, ite_true]⟩
                  · simp only [lengths, ite_false] at holds
                    exact holds.elim
      | guard site =>
          rcases operands with _ | ⟨condition, _ | ⟨_, _⟩⟩
          all_goals try exact holds.elim
          simp only [idealStep] at holds
          cases found : env[condition]? with
          | none => simp only [found] at holds; exact holds.elim
          | some value =>
              rcases value with ⟨(_ | _) | _ | _⟩ | _ | _ | _ | _
              all_goals simp only [found] at holds
              all_goals first
                | exact holds.elim
                | exact ⟨_, _, holds, fun R next' => by simp only [idealStep, found]⟩
      | send => exact holds.elim
      | unsupported => exact holds.elim
end

end Oracle

/-! ## Charges -/

section Charges
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

theorem Continues.mono {instruction : Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds holds' : List (Value F G) → Proof F G → Prop} (weaker : ∀ env' unread, holds env' unread → holds' env' unread)
    (continues : Continues context table instruction env proof holds) :
    Continues context table instruction env proof holds' :=
  idealStep_mono context table everyAnswer (fun _ _ _ weaker' holds answer => weaker' answer (holds answer))
    instruction env proof _ _ _ _ (fun env' unread found => weaker env' unread found) (fun _ found => found) continues

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem FitsIterate.mono
    {body : List (Value F G) → Proof F G → Nat → (List (Value F G) → Proof F G → Nat → Prop) → Prop}
    (bodyMono : ∀ start proof used (holds holds' : List (Value F G) → Proof F G → Nat → Prop),
      (∀ final unread used', holds final unread used' → holds' final unread used') →
        body start proof used holds → body start proof used holds')
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds holds' : List (Value F G) → Proof F G → Nat → Prop),
      (∀ final unread used', holds final unread used' → holds' final unread used') →
        FitsIterate budget body env yielded items carried proof used holds →
          FitsIterate budget body env yielded items carried proof used holds'
  | [], carried, proof, used, _, _, weaker, fits => weaker carried proof used fits
  | index :: rest, carried, proof, used, holds, holds', weaker, fits => by
      simp only [FitsIterate] at fits ⊢
      exact bodyMono _ _ _ _ _ (fun final unread used' found =>
        ⟨found.1, fun carried' readEq =>
          FitsIterate.mono bodyMono env yielded rest carried' unread _ holds holds' weaker (found.2 carried' readEq)⟩)
        fits

set_option linter.unusedSectionVars false in
mutual
/-- The charge bound is monotone in what the continuation needs. -/
theorem FitsK.mono :
    ∀ (code : List Code) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds holds' : List (Value F G) → Proof F G → Nat → Prop),
      (∀ env' unread used', holds env' unread used' → holds' env' unread used') →
        FitsK context table cost budget code env proof used holds →
          FitsK context table cost budget code env proof used holds'
  | [], env, proof, used, _, _, weaker, fits => weaker env proof used fits
  | item :: rest, env, proof, used, holds, holds', weaker, fits => by
      simp only [FitsK] at fits ⊢
      exact FitsStep.mono item env proof used _ _
        (fun env' unread used' found => FitsK.mono rest env' unread used' holds holds' weaker found) fits

theorem FitsStep.mono :
    ∀ (item : Code) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds holds' : List (Value F G) → Proof F G → Nat → Prop),
      (∀ env' unread used', holds env' unread used' → holds' env' unread used') →
        FitsStep context table cost budget item env proof used holds →
          FitsStep context table cost budget item env proof used holds'
  | .charge count, env, proof, used, _, _, weaker, fits => ⟨fits.1, weaker _ _ _ fits.2⟩
  | .step instruction charged, env, proof, used, _, _, weaker, fits =>
      ⟨fits.1, Continues.mono context table (fun env' unread found => weaker _ _ _ found) fits.2⟩
  | .helper instruction, env, proof, used, holds, holds', weaker, fits => by
      obtain ⟨first, called⟩ := fits
      refine ⟨first, ?_⟩
      revert called
      generalize instruction.operation = operation
      generalize Construction.read env instruction.operands = found
      intro called
      cases operation with
      | call name =>
          cases found with
          | none => trivial
          | some arguments =>
              exact ⟨called.1, Continues.mono context table (fun env' unread found => weaker _ _ _ found) called.2⟩
      | _ => exact called
  | .loop site maximum yielded operands results body, env, proof, used, holds, holds', weaker, fits => by
      simp only [FitsStep] at fits ⊢
      cases operands with
      | nil => trivial
      | cons count initial =>
          simp only at fits ⊢
          cases countEq : indexAt env count with
          | none => simp only
          | some bound =>
              cases initialEq : Construction.read env initial with
              | none => simp only
              | some carried =>
                  simp only [countEq, initialEq] at fits ⊢
                  intro bounded
                  obtain ⟨start, iterations⟩ := fits bounded
                  exact ⟨start, FitsIterate.mono budget
                    (fun start' unread used' holds₁ holds₂ weaker' found =>
                      FitsK.mono body start' unread used' holds₁ holds₂ weaker' found)
                    env yielded _ _ proof _ _ _ (fun final unread used' found => weaker _ _ _ found) iterations⟩
end

/-- What code without loops charges: the instructions its items charge, a helper
call its call and at most `bound` for its body; `none` for code with a loop or a
helper without a bound. -/
def Code.charges (bound : String → Option Nat) : List Code → Option Nat
  | [] => some 0
  | .charge count :: rest => (Code.charges bound rest).map (count + ·)
  | .step _ charged :: rest => (Code.charges bound rest).map (charged + ·)
  | .helper instruction :: rest =>
      match instruction.operation with
      | .call name =>
          match bound name, Code.charges bound rest with
          | some most, some others => some (1 + most + others)
          | _, _ => none
      | _ => none
  | .loop .. :: _ => none

theorem passes_cons_step {admitted : History F G → F → Prop} {stopped : PIR.Outcome Unit × Proof F G → Prop}
    {instruction : Instruction} {rest : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (passes : Passes context table admitted stopped (instruction :: rest) env proof holds) :
    PassesStep context table admitted stopped instruction env proof fun env' unread =>
      Passes context table admitted stopped rest env' unread holds := by
  unfold Passes at passes
  simp only [idealK] at passes
  exact idealStep_mono context table (answers admitted) (answers_mono admitted) instruction env proof _
    (fun env' unread _ => Passes context table admitted stopped rest env' unread holds) stopped stopped
    (fun env' unread found => found) (fun _ found => found) passes

/-- Code without loops fits within its charge, computed by `Code.charges`, when
the ideal meaning, on every answer, passes on only where the continuation fits
at every smaller charge. -/
theorem FitsK.of_charges {bound : String → Option Nat}
    (bounds : ∀ helper most arguments, bound helper = some most → cost helper arguments ≤ most) :
    ∀ (code : List Code) (charge : Nat) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds : List (Value F G) → Proof F G → Nat → Prop),
      Code.charges bound code = some charge → used + charge ≤ budget →
      Passes context table (fun _ _ => True) (fun _ => True) (Code.instructions code) env proof
        (fun env' unread => ∀ used', used' ≤ used + charge → holds env' unread used') →
      FitsK context table cost budget code env proof used holds
  | [], charge, env, proof, used, holds, charged, _, passes => by
      simp only [Code.charges, Option.some.injEq] at charged
      subst charged
      unfold Passes at passes
      simp only [Code.instructions, idealK] at passes
      exact passes used (by omega)
  | .charge count :: rest, charge, env, proof, used, holds, charged, fits, passes => by
      simp only [Code.charges] at charged
      simp only [Code.instructions] at passes
      cases restCharged : Code.charges bound rest with
      | none => simp [restCharged] at charged
      | some others =>
          simp only [restCharged, Option.map_some, Option.some.injEq] at charged
          subst charged
          refine FitsK.charge context table cost budget (by omega) ?_
          exact FitsK.of_charges bounds rest others env proof (used + count) holds restCharged (by omega)
            (Passes.mono context table (fun env' unread found used' smaller => found used' (by omega))
              (fun _ found => found) passes)
  | .step instruction charged' :: rest, charge, env, proof, used, holds, charged, fits, passes => by
      simp only [Code.charges] at charged
      simp only [Code.instructions] at passes
      cases restCharged : Code.charges bound rest with
      | none => simp [restCharged] at charged
      | some others =>
          simp only [restCharged, Option.map_some, Option.some.injEq] at charged
          subst charged
          refine FitsK.step context table cost budget (by omega) ?_
          apply continues_of_passes
          refine idealStep_mono context table (answers fun _ _ => True) (answers_mono _) instruction env proof _ _ _ _
            ?_ (fun _ found => found) (passes_cons_step context table passes)
          intro env' unread found
          exact FitsK.of_charges bounds rest others env' unread (used + charged') holds restCharged (by omega)
            (Passes.mono context table (fun env'' unread' found' used' smaller => found' used' (by omega))
              (fun _ found => found) found)
  | .helper instruction :: rest, charge, env, proof, used, holds, charged, fits, passes => by
      unfold Code.charges at charged
      simp only [Code.instructions] at passes
      cases operationEq : instruction.operation with
      | call name =>
          rw [operationEq] at charged
          cases mostEq : bound name with
          | none => simp [mostEq] at charged
          | some most =>
              cases othersEq : Code.charges bound rest with
              | none => simp [mostEq, othersEq] at charged
              | some others =>
                  simp only [mostEq, othersEq, Option.some.injEq] at charged
                  subst charged
                  simp only [FitsK, FitsStep]
                  refine ⟨by omega, ?_⟩
                  rw [operationEq]
                  cases argumentsEq : Construction.read env instruction.operands with
                  | none => trivial
                  | some arguments =>
                      simp only
                      have helperCost := bounds name most arguments mostEq
                      refine ⟨by omega, ?_⟩
                      apply continues_of_passes
                      refine idealStep_mono context table (answers fun _ _ => True) (answers_mono _) instruction env
                        proof _ _ _ _ ?_ (fun _ found => found) (passes_cons_step context table passes)
                      intro env' unread found
                      exact FitsK.of_charges bounds rest others env' unread _ holds othersEq (by omega)
                        (Passes.mono context table (fun env'' unread' found' used' smaller => found' used' (by omega))
                          (fun _ found => found) found)
      | _ => simp [operationEq] at charged
  | .loop .. :: _, _, _, _, _, _, charged, _, _ => by simp [Code.charges] at charged

end Charges

/-! ## Loops -/

/-- What `count` iterations charge from iteration `start` on: each iteration's
body and its yield. -/
def chargeSum (cost : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 => cost start + 1 + chargeSum cost (start + 1) count

theorem chargeSum_uniform {cost : Nat → Nat} {most : Nat} (bounded : ∀ index, cost index ≤ most) :
    ∀ start count, chargeSum cost start count ≤ count * (most + 1)
  | _, 0 => by simp [chargeSum]
  | start, count + 1 => by
      have rest := chargeSum_uniform bounded (start + 1) count
      have first := bounded start
      simp only [chargeSum]
      rw [Nat.succ_mul]
      omega

theorem chargeSum_const (most : Nat) : ∀ start count, chargeSum (fun _ => most) start count = count * (most + 1)
  | _, 0 => by simp [chargeSum]
  | start, count + 1 => by
      simp only [chargeSum, chargeSum_const most (start + 1) count, Nat.succ_mul]
      omega

section Invariants
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Iterations from a loop invariant fit within the sum of their charges. An
iteration from carried values and an unread proof the invariant holds of fits
within its charge and yields carried values the invariant holds of next. -/
theorem FitsIterate.invariant
    {body : List (Value F G) → Proof F G → Nat → (List (Value F G) → Proof F G → Nat → Prop) → Prop}
    (bodyMono : ∀ start proof used (holds holds' : List (Value F G) → Proof F G → Nat → Prop),
      (∀ final unread used', holds final unread used' → holds' final unread used') →
        body start proof used holds → body start proof used holds')
    (env : List (Value F G)) (yielded : List Nat) (invariant : Nat → List (Value F G) → Proof F G → Prop)
    (charge : Nat → Nat) (first limit : Nat)
    (iteration : ∀ index carried proof used, index < limit → invariant index carried proof →
      used + charge index ≤ budget →
        body (env ++ .index (first + index) :: carried) proof used fun final unread used' =>
          used' ≤ used + charge index ∧
            ∀ carried', read final yielded = some carried' → invariant (index + 1) carried' unread) :
    ∀ (count index : Nat) (carried : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds : List (Value F G) → Proof F G → Nat → Prop),
      index + count ≤ limit → invariant index carried proof → used + chargeSum charge index count ≤ budget →
      (∀ carried' unread used', invariant (index + count) carried' unread →
        used' ≤ used + chargeSum charge index count → holds carried' unread used') →
      FitsIterate budget body env yielded (List.range' (first + index) count) carried proof used holds
  | 0, index, carried, proof, used, holds, _, holds₀, _, finish => by
      simp only [List.range'_zero, FitsIterate]
      exact finish carried proof used holds₀ (by simp [chargeSum])
  | count + 1, index, carried, proof, used, holds, inside, holds₀, fits, finish => by
      simp only [List.range'_succ, FitsIterate]
      have bound : used + charge index ≤ budget := by simp only [chargeSum] at fits; omega
      refine bodyMono _ _ _ _ _ ?_ (iteration index carried proof used (by omega) holds₀ bound)
      intro final unread used' found
      obtain ⟨charged, next⟩ := found
      refine ⟨by simp only [chargeSum] at fits; omega, fun carried' readEq => ?_⟩
      have rest := FitsIterate.invariant bodyMono env yielded invariant charge first limit iteration count (index + 1)
        carried' unread (used' + 1) holds (by omega) (next carried' readEq)
        (by simp only [chargeSum] at fits; omega)
        (fun carried'' unread' used'' found' smaller => finish carried'' unread' used''
          (by rw [show index + (count + 1) = index + 1 + count by omega]; exact found')
          (by simp only [chargeSum]; omega))
      rw [show first + (index + 1) = first + index + 1 by omega] at rest
      exact rest

/-- A loop fits within its entry and the sum of its iterations' charges, from a
loop invariant of its carried values and the unread proof, for every runtime
count the loop admits. -/
theorem FitsK.loop_invariant {site : String} {maximum : Nat} {yielded : List Nat} {count : Nat}
    {initial : List Nat} {results : List ValueSort} {body rest : List Code} {env : List (Value F G)}
    {proof : Proof F G} {used : Nat} {holds : List (Value F G) → Proof F G → Nat → Prop} {bound : Nat}
    {carried : List (Value F G)} (countEq : indexAt env count = some bound)
    (initialEq : Construction.read env initial = some carried)
    (invariant : Nat → List (Value F G) → Proof F G → Prop) (charge : Nat → Nat)
    (start : invariant 0 carried proof)
    (iteration : ∀ index carried proof used, index < bound → invariant index carried proof →
      used + charge index ≤ budget →
        FitsK context table cost budget body (env ++ .index index :: carried) proof used fun final unread used' =>
          used' ≤ used + charge index ∧
            ∀ carried', read final yielded = some carried' → invariant (index + 1) carried' unread)
    (fits : bound ≤ maximum → used + 1 + chargeSum charge 0 bound ≤ budget)
    (finish : bound ≤ maximum → ∀ carried' unread used', invariant bound carried' unread →
      used' ≤ used + 1 + chargeSum charge 0 bound → FitsK context table cost budget rest (env ++ carried') unread used' holds) :
    FitsK context table cost budget (.loop site maximum yielded (count :: initial) results body :: rest) env proof
      used holds := by
  refine FitsK.loop context table cost budget countEq initialEq fun bounded => ⟨by have := fits bounded; omega, ?_⟩
  rw [List.range_eq_range', show (0 : Nat) = 0 + 0 from rfl]
  exact FitsIterate.invariant budget
    (fun start' unread used' holds₁ holds₂ weaker found =>
      FitsK.mono context table cost budget body start' unread used' holds₁ holds₂ weaker found)
    env yielded invariant charge 0 bound
    (fun index carried' proof' used' inside holds' fits' => by
      simpa using iteration index carried' proof' used' inside holds' fits')
    bound 0 carried proof (used + 1) _ (by omega) start (by have := fits bounded; omega)
    (fun carried' unread used' found smaller => finish bounded carried' unread used' (by simpa using found) smaller)

end Invariants

section Honest
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (oracle : History F G → F)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An honest run through a loop: when every iteration from carried values and
an unread proof the invariant holds of passes on, in `Id`, to carried values the
invariant holds of next, the iterations pass on to carried values the invariant
holds of after them. -/
theorem iterateM_invariant
    (body : (R : Type) → List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)) → Id (PIR.Outcome R × Proof F G))
    (env : List (Value F G)) (yielded : List Nat) (invariant : Nat → List (Value F G) → Proof F G → Prop)
    (first limit : Nat)
    (iteration : ∀ index carried proof, index < limit → invariant index carried proof →
      ∃ final carried' unread, read final yielded = some carried' ∧ invariant (index + 1) carried' unread ∧
        ∀ (R : Type) (next : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
          body R (env ++ .index (first + index) :: carried) proof next = next final unread) :
    ∀ (count index : Nat) (carried : List (Value F G)) (proof : Proof F G),
      index + count ≤ limit → invariant index carried proof →
      ∃ carried' unread, invariant (index + count) carried' unread ∧
        ∀ (R : Type) (next : List (Value F G) → Proof F G → Id (PIR.Outcome R × Proof F G)),
          iterateM (body R) env yielded (List.range' (first + index) count) carried proof next = next carried' unread
  | 0, index, carried, proof, _, holds => ⟨carried, proof, holds, fun _ _ => rfl⟩
  | count + 1, index, carried, proof, inside, holds => by
      obtain ⟨final, carried', unread, readEq, holds', run⟩ := iteration index carried proof (by omega) holds
      obtain ⟨carried'', unread', holds'', run'⟩ :=
        iterateM_invariant body env yielded invariant first limit iteration count (index + 1) carried' unread
          (by omega) holds'
      refine ⟨carried'', unread', by rw [show index + (count + 1) = index + 1 + count by omega]; exact holds'',
        fun R next => ?_⟩
      simp only [List.range'_succ, iterateM, run, readEq]
      rw [show first + index + 1 = first + (index + 1) by omega]
      exact run' R next

end Honest

end Zkc.Executable

module

public import Zkc.Executable.Pruning

@[expose] public section

/-! Completeness at a sufficient budget.

The metered meaning of a reading charges its instructions against the budget;
`Zkc.Executable.Pruning` shows that at every budget it prunes the ideal meaning.
This module gives the converse direction for readings with loops and helper
calls, whose charges depend on the run: if every run of the reading, under every
answer of the challenge function, charges at most the budget, its return
included, then the metered meaning is the ideal meaning (`metered_sufficient`).
Host validation is then the ideal acceptance of the decoded proof
(`validate_sufficient`), which is what an honest producer's completeness needs.

The charge bound is a predicate on runs, `FitsK`, which follows the metered
meaning's own structure: a charge, an instruction or a loop iteration must fit
within the budget before it runs, a helper call must fit with what its body
charges on its actual arguments, and the continuation is required to fit
wherever the ideal meaning passes on. Where the ideal meaning passes on is
`Continues`: the ideal step read in the predicate-transformer monad `Always`,
in which a challenge holds of every answer and a stop holds trivially. A run that
stops needs no further budget, since the metered meaning then stops for the same
reason.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- Computations read as predicate transformers: a computation states what must
hold of its results for a postcondition to hold. -/
abbrev Always (α : Type) : Type := (α → Prop) → Prop

instance : Monad Always where
  pure value := fun post => post value
  bind computation next := fun post => computation fun value => next value post

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every answer of the challenge function: the challenge function of `Always`. -/
def everyAnswer (_ : History F G) : Always F := fun post => ∀ answer, post answer

section Continuations
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- `holds` holds of every environment and unread proof with which the ideal step
of `instruction` passes on to its continuation, under every challenge answer. A
step that stops imposes nothing. -/
def Continues (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
    (holds : List (Value F G) → Proof F G → Prop) : Prop :=
  idealStep (m := Always) (R := Unit) context everyAnswer table instruction env proof
    (fun env' unread _ => holds env' unread) (fun _ => True)

/-! ### Continuations of single instructions

Sufficient conditions for `Continues`, one per instruction form, for following
a concrete reading on symbolic values. -/

theorem Continues.receive {site schema peer : String} {ty : Structured.Ty} {results : List ValueSort}
    {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop} {common : Common.Native.Ty}
    (scalar : scalarType ty = some common)
    (next : ∀ payload rest, proof = payload :: rest → payload.ty = common → holds (env ++ [.data payload]) rest) :
    Continues context table ⟨.receive site schema peer ty, [], results, body⟩ env proof holds := by
  unfold Continues
  simp only [idealStep, scalar]
  cases proof with
  | nil => trivial
  | cons payload rest =>
      simp only
      by_cases typed : payload.ty = common
      · simp only [typed, ↓reduceIte]
        exact next payload rest rfl typed
      · simp only [typed, ↓reduceIte]
        trivial

theorem Continues.indicesEmpty {results : List ValueSort} {body : List Instruction}
    {env : List (Value F G)} {proof : Proof F G} {holds : List (Value F G) → Proof F G → Prop}
    (next : holds (env ++ [.indices []]) proof) :
    Continues context table ⟨.indicesEmpty, [], results, body⟩ env proof holds :=
  next

theorem Continues.indicesAppend {coordinates index : Nat} {results : List ValueSort} {body : List Instruction}
    {env : List (Value F G)} {proof : Proof F G} {holds : List (Value F G) → Proof F G → Prop}
    (next : ∀ appended, holds (env ++ [.indices appended]) proof) :
    Continues context table ⟨.indicesAppend, [coordinates, index], results, body⟩ env proof holds :=
  next _

theorem Continues.observe {suite : String} {template : Template} {state value coordinates : Nat}
    {results : List ValueSort} {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (next : ∀ history origin payload, transcriptAt env state = some history → template.origin context = some origin →
      dataAt env value = some payload →
      holds (env ++ [.transcript (history ++ [.message origin payload])]) proof) :
    Continues context table ⟨.observe suite template, [state, value, coordinates], results, body⟩ env proof
      holds := by
  unfold Continues
  simp only [idealStep]
  cases stateEq : transcriptAt env state with
  | none => trivial
  | some history =>
      cases originEq : template.origin context with
      | none => trivial
      | some origin =>
          cases valueEq : dataAt env value with
          | none => trivial
          | some payload => exact next history origin payload stateEq originEq valueEq

theorem Continues.challenge {suite field : String} {template : Template} {state coordinates : Nat}
    {results : List ValueSort} {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (next : ∀ history origin answer, transcriptAt env state = some history → template.origin context = some origin →
      holds (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])]) proof) :
    Continues context table ⟨.challenge suite field template, [state, coordinates], results, body⟩ env proof
      holds := by
  unfold Continues
  simp only [idealStep]
  cases stateEq : transcriptAt env state with
  | none => trivial
  | some history =>
      cases originEq : template.origin context with
      | none => trivial
      | some origin =>
          intro answer
          exact next history origin answer stateEq originEq

theorem Continues.calculate {calculation : Calculation} {operands : List Nat} {results : List ValueSort}
    {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (next : ∀ arguments values, Construction.read env operands = some arguments →
      Zkc.Construction.calculate calculation arguments = .returned values → holds (env ++ values) proof) :
    Continues context table ⟨.calculate calculation, operands, results, body⟩ env proof holds := by
  unfold Continues
  simp only [idealStep]
  cases argumentsEq : Construction.read env operands with
  | none => trivial
  | some arguments =>
      simp only
      cases computed : Zkc.Construction.calculate calculation arguments with
      | stopped => trivial
      | returned values => exact next arguments values argumentsEq computed

theorem Continues.call {name : String} {operands : List Nat} {results : List ValueSort}
    {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (next : ∀ arguments values, Construction.read env operands = some arguments →
      callHelper table name arguments = .returned values → values.length = results.length →
        holds (env ++ values) proof) :
    Continues context table ⟨.call name, operands, results, body⟩ env proof holds := by
  unfold Continues
  simp only [idealStep]
  cases argumentsEq : Construction.read env operands with
  | none => trivial
  | some arguments =>
      simp only
      cases computed : callHelper table name arguments with
      | stopped => trivial
      | returned values =>
          simp only
          by_cases lengths : values.length = results.length
          · simp only [lengths, ↓reduceIte]
            exact next arguments values argumentsEq computed lengths
          · simp only [lengths, ↓reduceIte]
            trivial

theorem Continues.guard {site : String} {condition : Nat} {results : List ValueSort}
    {body : List Instruction} {env : List (Value F G)} {proof : Proof F G}
    {holds : List (Value F G) → Proof F G → Prop}
    (next : env[condition]? = some (.data (.boolean true)) → holds env proof) :
    Continues context table ⟨.guard site, [condition], results, body⟩ env proof holds := by
  unfold Continues
  simp only [idealStep]
  cases found : env[condition]? with
  | none => trivial
  | some value =>
      rcases value with ⟨(_ | _) | _ | _⟩ | _ | _ | _ | _
      all_goals first | trivial | exact next found

variable {m : Type → Type} [Monad m] (challenge : History F G → m F)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Loop iterations whose bodies agree on every continuation they pass on agree. -/
theorem iterateM_congr {R : Type}
    (bodyAlways : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G)) →
        Always (PIR.Outcome Unit × Proof F G))
    (body : List (Value F G) → Proof F G →
      (List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)) → m (PIR.Outcome R × Proof F G))
    (bodyCongr : ∀ start proof nextAlways (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      bodyAlways start proof nextAlways (fun _ => True) →
      (∀ env unread, nextAlways env unread (fun _ => True) → next env unread = next' env unread) →
      body start proof next = body start proof next')
    (env : List (Value F G)) (yielded : List Nat) :
    ∀ (items : List Nat) (carried : List (Value F G)) (proof : Proof F G)
      (nextAlways : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G))
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      iterateM bodyAlways env yielded items carried proof nextAlways (fun _ => True) →
      (∀ final unread, nextAlways final unread (fun _ => True) → next final unread = next' final unread) →
      iterateM body env yielded items carried proof next = iterateM body env yielded items carried proof next'
  | [], carried, proof, _, _, _, holds, continues => continues carried proof holds
  | index :: rest, carried, proof, nextAlways, next, next', holds, continues => by
      simp only [iterateM] at holds ⊢
      apply bodyCongr _ _ _ _ _ holds
      intro final unread found
      split
      · rename_i carried' readEq
        simp only [readEq] at found
        exact iterateM_congr bodyAlways body bodyCongr env yielded rest carried' unread nextAlways next next'
          found continues
      · rfl

set_option linter.unusedSectionVars false in
mutual
/-- Instructions agree on continuations that agree wherever the ideal meaning
passes on. -/
theorem idealK_congr {R : Type} :
    ∀ (instructions : List Instruction) (env : List (Value F G)) (proof : Proof F G)
      (nextAlways : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G))
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      idealK (m := Always) context everyAnswer table instructions env proof nextAlways (fun _ => True) →
      (∀ env' unread, nextAlways env' unread (fun _ => True) → next env' unread = next' env' unread) →
      idealK context challenge table instructions env proof next =
        idealK context challenge table instructions env proof next'
  | [], env, proof, _, _, _, holds, continues => by
      simp only [idealK] at holds ⊢
      exact continues env proof holds
  | instruction :: rest, env, proof, nextAlways, next, next', holds, continues => by
      simp only [idealK] at holds ⊢
      exact idealStep_congr instruction env proof _ _ _ holds
        (fun env' unread found => idealK_congr rest env' unread nextAlways next next' found continues)

theorem idealStep_congr {R : Type} :
    ∀ (instruction : Instruction) (env : List (Value F G)) (proof : Proof F G)
      (nextAlways : List (Value F G) → Proof F G → Always (PIR.Outcome Unit × Proof F G))
      (next next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      idealStep (m := Always) context everyAnswer table instruction env proof nextAlways (fun _ => True) →
      (∀ env' unread, nextAlways env' unread (fun _ => True) → next env' unread = next' env' unread) →
      idealStep context challenge table instruction env proof next =
        idealStep context challenge table instruction env proof next'
  | ⟨operation, operands, results, body⟩, env, proof, nextAlways, next, next', holds, continues => by
      cases operation with
      | localService => rfl
      | loop site maximum yielded =>
          cases operands with
          | nil => rfl
          | cons count initial =>
              simp only [idealStep] at holds ⊢
              split
              · rename_i bound carried countEq initialEq
                simp only [countEq, initialEq] at holds
                split
                · rename_i bounded
                  simp only [bounded, ite_true] at holds
                  exact iterateM_congr _ _
                    (fun start unread nextAlways' continuation continuation' bodyHolds bodyContinues =>
                      idealK_congr body start unread nextAlways' continuation continuation' bodyHolds
                        bodyContinues)
                    env yielded _ _ proof _ _ _ holds (fun final unread found => continues _ _ found)
                · rfl
              · rfl
      | receive site schema peer ty =>
          rcases operands with _ | ⟨_, _⟩
          · simp only [idealStep] at holds ⊢
            cases scalar : scalarType ty with
            | none => rfl
            | some common =>
                cases proof with
                | nil => rfl
                | cons payload rest =>
                    simp only [scalar] at holds ⊢
                    by_cases typed : payload.ty = common
                    · simp only [typed, ite_true] at holds ⊢
                      exact continues _ _ holds
                    · simp only [typed, ite_false]
          · rfl
      | indicesEmpty =>
          rcases operands with _ | ⟨_, _⟩
          · exact continues _ _ holds
          · rfl
      | indicesAppend =>
          rcases operands with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals first | rfl | exact continues _ _ holds
      | observe suite template =>
          rcases operands with _ | ⟨state, _ | ⟨value, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩
          all_goals try rfl
          simp only [idealStep] at holds ⊢
          cases stateEq : transcriptAt env state with
          | none => rfl
          | some history =>
              cases originEq : template.origin context with
              | none => rfl
              | some origin =>
                  cases valueEq : dataAt env value with
                  | none => rfl
                  | some payload =>
                      simp only [stateEq, originEq, valueEq] at holds ⊢
                      exact continues _ _ holds
      | challenge suite field template =>
          rcases operands with _ | ⟨state, _ | ⟨_, _ | ⟨_, _⟩⟩⟩
          all_goals try rfl
          simp only [idealStep] at holds ⊢
          cases stateEq : transcriptAt env state with
          | none => rfl
          | some history =>
              cases originEq : template.origin context with
              | none => rfl
              | some origin =>
                  simp only [stateEq, originEq] at holds ⊢
                  congr 1
                  funext answer
                  exact continues _ _ (holds answer)
      | calculate calculation =>
          simp only [idealStep] at holds ⊢
          cases argumentsEq : Construction.read env operands with
          | none => rfl
          | some arguments =>
              simp only [argumentsEq] at holds ⊢
              cases computed : Zkc.Construction.calculate calculation arguments with
              | stopped reason => rfl
              | returned values =>
                  simp only [computed] at holds ⊢
                  exact continues _ _ holds
      | call name =>
          simp only [idealStep] at holds ⊢
          cases argumentsEq : Construction.read env operands with
          | none => rfl
          | some arguments =>
              simp only [argumentsEq] at holds ⊢
              cases computed : callHelper table name arguments with
              | stopped reason => rfl
              | returned values =>
                  simp only [computed] at holds ⊢
                  by_cases lengths : values.length = results.length
                  · simp only [lengths, ite_true] at holds ⊢
                    exact continues _ _ holds
                  · simp only [lengths, ite_false]
      | guard site =>
          rcases operands with _ | ⟨condition, _ | ⟨_, _⟩⟩
          all_goals try rfl
          simp only [idealStep] at holds ⊢
          split
          · rename_i conditionEq
            simp only [conditionEq] at holds
            exact continues _ _ holds
          · rfl
          · rfl
      | send => rfl
      | unsupported => rfl
end

end Continuations

/-! ## Following the ideal meaning instruction by instruction

Equations for the ideal meaning of a concrete instruction list on symbolic
values, one per instruction form. -/

section IdealSteps
variable {m : Type → Type} [Monad m] (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
variable {R : Type} {rest : List Instruction} {env : List (Value F G)} {proof : Proof F G}
  {next : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)}
  {results : List ValueSort} {body : List Instruction}

theorem idealK_receive {site schema peer : String} {ty : Structured.Ty} {common : Common.Native.Ty}
    {payload : Payload F G} (scalar : scalarType ty = some common) (typed : payload.ty = common) :
    idealK context challenge table (⟨.receive site schema peer ty, [], results, body⟩ :: rest) env
        (payload :: proof) next =
      idealK context challenge table rest (env ++ [.data payload]) proof next := by
  simp only [idealK, idealStep, scalar, typed, ite_true]

theorem idealK_indicesEmpty :
    idealK context challenge table (⟨.indicesEmpty, [], results, body⟩ :: rest) env proof next =
      idealK context challenge table rest (env ++ [.indices []]) proof next := rfl

theorem idealK_indicesAppend {coordinates index : Nat} {current : List Nat} {appended : Nat}
    (coordinatesEq : indicesAt env coordinates = current) (indexEq : indexAt env index = some appended) :
    idealK context challenge table (⟨.indicesAppend, [coordinates, index], results, body⟩ :: rest) env proof
        next =
      idealK context challenge table rest (env ++ [.indices (current ++ [appended])]) proof next := by
  simp only [idealK, idealStep, coordinatesEq, indexEq, Option.toList_some]

theorem idealK_observe {suite : String} {template : Template} {state value coordinates : Nat}
    {history : History F G} {origin : Origin} {payload : Payload F G}
    (stateEq : transcriptAt env state = some history) (originEq : template.origin context = some origin)
    (valueEq : dataAt env value = some payload) :
    idealK context challenge table (⟨.observe suite template, [state, value, coordinates], results, body⟩ :: rest)
        env proof next =
      idealK context challenge table rest (env ++ [.transcript (history ++ [.message origin payload])]) proof
        next := by
  simp only [idealK, idealStep, stateEq, originEq, valueEq]

theorem idealK_challenge {suite field : String} {template : Template} {state coordinates : Nat}
    {history : History F G} {origin : Origin}
    (stateEq : transcriptAt env state = some history) (originEq : template.origin context = some origin) :
    idealK context challenge table (⟨.challenge suite field template, [state, coordinates], results, body⟩ :: rest)
        env proof next =
      challenge (history ++ [.challenge origin]) >>= fun answer =>
        idealK context challenge table rest
          (env ++ [.data (.field field answer), .transcript (history ++ [.challenge origin])]) proof next := by
  simp only [idealK, idealStep, stateEq, originEq]

theorem idealK_calculate {calculation : Calculation} {operands : List Nat} {arguments values : List (Value F G)}
    (found : read env operands = some arguments)
    (computed : Zkc.Construction.calculate calculation arguments = .returned values) :
    idealK context challenge table (⟨.calculate calculation, operands, results, body⟩ :: rest) env proof next =
      idealK context challenge table rest (env ++ values) proof next := by
  simp only [idealK, idealStep, found, computed]

theorem idealK_call {name : String} {operands : List Nat} {arguments values : List (Value F G)}
    (found : read env operands = some arguments) (called : callHelper table name arguments = .returned values)
    (lengths : values.length = results.length) :
    idealK context challenge table (⟨.call name, operands, results, body⟩ :: rest) env proof next =
      idealK context challenge table rest (env ++ values) proof next := by
  simp only [idealK, idealStep, found, called, lengths, ite_true]

theorem idealK_guard {site : String} {condition : Nat}
    (passes : env[condition]? = some (.data (.boolean true))) :
    idealK context challenge table (⟨.guard site, [condition], results, body⟩ :: rest) env proof next =
      idealK context challenge table rest env proof next := by
  simp only [idealK, idealStep, passes]

theorem idealK_loop {site : String} {maximum : Nat} {yielded : List Nat} {count : Nat} {initial : List Nat}
    {bound : Nat} {carried : List (Value F G)} (countEq : indexAt env count = some bound)
    (initialEq : read env initial = some carried) (bounded : bound ≤ maximum) :
    idealK context challenge table (⟨.loop site maximum yielded, count :: initial, results, body⟩ :: rest) env proof
        next =
      iterateM (fun start unread continuation => idealK context challenge table body start unread continuation)
        env yielded (List.range bound) carried proof fun final unread =>
          idealK context challenge table rest (env ++ final) unread next := by
  simp only [idealK, idealStep, countEq, initialEq, bounded, ite_true]

theorem idealK_nil : idealK context challenge table [] env proof next = next env proof := rfl

end IdealSteps

/-! ## The charge bound -/

section Fits
variable (context : Context) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

/-- Iterations of a loop body fit within the budget: each iteration's body fits,
and its yield, charged one instruction, fits before the next iteration starts. -/
def FitsIterate
    (body : List (Value F G) → Proof F G → Nat → (List (Value F G) → Proof F G → Nat → Prop) → Prop)
    (env : List (Value F G)) (yielded : List Nat) :
    List Nat → List (Value F G) → Proof F G → Nat → (List (Value F G) → Proof F G → Nat → Prop) → Prop
  | [], carried, proof, used, holds => holds carried proof used
  | index :: rest, carried, proof, used, holds =>
      body (env ++ .index index :: carried) proof used fun final unread used' =>
        used' + 1 ≤ budget ∧ ∀ carried', read final yielded = some carried' →
          FitsIterate body env yielded rest carried' unread (used' + 1) holds

mutual
/-- Every run of the code from `used` charged instructions, under every challenge
answer, keeps its charges within the budget until it stops or passes on to a
continuation of which `holds` holds, with the instructions charged until then. -/
def FitsK : List Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → Prop) → Prop
  | [], env, proof, used, holds => holds env proof used
  | code :: rest, env, proof, used, holds =>
      FitsStep code env proof used fun env' unread used' => FitsK rest env' unread used' holds

/-- One code item fits within the budget. -/
def FitsStep : Code → List (Value F G) → Proof F G → Nat →
    (List (Value F G) → Proof F G → Nat → Prop) → Prop
  | .charge count, env, proof, used, holds => used + count ≤ budget ∧ holds env proof (used + count)
  | .step instruction charged, env, proof, used, holds =>
      used + charged ≤ budget ∧
        Continues context table instruction env proof fun env' unread => holds env' unread (used + charged)
  | .helper instruction, env, proof, used, holds =>
      used + 1 ≤ budget ∧
        match instruction.operation, read env instruction.operands with
        | .call helper, some arguments =>
            used + 1 + cost helper arguments ≤ budget ∧
              Continues context table instruction env proof fun env' unread =>
                holds env' unread (used + 1 + cost helper arguments)
        | .call _, none => True
        | _, _ => False
  | .loop _ maximum yielded operands _ body, env, proof, used, holds =>
      match operands with
      | count :: initial =>
          match indexAt env count, read env initial with
          | some bound, some carried =>
              bound ≤ maximum →
                used + 1 ≤ budget ∧
                  FitsIterate budget (fun start unread used' holds' => FitsK body start unread used' holds') env
                    yielded (List.range bound) carried proof (used + 1) fun final unread used' =>
                      holds (env ++ final) unread used'
          | _, _ => True
      | [] => True
end

/-! ### Following code item by item -/

theorem FitsK.charge {count : Nat} {rest : List Code} {env : List (Value F G)} {proof : Proof F G}
    {used : Nat} {holds : List (Value F G) → Proof F G → Nat → Prop} (fits : used + count ≤ budget)
    (continues : FitsK context table cost budget rest env proof (used + count) holds) :
    FitsK context table cost budget (.charge count :: rest) env proof used holds :=
  ⟨fits, continues⟩

theorem FitsK.step {instruction : Instruction} {charged : Nat} {rest : List Code} {env : List (Value F G)}
    {proof : Proof F G} {used : Nat} {holds : List (Value F G) → Proof F G → Nat → Prop}
    (fits : used + charged ≤ budget)
    (continues : Continues context table instruction env proof fun env' unread =>
      FitsK context table cost budget rest env' unread (used + charged) holds) :
    FitsK context table cost budget (.step instruction charged :: rest) env proof used holds :=
  ⟨fits, continues⟩

theorem FitsK.helper {instruction : Instruction} {helper : String} {arguments : List (Value F G)}
    {rest : List Code} {env : List (Value F G)} {proof : Proof F G} {used : Nat}
    {holds : List (Value F G) → Proof F G → Nat → Prop}
    (called : instruction.operation = .call helper) (found : read env instruction.operands = some arguments)
    (fits : used + 1 + cost helper arguments ≤ budget)
    (continues : Continues context table instruction env proof fun env' unread =>
      FitsK context table cost budget rest env' unread (used + 1 + cost helper arguments) holds) :
    FitsK context table cost budget (.helper instruction :: rest) env proof used holds := by
  simp only [FitsK, FitsStep, called, found]
  exact ⟨by omega, fits, continues⟩

theorem FitsK.loop {site : String} {maximum : Nat} {yielded : List Nat} {count : Nat} {initial : List Nat}
    {results : List ValueSort} {body rest : List Code} {env : List (Value F G)} {proof : Proof F G}
    {used : Nat} {holds : List (Value F G) → Proof F G → Nat → Prop} {bound : Nat}
    {carried : List (Value F G)} (countEq : indexAt env count = some bound)
    (initialEq : read env initial = some carried)
    (iterations : bound ≤ maximum → used + 1 ≤ budget ∧
      FitsIterate budget (fun start unread used' holds' => FitsK context table cost budget body start unread used'
        holds') env yielded (List.range bound) carried proof (used + 1) fun final unread used' =>
          FitsK context table cost budget rest (env ++ final) unread used' holds) :
    FitsK context table cost budget (.loop site maximum yielded (count :: initial) results body :: rest) env proof
      used holds := by
  simp only [FitsK, FitsStep, countEq, initialEq]
  exact iterations

theorem FitsK.done {env : List (Value F G)} {proof : Proof F G} {used : Nat}
    {holds : List (Value F G) → Proof F G → Nat → Prop} (finished : holds env proof used) :
    FitsK context table cost budget [] env proof used holds :=
  finished

/-- Every run of the reading, under every challenge answer, charges at most
`budget` instructions, its return included. It is irreducible: it unfolds to
the charge bound of the reading's code, which elaboration must not compute. -/
@[irreducible] def Sufficient (lowered : Lowered) (env : List (Value F G)) (proof : Proof F G) : Prop :=
  FitsK context table cost budget lowered.code env proof 0 fun _ _ used => used + 1 ≤ budget

end Fits

/-! ## The metered meaning at a sufficient budget -/

section Metered
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (context : Context) (challenge : History F G → m F)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (cost : String → List (Value F G) → Nat) (budget : Nat)

omit [LawfulMonad m] in
/-- Within a sufficient budget the metered meaning of code is the ideal meaning
of its constructed instructions. -/
theorem meteredK_fits {R : Type} :
    ∀ (code : List Code) (env : List (Value F G)) (proof : Proof F G) (used : Nat)
      (holds : List (Value F G) → Proof F G → Nat → Prop)
      (next : List (Value F G) → Proof F G → Nat → m (PIR.Outcome R × Proof F G))
      (next' : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G)),
      FitsK context table cost budget code env proof used holds →
      (∀ env' unread used', holds env' unread used' → next env' unread used' = next' env' unread) →
      meteredK context challenge table cost budget code env proof used next =
        idealK context challenge table (Code.instructions code) env proof next'
  | [], env, proof, used, holds, next, next', fits, continues => by
      simp only [FitsK] at fits
      simpa only [meteredK, Code.instructions, idealK] using continues env proof used fits
  | .charge count :: rest, env, proof, used, holds, next, next', fits, continues => by
      simp only [FitsK, FitsStep] at fits
      simp only [meteredK, meteredStep, Code.instructions, fits.1, ite_true]
      exact meteredK_fits rest env proof (used + count) holds next next' fits.2 continues
  | .step instruction charged :: rest, env, proof, used, holds, next, next', fits, continues => by
      simp only [FitsK, FitsStep] at fits
      simp only [meteredK, meteredStep, Code.instructions, idealK, fits.1, ite_true]
      exact idealStep_congr context table challenge instruction env proof _ _ _ fits.2
        (fun env' unread found => meteredK_fits rest env' unread _ holds next next' found continues)
  | .helper instruction :: rest, env, proof, used, holds, next, next', fits, continues => by
      simp only [FitsK, FitsStep] at fits
      obtain ⟨first, called⟩ := fits
      simp only [meteredK, meteredStep, Code.instructions, idealK, first, ite_true]
      rcases instruction with ⟨operation, operands, results, body⟩
      cases operation with
      | call helper =>
          simp only at called ⊢
          cases argumentsEq : read env operands with
          | none =>
              simp only [idealStep, argumentsEq]
          | some arguments =>
              simp only [argumentsEq] at called
              simp only [called.1, ite_true]
              exact idealStep_congr context table challenge _ env proof _ _ _ called.2
                (fun env' unread found => meteredK_fits rest env' unread _ holds next next' found continues)
      | _ => simp at called
  | .loop site maximum yielded operands results body :: rest, env, proof, used, holds, next, next',
      fits, continues => by
      simp only [FitsK, FitsStep] at fits
      simp only [meteredK, meteredStep, Code.instructions, idealK]
      cases operands with
      | nil => simp [idealStep]
      | cons count initial =>
          simp only [idealStep]
          simp only at fits
          cases countEq : indexAt env count with
          | none => simp
          | some bound =>
              cases initialEq : Construction.read env initial with
              | none => simp
              | some carried =>
                  simp only [countEq, initialEq] at fits
                  simp only
                  by_cases bounded : bound ≤ maximum
                  · obtain ⟨start, iterations⟩ := fits bounded
                    simp only [bounded, start, ite_true]
                    -- The iterations agree as their bodies and yields do.
                    have agree : ∀ (items : List Nat) (values : List (Value F G)) (unread : Proof F G)
                        (charged : Nat),
                        FitsIterate budget (fun start unread used' holds' =>
                            FitsK context table cost budget body start unread used' holds') env yielded items
                          values unread charged (fun final unread' used' =>
                            FitsK context table cost budget rest (env ++ final) unread' used' holds) →
                        meteredIterate budget (fun start unread' used' continuation =>
                            meteredK context challenge table cost budget body start unread' used' continuation)
                          env yielded items values unread charged (fun final unread' used' =>
                            meteredK context challenge table cost budget rest (env ++ final) unread' used' next) =
                        iterateM (fun start unread' continuation =>
                            idealK context challenge table (Code.instructions body) start unread' continuation)
                          env yielded items values unread (fun final unread' =>
                            idealK context challenge table (Code.instructions rest) (env ++ final) unread'
                              next') := by
                      intro items
                      induction items with
                      | nil =>
                          intro values unread charged within
                          exact meteredK_fits rest (env ++ values) unread charged holds next next' within
                            continues
                      | cons index indices ih =>
                          intro values unread charged within
                          simp only [FitsIterate] at within
                          simp only [meteredIterate, iterateM]
                          apply meteredK_fits body _ unread charged _ _ _ within
                          intro final unread' used' found
                          simp only [found.1, ite_true]
                          cases yieldedEq : Construction.read final yielded with
                          | none => rfl
                          | some carried' => exact ih carried' unread' (used' + 1) (found.2 carried' yieldedEq)
                    exact agree _ _ _ _ iterations
                  · simp only [bounded, ite_false]

omit [LawfulMonad m] in
/-- At a sufficient budget the metered meaning of a reading is the ideal meaning
of its constructed instructions. -/
theorem metered_sufficient {lowered : Lowered} {env : List (Value F G)} {proof : Proof F G}
    (sufficient : Sufficient context table cost budget lowered env proof) :
    metered context challenge table cost budget lowered env proof =
      ideal context challenge table lowered.returned (Code.instructions lowered.code) env proof := by
  unfold metered ideal
  unfold Sufficient at sufficient
  apply meteredK_fits context challenge table cost budget lowered.code env proof 0 _ _ _ sufficient
  intro final unread used fits
  simp [fits]

end Metered

/-! ## The executable at a sufficient budget -/

section Executable
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (vocabulary : Vocabulary) (validator : Validator) (context : Context)
  (challenge : History F G → m F) (table : Structured.Evaluation.Meanings F G Structured.closedInterface)
  (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)

/-- At a budget sufficient for every run of the reading on the decoded proof,
the executable has the ideal meaning's observation and challenge interaction. -/
theorem execute_sufficient (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) (data : List (Value F G)) (history : History F G)
    (bytes : List UInt8) (admitted : validator.admits data = true)
    (sufficient : Sufficient context table (helperCost vocabulary validator) budget L
      (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes)) :
    Run.observe <$> execute vocabulary validator context challenge decode budget data history bytes =
      idealObservation <$> ideal context challenge table L.returned (Code.instructions L.code)
        (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) bytes) := by
  rw [execute_metered vocabulary validator context challenge table decode budget helpers prepared reading data
    history bytes admitted, metered_sufficient context challenge table _ budget sufficient]

/-- With the expected framing header and a budget sufficient for every run of
the reading on the decoded proof, host validation is the ideal acceptance of the
decoded proof. -/
theorem validate_sufficient (helpers : List String)
    (prepared : ∀ name ∈ helpers, Prepared vocabulary validator table name) {L : Lowered}
    (reading : validator.read vocabulary helpers = .ok L) (binding : List UInt8) (acceptance : Nat)
    (data : List (Value F G)) (history : History F G) (bytes : List UInt8)
    (admitted : validator.admits data = true) (header : bytes.take 40 = magic ++ binding)
    (sufficient : Sufficient context table (helperCost vocabulary validator) budget L
      (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) (bytes.drop 40))) :
    validate vocabulary validator context challenge decode budget binding acceptance data history bytes =
      (fun result => Accepts acceptance (idealObservation result)) <$>
        ideal context challenge table L.returned (Code.instructions L.code)
          (data ++ [.transcript history]) (decodeProof decode (Plan.types data L.plan) (bytes.drop 40)) := by
  rw [validate_metered vocabulary validator context challenge table decode budget helpers prepared reading
    binding acceptance data history bytes admitted header,
    metered_sufficient context challenge table _ budget sufficient]

end Executable

end Zkc.Executable

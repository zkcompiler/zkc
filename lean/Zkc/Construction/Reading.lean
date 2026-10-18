module

public import Zkc.Construction.Semantics

@[expose] public section

/-! Reasoning about the interactive reading of exported programs.

`spec` computes transcript values as inert histories: observations and
challenges extend them, but no action, stop or data value reads one. Two
environments that agree except for transcript histories (`Similar`) therefore
give the same interactive reading, for continuations that themselves only
distinguish environments up to histories (`specK_similar`). A loop whose body
reads, on the encoding of every valid state, as one step of a plain process
followed by the encoding of that step's result then reads as the repeated
steps (`iterate_repeatN`, `iterate_range_repeatN`): the yielded transcript
values may carry any histories. `Yields` states what every value a plain
process returns satisfies, which such loop laws may assume of earlier steps,
and `specK_append` reads concatenated instruction lists in sequence.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source

variable {F G : Type}

/-- A value with any transcript history forgotten. -/
def Value.forget : Value F G → Value F G
  | .transcript _ => .transcript []
  | value => value

/-- Values with the same forgotten form are equal or are both transcripts. -/
theorem Value.forget_eq {left right : Value F G} (same : left.forget = right.forget) :
    left = right ∨ ∃ first second, left = .transcript first ∧ right = .transcript second := by
  cases left <;> cases right <;> simp_all [Value.forget]

/-- Environments that agree except for transcript histories. -/
def Similar (left right : List (Value F G)) : Prop :=
  left.map Value.forget = right.map Value.forget

theorem Similar.refl (env : List (Value F G)) : Similar env env := rfl

theorem Similar.append {left right extra extra' : List (Value F G)} (similar : Similar left right)
    (similarExtra : Similar extra extra') : Similar (left ++ extra) (right ++ extra') := by
  simp only [Similar, List.map_append] at *
  rw [similar, similarExtra]

theorem Similar.cons {left right : List (Value F G)} (value : Value F G)
    (similar : Similar left right) : Similar (value :: left) (value :: right) := by
  simp only [Similar, List.map_cons] at *
  rw [similar]

theorem Similar.transcripts (left right : List (Value F G)) (first second : History F G)
    (similar : Similar left right) :
    Similar (left ++ [.transcript first]) (right ++ [.transcript second]) :=
  Similar.append similar rfl

theorem Similar.getElem? {left right : List (Value F G)} (similar : Similar left right) (index : Nat) :
    (left[index]?).map Value.forget = (right[index]?).map Value.forget := by
  have := congrArg (·[index]?) similar
  simpa only [List.getElem?_map] using this

/-- Two similar environments hold the same value at each position, or
transcripts at the same positions. -/
theorem Similar.entry {left right : List (Value F G)} (similar : Similar left right) (index : Nat) :
    left[index]? = right[index]? ∨
      ∃ first second, left[index]? = some (.transcript first) ∧
        right[index]? = some (.transcript second) := by
  have entries := similar.getElem? index
  cases leftEntry : left[index]? with
  | none =>
      rw [leftEntry] at entries
      cases rightEntry : right[index]? with
      | none => exact .inl rfl
      | some value => rw [rightEntry] at entries; cases entries
  | some value =>
      rw [leftEntry] at entries
      cases rightEntry : right[index]? with
      | none => rw [rightEntry] at entries; cases entries
      | some value' =>
          rw [rightEntry] at entries
          simp only [Option.map_some, Option.some.injEq] at entries
          rcases Value.forget_eq entries with same | ⟨first, second, rfl, rfl⟩
          · exact .inl (by rw [same])
          · exact .inr ⟨first, second, rfl, rfl⟩

theorem dataAt_similar {left right : List (Value F G)} (similar : Similar left right) (index : Nat) :
    dataAt left index = dataAt right index := by
  unfold dataAt
  rcases similar.entry index with same | ⟨_, _, leftEntry, rightEntry⟩
  · rw [same]
  · rw [leftEntry, rightEntry]

theorem indexAt_similar {left right : List (Value F G)} (similar : Similar left right) (index : Nat) :
    indexAt left index = indexAt right index := by
  unfold indexAt
  rcases similar.entry index with same | ⟨_, _, leftEntry, rightEntry⟩
  · rw [same]
  · rw [leftEntry, rightEntry]

theorem indicesAt_similar {left right : List (Value F G)} (similar : Similar left right) (index : Nat) :
    indicesAt left index = indicesAt right index := by
  unfold indicesAt
  rcases similar.entry index with same | ⟨_, _, leftEntry, rightEntry⟩
  · rw [same]
  · rw [leftEntry, rightEntry]

/-- Reading similar environments fails at the same references and otherwise
returns similar values. -/
theorem read_similar {left right : List (Value F G)} (similar : Similar left right) :
    ∀ references : List Nat,
      (read left references = none ∧ read right references = none) ∨
        ∃ values values', read left references = some values ∧
          read right references = some values' ∧ Similar values values'
  | [] => .inr ⟨[], [], rfl, rfl, rfl⟩
  | reference :: rest => by
      simp only [read, List.mapM_cons] at *
      rcases read_similar similar rest with ⟨none, none'⟩ | ⟨values, values', found, found', same⟩
      · simp only [read] at none none'
        left
        constructor <;> simp [none, none']
      · simp only [read] at found found'
        rcases similar.entry reference with entry | ⟨first, second, leftEntry, rightEntry⟩
        · cases leftEntry : left[reference]? with
          | none =>
              have rightEntry : right[reference]? = none := by rw [← entry, leftEntry]
              left
              simp [rightEntry]
          | some value =>
              have rightEntry : right[reference]? = some value := by rw [← entry, leftEntry]
              right
              refine ⟨value :: values, value :: values', ?_, ?_, ?_⟩
              · simp [found]
              · simp [rightEntry, found']
              · simp only [Similar, List.map_cons] at same ⊢
                rw [same]
        · right
          refine ⟨.transcript first :: values, .transcript second :: values', ?_, ?_, ?_⟩
          · simp [leftEntry, found]
          · simp [rightEntry, found']
          · simp only [Similar, List.map_cons] at same ⊢
            rw [same]
            rfl

theorem decode_forget (ty : Structured.Ty) {value value' : Value F G}
    (same : value.forget = value'.forget) : Value.decode ty value = Value.decode ty value' := by
  rcases Value.forget_eq same with rfl | ⟨_, _, rfl, rfl⟩
  · rfl
  · cases ty <;> rfl

theorem decodeValues_similar :
    ∀ (types : List Structured.Ty) (values values' : List (Value F G)), Similar values values' →
      decodeValues types values = decodeValues types values'
  | [], [], [], _ => rfl
  | [], _ :: _, [], similar => by simp [Similar] at similar
  | [], [], _ :: _, similar => by simp [Similar] at similar
  | [], _ :: _, _ :: _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: _, _ :: _, [], similar => by simp [Similar] at similar
  | _ :: _, [], _ :: _, similar => by simp [Similar] at similar
  | ty :: types, value :: values, value' :: values', similar => by
      simp only [Similar, List.map_cons, List.cons.injEq] at similar
      simp only [decodeValues, decode_forget ty similar.1,
        decodeValues_similar types values values' similar.2]

theorem calculate_similar [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (calculation : Calculation) {arguments arguments' : List (Value F G)}
    (similar : Similar arguments arguments') :
    calculate calculation arguments = calculate calculation arguments' := by
  unfold calculate
  rw [decodeValues_similar _ _ _ similar]

theorem callHelper_similar [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (name : String)
    {arguments arguments' : List (Value F G)} (similar : Similar arguments arguments') :
    callHelper table name arguments = callHelper table name arguments' := by
  unfold callHelper
  split
  · rfl
  · rw [decodeValues_similar _ _ _ similar]

section Interactive
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (context : Context) (handle : Nat)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Continuations that do not distinguish transcript histories. -/
def AgreeUpToHistories {A : Type} (first second : List (Value F G) → PIR.Proc (Actions F G) A) : Prop :=
  ∀ left right, Similar left right → first left = second right

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem iterate_similar {A : Type}
    (body body' : List (Value F G) → (List (Value F G) → PIR.Proc (Actions F G) A) →
      PIR.Proc (Actions F G) A)
    (bodySimilar : ∀ start start' next next', Similar start start' → AgreeUpToHistories next next' →
      body start next = body' start' next')
    {env env' : List (Value F G)} (similar : Similar env env') (yielded : List Nat) :
    ∀ (items : List Nat) (carried carried' : List (Value F G))
      (next next' : List (Value F G) → PIR.Proc (Actions F G) A),
      Similar carried carried' → AgreeUpToHistories next next' →
      iterate body env yielded items carried next = iterate body' env' yielded items carried' next'
  | [], _, _, _, _, carriedSimilar, agree => agree _ _ carriedSimilar
  | index :: rest, carried, carried', next, next', carriedSimilar, agree => by
      simp only [iterate]
      apply bodySimilar _ _ _ _ (Similar.append similar (Similar.cons _ carriedSimilar))
      intro final final' finalSimilar
      dsimp only
      rcases read_similar finalSimilar yielded with ⟨none, none'⟩ |
        ⟨values, values', found, found', same⟩
      · rw [none, none']
      · rw [found, found']
        exact iterate_similar body body' bodySimilar similar yielded rest values values' next next'
          same agree

mutual
/-- The interactive reading is the same on environments that agree except for
transcript histories. -/
theorem specK_similar {A : Type} :
    ∀ (instructions : List Instruction) (env env' : List (Value F G))
      (next next' : List (Value F G) → PIR.Proc (Actions F G) A),
      Similar env env' → AgreeUpToHistories next next' →
      specK context handle table instructions env next = specK context handle table instructions env' next'
  | [], env, env', next, next', similar, agree => agree env env' similar
  | instruction :: rest, env, env', next, next', similar, agree => by
      simp only [specK]
      exact specStep_similar instruction env env' _ _ similar
        (fun final final' finalSimilar => specK_similar rest final final' next next' finalSimilar agree)

theorem specStep_similar {A : Type} :
    ∀ (instruction : Instruction) (env env' : List (Value F G))
      (next next' : List (Value F G) → PIR.Proc (Actions F G) A),
      Similar env env' → AgreeUpToHistories next next' →
      specStep context handle table instruction env next = specStep context handle table instruction env' next'
  | ⟨operation, operands, results, body⟩, env, env', next, next', similar, agree => by
      cases operation with
      | loop site maximum yielded =>
        match operands with
        | [] => rfl
        | count :: initial =>
          simp only [specStep]
          rw [indexAt_similar similar count]
          rcases read_similar similar initial with ⟨none, none'⟩ |
            ⟨carried, carried', found, found', same⟩
          · rw [none, none']
            cases indexAt env' count <;> rfl
          · rw [found, found']
            cases indexAt env' count with
            | none => rfl
            | some bound =>
              dsimp only
              split
              · exact iterate_similar (fun start continuation => specK context handle table body start continuation)
                  (fun start continuation => specK context handle table body start continuation)
                  (fun start start' continuation continuation' startSimilar continuationAgree =>
                    specK_similar body start start' continuation continuation' startSimilar continuationAgree)
                  similar yielded _ carried carried' _ _ same
                  (fun final final' finalSimilar => agree _ _ (Similar.append similar finalSimilar))
              · rfl
      | receive site schema peer ty =>
        cases operands with
        | nil =>
          simp only [specStep]
          split
          · congr 1
            funext value
            split
            · exact agree _ _ (Similar.append similar rfl)
            · rfl
          · rfl
        | cons => rfl
      | indicesEmpty =>
        cases operands with
        | nil => exact agree _ _ (Similar.append similar rfl)
        | cons => rfl
      | indicesAppend =>
        match operands with
        | [coordinates, index] =>
          simp only [specStep]
          rw [indicesAt_similar similar coordinates, indexAt_similar similar index]
          exact agree _ _ (Similar.append similar rfl)
        | [] => rfl
        | [_] => rfl
        | _ :: _ :: _ :: _ => rfl
      | observe suite template =>
        match operands with
        | [state, value, coordinates] =>
          simp only [specStep]
          rw [dataAt_similar similar value]
          cases template.origin context with
          | none => exact agree _ _ (Similar.transcripts _ _ _ _ similar)
          | some origin =>
            cases dataAt env' value with
            | none => exact agree _ _ (Similar.transcripts _ _ _ _ similar)
            | some payload =>
              dsimp only
              split
              · cases payload <;>
                  simp only [sendPayload] <;>
                  exact congrArg _ (funext fun _ => agree _ _ (Similar.transcripts _ _ _ _ similar))
              · exact agree _ _ (Similar.transcripts _ _ _ _ similar)
        | [] => rfl
        | [_] => rfl
        | [_, _] => rfl
        | _ :: _ :: _ :: _ :: _ => rfl
      | challenge suite field template =>
        match operands with
        | [state, coordinates] =>
          simp only [specStep]
          split
          · congr 1
            funext answer
            exact agree _ _ (Similar.append similar
              (Similar.append (rfl : Similar [Value.data (.field field answer)] [_]) rfl))
          · rfl
        | [] => rfl
        | [_] => rfl
        | _ :: _ :: _ :: _ => rfl
      | calculate calculation =>
        simp only [specStep]
        rcases read_similar similar operands with ⟨none, none'⟩ |
          ⟨arguments, arguments', found, found', same⟩
        · rw [none, none']
        · rw [found, found']
          dsimp only
          rw [calculate_similar calculation same]
          split
          · exact agree _ _ (Similar.append similar rfl)
          · rfl
      | call name =>
        simp only [specStep]
        rcases read_similar similar operands with ⟨none, none'⟩ |
          ⟨arguments, arguments', found, found', same⟩
        · rw [none, none']
        · rw [found, found']
          dsimp only
          rw [callHelper_similar table name same]
          split
          · split
            · exact agree _ _ (Similar.append similar rfl)
            · rfl
          · rfl
      | guard site =>
        match operands with
        | [condition] =>
          simp only [specStep]
          rcases similar.entry condition with same | ⟨_, _, leftEntry, rightEntry⟩
          · rw [same]
            split
            · exact agree _ _ similar
            · rfl
            · rfl
          · rw [leftEntry, rightEntry]
        | [] => rfl
        | _ :: _ :: _ => rfl
      | send site schema peer => rfl
      | unsupported name => rfl
end

/-- Reading a concatenation of instruction lists reads the second list after
the first. -/
theorem specK_append {A : Type} (first second : List Instruction) :
    ∀ (env : List (Value F G)) (next : List (Value F G) → PIR.Proc (Actions F G) A),
      specK context handle table (first ++ second) env next =
        specK context handle table first env fun env' => specK context handle table second env' next := by
  induction first with
  | nil => intro env next; rfl
  | cons instruction rest ih =>
      intro env next
      simp only [List.cons_append, specK]
      congr 1
      funext env'
      exact ih env' next

end Interactive

/-! ## Loops as repeated steps -/

/-- Every value a process can return satisfies `property`. -/
def Yields {I : PIR.Signature} {A : Type} (property : A → Prop) : PIR.Proc I A → Prop
  | .done value => property value
  | .halt _ => True
  | .call _ next => ∀ reply, Yields property (next reply)

theorem Yields.bind_congr {I : PIR.Signature} {A B : Type} {property : A → Prop}
    {process : PIR.Proc I A} (yields : Yields property process) {first second : A → PIR.Proc I B}
    (same : ∀ value, property value → first value = second value) :
    process.bind first = process.bind second := by
  induction process with
  | done value => exact same value yields
  | halt reason => rfl
  | call operation next ih =>
      simp only [PIR.Proc.bind]
      congr 1
      funext reply
      exact ih reply (yields reply)

theorem Yields.bind {I : PIR.Signature} {A B : Type} {property : A → Prop} {result : B → Prop}
    {process : PIR.Proc I A} (yields : Yields property process) {next : A → PIR.Proc I B}
    (nextYields : ∀ value, property value → Yields result (next value)) :
    Yields result (process.bind next) := by
  induction process with
  | done value => exact nextYields value yields
  | halt reason => trivial
  | call operation continuation ih => exact fun reply => ih reply (yields reply)

theorem Yields.mono {I : PIR.Signature} {A : Type} {property weaker : A → Prop}
    {process : PIR.Proc I A} (yields : Yields property process)
    (implies : ∀ value, property value → weaker value) : Yields weaker process := by
  induction process with
  | done value => exact implies value yields
  | halt reason => trivial
  | call operation continuation ih => exact fun reply => ih reply (yields reply)

/-- Repeated steps preserve a counted invariant. -/
theorem Yields.repeatN {I : PIR.Signature} {A : Type} {invariant : Nat → A → Prop}
    {step : A → PIR.Proc I A}
    (preserved : ∀ index value, invariant index value → Yields (invariant (index + 1)) (step value)) :
    ∀ (count index : Nat) (value : A), invariant index value →
      Yields (invariant (index + count)) (PIR.repeatN count step value)
  | 0, _, _, holds => holds
  | count + 1, index, value, holds =>
      (preserved index value holds).bind fun next nextHolds => by
        have rest := Yields.repeatN preserved count (index + 1) next nextHolds
        rwa [Nat.add_right_comm, Nat.add_assoc] at rest

section Iterations

/-- The continuation of one loop iteration: read the yielded values, then
continue with them. -/
def afterIteration {A : Type} (yielded : List Nat) (next : List (Value F G) → PIR.Proc (Actions F G) A)
    (final : List (Value F G)) : PIR.Proc (Actions F G) A :=
  match read final yielded with
  | some carried => next carried
  | none => .halt .refused

theorem iterate_cons {A : Type}
    (body : List (Value F G) → (List (Value F G) → PIR.Proc (Actions F G) A) → PIR.Proc (Actions F G) A)
    (env : List (Value F G)) (yielded : List Nat) (index : Nat) (rest : List Nat)
    (carried : List (Value F G)) (next : List (Value F G) → PIR.Proc (Actions F G) A) :
    iterate body env yielded (index :: rest) carried next =
      body (env ++ .index index :: carried)
        (afterIteration yielded fun carried' => iterate body env yielded rest carried' next) := rfl

theorem afterIteration_agree {A : Type} (yielded : List Nat)
    {next next' : List (Value F G) → PIR.Proc (Actions F G) A} (agree : AgreeUpToHistories next next') :
    AgreeUpToHistories (afterIteration yielded next) (afterIteration yielded next') := by
  intro final final' finalSimilar
  unfold afterIteration
  rcases read_similar finalSimilar yielded with ⟨none, none'⟩ | ⟨values, values', found, found', same⟩
  · rw [none, none']
  · rw [found, found']
    exact agree values values' same

/-- A loop whose body reads, on the encoding of every valid state at an
induction index below `bound`, as one step followed by the encoding of the
step's result reads as that many repeated steps. The body may depend on the
index through `Valid`; the continuation sees the yielded values only up to
transcript histories. -/
theorem iterate_repeatN {S A : Type}
    (body : List (Value F G) → (List (Value F G) → PIR.Proc (Actions F G) A) → PIR.Proc (Actions F G) A)
    (bodySimilar : ∀ start start' next next', Similar start start' → AgreeUpToHistories next next' →
      body start next = body start' next')
    (env : List (Value F G)) (yielded : List Nat) (encode : S → List (Value F G))
    (step : S → PIR.Proc (Actions F G) S) (Valid : Nat → S → Prop) (bound : Nat)
    (law : ∀ index state (next : List (Value F G) → PIR.Proc (Actions F G) A),
      index < bound → Valid index state → AgreeUpToHistories next next →
      body (env ++ .index index :: encode state) (afterIteration yielded next) =
        (step state).bind fun state' => next (encode state'))
    (preserved : ∀ index state, index < bound → Valid index state →
      Yields (Valid (index + 1)) (step state)) :
    ∀ (count start : Nat) (state : S) (carried : List (Value F G))
      (next : List (Value F G) → PIR.Proc (Actions F G) A),
      start + count ≤ bound → Valid start state → Similar carried (encode state) → AgreeUpToHistories next next →
      iterate body env yielded (List.range' start count) carried next =
        (PIR.repeatN count step state).bind fun state' => next (encode state')
  | 0, _, _, _, _, _, _, similar, agree => agree _ _ similar
  | count + 1, start, state, carried, next, inside, valid, similar, agree => by
      have restAgree : AgreeUpToHistories (fun carried' => iterate body env yielded (List.range' (start + 1) count) carried' next)
          (fun carried' => iterate body env yielded (List.range' (start + 1) count) carried' next) :=
        fun carried' carried'' carriedSimilar =>
          iterate_similar body body bodySimilar (Similar.refl env) yielded _ carried' carried'' next next
            carriedSimilar agree
      rw [List.range'_succ, iterate_cons,
        bodySimilar _ (env ++ .index start :: encode state) _ _
          (Similar.append (Similar.refl env) (Similar.cons _ similar))
          (afterIteration_agree yielded restAgree),
        law start state _ (by omega) valid restAgree]
      simp only [PIR.repeatN, PIR.Proc.bind_assoc]
      exact (preserved start state (by omega) valid).bind_congr fun state' valid' =>
        iterate_repeatN body bodySimilar env yielded encode step Valid bound law preserved count (start + 1)
          state' (encode state') next (by omega) valid' (Similar.refl _) agree

/-- The same for the loop domain `0, …, count - 1` of the interactive reading. -/
theorem iterate_range_repeatN {S A : Type}
    (body : List (Value F G) → (List (Value F G) → PIR.Proc (Actions F G) A) → PIR.Proc (Actions F G) A)
    (bodySimilar : ∀ start start' next next', Similar start start' → AgreeUpToHistories next next' →
      body start next = body start' next')
    (env : List (Value F G)) (yielded : List Nat) (encode : S → List (Value F G))
    (step : S → PIR.Proc (Actions F G) S) (Valid : Nat → S → Prop) (count : Nat)
    (law : ∀ index state (next : List (Value F G) → PIR.Proc (Actions F G) A),
      index < count → Valid index state → AgreeUpToHistories next next →
      body (env ++ .index index :: encode state) (afterIteration yielded next) =
        (step state).bind fun state' => next (encode state'))
    (preserved : ∀ index state, index < count → Valid index state →
      Yields (Valid (index + 1)) (step state))
    (state : S) (carried : List (Value F G)) (next : List (Value F G) → PIR.Proc (Actions F G) A)
    (valid : Valid 0 state) (similar : Similar carried (encode state)) (agree : AgreeUpToHistories next next) :
    iterate body env yielded (List.range count) carried next =
      (PIR.repeatN count step state).bind fun state' => next (encode state') := by
  rw [List.range_eq_range']
  exact iterate_repeatN body bodySimilar env yielded encode step Valid count law preserved count 0 state
    carried next (by omega) valid similar agree

end Iterations


end Zkc.Construction

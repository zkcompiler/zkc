module

public import Zkc.Executable.DomainTermSemantics
public import Zkc.Executable.DomainAnchorSemantics

@[expose] public section

/-! Soundness of finite scoped normalization against actual Domain execution.
Acceptance proves equality of observable Processes, including stopped paths.
It does not imply participant admission or successful execution: unchanged
anchors can retain the same refusal on both sides. Helper behavior comes from
the actual program and the canonical Domain interpreter. -/
set_option autoImplicit false
namespace Zkc.Executable.CanonicalNormalization
open Zkc.Construction Zkc.Source
variable {F G : Type}

theorem SortedValues.eq {values : List (Value F G)} {sorts : List ValueSort}
    (sorted : SortedValues values sorts) : values.map Domain.Value.sort = sorts := by
  induction values generalizing sorts with
  | nil => cases sorts <;> simp_all [SortedValues]
  | cons value rest ih =>
      cases sorts with
      | nil => simp [SortedValues] at sorted
      | cons sort sorts =>
          have head := sorted.2 0 value sort rfl rfl
          have tail : SortedValues rest sorts :=
            ⟨by simpa using sorted.1, fun i v s h h' => sorted.2 (i + 1) v s h h'⟩
          simp only [List.map_cons, head, ih tail]

theorem SortedValues.of_eq {values : List (Value F G)} {sorts : List ValueSort}
    (sorted : values.map Domain.Value.sort = sorts) : SortedValues values sorts := by
  subst sorts
  refine ⟨by simp, ?_⟩
  intro i value sort found sortFound
  simpa [List.getElem?_map, found] using sortFound

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem sort_eval {terms : Terms} {valuation : Valuation F G} (sorted : terms.Sorted valuation)
    {id : Nat} {sort : ValueSort} {value : Value F G}
    (found : terms.sort? id = some sort) (evaluated : terms.eval valuation id = some value) :
    value.sort = sort := by
  unfold Terms.sort? at found
  cases entry : terms[id]? with
  | none => simp [entry] at found
  | some pair =>
      rcases pair with ⟨node, actual⟩
      simp only [entry, Option.map_some, Option.some.injEq] at found
      subst actual
      exact sorted id node sort value entry evaluated

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem indices_of_sort {value : Value F G} (sorted : value.sort = .indices) :
    ∃ path, value = .indices path := by
  cases value with
  | data payload => cases sorted
  | transcript => cases sorted
  | indices path => exact ⟨path, rfl⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem index_of_sort {value : Value F G} (sorted : value.sort = .data .index) :
    ∃ index, value = .data (.index index) := by
  obtain ⟨index, decoded⟩ := DomainVM.decode_of_sort sorted
  have encoded := Domain.Value.encode_decode decoded
  exact ⟨index, (Option.some.inj encoded).symm⟩

/-- Only a total, well-declared, well-sorted node can disappear from a schedule. -/
theorem term_spec {terms : Terms} {ids : List Nat} {anchor : Nat} {instruction : Instruction}
    {terms' : Terms} {id : Nat} (movable : Instruction.movable instruction = true)
    (term : terms.term ids anchor instruction = .ok (terms', id))
    {valuation : Valuation F G} {env : List (Value F G)} (denotes : Denotes terms valuation ids env)
    (bounded : Bounded terms ids) (formed : terms.Formed) (sorted : terms.Sorted valuation) :
    ∃ value, (∃ more, terms' = terms ++ more) ∧ id < terms'.length ∧ terms'.Formed ∧
      terms'.Sorted valuation ∧ (∀ anchor', terms.Before anchor' → terms'.Before anchor') ∧
      terms'.eval valuation id = some value ∧
      ∀ (program : Structured.Program) (context : Context),
        Domain.step (Structured.ringModel F G) program context instruction env = .done (env ++ [value]) := by
  rcases (movable_iff instruction).mp movable with
    ⟨calculation, operands, results, rfl, total⟩ | ⟨results, rfl⟩ | ⟨coordinates, index, results, rfl⟩
  · simp only [Terms.term] at term
    split at term
    · rename_i declared
      subst results
      cases found : operandIds ids operands with
      | none => simp [found] at term
      | some operands' =>
          cases resultsEq : calculation.op.results with
          | nil => simp [found, resultsEq] at term
          | cons result more =>
            cases more with
            | cons => simp [found, resultsEq] at term
            | nil =>
              simp only [found, resultsEq] at term
              split at term
              · rename_i checks
                obtain ⟨sortsEq, data⟩ := checks
                simp only [Except.ok.injEq] at term
                obtain ⟨rfl, rfl⟩ : (terms.intern (.calculate calculation operands', .data result)).1 = terms' ∧
                    (terms.intern (.calculate calculation operands', .data result)).2 = id := by
                  rw [term]; exact ⟨rfl, rfl⟩
                obtain ⟨arguments, readEq, argumentsEq⟩ := denotes.read_some found
                have below := operandIds_bounded bounded found
                have argumentsSorted := sorted_values sorted argumentsEq
                  (sorts := calculation.op.arguments.map .data) (by rw [sortsEq, List.map_map])
                obtain ⟨values, computed, valuesSorted⟩ :=
                  DomainVM.calculate_total calculation total arguments data argumentsSorted.eq
                have single : values.length = 1 := by
                  have := congrArg List.length valuesSorted
                  simpa [resultsEq] using this
                rcases values with _ | ⟨value, _ | ⟨_, _⟩⟩ <;> simp only [List.length_nil, List.length_cons] at single
                all_goals try omega
                have valueEq : (Node.calculate calculation operands').value terms valuation = some value := by
                  simp only [Node.value, argumentsEq, computed]
                obtain ⟨evaluates, formed', grown, within, -⟩ :=
                  intern_eval (node := .calculate calculation operands') (sort := .data result)
                    (valuation := valuation) formed below
                refine ⟨value, grown, within, formed', ?_, ?_, by rw [evaluates, valueEq], ?_⟩
                · refine intern_sorted (node := .calculate calculation operands') sorted below ?_
                  intro value' found'
                  rw [valueEq, Option.some.injEq] at found'
                  subst value'
                  simpa [resultsEq] using valuesSorted
                · intro anchor' before
                  exact intern_before before (fun _ _ equal => by cases equal)
                · intro program context
                  simpa only [resultsEq] using DomainVM.step_calculate program context readEq computed valuesSorted
              · cases term
    · cases term
  · simp only [Terms.term] at term
    split at term
    · rename_i declared
      subst results
      simp only [Except.ok.injEq] at term
      obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesEmpty, .indices)).1 = terms' ∧
          (terms.intern (.indicesEmpty, .indices)).2 = id := by rw [term]; exact ⟨rfl, rfl⟩
      have below : ∀ operand ∈ Node.indicesEmpty.operands, operand < terms.length := by simp [Node.operands]
      obtain ⟨evaluates, formed', grown, within, -⟩ := intern_eval (sort := .indices) (valuation := valuation) formed below
      refine ⟨.indices [], grown, within, formed', ?_, ?_, by rw [evaluates]; rfl, ?_⟩
      · refine intern_sorted sorted below ?_
        intro value found'
        simp only [Node.value, Option.some.injEq] at found'
        subst value
        rfl
      · intro anchor' before
        exact intern_before before (fun _ _ equal => by cases equal)
      · intros; rfl
    · cases term
  · simp only [Terms.term] at term
    cases coordinatesFound : ids[coordinates]? with
    | none => simp [coordinatesFound] at term
    | some coordinatesId =>
      cases indexFound : ids[index]? with
      | none => simp [coordinatesFound, indexFound] at term
      | some indexId =>
        simp only [coordinatesFound, indexFound] at term
        split at term
        · rename_i checks
          obtain ⟨declared, coordinatesSort, indexSort⟩ := checks
          subst results
          simp only [Except.ok.injEq] at term
          obtain ⟨rfl, rfl⟩ : (terms.intern (.indicesAppend coordinatesId indexId, .indices)).1 = terms' ∧
              (terms.intern (.indicesAppend coordinatesId indexId, .indices)).2 = id := by
            rw [term]; exact ⟨rfl, rfl⟩
          have below : ∀ operand ∈ (Node.indicesAppend coordinatesId indexId).operands,
              operand < terms.length := by
            simp only [Node.operands, List.mem_cons, List.not_mem_nil, or_false]
            rintro operand (rfl | rfl)
            · exact bounded _ (List.mem_of_getElem? coordinatesFound)
            · exact bounded _ (List.mem_of_getElem? indexFound)
          have cWithin : coordinates < env.length := by rw [← denotes.1]; exact (List.getElem?_eq_some_iff.mp coordinatesFound).1
          have iWithin : index < env.length := by rw [← denotes.1]; exact (List.getElem?_eq_some_iff.mp indexFound).1
          have cValue := denotes.2 coordinates coordinatesId coordinatesFound
          have iValue := denotes.2 index indexId indexFound
          rw [List.getElem?_eq_getElem cWithin] at cValue
          rw [List.getElem?_eq_getElem iWithin] at iValue
          obtain ⟨path, pathEq⟩ := indices_of_sort (sort_eval sorted coordinatesSort cValue)
          obtain ⟨number, numberEq⟩ := index_of_sort (sort_eval sorted indexSort iValue)
          rw [pathEq] at cValue
          rw [numberEq] at iValue
          obtain ⟨evaluates, formed', grown, within, -⟩ := intern_eval (sort := .indices) (valuation := valuation) formed below
          have valueEq : (Node.indicesAppend coordinatesId indexId).value terms valuation = some (.indices (path ++ [number])) := by
            simp only [Node.value, cValue, iValue]
          refine ⟨.indices (path ++ [number]), grown, within, formed', ?_, ?_, by rw [evaluates, valueEq], ?_⟩
          · refine intern_sorted sorted below ?_
            intro value found'
            rw [valueEq, Option.some.injEq] at found'
            subst value
            rfl
          · intro anchor' before
            exact intern_before before (fun _ _ equal => by cases equal)
          · intro program context
            simp only [Domain.step, List.getElem?_eq_getElem cWithin, List.getElem?_eq_getElem iWithin, pathEq, numberEq]
            rfl
        · cases term

/-- Abbreviations at the checkpoint quotient, not new execution recursors. -/
abbrev run (program : Structured.Program) (context : Context) (instructions : List Instruction)
    (env : List (Value F G)) {R : Type}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R) :=
  ((Domain.evaluate (Structured.ringModel F G) program context instructions env).interpret
    Original.forgetCheckpoints).bind next

abbrev step (program : Structured.Program) (context : Context) (instruction : Instruction)
    (env : List (Value F G)) {R : Type}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R) :=
  ((Domain.step (Structured.ringModel F G) program context instruction env).interpret
    Original.forgetCheckpoints).bind next

theorem run_cons (program : Structured.Program) (context : Context) (instruction : Instruction)
    (rest : List Instruction) (env : List (Value F G)) {R : Type}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R) :
    run program context (instruction :: rest) env next =
      step program context instruction env (fun final => run program context rest final next) := by
  simp only [run, step, Domain.Correspondence.evaluate_cons, PIR.Process.interpret,
    Original.forgetCheckpoints, PIR.Process.bind, PIR.Process.interpret_bind, PIR.Process.bind_assoc]

theorem normalize_total {anchor : Nat} :
    ∀ {program : List Instruction} {terms : Terms} {ids : List Nat} {terms' : Terms} {ids' : List Nat}
      {rest : List Instruction}, advance anchor terms ids program = .ok (terms', ids', rest) →
      ∀ {valuation : Valuation F G} {env : List (Value F G)}, Denotes terms valuation ids env →
        Bounded terms ids → terms.Formed → terms.Sorted valuation →
        ∃ env', (∃ more, terms' = terms ++ more) ∧ Denotes terms' valuation ids' env' ∧ Bounded terms' ids' ∧
          terms'.Formed ∧ terms'.Sorted valuation ∧ (∀ anchor', terms.Before anchor' → terms'.Before anchor') ∧
          ∀ (source : Structured.Program) (context : Context) (R : Type)
            (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R),
            run source context program env next = run source context rest env' next
  | [], terms, ids, terms', ids', rest, advanced, valuation, env, denotes, bounded, formed, sorted => by
      simp only [advance, Except.ok.injEq, Prod.mk.injEq] at advanced
      obtain ⟨rfl, rfl, rfl⟩ := advanced
      exact ⟨env, ⟨[], by simp⟩, denotes, bounded, formed, sorted, fun _ before => before,
        by intros; rfl⟩
  | instruction :: program, terms, ids, terms', ids', rest, advanced, valuation, env, denotes, bounded, formed,
      sorted => by
      simp only [advance] at advanced
      split at advanced
      · rename_i movable
        cases termed : terms.term ids anchor instruction with
        | error refusal => simp [termed] at advanced
        | ok result =>
            obtain ⟨terms₁, id⟩ := result
            simp only [termed] at advanced
            obtain ⟨value, ⟨more, grown⟩, within, formed₁, sorted₁, before₁, evaluated, step⟩ :=
              term_spec movable termed denotes bounded formed sorted
            have denotes₁ : Denotes terms₁ valuation (ids ++ [id]) (env ++ [value]) := by
              rw [grown]
              exact (denotes.append bounded).push (by rw [← grown]; exact evaluated)
            have bounded₁ : Bounded terms₁ (ids ++ [id]) := by
              intro id' member
              rcases List.mem_append.mp member with member | member
              · rw [grown]; exact (bounded.append) id' member
              · simp only [List.mem_singleton] at member
                subst member
                exact within
            obtain ⟨env', ⟨more', grown'⟩, denotes', bounded', formed', sorted', before', run⟩ :=
              normalize_total advanced denotes₁ bounded₁ formed₁ sorted₁
            refine ⟨env', ⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, denotes', bounded', formed',
              sorted', fun anchor' before => before' anchor' (before₁ anchor' before), ?_⟩
            intro source context R next
            rw [run_cons]
            unfold CanonicalNormalization.step
            rw [step source context]
            exact run source context R next
      · simp only [Except.ok.injEq, Prod.mk.injEq] at advanced
        obtain ⟨rfl, rfl, rfl⟩ := advanced
        exact ⟨env, ⟨[], by simp⟩, denotes, bounded, formed, sorted, fun _ before => before,
          by intros; rfl⟩


theorem yields_all {I : PIR.Signature} {A B : Type} (process : PIR.Process I A)
    (property : B → Prop) (next : A → PIR.Process I B)
    (checked : ∀ value, PIR.Yields property (next value)) :
    PIR.Yields property (process.bind next) := by
  induction process with
  | done value => exact checked value
  | halt => trivial
  | call operation continuation ih => exact fun reply => ih reply

theorem yields_interpret {I J : PIR.Signature} {A : Type}
    (operations : PIR.OperationInterpretation I J) (process : PIR.Process I A)
    (property : A → Prop) (checked : PIR.Yields property process) :
    PIR.Yields property (process.interpret operations) := by
  induction process with
  | done value => exact checked
  | halt => trivial
  | call operation continuation ih =>
      exact yields_all (operations operation) property _ (fun reply => ih reply (checked reply))

theorem step_local_projected (program : Structured.Program) (context : Context)
    {R : Type} {operation : Operation} {operands : List Nat} {results : List ValueSort}
    {env arguments : List (Value F G)}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R)
    (notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded)
    (notLocal : ∀ port request template coordinates,
      operation ≠ .localService port request template coordinates)
    (found : Domain.read env operands = some arguments) :
    step program context ⟨operation, operands, results, []⟩ env next =
      step program context ⟨operation, List.range' 0 arguments.length, results, []⟩ arguments
        (fun final => next (env ++ final.drop arguments.length)) := by
  have localized :=  step_local program context (R := List (Value F G)) (results := results) PIR.Process.done notLoop notLocal found
  rw [PIR.Process.bind_done] at localized
  unfold step
  rw [localized, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
  rfl


omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem iterate_schema
    (body : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) (List (Value F G)))
    (outer : List (Value F G)) (yielded : List Nat) (declared : List ValueSort) :
    ∀ (items : List Nat) (current : List (Value F G)), Domain.sortsMatch declared current = true →
      PIR.Yields (fun final => Domain.sortsMatch declared final = true)
        (Domain.iterate body outer yielded declared items current) := by
  intro items
  induction items with
  | nil => intro current sorted; exact sorted
  | cons index rest ih =>
      intro current sorted
      simp only [Domain.iterate]
      apply yields_all
      intro final
      cases found : Domain.read final yielded with
      | none => trivial
      | some next =>
          dsimp only
          split
          · exact ih next (by assumption)
          · trivial

theorem loop_projected (program : Structured.Program) (context : Context)
    (site : String) (maximum : Nat) (yielded : List Nat) (count : Nat) (initial : List Nat)
    (declared : List ValueSort) (body : List Instruction) (env carried : List (Value F G))
    (bound : Nat) (counted : env[count]? = some (.data (.index bound)))
    (found : Domain.read env initial = some carried) (bounded : bound ≤ maximum)
    (sorted : Domain.sortsMatch declared carried = true) {R : Type}
    (next : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R) :
    step program context ⟨.loop site maximum yielded, count :: initial, declared, body⟩ env next =
      ((Domain.iterate (Domain.evaluate (Structured.ringModel F G) program context body)
        env yielded declared (List.range bound) carried).interpret Original.forgetCheckpoints).bind
        (fun final => next (env ++ final)) := by
  simp only [step, Domain.step, counted, found, bounded, sorted, and_self, ite_true,
    PIR.Process.interpret_bind, PIR.Process.bind_assoc]
  apply (yields_interpret Original.forgetCheckpoints _ _
    (iterate_schema _ env yielded declared (List.range bound) carried sorted)).bind_congr
  intro final checked
  simp only [checked, ite_true, PIR.Process.interpret, PIR.Process.bind]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem mapM_map_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.map f = ys.map some
  | [], ys, found => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst found
      rfl
  | x :: xs, ys, found => by
      simp only [List.mapM_cons] at found
      cases first : f x with
      | none => simp [first] at found
      | some y =>
          cases rest : xs.mapM f with
          | none => simp [first, rest] at found
          | some ys' =>
              simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at found
              subst found
              simp [first, mapM_map_some rest]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_cons_some {env : List (Value F G)} {operand : Nat} {operands : List Nat}
    {arguments : List (Value F G)} (found : Domain.read env (operand :: operands) = some arguments) :
    ∃ value rest, arguments = value :: rest ∧ env[operand]? = some value ∧
      Domain.read env operands = some rest := by
  simp only [Domain.read, List.mapM_cons] at found
  cases first : env[operand]? with
  | none => simp [first] at found
  | some value =>
      cases others : operands.mapM (fun reference => env[reference]?) with
      | none => simp [first, others] at found
      | some rest =>
          simp only [first, others, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at found
          exact ⟨value, rest, found.symm, rfl, others⟩

section Sound
variable (program : Structured.Program) (context : Context)

def ScopeSound (fuel : Nat) : Prop :=
  ∀ (terms : Terms) (exportedIds : List Nat) (exported : List Instruction) (readingIds : List Nat)
    (reading : List Instruction) (anchor : Nat) (terms' : Terms) (exportedIds' readingIds' : List Nat),
    checkScope fuel terms exportedIds exported readingIds reading anchor = .ok (terms', exportedIds', readingIds') →
    ∀ (valuation : Valuation F G) (exportedEnv readingEnv : List (Value F G)) (R : Type)
      (next next' : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R),
      Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv →
      (∀ (valuation' : Valuation F G) (anchor' : Nat) (exportedEnv' readingEnv' : List (Value F G)),
        Holds terms' valuation' anchor' exportedIds' exportedEnv' readingIds' readingEnv' →
          next exportedEnv' = next' readingEnv') →
      run program context exported exportedEnv next = run program context reading readingEnv next'

def AnchorSound (fuel : Nat) : Prop :=
  ∀ (terms : Terms) (exportedIds : List Nat) (first : Instruction) (readingIds : List Nat) (first' : Instruction)
    (anchor : Nat) (terms' : Terms) (resultIds : List Nat),
    checkAnchor fuel terms exportedIds first readingIds first' anchor = .ok (terms', resultIds) →
    ∀ (valuation : Valuation F G) (exportedEnv readingEnv : List (Value F G)) (R : Type)
      (next next' : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R),
      Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv →
      (∀ (results : List (Value F G)),
        Holds terms' { valuation with results := valuation.results ++ [results] } (anchor + 1)
          (exportedIds ++ resultIds) (exportedEnv ++ results) (readingIds ++ resultIds) (readingEnv ++ results) →
          next (exportedEnv ++ results) = next' (readingEnv ++ results)) →
      step program context first exportedEnv next = step program context first' readingEnv next'

theorem sound_zero : ScopeSound (F := F) (G := G) program context 0 ∧ AnchorSound (F := F) (G := G) program context 0 := by
  constructor
  · intro _ _ _ _ _ _ _ _ _ checked
    simp [checkScope] at checked
  · intro _ _ _ _ _ _ _ _ checked
    simp [checkAnchor] at checked

theorem scopeSound_succ (fuel : Nat) (scope : ScopeSound (F := F) (G := G) program context fuel)
    (anchors : AnchorSound (F := F) (G := G) program context fuel) : ScopeSound (F := F) (G := G) program context (fuel + 1) := by
  intro terms exportedIds exported readingIds reading anchor terms' exportedIds' readingIds' checked
    valuation exportedEnv readingEnv R next next' holds finishes
  simp only [checkScope] at checked
  cases advancedE : advance anchor terms exportedIds exported with
  | error refusal => simp [advancedE] at checked
  | ok resultE =>
    obtain ⟨terms₁, exportedIds₁, exported₁⟩ := resultE
    simp only [advancedE] at checked
    cases advancedR : advance anchor terms₁ readingIds reading with
    | error refusal => simp [advancedR] at checked
    | ok resultR =>
      obtain ⟨terms₂, readingIds₁, reading₁⟩ := resultR
      simp only [advancedR] at checked
      obtain ⟨exportedEnv₁, ⟨moreE, grownE⟩, denotesE, boundedE, formed₁, sorted₁, before₁, runE⟩ :=
        normalize_total advancedE holds.exported holds.exportedBounded holds.formed holds.sorted
      have readingDenotes₁ : Denotes terms₁ valuation readingIds readingEnv := by
        rw [grownE]; exact holds.reading.append holds.readingBounded
      have readingBounded₁ : Bounded terms₁ readingIds := by rw [grownE]; exact holds.readingBounded.append
      obtain ⟨readingEnv₁, ⟨moreR, grownR⟩, denotesR, boundedR, formed₂, sorted₂, before₂, runR⟩ :=
        normalize_total advancedR readingDenotes₁ readingBounded₁ formed₁ sorted₁
      have holds₂ : Holds terms₂ valuation anchor exportedIds₁ exportedEnv₁ readingIds₁ readingEnv₁ :=
        ⟨by rw [grownR]; exact denotesE.append boundedE, denotesR, by rw [grownR]; exact boundedE.append, boundedR,
          formed₂, sorted₂, before₂ anchor (before₁ anchor holds.before), holds.results⟩
      rw [runE program context R next, runR program context R next']
      obtain ⟨skipped, rfl⟩ := advance_suffix advancedE
      cases exported₁ with
      | nil =>
          cases reading₁ with
          | nil =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at checked
              obtain ⟨rfl, rfl, rfl⟩ := checked
              exact finishes valuation anchor exportedEnv₁ readingEnv₁ holds₂
          | cons => simp at checked
      | cons first exportedRest =>
          cases reading₁ with
          | nil => simp at checked
          | cons first' readingRest =>
              simp only at checked
              cases anchored : checkAnchor fuel terms₂ exportedIds₁ first readingIds₁ first' anchor with
              | error refusal => simp [anchored] at checked
              | ok resultA =>
                  obtain ⟨terms₃, resultIds⟩ := resultA
                  simp only [anchored] at checked
                  rw [run_cons, run_cons]
                  refine anchors terms₂ exportedIds₁ first readingIds₁ first' anchor terms₃ resultIds anchored
                    valuation exportedEnv₁ readingEnv₁ R _ _ holds₂ ?_
                  intro results holds₃
                  exact scope terms₃ _ exportedRest _ readingRest (anchor + 1) terms' exportedIds' readingIds'
                    checked _ _ _ R next next' holds₃
                    finishes

theorem loop_step (fuel : Nat) (scope : ScopeSound (F := F) (G := G) program context fuel)
    {terms : Terms} {valuation : Valuation F G} {anchor : Nat} {exportedIds readingIds : List Nat}
    {exportedEnv readingEnv : List (Value F G)}
    (holds : Holds terms valuation anchor exportedIds exportedEnv readingIds readingEnv)
    {loop loop' : LoopParts}
    (maximumEq : loop.maximum = loop'.maximum) (resultsEq : loop.results = loop'.results)
    {counted : Nat} {carried : List Nat} (countSort : terms.sort? counted = some (.data .index))
    (foundE : operandIds exportedIds (loop.count :: loop.initial) = some (counted :: carried))
    (foundR : operandIds readingIds (loop'.count :: loop'.initial) = some (counted :: carried))
    {sorts : List ValueSort} (declared : loop.results = sorts) (sortsFound : carried.mapM terms.sort? = some sorts)
    {body₁ : Terms} {outerIds : List Nat} (outersE : Terms.outers [] terms exportedIds = some (body₁, outerIds))
    {body₂ : Terms} {outerIds' : List Nat} (outersR : body₁.outers terms readingIds = some (body₂, outerIds'))
    {body₃ : Terms} {indexId : Nat} (indexed : body₂.intern (.leaf .index, .data .index) = (body₃, indexId))
    {body₄ : Terms} {carriedIds : List Nat} (carriedLeaves : body₃.leaves .carried sorts 0 = (body₄, carriedIds))
    {body₅ : Terms} {bodyIds bodyIds' : List Nat}
    (bodyChecked : checkScope fuel body₄ (outerIds ++ indexId :: carriedIds) loop.body
      (outerIds' ++ indexId :: carriedIds) loop'.body 0 = .ok (body₅, bodyIds, bodyIds'))
    {yieldedIds : List Nat} (yieldedE : operandIds bodyIds loop.yielded = some yieldedIds)
    (yieldedR : operandIds bodyIds' loop'.yielded = some yieldedIds)
    (yieldedSorts : yieldedIds.map body₅.sort? = sorts.map some)
    {terms' : Terms} {resultIds : List Nat} (checked : terms.leaves (.result anchor) sorts 0 = (terms', resultIds))
    {R : Type} {next next' : List (Value F G) → PIR.Process (Domain.effects (Structured.uniformCarriers F G)) R}
    (continues : ∀ (results : List (Value F G)),
      Holds terms' { valuation with results := valuation.results ++ [results] } (anchor + 1)
        (exportedIds ++ resultIds) (exportedEnv ++ results) (readingIds ++ resultIds) (readingEnv ++ results) →
        next (exportedEnv ++ results) = next' (readingEnv ++ results)) :
    step program context ⟨.loop loop.site loop.maximum loop.yielded, loop.count :: loop.initial,
        loop.results, loop.body⟩ exportedEnv next =
      step program context ⟨.loop loop'.site loop'.maximum loop'.yielded,
        loop'.count :: loop'.initial, loop'.results, loop'.body⟩ readingEnv next'  := by
  obtain ⟨argumentsE, readE, evalE⟩ := holds.exported.read_some foundE
  obtain ⟨argumentsR, readR, evalR⟩ := holds.reading.read_some foundR
  rw [evalE, Option.some.injEq] at evalR
  subst evalR
  obtain ⟨value, values, rfl, countE, initialE⟩ := read_cons_some readE
  obtain ⟨value', values', equal, countR, initialR⟩ := read_cons_some readR
  simp only [List.cons.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  have evalSplit : terms.eval valuation counted = some value ∧
      carried.mapM (terms.eval valuation) = some values := by
    simp only [List.mapM_cons] at evalE
    cases first : terms.eval valuation counted with
    | none => simp [first] at evalE
    | some actual =>
      cases rest : carried.mapM (terms.eval valuation) with
      | none => simp [first, rest] at evalE
      | some others =>
        simp only [first, rest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, List.cons.injEq] at evalE
        exact ⟨congrArg some evalE.1, congrArg some evalE.2⟩
  obtain ⟨bound, rfl⟩ := index_of_sort (sort_eval holds.sorted countSort evalSplit.1)
  have valuesSorted : SortedValues values sorts := sorted_values holds.sorted evalSplit.2 (mapM_map_some sortsFound)
  -- The iterations agree as their bodies and yields do.
  have iterations : ∀ (items : List Nat) (current : List (Value F G)),
      SortedValues current sorts →
      ((Domain.iterate (Domain.evaluate (Structured.ringModel F G) program context loop.body)
          exportedEnv loop.yielded loop.results items current).interpret Original.forgetCheckpoints).bind
          (fun final => next (exportedEnv ++ final)) =
      ((Domain.iterate (Domain.evaluate (Structured.ringModel F G) program context loop'.body)
          readingEnv loop'.yielded loop'.results items current).interpret Original.forgetCheckpoints).bind
          (fun final => next' (readingEnv ++ final)) := by
    intro items
    induction items with
    | nil =>
        intro current sortedCurrent
        have recorded := holds.record sortedCurrent
        rw [checked] at recorded
        exact continues current recorded
    | cons index items ih =>
        intro current sortedCurrent
        simp only [Domain.iterate, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
        refine scope body₄ _ loop.body _ loop'.body 0 body₅ bodyIds bodyIds' bodyChecked _ _ _ R _ _
          (holds.body outersE outersR indexed carriedLeaves (index := index) sortedCurrent) ?_
        intro valuation' anchor' finalE finalR finalHolds
        obtain ⟨yieldedValues, readFinalE, evalFinalE⟩ := finalHolds.exported.read_some yieldedE
        obtain ⟨yieldedValues', readFinalR, evalFinalR⟩ := finalHolds.reading.read_some yieldedR
        rw [evalFinalE, Option.some.injEq] at evalFinalR
        subst evalFinalR
        have yieldedSorted := sorted_values finalHolds.sorted evalFinalE yieldedSorts
        have sortedE : Domain.sortsMatch loop.results yieldedValues = true := by
          simp only [Domain.sortsMatch, declared, yieldedSorted.eq, beq_self_eq_true]
        have sortedR : Domain.sortsMatch loop'.results yieldedValues = true := by rwa [← resultsEq]
        simp only [readFinalE, readFinalR, sortedE, sortedR, ite_true]
        exact ih yieldedValues yieldedSorted
  have sortedE : Domain.sortsMatch loop.results values = true := by
    simp only [Domain.sortsMatch, declared, valuesSorted.eq, beq_self_eq_true]
  have sortedR : Domain.sortsMatch loop'.results values = true := by rwa [← resultsEq]
  by_cases bounded : bound ≤ loop.maximum
  · rw [loop_projected program context _ _ _ _ _ _ _ _ _ bound countE initialE bounded sortedE,
      loop_projected program context _ _ _ _ _ _ _ _ _ bound countR initialR (by rwa [← maximumEq]) sortedR]
    exact iterations _ values valuesSorted
  · simp only [step, Domain.step, countE, countR, initialE, initialR, ← maximumEq, bounded,
      false_and, ite_false, PIR.Process.interpret, PIR.Process.bind]

theorem anchorSound_succ (fuel : Nat) (scope : ScopeSound (F := F) (G := G) program context fuel) :
    AnchorSound (F := F) (G := G) program context (fuel + 1) := by
  intro terms exportedIds first readingIds first' anchor terms' resultIds checked
    valuation exportedEnv readingEnv R next next' holds continues
  simp only [checkAnchor] at checked
  cases loopE : Instruction.loopParts first with
  | none =>
      cases loopR : Instruction.loopParts first' with
      | some _ => simp [loopE, loopR] at checked
      | none =>
          simp only [loopE, loopR] at checked
          cases loopy : (loopOperation first.operation || loopOperation first'.operation)
          · simp only [loopy, Bool.false_eq_true, ite_false] at checked
            by_cases same : first.operation = first'.operation ∧ first.results = first'.results ∧
                plainAnchor first = true ∧ plainAnchor first' = true
            · simp only [same, and_self, ite_true] at checked
              obtain ⟨operationEq, resultsEq, plainE, plainR⟩ := same
              cases foundE : operandIds exportedIds first.operands with
              | none => simp [foundE] at checked
              | some operands =>
                  cases foundR : operandIds readingIds first'.operands with
                  | none => simp [foundE, foundR] at checked
                  | some operands' =>
                      simp only [foundE, foundR] at checked
                      by_cases equal : operands = operands'
                      · subst equal
                        simp only [ite_true, Except.ok.injEq] at checked
                        obtain ⟨argumentsE, readE, evalE⟩ := holds.exported.read_some foundE
                        obtain ⟨argumentsR, readR, evalR⟩ := holds.reading.read_some foundR
                        rw [evalE, Option.some.injEq] at evalR
                        subst evalR
                        rcases first with ⟨operation, operandsE, results, bodyE⟩
                        rcases first' with ⟨operation', operandsR, results', bodyR⟩
                        simp only at operationEq resultsEq readE readR checked loopy
                        subst operationEq resultsEq
                        have notLoop : ∀ site maximum yielded, operation ≠ .loop site maximum yielded := by
                          intro site maximum yielded equal
                          subst equal
                          simp [loopOperation] at loopy
                        have emptyE : bodyE = [] := by
                          have admitted := plainE
                          simp only [plainAnchor, Bool.and_eq_true] at admitted
                          exact List.isEmpty_iff.mp admitted.1
                        have emptyR : bodyR = [] := by
                          have admitted := plainR
                          simp only [plainAnchor, Bool.and_eq_true] at admitted
                          exact List.isEmpty_iff.mp admitted.1
                        subst bodyE bodyR
                        have notLocal : ∀ port request template coordinates,
                            operation ≠ .localService port request template coordinates := by
                          intro port request template coordinates equal
                          subst operation
                          simp [plainAnchor] at plainE
                        rw [step_local_projected program context next notLoop notLocal readE,
                          step_local_projected program context next' notLoop notLocal readR]
                        unfold step
                        apply (yields_interpret Original.forgetCheckpoints _ _
                          (DomainVM.step_schema (Structured.ringModel F G) program context
                            ⟨operation, List.range' 0 argumentsE.length, results, []⟩ argumentsE)).bind_congr
                        rintro final ⟨appended, rfl, sortedAppended⟩
                        simp only [List.drop_left]
                        have sortedValues : SortedValues appended results := SortedValues.of_eq
                          (by simpa only [Domain.sortsMatch, beq_iff_eq] using sortedAppended)
                        have recorded := holds.record sortedValues
                        change terms.leaves (.result anchor) results 0 = (terms', resultIds) at checked
                        rw [checked] at recorded
                        exact continues appended recorded
                      · simp only [equal, ite_false] at checked
                        cases checked
            · simp only [same, ite_false] at checked
              cases checked
          · simp only [loopy, ite_true] at checked
            cases checked
  | some loop =>
      cases loopR : Instruction.loopParts first' with
      | none => simp [loopE, loopR] at checked
      | some loop' =>
          simp only [loopE, loopR] at checked
          have firstEq := Instruction.loopParts_some loopE
          have firstEq' := Instruction.loopParts_some loopR
          subst firstEq firstEq'
          by_cases header : loop.site = loop'.site ∧ loop.maximum = loop'.maximum ∧
              loop.yielded.length = loop'.yielded.length ∧ loop.results = loop'.results
          · simp only [header, and_self, ite_true] at checked
            obtain ⟨-, maximumEq, -, resultEq⟩ := header
            cases foundE : operandIds exportedIds (loop.count :: loop.initial) with
            | none => simp [foundE] at checked
            | some operandsE =>
                cases operandsE with
                | nil => simp [foundE] at checked
                | cons counted carried =>
                    cases foundR : operandIds readingIds (loop'.count :: loop'.initial) with
                    | none => simp [foundE, foundR] at checked
                    | some operandsR =>
                        simp only [foundE, foundR] at checked
                        by_cases equal : counted :: carried = operandsR ∧ terms.sort? counted = some (.data .index)
                        · obtain ⟨equal, countSort⟩ := equal
                          subst equal
                          simp only [countSort, and_self, ite_true] at checked
                          cases sortsFound : carried.mapM terms.sort? with
                          | none => simp [sortsFound] at checked
                          | some sorts =>
                              by_cases declared : loop'.results = sorts
                              · simp only [sortsFound, declared, ite_true] at checked
                                cases outersE : Terms.outers [] terms exportedIds with
                                | none => simp [outersE] at checked
                                | some resultO =>
                                    obtain ⟨body₁, outerIds⟩ := resultO
                                    simp only [outersE] at checked
                                    cases outersR : body₁.outers terms readingIds with
                                    | none => simp [outersR] at checked
                                    | some resultO' =>
                                        obtain ⟨body₂, outerIds'⟩ := resultO'
                                        simp only [outersR] at checked
                                        generalize indexed : body₂.intern (.leaf .index, .data .index) = indexResult
                                          at checked
                                        obtain ⟨body₃, indexId⟩ := indexResult
                                        generalize carriedLeaves : body₃.leaves .carried sorts 0 = carriedResult
                                          at checked
                                        obtain ⟨body₄, carriedIds⟩ := carriedResult
                                        simp only at checked
                                        cases bodyChecked : checkScope fuel body₄ (outerIds ++ indexId :: carriedIds)
                                            loop.body (outerIds' ++ indexId :: carriedIds) loop'.body 0 with
                                        | error refusal => simp [bodyChecked] at checked
                                        | ok bodyResult =>
                                            obtain ⟨body₅, bodyIds, bodyIds'⟩ := bodyResult
                                            simp only [bodyChecked] at checked
                                            cases yieldedE : operandIds bodyIds loop.yielded with
                                            | none => simp [yieldedE] at checked
                                            | some yieldedIds =>
                                                cases yieldedR : operandIds bodyIds' loop'.yielded with
                                                | none => simp [yieldedE, yieldedR] at checked
                                                | some yieldedIds' =>
                                                    simp only [yieldedE, yieldedR] at checked
                                                    by_cases yieldedOk : yieldedIds = yieldedIds' ∧
                                                        yieldedIds.map body₅.sort? = sorts.map some
                                                    · obtain ⟨yieldedSame, yieldedSorts⟩ := yieldedOk
                                                      subst yieldedSame
                                                      simp [yieldedSorts] at checked
                                                      exact loop_step program context fuel scope holds
                                                        maximumEq resultEq countSort foundE foundR (resultEq.trans declared) sortsFound outersE outersR indexed
                                                        carriedLeaves bodyChecked yieldedE yieldedR yieldedSorts checked
                                                        continues
                                                    · simp only [yieldedOk, ite_false] at checked
                                                      cases checked
                              · simp only [sortsFound, declared, ite_false] at checked
                                cases checked
                        · simp only [equal, ite_false] at checked
                          cases checked
          · simp only [header, ite_false] at checked
            cases checked

/-- Accepted scopes and anchors are sound at every fuel. -/
theorem sound_at : ∀ fuel, ScopeSound (F := F) (G := G) program context fuel ∧ AnchorSound (F := F) (G := G) program context fuel
  | 0 => sound_zero program context
  | fuel + 1 =>
      ⟨scopeSound_succ program context fuel (sound_at fuel).1 (sound_at fuel).2,
        anchorSound_succ program context fuel (sound_at fuel).1⟩


omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem readback_interpret (refs : List Nat) (env : List (Value F G)) :
    (DomainVM.readback refs env).interpret Original.forgetCheckpoints = DomainVM.readback refs env := by
  unfold DomainVM.readback
  cases Domain.read env refs <;> rfl

/-- Successful finite checking implies equality of canonical observations,
including failed paths and every nonadministrative effect under every reply. -/
theorem checkNormalized_sound {inputs : List ValueSort} {exported : List Instruction}
    {exportedReturned : List Nat} {reading : List Instruction} {readingReturned : List Nat}
    {result : Terms × List Nat × List Nat}
    (accepted : checkNormalized inputs exported exportedReturned reading readingReturned = .ok result)
    (env : List (Value F G)) (schema : env.map Domain.Value.sort = inputs) :
    DomainVM.observation program context reading readingReturned env =
      DomainVM.observation program context exported exportedReturned env := by
  have sorted := SortedValues.of_eq schema
  unfold checkNormalized at accepted
  obtain ⟨⟨more, grown⟩, lengths, bounded, entries⟩ := Terms.leaves_spec .outer inputs [] 0
  have fresh := Terms.leaves_new .outer inputs [] 0
  generalize Terms.leaves [] .outer inputs 0 = initial at accepted grown lengths bounded entries fresh
  obtain ⟨terms, initialIds⟩ := initial
  simp only [List.nil_append] at accepted grown lengths bounded entries fresh
  subst grown
  cases checked : checkScope (Instruction.sizeList exported + Instruction.sizeList reading + 1) terms initialIds
      exported initialIds reading 0 with
  | error refusal => simp [checked] at accepted
  | ok final =>
      obtain ⟨terms', exportedIds, readingIds⟩ := final
      simp only [checked] at accepted
      cases returnedE : operandIds exportedIds exportedReturned with
      | none => simp [returnedE] at accepted
      | some returned =>
          cases returnedR : operandIds readingIds readingReturned with
          | none => simp [returnedE, returnedR] at accepted
          | some returned' =>
              simp only [returnedE, returnedR] at accepted
              by_cases same : returned = returned'
              · subst same
                set valuation : Valuation F G := ⟨fun position => env[position]?, none, [], []⟩
                have leafValue : ∀ (id : Nat) (entry : Node × ValueSort), terms[id]? = some entry →
                    ∃ position sort, inputs[position]? = some sort ∧ entry = (.leaf (.outer position), sort) ∧
                      terms.eval valuation id = env[position]? := by
                  intro id entry found
                  obtain ⟨position, sort, sortFound, rfl⟩ := fresh id entry (Nat.zero_le _) found
                  refine ⟨position, sort, sortFound, by simp, ?_⟩
                  rw [eval_node found (by simp [Node.operands])]
                  simp [Node.value, Leaf.value, valuation]
                have denotes : Denotes terms valuation initialIds env := by
                  refine ⟨by rw [lengths, sorted.1], fun position id found => ?_⟩
                  have inside : position < inputs.length := by
                    rw [← lengths]; exact (List.getElem?_eq_some_iff.mp found).1
                  have entry := entries position id inputs[position] found (List.getElem?_eq_getElem inside)
                  obtain ⟨position', sort, -, equal, value⟩ := leafValue id _ entry
                  simp only [Prod.mk.injEq, Node.leaf.injEq, Leaf.outer.injEq, Nat.zero_add] at equal
                  rw [value, ← equal.1]
                have holds : Holds terms valuation 0 initialIds env initialIds env := by
                  refine ⟨denotes, denotes, bounded, bounded, ?_, ?_, ?_, rfl⟩
                  · intro id node sort found operand member
                    obtain ⟨position, sort', -, equal, -⟩ := leafValue id _ found
                    simp only [Prod.mk.injEq] at equal
                    rw [equal.1] at member
                    simp [Node.operands] at member
                  · intro id node sort value found evaluated
                    obtain ⟨position, sort', sortFound, equal, valueEq⟩ := leafValue id _ found
                    simp only [Prod.mk.injEq] at equal
                    obtain ⟨-, rfl⟩ := equal
                    rw [valueEq] at evaluated
                    exact sorted.2 position value sort evaluated sortFound
                  · intro id leafAnchor position sort found
                    obtain ⟨position', sort', -, equal, -⟩ := leafValue id _ found
                    simp at equal
                symm
                unfold DomainVM.observation DomainVM.outcome
                simp only [PIR.Process.interpret_bind, readback_interpret]
                refine (sound_at program context _).1 terms initialIds exported initialIds reading 0 terms'
                  exportedIds readingIds checked valuation env env _ _ _ holds ?_
                intro valuation' anchor' exportedEnv readingEnv finalHolds
                obtain ⟨valuesE, readE, evalE⟩ := finalHolds.exported.read_some returnedE
                obtain ⟨valuesR, readR, evalR⟩ := finalHolds.reading.read_some returnedR
                rw [evalE, Option.some.injEq] at evalR
                subst evalR
                simp only [DomainVM.readback, readE, readR]
              · simp [same] at accepted


/-- The public checker verifies the selected output schema and normalization
structure. Actual participant admission is separate. The equality requires
only the reached input schema and retains any common anchor refusal. -/
theorem check_sound {inputs outputs : List ValueSort} {exported reading : List Instruction}
    {exportedReturned readingReturned : List Nat} {result : Terms × List Nat × List Nat}
    (accepted : check inputs outputs exported exportedReturned reading readingReturned = .ok result)
    (env : List (Value F G)) (schema : env.map Domain.Value.sort = inputs) :
    DomainVM.observation program context reading readingReturned env =
      DomainVM.observation program context exported exportedReturned env := by
  unfold check at accepted
  cases normalized : checkNormalized inputs exported exportedReturned reading readingReturned with
  | error refusal => simp [normalized, bind, Except.bind] at accepted
  | ok certificate => exact checkNormalized_sound program context normalized env schema

/-- A Boolean receipt can be produced by kernel reduction of the finite checker. -/
theorem accepted_sound {inputs outputs : List ValueSort} {exported reading : List Instruction}
    {exportedReturned readingReturned : List Nat}
    (accepted : (check inputs outputs exported exportedReturned reading readingReturned).toOption.isSome = true)
    (env : List (Value F G)) (schema : env.map Domain.Value.sort = inputs) :
    DomainVM.observation program context reading readingReturned env =
      DomainVM.observation program context exported exportedReturned env := by
  cases checked : check inputs outputs exported exportedReturned reading readingReturned with
  | error refusal => simp [checked, Except.toOption] at accepted
  | ok certificate => exact check_sound program context checked env schema

/-- Normalize the exact Code reading at its own static sufficient budget.
Rescheduling does not assert equality of the two instruction charge schedules. -/
theorem metered_checked {m : Type → Type} [Monad m]
    (key : Origin → Origin) (initial : Zkc.Construction.History F G) (challenge : Zkc.Construction.History F G → m F)
    (cost : String → List (Zkc.Construction.Value F G) → Nat) (budget : Nat)
    {inputs outputs : List ValueSort} {exported : List Instruction} {returned : List Nat}
    {lowered : Lowered} {total : Nat}
    (accepted : (check inputs outputs exported returned
      (Code.instructions lowered.code) lowered.returned).toOption.isSome = true)
    (static : lowered.total? = some total) (sufficient : total ≤ budget)
    (env : List (Value F G)) (schema : env.map Domain.Value.sort = inputs) (proof : Zkc.Construction.Proof F G) :
    DomainVM.metered program context key initial challenge cost budget lowered env proof =
      Uniform.DomainAdapter.run key initial challenge
        (DomainVM.observation program context exported returned env) proof := by
  rw [DomainVM.metered_static_observation program context key initial challenge cost budget static sufficient,
    accepted_sound program context accepted env schema]

theorem metered_prunes_checked {m : Type → Type} [Monad m]
    (key : Origin → Origin) (initial : Zkc.Construction.History F G) (challenge : Zkc.Construction.History F G → m F)
    (cost : String → List (Zkc.Construction.Value F G) → Nat) (budget : Nat)
    {inputs outputs : List ValueSort} {exported : List Instruction} {returned : List Nat}
    (lowered : Lowered)
    (accepted : (check inputs outputs exported returned
      (Code.instructions lowered.code) lowered.returned).toOption.isSome = true)
    (env : List (Value F G)) (schema : env.map Domain.Value.sort = inputs) (proof : Zkc.Construction.Proof F G) :
    Prunes Stopped (DomainVM.metered program context key initial challenge cost budget lowered env proof)
      (Uniform.DomainAdapter.run key initial challenge
        (DomainVM.observation program context exported returned env) proof) := by
  rw [← accepted_sound program context accepted env schema]
  exact DomainVM.metered_prunes_observation program context key initial challenge cost budget lowered env proof


end Sound
end Zkc.Executable.CanonicalNormalization

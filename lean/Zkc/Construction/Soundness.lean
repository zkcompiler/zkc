module

public import Zkc.Construction.Rule

@[expose] public section

/-! Soundness of the transcript-construction rule.

For every program the rule accepts, every challenge function in every lawful
monad, every helper table, data input, initial transcript, service handle and
proof, the ideal meaning equals the Fiat–Shamir transform of the program's
interactive reading. Outcomes, stops and the unread proof suffix are all equal;
no typing premise on the supplied values is needed because both readings
perform the same dynamic checks. Each accepted step transports agreement of
continuations backwards (`Agree`), with the simulation invariant
`Synchronized`: the transform's absorbed history is the current transcript
state, followed by the one received message awaiting observation.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source

variable {F G : Type}

section Transform
variable {m : Type → Type} [Monad m]

export Zkc.Transcript (mapOutcome)

/-- A pure final projection commutes with the transform. -/
theorem transform_bind_done [LawfulMonad m] {A B : Type} (context : Context)
    (challenge : History F G → m F) (f : A → B) (process : PIR.Proc (Actions F G) A) :
    ∀ (history : History F G) (proof : Proof F G),
      transform context challenge (process.bind fun value => .done (f value)) history proof =
        (fun result => (mapOutcome f result.1, result.2)) <$>
          transform context challenge process history proof :=
  Transcript.transform_bind_done context.interface _ f process

end Transform

section Environment
variable {env : List (Value F G)}

theorem getElem?_append_left' {values : List (Value F G)} {index : Nat}
    (bound : index < env.length) : (env ++ values)[index]? = env[index]? :=
  List.getElem?_append_left bound

theorem lt_of_getElem?_eq_some {index : Nat} {value : Value F G}
    (found : env[index]? = some value) : index < env.length := by
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

theorem transcriptAt_append {values : List (Value F G)} {index : Nat} {history : History F G}
    (found : transcriptAt env index = some history) :
    transcriptAt (env ++ values) index = some history := by
  unfold transcriptAt at found ⊢
  split at found
  · rename_i found'
    rw [getElem?_append_left' (lt_of_getElem?_eq_some found'), found']
    exact found
  · cases found

theorem dataAt_append {values : List (Value F G)} {index : Nat} {payload : Payload F G}
    (found : dataAt env index = some payload) :
    dataAt (env ++ values) index = some payload := by
  unfold dataAt at found ⊢
  split at found
  · rename_i found'
    rw [getElem?_append_left' (lt_of_getElem?_eq_some found'), found']
    exact found
  · cases found

theorem transcriptAt_last (history : History F G) (values : List (Value F G)) :
    transcriptAt (env ++ .transcript history :: values) env.length = some history := by
  simp [transcriptAt]

theorem dataAt_last (payload : Payload F G) (values : List (Value F G)) :
    dataAt (env ++ .data payload :: values) env.length = some payload := by
  simp [dataAt]

end Environment

/-- The simulation invariant: the transform's absorbed history is the current
transcript state, followed by the one received message awaiting observation. -/
def Synchronized (state : CheckState) (env : List (Value F G)) (absorbed : History F G) : Prop :=
  env.length = state.sorts.length ∧
  ∃ current, transcriptAt env state.current = some current ∧
    match state.pending with
    | .none => absorbed = current
    | .observe index origin =>
        ∃ payload, dataAt env index = some payload ∧ absorbed = current ++ [.message origin payload]
    | .deliver index _ => (∃ payload, dataAt env index = some payload) ∧ absorbed = current

/-- Appending values preserves synchronization when the sort list grows by the
same number of entries, with the transcript state and pending observation kept. -/
theorem Synchronized.append {state : CheckState} {env : List (Value F G)} {absorbed : History F G}
    (synchronized : Synchronized state env absorbed) (values : List (Value F G))
    (sorts : List ValueSort) (length : values.length = sorts.length) :
    Synchronized { state with sorts := state.sorts ++ sorts } (env ++ values) absorbed := by
  obtain ⟨envLength, current, currentAt, pending⟩ := synchronized
  refine ⟨by simp [envLength, length], current, transcriptAt_append currentAt, ?_⟩
  cases pendingEq : state.pending with
  | none => rw [pendingEq] at pending; exact pending
  | observe index origin =>
      rw [pendingEq] at pending
      obtain ⟨payload, found, absorbedEq⟩ := pending
      exact ⟨payload, dataAt_append found, absorbedEq⟩
  | deliver index origin =>
      rw [pendingEq] at pending
      obtain ⟨⟨payload, found⟩, absorbedEq⟩ := pending
      exact ⟨⟨payload, dataAt_append found⟩, absorbedEq⟩


section Rule
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]
variable (context : Context) (challenge : History F G → m F) (handle : Nat)
  (table : Structured.Evaluation.Meanings F G Structured.closedInterface)

/-- Two continuations agree on every environment and absorbed history that are
synchronized with `state`: the ideal continuation equals the transform of the
interactive one. -/
def Agree {R : Type} (state : CheckState)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R) : Prop :=
  ∀ env absorbed unread, Synchronized state env absorbed →
    nextIdeal env unread = transform context challenge (nextSpec env) absorbed unread

theorem receive_sound {R : Type} (state successor : CheckState)
    (site schema peer : String) (ty : Structured.Ty) (operands : List Nat)
    (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.receive site schema peer ty, operands, results, body⟩ =
      .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.receive site schema peer ty, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.receive site schema peer ty, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, body with
  | [], [] =>
    simp only [checkStep] at accepted
    split at accepted
    · rename_i common pendingNone typed
      split_ifs at accepted with conditions
      cases accepted
      obtain ⟨length, current, currentAt, pending⟩ := synchronized
      rw [pendingNone] at pending
      simp only [idealStep, specStep, typed]
      simp only at pending
      subst pending
      clear conditions
      cases unread with
      | nil => simp [transform_eq_receive]
      | cons payload rest =>
        simp only [transform_eq_receive]
        cases decoded : payload.value common with
        | none =>
          have different := Zkc.Construction.Payload.value_isSome (payload := payload) (ty := common)
          rw [decoded] at different
          simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not] at different
          simp [different]
        | some value =>
          have same := Zkc.Construction.Payload.value_isSome (payload := payload) (ty := common)
          rw [decoded] at same
          simp only [Option.isSome_some, Bool.true_eq, decide_eq_true_eq] at same
          simp only [same, ↓reduceIte, Zkc.Construction.Payload.value_some decoded]
          apply agree
          refine ⟨by simp [length], absorbed, transcriptAt_append currentAt, ?_⟩
          exact ⟨payload, by rw [← length]; exact dataAt_last payload [], rfl⟩
    · cases accepted
    · cases accepted
  | _ :: _, _ => simp [checkStep] at accepted
  | [], _ :: _ => simp [checkStep] at accepted

theorem indicesEmpty_sound {R : Type} (state successor : CheckState) (operands : List Nat)
    (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.indicesEmpty, operands, results, body⟩ = .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.indicesEmpty, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.indicesEmpty, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, results, body, accepted with
  | [], [.indices], [], accepted =>
    simp only [checkStep] at accepted
    cases accepted
    simp only [idealStep, specStep]
    exact agree _ _ _ (synchronized.append [.indices []] [.indices] rfl)

theorem indicesAppend_sound {R : Type} (state successor : CheckState) (operands : List Nat)
    (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.indicesAppend, operands, results, body⟩ = .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.indicesAppend, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.indicesAppend, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, results, body, accepted with
  | [coordinates, index], [.indices], [], accepted =>
    simp only [checkStep] at accepted
    split at accepted
    · split_ifs at accepted
      cases accepted
      simp only [idealStep, specStep]
      exact agree _ _ _ (synchronized.append _ [.indices] rfl)
    · cases accepted

theorem guard_sound {R : Type} (state successor : CheckState) (site : String) (operands : List Nat)
    (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.guard site, operands, results, body⟩ = .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.guard site, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.guard site, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, results, body, accepted with
  | [condition], [], [], accepted =>
    simp only [checkStep] at accepted
    split at accepted
    · cases accepted
    · split_ifs at accepted
      cases accepted
      simp only [idealStep, specStep]
      split
      · exact agree _ _ _ synchronized
      · simp [transform_eq_halt]
      · simp [transform_eq_halt]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem encodeValues_length {tys : List Structured.Ty}
    (values : Values (Structured.assignment F G) tys) : (encodeValues values).length = tys.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [encodeValues, ih]

theorem calculate_length (calculation : Calculation) {arguments results : List (Value F G)}
    (computed : Zkc.Construction.calculate calculation arguments = .returned results) :
    results.length = calculation.op.results.length := by
  unfold Zkc.Construction.calculate at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
      exact encodeValues_length _
    · cases computed

theorem calculate_sound {R : Type} (state successor : CheckState) (calculation : Calculation)
    (operands : List Nat) (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.calculate calculation, operands, results, body⟩ =
      .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.calculate calculation, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.calculate calculation, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match body, accepted with
  | [], accepted =>
    simp only [checkStep] at accepted
    split at accepted
    · cases accepted
    · split_ifs at accepted with conditions
      cases accepted
      obtain ⟨_, resultsEq⟩ := conditions
      simp only [idealStep, specStep]
      split
      · split
        · rename_i computed
          apply agree
          refine synchronized.append _ results ?_
          rw [calculate_length calculation computed, resultsEq, List.length_map]
        · simp [transform_eq_halt]
      · simp [transform_eq_halt]

theorem call_sound {R : Type} (state successor : CheckState) (name : String)
    (operands : List Nat) (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.call name, operands, results, body⟩ = .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.call name, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.call name, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match body, accepted with
  | [], accepted =>
    simp only [checkStep] at accepted
    split at accepted
    · cases accepted
    · split_ifs at accepted
      cases accepted
      simp only [idealStep, specStep]
      split
      · split
        · split
          · rename_i arity
            exact agree _ _ _ (synchronized.append _ results arity)
          · simp [transform_eq_halt]
        · simp [transform_eq_halt]
      · simp [transform_eq_halt]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A delivery send is absorbed by the transform with its payload. -/
theorem transform_sendPayload {R : Type} (site : String) (receiver : Nat) (payload : Payload F G)
    (next : PIR.Proc (Actions F G) R) (absorbed : History F G) (unread : Proof F G) :
    transform context challenge (sendPayload site receiver payload next) absorbed unread =
      transform context challenge next
        (absorbed ++ [.message (context.message site context.validator receiver) payload]) unread := by
  cases payload <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Template.messageSite_of_origin {template : Template} {site : String} {sender receiver : String}
    (found : template.origin context = some (Origin.message context.entry site sender receiver)) :
    template.messageSite? = some site := by
  unfold Template.origin at found
  split at found
  · rename_i event
    split_ifs at found with schemaEq
    simp only [Option.some.injEq, Origin.message, Zkc.Construction.Origin.mk.injEq, List.cons.injEq,
      and_true, true_and] at found
    simp [Template.messageSite?, event, found.1]
  · simp [Context.query, Origin.query, Origin.message] at found
  · cases found

theorem observe_sound {R : Type} (state successor : CheckState) (suite : String)
    (template : Template) (operands : List Nat) (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.observe suite template, operands, results, body⟩ =
      .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table ⟨.observe suite template, operands, results, body⟩
        env proof nextIdeal)
      (fun env => specStep context handle table ⟨.observe suite template, operands, results, body⟩
        env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, body, accepted with
  | [current, value, coordinates], [], accepted =>
    simp only [checkStep] at accepted
    obtain ⟨length, history, historyAt, pending⟩ := synchronized
    split at accepted
    · rename_i expected origin pendingEq
      rw [pendingEq] at pending
      obtain ⟨payload, found, absorbedEq⟩ := pending
      split_ifs at accepted with conditions
      obtain ⟨_, currentEq, valueEq, _, originEq, sent, _, _⟩ := conditions
      cases accepted
      subst currentEq valueEq absorbedEq
      simp only [idealStep, specStep, historyAt, originEq, found, Option.getD_some]
      simp only [sent, Bool.false_eq_true, ↓reduceIte]
      apply agree
      refine ⟨by simp [length], history ++ [.message origin payload], ?_, rfl⟩
      rw [← length]
      exact transcriptAt_last _ []
    · rename_i expected site pendingEq
      rw [pendingEq] at pending
      obtain ⟨⟨payload, found⟩, absorbedEq⟩ := pending
      split_ifs at accepted with conditions
      obtain ⟨_, currentEq, valueEq, _, originEq, sent, _, _⟩ := conditions
      cases accepted
      subst currentEq valueEq absorbedEq
      have siteEq := Template.messageSite_of_origin context originEq
      simp only [idealStep, specStep, historyAt, originEq, found, Option.getD_some]
      simp only [sent, ↓reduceIte, siteEq, Option.getD_some]
      rw [transform_sendPayload]
      apply agree
      refine ⟨by simp [length], _, ?_, rfl⟩
      rw [← length]
      exact transcriptAt_last _ []
    · cases accepted

theorem challenge_sound {R : Type} (state successor : CheckState) (suite field : String)
    (template : Template) (operands : List Nat) (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.challenge suite field template, operands, results, body⟩ =
      .ok successor)
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table
        ⟨.challenge suite field template, operands, results, body⟩ env proof nextIdeal)
      (fun env => specStep context handle table
        ⟨.challenge suite field template, operands, results, body⟩ env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, body, accepted with
  | [current, coordinates], [], accepted =>
    simp only [checkStep] at accepted
    obtain ⟨length, history, historyAt, pending⟩ := synchronized
    split at accepted
    · rename_i site pendingEq querySite
      rw [pendingEq] at pending
      simp only at pending
      subst pending
      split at accepted
      · rename_i delivery _
        split_ifs at accepted with conditions
        obtain ⟨_, currentEq, _, originEq, _, _, _, _⟩ := conditions
        cases accepted
        subst currentEq
        simp only [idealStep, specStep, historyAt, originEq, querySite, Option.getD_some,
          transform_eq_query]
        congr 1
        funext answer
        apply agree
        refine ⟨by simp [length], _, ?_, ⟨.field field answer, ?_⟩, rfl⟩
        · rw [← length]
          simp [transcriptAt]
        · rw [← length]
          exact dataAt_last _ _
      · cases accepted
    · cases accepted
    · cases accepted

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_length {env values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) : values.length = references.length := by
  induction references generalizing values with
  | nil => simp [read] at found; simp [← found]
  | cons reference rest ih =>
    simp only [read, List.mapM_cons, Option.bind_eq_bind] at found
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : rest.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some tail =>
        simp [first, others] at found
        subst found
        simp [ih (show read env rest = some tail from others)]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_getElem? {env values : List (Value F G)} {references : List Nat}
    (found : read env references = some values) (index : Nat) :
    values[index]? = references[index]?.bind (env[·]?) := by
  induction references generalizing values index with
  | nil => simp [read] at found; subst found; simp
  | cons reference rest ih =>
    simp only [read, List.mapM_cons, Option.bind_eq_bind] at found
    cases first : env[reference]? with
    | none => simp [first] at found
    | some value =>
      cases others : rest.mapM (env[·]?) with
      | none => simp [first, others] at found
      | some tail =>
        simp [first, others] at found
        subst found
        cases index with
        | zero => simp [first]
        | succ index => simpa using ih (show read env rest = some tail from others) index

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem read_some {env : List (Value F G)} {references : List Nat}
    (bounded : ∀ reference ∈ references, reference < env.length) :
    ∃ values, read env references = some values := by
  induction references with
  | nil => exact ⟨[], rfl⟩
  | cons reference rest ih =>
    obtain ⟨tail, found⟩ := ih (fun other member => bounded other (List.mem_cons_of_mem _ member))
    have bound := bounded reference List.mem_cons_self
    refine ⟨env[reference] :: tail, ?_⟩
    simp only [read, List.mapM_cons, Option.bind_eq_bind, List.getElem?_eq_getElem bound]
    simp only [read] at found
    simp [found]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- References with known sorts are within a synchronized environment. -/
theorem bounded_of_sorts {sorts : List ValueSort} {env : List (Value F G)}
    (length : env.length = sorts.length) {references : List Nat} {expected : List ValueSort}
    (typed : references.map (sorts[·]?) = expected.map some) :
    ∀ reference ∈ references, reference < env.length := by
  intro reference member
  have := List.mem_map_of_mem (f := (sorts[·]?)) member
  rw [typed] at this
  obtain ⟨sort, _, found⟩ := List.mem_map.mp this
  rw [length]
  by_contra outside
  rw [List.getElem?_eq_none (by omega)] at found
  cases found

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem transcriptAt_block {env carried : List (Value F G)} (index position : Nat) :
    transcriptAt (env ++ .index index :: carried) (env.length + 1 + position) =
      transcriptAt carried position := by
  unfold transcriptAt
  rw [List.getElem?_append_right (by omega)]
  simp [show env.length + 1 + position - env.length = position + 1 by omega]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem transcriptAt_suffix {env carried : List (Value F G)} (position : Nat) :
    transcriptAt (env ++ carried) (env.length + position) = transcriptAt carried position := by
  unfold transcriptAt
  rw [List.getElem?_append_right (by omega)]
  simp

theorem getElem?_of_idxOf? {list : List Nat} {value position : Nat}
    (found : list.idxOf? value = some position) : list[position]? = some value := by
  obtain ⟨bound, at_, _⟩ := List.idxOf?_eq_some_iff.mp found
  rw [List.getElem?_eq_getElem bound, at_]

/-- Soundness of loop iteration, for a body whose own soundness is supplied. -/
theorem iterate_sound (body : List Instruction) (bodyState bodyFinal : CheckState)
    (sorts results : List ValueSort) (position : Nat) (yielded : List Nat)
    (start : bodyState.sorts = sorts ++ .data .index :: results ∧
      bodyState.current = sorts.length + 1 + position ∧ bodyState.pending = .none)
    (finalPending : bodyFinal.pending = .none)
    (yieldSorts : yielded.map (bodyFinal.sorts[·]?) = results.map some)
    (yieldCurrent : yielded[position]? = some bodyFinal.current)
    (bodySound : ∀ {R : Type} (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
      (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R),
      Agree context challenge bodyFinal nextIdeal nextSpec →
      Agree context challenge bodyState
        (fun start proof => idealK context challenge table body start proof nextIdeal)
        (fun start => specK context handle table body start nextSpec))
    (env : List (Value F G)) (length : env.length = sorts.length) :
    ∀ {R : Type} (items : List Nat) (carried : List (Value F G)) (absorbed : History F G)
      (proof : Proof F G) (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
      (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R),
      carried.length = results.length → transcriptAt carried position = some absorbed →
      (∀ final absorbed' unread, final.length = results.length →
        transcriptAt final position = some absorbed' →
        nextIdeal final unread = transform context challenge (nextSpec final) absorbed' unread) →
      iterateM (fun start unread continuation => idealK context challenge table body start unread continuation)
          env yielded items carried proof nextIdeal =
        transform context challenge
          (iterate (fun start continuation => specK context handle table body start continuation)
            env yielded items carried nextSpec) absorbed proof := by
  intro R items
  induction items with
  | nil =>
    intro carried absorbed proof nextIdeal nextSpec carriedLength carriedAt finish
    exact finish carried absorbed proof carriedLength carriedAt
  | cons index rest ih =>
    intro carried absorbed proof nextIdeal nextSpec carriedLength carriedAt finish
    simp only [iterateM, iterate]
    obtain ⟨sortsEq, currentEq, pendingEq⟩ := start
    apply bodySound
    · intro final absorbed' unread synchronized
      obtain ⟨finalLength, current, currentAt, pending⟩ := synchronized
      rw [finalPending] at pending
      simp only at pending
      subst pending
      obtain ⟨next, found⟩ := read_some (bounded_of_sorts finalLength yieldSorts)
      simp only [found]
      apply ih
      · rw [read_length found]
        have := congrArg List.length yieldSorts
        simpa using this
      · unfold transcriptAt
        rw [read_getElem? found, yieldCurrent]
        exact currentAt
      · exact finish
    · refine ⟨?_, absorbed, ?_, ?_⟩
      · simp [sortsEq, length, carriedLength]
      · rw [currentEq, ← length, transcriptAt_block]
        exact carriedAt
      · simp [pendingEq]

theorem loop_sound {R : Type} (state successor : CheckState) (site : String) (maximum : Nat)
    (yielded : List Nat) (operands : List Nat) (results : List ValueSort) (body : List Instruction)
    (accepted : checkStep context state ⟨.loop site maximum yielded, operands, results, body⟩ =
      .ok successor)
    (bodySound : ∀ (start final : CheckState), checkFrom context start body = .ok final →
      ∀ {R : Type} (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
        (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R),
        Agree context challenge final nextIdeal nextSpec →
        Agree context challenge start
          (fun start proof => idealK context challenge table body start proof nextIdeal)
          (fun start => specK context handle table body start nextSpec))
    (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
    (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R)
    (agree : Agree context challenge successor nextIdeal nextSpec) :
    Agree context challenge state
      (fun env proof => idealStep context challenge table
        ⟨.loop site maximum yielded, operands, results, body⟩ env proof nextIdeal)
      (fun env => specStep context handle table
        ⟨.loop site maximum yielded, operands, results, body⟩ env nextSpec) := by
  intro env absorbed unread synchronized
  match operands, accepted with
  | count :: initial, accepted =>
    simp only [checkStep] at accepted
    obtain ⟨length, history, historyAt, pending⟩ := synchronized
    split at accepted
    · rename_i position pendingNone found
      rw [pendingNone] at pending
      simp only at pending
      subst pending
      split_ifs at accepted with conditions
      obtain ⟨_, initialSorts, _, _, _⟩ := conditions
      split at accepted
      · rename_i final bodyChecked
        split_ifs at accepted with finalConditions
        obtain ⟨finalPending, yieldSorts, yieldCurrent⟩ := finalConditions
        cases accepted
        simp only [idealStep, specStep]
        split
        · rename_i bound carried _ carriedFound
          split
          · apply iterate_sound context challenge handle table body _ final state.sorts results position
              yielded ⟨rfl, rfl, rfl⟩ finalPending yieldSorts yieldCurrent
              (bodySound _ final bodyChecked) env length
            · rw [read_length carriedFound]
              have := congrArg List.length initialSorts
              simpa using this
            · unfold transcriptAt
              rw [read_getElem? carriedFound, getElem?_of_idxOf? found]
              exact historyAt
            · intro final' absorbed' unread' finalLength finalAt
              apply agree
              refine ⟨by simp [length, finalLength], absorbed', ?_, by simp [pendingNone]⟩
              rw [← length, transcriptAt_suffix]
              exact finalAt
          · simp [transform_eq_halt]
        · simp [transform_eq_halt]
      · cases accepted
    · cases accepted
    · cases accepted

mutual
theorem checkFrom_sound : ∀ (instructions : List Instruction) (state final : CheckState),
    checkFrom context state instructions = .ok final →
    ∀ {R : Type} (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
      (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R),
      Agree context challenge final nextIdeal nextSpec →
      Agree context challenge state
        (fun env proof => idealK context challenge table instructions env proof nextIdeal)
        (fun env => specK context handle table instructions env nextSpec)
  | [], state, final, accepted => by
      intro nextIdeal nextSpec agree env absorbed unread synchronized
      simp only [checkFrom, Except.ok.injEq] at accepted
      subst accepted
      exact agree env absorbed unread synchronized
  | instruction :: rest, state, final, accepted => by
      intro nextIdeal nextSpec agree
      simp only [checkFrom] at accepted
      cases stepped : checkStep context state instruction with
      | error error => simp [stepped] at accepted; cases accepted
      | ok successor =>
        simp only [stepped] at accepted
        have restSound := checkFrom_sound rest successor final accepted nextIdeal nextSpec agree
        intro env absorbed unread synchronized
        exact checkStep_sound instruction state successor stepped _ _ restSound env absorbed unread
          synchronized

theorem checkStep_sound : ∀ (instruction : Instruction) (state successor : CheckState),
    checkStep context state instruction = .ok successor →
    ∀ {R : Type} (nextIdeal : List (Value F G) → Proof F G → m (PIR.Outcome R × Proof F G))
      (nextSpec : List (Value F G) → PIR.Proc (Actions F G) R),
      Agree context challenge successor nextIdeal nextSpec →
      Agree context challenge state
        (fun env proof => idealStep context challenge table instruction env proof nextIdeal)
        (fun env => specStep context handle table instruction env nextSpec)
  | ⟨operation, operands, results, body⟩, state, successor, accepted => by
      intro nextIdeal nextSpec agree
      cases operation with
      | receive site schema peer ty =>
        exact receive_sound context challenge handle table state successor site schema peer ty operands
          results body accepted nextIdeal nextSpec agree
      | send site schema peer => simp [checkStep] at accepted
      | indicesEmpty =>
        exact indicesEmpty_sound context challenge handle table state successor operands results body
          accepted nextIdeal nextSpec agree
      | indicesAppend =>
        exact indicesAppend_sound context challenge handle table state successor operands results body
          accepted nextIdeal nextSpec agree
      | observe suite template =>
        exact observe_sound context challenge handle table state successor suite template operands
          results body accepted nextIdeal nextSpec agree
      | challenge suite field template =>
        exact challenge_sound context challenge handle table state successor suite field template
          operands results body accepted nextIdeal nextSpec agree
      | calculate calculation =>
        exact calculate_sound context challenge handle table state successor calculation operands
          results body accepted nextIdeal nextSpec agree
      | call name =>
        exact call_sound context challenge handle table state successor name operands results body
          accepted nextIdeal nextSpec agree
      | guard site =>
        exact guard_sound context challenge handle table state successor site operands results body
          accepted nextIdeal nextSpec agree
      | loop site maximum yielded =>
        exact loop_sound context challenge handle table state successor site maximum yielded operands
          results body accepted (fun start final checked => checkFrom_sound body start final checked)
          nextIdeal nextSpec agree
      | unsupported name => simp [checkStep] at accepted
end

/-- The transcript-construction rule is sound: an accepted program's ideal
meaning is the Fiat–Shamir transform of its interactive reading, for every
challenge function in every lawful monad, every helper table, all data inputs,
initial histories, service handles and proofs. -/
theorem check_sound (participant : Participant) (accepted : check context participant = .ok ())
    (data : List (Value F G)) (initial : History F G) (proof : Proof F G)
    (arity : data.length + 1 = participant.inputs.length) :
    ideal context challenge table participant.returned participant.instructions
        (data ++ [.transcript initial]) proof =
      transform context challenge
        (spec context handle table participant.returned participant.instructions
          (data ++ [.transcript initial])) initial proof := by
  unfold check at accepted
  split at accepted
  · split_ifs at accepted with inputs
    split at accepted
    · rename_i final checked
      split_ifs at accepted with _ finalConditions
      obtain ⟨finalPending, _⟩ := finalConditions
      apply checkFrom_sound context challenge handle table participant.instructions _ final checked
      · intro env absorbed unread synchronized
        obtain ⟨_, current, _, pending⟩ := synchronized
        rw [finalPending] at pending
        simp only at pending
        subst pending
        simp only [finish]
        split <;> simp [transform_eq_done, transform_eq_halt]
      · refine ⟨by simp; omega, initial, ?_, rfl⟩
        have index : participant.inputs.length - 1 = data.length := by omega
        rw [index]
        exact transcriptAt_last initial []
    · cases accepted
  · cases accepted

end Rule

end Zkc.Construction

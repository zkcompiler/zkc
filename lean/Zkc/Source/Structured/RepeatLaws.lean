module

public import Zkc.Source.Structured.Repeat
public import Zkc.Semantics.Boundary

@[expose] public section

/-! Laws of the retained optional repeat. Residual loops below are abbreviations
for the existing finite fold, after the original count has been admitted. They
neither recheck a residual count nor change the callback's context or captures. -/

namespace Zkc.Source.Finite

/-- An index-independent finite range fold is the existing fixed-trip process,
including every interaction and early stop, for any starting index and count. -/
theorem fold_range_repeatN {I : PIR.Signature} {S : Type}
    (step : S → PIR.Proc I S) (start count : Nat) (initial : S) :
    fold (fun state (_ : Nat) => step state) (List.range' start count) initial =
      PIR.repeatN count step initial := by
  induction count generalizing start initial with
  | zero => rfl
  | succ count ih => simp only [List.range'_succ, fold, PIR.repeatN, ih]

end Zkc.Source.Finite

namespace Zkc.Source.Structured

variable {F G : Type} {I : PIR.Signature}

namespace Repeat

/-- Residual iteration on an already admitted count. The initial state supplied
by `denoteRepeat` is masked; every transition masks its input and output too. -/
abbrev loop (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (start count : Nat) (state : Values (Component (assignment F G)) spec.state) :=
  Finite.fold (step spec context self captures body) (List.range' start count) state

variable (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))

/-- The induction value is fresh; the entire optional capture suffix is unchanged. -/
theorem step_equation (state : Values (Component (assignment F G)) spec.state) (index : Nat) :
    step spec context self captures body state index =
      (body (.cons (some index)
        ((maskValues self (context.mapScopes spec.stateScopes) state).append captures))).bind
        (fun result => .done (maskValues self (context.mapScopes spec.stateScopes) result)) := rfl

@[simp] theorem loop_zero (start : Nat)
    (state : Values (Component (assignment F G)) spec.state) :
    loop spec context self captures body start 0 state = .done state := rfl

theorem loop_succ (start count : Nat)
    (state : Values (Component (assignment F G)) spec.state) :
    loop spec context self captures body start (count + 1) state =
      (step spec context self captures body state start).bind
        (loop spec context self captures body (start + 1) count) := rfl

/-- Factor the concrete masked transition through a smaller state. Returned
values are embedded using bind/done; effects, arbitrary replies and halts remain.
No injectivity or totality premise is needed. -/
theorem loop_embed {S : Type}
    (embed : S → Values (Component (assignment F G)) spec.state)
    (smallStep : S → Nat → PIR.Proc I S)
    (start count : Nat) (initial : S)
    (same : ∀ value index,
      step spec context self captures body (embed value) index =
        (smallStep value index).bind (fun result => .done (embed result))) :
    loop spec context self captures body start count (embed initial) =
      (Finite.fold smallStep (List.range' start count) initial).bind
        (fun result => .done (embed result)) := by
  induction count generalizing start initial with
  | zero => rfl
  | succ count ih =>
    simp only [loop_succ, same, List.range'_succ, Finite.fold,
      PIR.Proc.bind_assoc, PIR.Proc.bind, ih]

/-- The second segment continues at start + first, never at zero. -/
theorem loop_split (start first rest : Nat)
    (state : Values (Component (assignment F G)) spec.state) :
    loop spec context self captures body start (first + rest) state =
      (loop spec context self captures body start first state).bind
        (loop spec context self captures body (start + first) rest) := by
  unfold loop
  rw [← List.range'_append_1, Finite.fold_append]

/-- Masking a successful yield a second time has no effect. -/
theorem step_masked (state : Values (Component (assignment F G)) spec.state) (index : Nat) :
    (step spec context self captures body state index).bind
      (fun result => .done (maskValues self (context.mapScopes spec.stateScopes) result)) =
        step spec context self captures body state index := by
  simp only [step, PIR.Proc.bind_assoc, PIR.Proc.bind, maskValues_idempotent]

/-- Every returning residual state remains masked, for arbitrary effects and stops. -/
theorem loop_masked (start count : Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (masked : maskValues self (context.mapScopes spec.stateScopes) state = state) :
    (loop spec context self captures body start count state).bind
      (fun result => .done (maskValues self (context.mapScopes spec.stateScopes) result)) =
        loop spec context self captures body start count state := by
  induction count generalizing start state with
  | zero => simp only [loop_zero, PIR.Proc.bind, masked]
  | succ count ih =>
    simp only [loop_succ, step, PIR.Proc.bind_assoc, PIR.Proc.bind]
    congr 1
    funext result
    exact ih (start + 1) _ (maskValues_idempotent _ _ _)

/-- Call-free done-step equations may depend on the exact shifted induction
value. The hypothesis requires each reached step itself to equal `Proc.done`;
it does not merely assert a returned value after interpreting interactions. -/
theorem loop_state (states : Nat → Values (Component (assignment F G)) spec.state)
    (start count : Nat)
    (law : ∀ index, start ≤ index → index < start + count →
      step spec context self captures body (states index) index = .done (states (index + 1))) :
    loop spec context self captures body start count (states start) =
      .done (states (start + count)) :=
  Finite.fold_range_state _ states start count law

/-- A stopped prefix bypasses every remaining iteration and any outer suffix,
retaining its handler state and ordered effects. -/
theorem loop_run_stops {A S E : Type} (start first rest : Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (handler : PIR.Handler I S E) (initial finalState : S) (events : List E) (reason : PIR.Stop)
    (stops : (loop spec context self captures body start first state).run handler initial =
      ⟨.stopped reason, finalState, events⟩)
    (next : Values (Component (assignment F G)) spec.state → PIR.Proc I A) :
    ((loop spec context self captures body start (first + rest) state).bind next).run handler initial =
      ⟨.stopped reason, finalState, events⟩ := by
  rw [loop_split, PIR.Proc.bind_assoc, PIR.run_bind, stops]
  rfl

/-- The stopping callback can itself have performed effects. Earlier successful
iterations and the reached callback keep their events and residual provider state. -/
theorem loop_first_stop {A S E : Type} (start before after : Nat)
    (state reached : Values (Component (assignment F G)) spec.state)
    (handler : PIR.Handler I S E) (initial middle finalState : S)
    (prefixEvents stopEvents : List E) (reason : PIR.Stop)
    (earlier : (loop spec context self captures body start before state).run handler initial =
      ⟨.returned reached, middle, prefixEvents⟩)
    (stops : (body (.cons (some (start + before))
      ((maskValues self (context.mapScopes spec.stateScopes) reached).append captures))).run
        handler middle = ⟨.stopped reason, finalState, stopEvents⟩)
    (next : Values (Component (assignment F G)) spec.state → PIR.Proc I A) :
    ((loop spec context self captures body start (before + (after + 1)) state).bind next).run
      handler initial = ⟨.stopped reason, finalState, prefixEvents ++ stopEvents⟩ := by
  rw [loop_split, PIR.Proc.bind_assoc, PIR.run_bind, earlier]
  simp only [PIR.Execution.follow]
  rw [loop_succ, step, PIR.Proc.bind_assoc, PIR.Proc.bind_assoc, PIR.run_bind, stops]
  rfl

/-- Execution of a returned prefix is sequenced with its actual residual handler
state. This equation also retains a stopped prefix without executing its suffix. -/
theorem loop_run_split {S E : Type} (start first rest : Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (handler : PIR.Handler I S E) (initial : S) :
    (loop spec context self captures body start (first + rest) state).run handler initial =
      ((loop spec context self captures body start first state).run handler initial).follow
        (fun result => (loop spec context self captures body (start + first) rest result).run handler) := by
  rw [loop_split, PIR.run_bind]

/-- Equality of continuations is needed only for values that can actually be
returned, with all operation replies quantified by the existing boundary model. -/
private theorem bind_congr_returns {A B : Type} (protocol : PIR.Interaction I)
    (post : A → protocol.Phase → Prop) (process : PIR.Proc I A) (phase : protocol.Phase)
    (exits : PIR.Boundary.Returns protocol post process phase)
    (left right : A → PIR.Proc I B)
    (same : ∀ value phase, post value phase → left value = right value) :
    process.bind left = process.bind right := by
  induction process generalizing phase with
  | done value => exact same value phase exits
  | halt reason => rfl
  | call op next ih =>
    apply congrArg (PIR.Proc.call op)
    funext reply
    exact ih reply _ (exits reply)

/-- Pointwise callback equations on the reached index and state invariant lift
through arbitrary interacting or stopping bodies. The invariant depends on the
reached interaction phase, and preservation is required only from a valid state
at that phase. Successful masked yields must satisfy it at their returned phase.
Boundary.Returns quantifies every reply; no honest or synchronized reply premise
is added, and halts require no invariant. -/
theorem loop_congr_on
    (other : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (protocol : PIR.Interaction I) (phase : protocol.Phase)
    (valid : Nat → Values (Component (assignment F G)) spec.state → protocol.Phase → Prop)
    (start count : Nat) (state : Values (Component (assignment F G)) spec.state)
    (initial : valid start state phase)
    (same : ∀ index, start ≤ index → index < start + count → ∀ state phase, valid index state phase →
      body (.cons (some index) ((maskValues self (context.mapScopes spec.stateScopes) state).append captures)) =
        other (.cons (some index) ((maskValues self (context.mapScopes spec.stateScopes) state).append captures)))
    (preserved : ∀ index, start ≤ index → index < start + count → ∀ state phase, valid index state phase →
      PIR.Boundary.Returns protocol
        (fun result nextPhase => valid (index + 1)
          (maskValues self (context.mapScopes spec.stateScopes) result) nextPhase)
        (body (.cons (some index)
          ((maskValues self (context.mapScopes spec.stateScopes) state).append captures))) phase) :
    loop spec context self captures body start count state =
      loop spec context self captures other start count state := by
  induction count generalizing start state phase with
  | zero => rfl
  | succ count ih =>
    simp only [loop_succ, step, PIR.Proc.bind_assoc, PIR.Proc.bind]
    rw [← same start (Nat.le_refl _) (by omega) state phase initial]
    apply bind_congr_returns protocol _ _ phase
      (preserved start (Nat.le_refl _) (by omega) state phase initial)
    intro result nextPhase resultValid
    apply ih (phase := nextPhase) (start := start + 1) (state := _) resultValid
    · intro index lower upper value reachedPhase valueValid
      exact same index (by omega) (by omega) value reachedPhase valueValid
    · intro index lower upper value reachedPhase valueValid
      exact preserved index (by omega) (by omega) value reachedPhase valueValid

/-- The universally available invariant is that callback state is masked.
Only indices in the admitted residual range need callback equations. -/
theorem loop_congr
    (other : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (start count : Nat) (state : Values (Component (assignment F G)) spec.state)
    (same : ∀ index, start ≤ index → index < start + count → ∀ state,
      maskValues self (context.mapScopes spec.stateScopes) state = state →
      body (.cons (some index) (state.append captures)) =
        other (.cons (some index) (state.append captures))) :
    loop spec context self captures body start count state =
      loop spec context self captures other start count state := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih =>
    simp only [loop_succ, step, PIR.Proc.bind_assoc, PIR.Proc.bind]
    rw [same start (Nat.le_refl _) (by omega) _ (maskValues_idempotent _ _ _)]
    congr 1
    funext result
    apply ih
    intro index lower upper value masked
    exact same index (by omega) (by omega) value masked

/-- The captured suffix is exactly the original tuple, including absent values
and repeated actual service handles. Masking touches only state slots. -/
theorem step_captures (state : Values (Component (assignment F G)) spec.state) :
    (Values.split spec.state
      ((maskValues self (context.mapScopes spec.stateScopes) state).append captures)).2 = captures := by
  rw [Values.split_append]

end Repeat

variable (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))

theorem repeat_outside (count : Option Nat)
    (outside : (spec.roles.map context.roles).contains self = false) :
    denoteRepeat spec context self count state captures body =
      .done (Values.absent (assignment F G) spec.state) := by
  simp only [denoteRepeat, outside, Bool.false_eq_true, ↓reduceIte]

theorem repeat_missing_count (inside : (spec.roles.map context.roles).contains self = true) :
    denoteRepeat spec context self none state captures body = .halt .incomplete := by
  simp only [denoteRepeat, inside, ↓reduceIte]

theorem repeat_above_maximum (count : Nat)
    (inside : (spec.roles.map context.roles).contains self = true) (large : spec.maximum < count) :
    denoteRepeat spec context self (some count) state captures body = .halt .refused := by
  simp only [denoteRepeat, inside, Nat.not_le_of_lt large, ↓reduceIte]

/-- Logical check/range equation; the executable definition checks before it
allocates the list, including when the natural count exceeds the wire range. -/
theorem repeat_checked (count : Nat)
    (inside : (spec.roles.map context.roles).contains self = true) :
    denoteRepeat spec context self (some count) state captures body =
      Finite.execute (.check (decide (count ≤ spec.maximum)) .refused (.elements (List.range count)))
        (Repeat.step spec context self captures body)
        (maskValues self (context.mapScopes spec.stateScopes) state) := by
  simp only [denoteRepeat, inside, ↓reduceIte]
  by_cases bounded : count ≤ spec.maximum
  · simp only [bounded, ↓reduceIte, decide_true, Finite.execute, Finite.Domain.admit, Finite.admitThen]
  · simp only [bounded, ↓reduceIte, decide_false, Finite.execute, Finite.Domain.admit, Finite.admitThen,
      Bool.false_eq_true]

theorem repeat_admitted (count : Nat)
    (inside : (spec.roles.map context.roles).contains self = true) (bounded : count ≤ spec.maximum) :
    denoteRepeat spec context self (some count) state captures body =
      Repeat.loop spec context self captures body 0 count
        (maskValues self (context.mapScopes spec.stateScopes) state) := by
  simp only [denoteRepeat, inside, bounded, ↓reduceIte, Finite.execute, Finite.Domain.admit,
    Finite.admitThen, List.range_eq_range']

/-- Zero demands neither optional captures nor any callback operation. -/
theorem repeat_zero (inside : (spec.roles.map context.roles).contains self = true) :
    denoteRepeat spec context self (some 0) state captures body =
      .done (maskValues self (context.mapScopes spec.stateScopes) state) := by
  rw [repeat_admitted spec context self state captures body 0 inside (Nat.zero_le _)]
  rfl

/-- The original count is checked exactly once before the shifted residual loop. -/
theorem repeat_split (first rest : Nat)
    (inside : (spec.roles.map context.roles).contains self = true)
    (bounded : first + rest ≤ spec.maximum) :
    denoteRepeat spec context self (some (first + rest)) state captures body =
      (Repeat.loop spec context self captures body 0 first
        (maskValues self (context.mapScopes spec.stateScopes) state)).bind
          (Repeat.loop spec context self captures body first rest) := by
  rw [repeat_admitted spec context self state captures body _ inside bounded, Repeat.loop_split,
    Nat.zero_add]

/-- Every successful final result respects the state scopes, including zero and
outside participants. This equation retains all original actions and halts. -/
theorem repeat_masked (count : Option Nat) :
    (denoteRepeat spec context self count state captures body).bind
      (fun result => .done (maskValues self (context.mapScopes spec.stateScopes) result)) =
        denoteRepeat spec context self count state captures body := by
  cases active : (spec.roles.map context.roles).contains self with
  | false => simp only [repeat_outside spec context self state captures body count active,
      PIR.Proc.bind, maskValues_absent]
  | true =>
    cases count with
    | none => rw [repeat_missing_count spec context self state captures body active]; rfl
    | some count =>
      by_cases bounded : count ≤ spec.maximum
      · rw [repeat_admitted spec context self state captures body count active bounded]
        exact Repeat.loop_masked spec context self captures body 0 count _
          (maskValues_idempotent _ _ _)
      · rw [repeat_above_maximum spec context self state captures body count active (by omega)]
        rfl

/-- Callback replacement is independent of the count failures, and preserves
all optional captures. Only masked callback inputs need agree. -/
theorem repeat_congr (count : Option Nat)
    (other : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (same : ∀ index state, maskValues self (context.mapScopes spec.stateScopes) state = state →
      body (.cons (some index) (state.append captures)) =
        other (.cons (some index) (state.append captures))) :
    denoteRepeat spec context self count state captures body =
      denoteRepeat spec context self count state captures other := by
  cases active : (spec.roles.map context.roles).contains self with
  | false => rw [repeat_outside spec context self state captures body count active,
      repeat_outside spec context self state captures other count active]
  | true =>
    cases count with
    | none => rw [repeat_missing_count spec context self state captures body active,
        repeat_missing_count spec context self state captures other active]
    | some count =>
      by_cases bounded : count ≤ spec.maximum
      · rw [repeat_admitted spec context self state captures body count active bounded,
          repeat_admitted spec context self state captures other count active bounded]
        exact Repeat.loop_congr spec context self captures body other 0 count _
          (fun index _ _ state masked => same index state masked)
      · rw [repeat_above_maximum spec context self state captures body count active (by omega),
          repeat_above_maximum spec context self state captures other count active (by omega)]

/-- An invariant-restricted call-free done-step law reuses the existing finite
exact replacement theorem. The hypothesis equates each reached process step to
`Proc.done`, not just its result under a handler. Count admission remains before
the replacement and suffix. -/
theorem repeat_replace_on {A : Type} (count : Nat)
    (inside : (spec.roles.map context.roles).contains self = true)
    (total : Values (Component (assignment F G)) spec.state → Nat →
      Values (Component (assignment F G)) spec.state)
    (valid : Values (Component (assignment F G)) spec.state → Prop)
    (initial : valid (maskValues self (context.mapScopes spec.stateScopes) state))
    (law : ∀ value index, index < count → valid value →
      Repeat.step spec context self captures body value index = .done (total value index) ∧
        valid (total value index))
    (next : Values (Component (assignment F G)) spec.state → PIR.Proc I A) :
    PIR.ExactRefinement ((denoteRepeat spec context self (some count) state captures body).bind next)
      ((Finite.admitThen
        (Finite.Domain.check (decide (count ≤ spec.maximum)) .refused
          (.elements (List.range count))).admit
        (fun items => .done (items.foldl total
          (maskValues self (context.mapScopes spec.stateScopes) state)))).bind next) := by
  rw [repeat_checked spec context self state captures body count inside]
  apply Finite.execute_replace_on _ _ total valid _ initial _ _ _ next
  · intro items admitted value index member valueValid
    have itemsEq : items = List.range count := by
      by_cases bounded : count ≤ spec.maximum
      · simpa only [Finite.Domain.admit, bounded, decide_true, ↓reduceIte, PIR.Outcome.returned.injEq]
          using admitted.symm
      · simp only [Finite.Domain.admit, bounded, decide_false, Bool.false_eq_true, ↓reduceIte] at admitted
        cases admitted
    subst items
    exact law value index (List.mem_range.mp member) valueValid
  · intros
    rfl

end Zkc.Source.Structured

module

public import Zkc.Construction.ConnectionLocalRangeProgress

@[expose] public section

/-! Resource accounting for the generated depth-first query schedule. This is
an erased work relation, not an evaluator: it carries no positions, answers,
field computation, provider, or outcome. The controller simulation must relate
these transitions to the actual source expansion and generated instructions.
Repeated child occurrences stay repeated, even when their handles coincide.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryWork

/-- The finite expansion of one query. A virtual node can have no children;
that is different from a base leaf, which asks the publication provider. -/
inductive Shape where
  | base
  | virtual (children : List Shape)
  deriving Repr

mutual
  def Shape.nodes : Shape → Nat
    | .base => 1
    | .virtual children => 1 + nodes children

  def nodes : List Shape → Nat
    | [] => 0
    | child :: rest => child.nodes + nodes rest
end

mutual
  def Shape.leaves : Shape → Nat
    | .base => 1
    | .virtual children => leaves children

  def leaves : List Shape → Nat
    | [] => 0
    | child :: rest => child.leaves + leaves rest
end

theorem Shape.nodes_pos (shape : Shape) : 0 < shape.nodes := by
  cases shape <;> simp [Shape.nodes]

/-- Each saved parent retains its ordered suffix of unvisited children. Its
own answer and return transition remain outstanding after those children. -/
abbrev Frames := List (List Shape)

def frameNodes : Frames → Nat
  | [] => 0
  | children :: rest => nodes children + frameNodes rest

def frameLeaves : Frames → Nat
  | [] => 0
  | children :: rest => leaves children + frameLeaves rest

/-- Only the work position is retained. Actual pending coordinates, source
continuations, captures and arenas belong to the controller representation. -/
inductive Position where
  | enter (shape : Shape) (frames : Frames)
  | returned (frames : Frames)
  | request (frames : Frames)
  | completed
  deriving Repr

/-- The producer's four header phases. A source-work position determines its
phase, but the physical header must still be related to this position. -/
def Position.phase : Position → Nat
  | .enter .. => 0
  | .returned .. => 1
  | .request .. => 2
  | .completed => 3

theorem Position.phase_le (position : Position) : position.phase ≤ 3 := by
  cases position <;> simp [Position.phase]

theorem Position.completed_iff (position : Position) :
    3 ≤ position.phase ↔ position = .completed := by
  cases position <;> simp [Position.phase]

def Position.transitions : Position → Nat
  | .enter shape frames => 2 * shape.nodes + 2 * frameNodes frames + frames.length
  | .returned frames | .request frames => 1 + 2 * frameNodes frames + frames.length
  | .completed => 0

def Position.reads : Position → Nat
  | .enter shape frames => shape.leaves + frameLeaves frames
  | .returned frames => frameLeaves frames
  | .request frames => 1 + frameLeaves frames
  | .completed => 0

def Position.answers : Position → Nat
  | .enter shape frames => shape.nodes + frameNodes frames + frames.length
  | .returned frames => frameNodes frames + frames.length
  | .request frames => 1 + frameNodes frames + frames.length
  | .completed => 0

def Position.saves : Position → Nat
  | .enter shape frames => shape.nodes - 1 + frameNodes frames
  | .returned frames | .request frames => frameNodes frames
  | .completed => 0

/-- One successful administrative transition, with its exact answer/frame
allocation counts. Failure is not represented as a successful transition. -/
inductive Advance : Position → Position → Nat → Nat → Prop where
  | base (frames) : Advance (.enter .base frames) (.request frames) 0 0
  | empty (frames) : Advance (.enter (.virtual []) frames) (.returned frames) 1 0
  | children (first rest frames) :
      Advance (.enter (.virtual (first :: rest)) frames) (.enter first (rest :: frames)) 0 1
  | sibling (first rest frames) :
      Advance (.returned ((first :: rest) :: frames)) (.enter first (rest :: frames)) 0 1
  | parent (frames) : Advance (.returned ([] :: frames)) (.returned frames) 1 0
  | finish : Advance (.returned []) .completed 0 0

/-- One actual base reply produces one answer. Its resume does not consume an
administrative transition; the subsequent Return step does. -/
inductive Respond : Position → Position → Prop where
  | base (frames) : Respond (.request frames) (.returned frames)

theorem Advance.accounting {before after : Position} {answers saves : Nat}
    (step : Advance before after answers saves) :
    after.transitions + 1 = before.transitions ∧ after.reads = before.reads ∧
      after.answers + answers = before.answers ∧ after.saves + saves = before.saves := by
  cases step <;>
    simp only [Position.transitions, Position.reads, Position.answers, Position.saves,
      Shape.nodes, Shape.leaves, nodes, leaves, frameNodes, frameLeaves,
      List.length_cons, List.length_nil] <;>
    try (rename_i first rest frames; have positive := first.nodes_pos)
  all_goals repeat' apply And.intro
  all_goals first | trivial | omega

theorem Respond.accounting {before after : Position} (step : Respond before after) :
    after.transitions = before.transitions ∧ after.reads + 1 = before.reads ∧
      after.answers + 1 = before.answers ∧ after.saves = before.saves := by
  cases step
  simp only [Position.transitions, Position.reads, Position.answers, Position.saves]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- A finite successful prefix, including suspension/resumption boundaries.
It does not assert that the source mathematics or provider returns. -/
inductive Prefix : Position → Position → Nat → Nat → Nat → Nat → Prop where
  | nil (position) : Prefix position position 0 0 0 0
  | advance {start current next : Position}
      {steps replies answers saves addedAnswers addedSaves : Nat}
      (before : Prefix start current steps replies answers saves)
      (step : Advance current next addedAnswers addedSaves) :
      Prefix start next (steps + 1) replies (answers + addedAnswers) (saves + addedSaves)
  | respond {start current next : Position} {steps replies answers saves : Nat}
      (before : Prefix start current steps replies answers saves)
      (step : Respond current next) :
      Prefix start next steps (replies + 1) (answers + 1) saves

theorem Prefix.accounting {start current : Position} {steps replies answers saves : Nat}
    (execution : Prefix start current steps replies answers saves) :
    current.transitions + steps = start.transitions ∧ current.reads + replies = start.reads ∧
      current.answers + answers = start.answers ∧ current.saves + saves = start.saves := by
  induction execution with
  | nil => simp
  | advance before step ih => have accounted := step.accounting; omega
  | respond before step ih => have accounted := step.accounting; omega

/-- All four budgets follow from the same expansion, including partial work.
Per-kind arenas and per-continuation stores can only use a subset of these
allocations; their routing and membership are proved by the representation. -/
theorem Prefix.bounds {shape : Shape} {current : Position} {steps replies answers saves : Nat}
    (execution : Prefix (.enter shape []) current steps replies answers saves) :
    steps ≤ 2 * shape.nodes ∧ replies ≤ shape.leaves ∧
      answers ≤ shape.nodes ∧ saves < shape.nodes := by
  have accounted := execution.accounting
  have positive := shape.nodes_pos
  simp only [Position.transitions, Position.reads, Position.answers, Position.saves,
    frameNodes, frameLeaves, List.length_nil, Nat.add_zero] at accounted
  omega

theorem Prefix.completed {shape : Shape} {steps replies answers saves : Nat}
    (execution : Prefix (.enter shape []) .completed steps replies answers saves) :
    steps = 2 * shape.nodes ∧ replies = shape.leaves ∧
      answers = shape.nodes ∧ saves = shape.nodes - 1 := by
  have accounted := execution.accounting
  simpa [Position.transitions, Position.reads, Position.answers, Position.saves,
    frameNodes, frameLeaves] using accounted

/-- The actual advance callback can use this relation as its progress fact.
The common rank is derived here; no protocol companion invents a machine rank.
The callback connection must still establish an actual administrative step. -/
theorem advance_progress {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧
        ∃ answers saves, Advance (position value) (position result.2) answers saves)
      (step value index)) :
    Zkc.Construction.ConnectionLocalRange.StepProgress step invariant
      (fun value ↦ (position value).transitions) := by
  intro value index held
  apply (connected value index held).mono
  rintro result ⟨retained, answers, saves, transition⟩
  refine ⟨retained, ?_⟩
  intro _
  change (position result.2).transitions < (position value).transitions
  have consumed := transition.accounting
  omega

/-- A complete local query cycle may traverse several administrative steps.
Every continuing cycle consumes a base reply; the final completed cycle need
not consume one. This accounts for the extra completion iteration. -/
theorem response_progress {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧ ∃ steps replies answers saves,
        Prefix (position value) (position result.2) steps replies answers saves ∧
        (result.1 = true → 0 < replies)) (step value index)) :
    Zkc.Construction.ConnectionLocalRange.StepProgress step invariant
      (fun value ↦ (position value).reads) := by
  intro value index held
  apply (connected value index held).mono
  rintro result ⟨retained, steps, replies, answers, saves, execution, consumed⟩
  refine ⟨retained, ?_⟩
  intro active
  change (position result.2).reads < (position value).reads
  have positive := consumed active
  have accounted := execution.accounting
  omega

/-- Any suspension point uses no more work than the original root. The
producer's `2 * nodes + 1` and `leaves + 1` bounds can therefore be reused
when entering either finite range, rather than re-proved by each protocol. -/
theorem Prefix.range_bounds {shape : Shape} {current : Position}
    {steps replies answers saves nodeCapacity leafCapacity : Nat}
    (execution : Prefix (.enter shape []) current steps replies answers saves)
    (nodeBound : shape.nodes ≤ nodeCapacity) (leafBound : shape.leaves ≤ leafCapacity) :
    current.transitions < 2 * nodeCapacity + 1 ∧ current.reads < leafCapacity + 1 := by
  have transitions := execution.accounting.1
  have reads := execution.accounting.2.1
  change current.transitions + steps = 2 * shape.nodes + 2 * 0 + 0 at transitions
  change current.reads + replies = shape.leaves + 0 at reads
  omega

/-- A successful next answer allocation has room below the source node bound.
The same result covers a virtual answer and a resumed base answer. It does
not use the length of a separately chosen arena as an assumption. -/
theorem Prefix.answer_room {shape : Shape} {current next : Position}
    {steps replies answers saves addedSaves : Nat}
    (execution : Prefix (.enter shape []) current steps replies answers saves)
    (allocates : Advance current next 1 addedSaves ∨ Respond current next) :
    answers < shape.nodes := by
  have accounted := execution.accounting.2.2.1
  change current.answers + answers = shape.nodes + 0 + 0 at accounted
  rcases allocates with advanced | responded
  · have allocated := advanced.accounting; omega
  · have allocated := responded.accounting; omega

/-- Every saved child continuation consumes one of the root's tree edges,
including separate edges for duplicate child occurrences. -/
theorem Prefix.frame_room {shape : Shape} {current next : Position}
    {steps replies answers saves addedAnswers : Nat}
    (execution : Prefix (.enter shape []) current steps replies answers saves)
    (allocates : Advance current next addedAnswers 1) : saves < shape.nodes - 1 := by
  have accounted := execution.accounting.2.2.2
  have allocated := allocates.accounting
  change current.saves + saves = shape.nodes - 1 + 0 at accounted
  omega

/-- Advancing exits only at a request or completed root. The yielded Boolean
must be the actual phase comparison; a premature false flag cannot establish
this result, even if the work decreases. -/
theorem advance_completed {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧
        (∃ answers saves, Advance (position value) (position result.2) answers saves) ∧
        result.1 = decide ((position result.2).phase < 2)) (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (enough : (position value).transitions < indices.length) :
    PIR.Yields (fun result ↦ invariant result ∧ 2 ≤ (position result).phase)
      ((Zkc.Source.Finite.fold (Zkc.Construction.ConnectionLocalRange.gated step)
        indices (true, value)).bind fun result ↦ .done result.2) := by
  apply Zkc.Construction.ConnectionLocalRange.fold_completed
    (advance_progress step invariant position (fun value index held ↦
      (connected value index held).mono fun _ result ↦ ⟨result.1, result.2.1⟩))
    (indices := indices) (value := value) (held := held) (enough := enough)
  intro value index held
  apply (connected value index held).mono
  rintro result ⟨retained, _, phase⟩
  refine ⟨retained, ?_⟩
  intro inactive
  have notAdvancing : ¬ (position result.2).phase < 2 := by
    simpa only [decide_eq_false_iff_not] using phase.symm.trans inactive
  omega

/-- The outer request loop exits at Completed, using the same root expansion
to bound its replies. A completed zero-reply cycle is allowed. A continuing
cycle must consume a reply, and the flag must come from the actual phase. -/
theorem evaluation_completed {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧
        (∃ steps replies answers saves,
          Prefix (position value) (position result.2) steps replies answers saves ∧
          (result.1 = true → 0 < replies)) ∧
        result.1 = decide ((position result.2).phase < 3)) (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (enough : (position value).reads < indices.length) :
    PIR.Yields (fun result ↦ invariant result ∧ position result = .completed)
      ((Zkc.Source.Finite.fold (Zkc.Construction.ConnectionLocalRange.gated step)
        indices (true, value)).bind fun result ↦ .done result.2) := by
  apply Zkc.Construction.ConnectionLocalRange.fold_completed
    (response_progress step invariant position (fun value index held ↦
      (connected value index held).mono fun _ result ↦ ⟨result.1, result.2.1⟩))
    (indices := indices) (value := value) (held := held) (enough := enough)
  intro value index held
  apply (connected value index held).mono
  rintro result ⟨retained, _, phase⟩
  refine ⟨retained, ?_⟩
  intro inactive
  have notActive : ¬ (position result.2).phase < 3 := by
    simpa only [decide_eq_false_iff_not] using phase.symm.trans inactive
  exact (Position.completed_iff _).mp (by omega)

/-- The actual advance range only invokes dispatch in Enter or Return.
Request and Completed remain valid outputs, without an impossible obligation
to give either one another administrative transition. -/
theorem advance_active_completed {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → (position value).phase < 2 → PIR.Yields
      (fun result ↦ invariant result.2 ∧
        (∃ answers saves, Advance (position value) (position result.2) answers saves) ∧
        result.1 = decide ((position result.2).phase < 2)) (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (starts : (position value).phase < 2)
    (enough : (position value).transitions < indices.length) :
    PIR.Yields (fun result ↦ invariant result ∧ 2 ≤ (position result).phase)
      ((Zkc.Source.Finite.fold (Zkc.Construction.ConnectionLocalRange.gated step)
        indices (true, value)).bind fun result ↦ .done result.2) := by
  apply Zkc.Construction.ConnectionLocalRange.fold_active_completed
    (active := fun value ↦ (position value).phase < 2)
    (remaining := fun value ↦ (position value).transitions) ?_
    indices value held starts enough
  intro value index held active
  apply (connected value index held active).mono
  rintro result ⟨retained, ⟨answers, saves, transition⟩, flag⟩
  refine ⟨retained, ?_, ?_⟩
  · intro continuing
    have nextActive : (position result.2).phase < 2 := by
      simpa only [decide_eq_true_eq] using flag.symm.trans continuing
    have accounted := transition.accounting
    exact ⟨nextActive, by omega⟩
  · intro inactive
    have stopped : ¬ (position result.2).phase < 2 := by
      simpa only [decide_eq_false_iff_not] using flag.symm.trans inactive
    omega

/-- The outer query range likewise invokes its cycle only before Completed.
Its capacity and exit proof use the same work relation as the inner range. -/
theorem evaluation_active_completed {carriers : Zkc.Source.Structured.Carriers} {A : Type}
    (step : A → Nat → PIR.Process (Zkc.Construction.Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (position : A → Position)
    (connected : ∀ value index, invariant value → (position value).phase < 3 → PIR.Yields
      (fun result ↦ invariant result.2 ∧
        (∃ steps replies answers saves,
          Prefix (position value) (position result.2) steps replies answers saves ∧
          (result.1 = true → 0 < replies)) ∧
        result.1 = decide ((position result.2).phase < 3)) (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (starts : (position value).phase < 3)
    (enough : (position value).reads < indices.length) :
    PIR.Yields (fun result ↦ invariant result ∧ position result = .completed)
      ((Zkc.Source.Finite.fold (Zkc.Construction.ConnectionLocalRange.gated step)
        indices (true, value)).bind fun result ↦ .done result.2) := by
  apply Zkc.Construction.ConnectionLocalRange.fold_active_completed
    (active := fun value ↦ (position value).phase < 3)
    (remaining := fun value ↦ (position value).reads) ?_
    indices value held starts enough
  intro value index held active
  apply (connected value index held active).mono
  rintro result ⟨retained, ⟨steps, replies, answers, saves, execution, consumed⟩, flag⟩
  refine ⟨retained, ?_, ?_⟩
  · intro continuing
    have nextActive : (position result.2).phase < 3 := by
      simpa only [decide_eq_true_eq] using flag.symm.trans continuing
    have used := consumed continuing
    have accounted := execution.accounting
    exact ⟨nextActive, by omega⟩
  · intro inactive
    apply (Position.completed_iff _).mp
    have stopped : ¬ (position result.2).phase < 3 := by
      simpa only [decide_eq_false_iff_not] using flag.symm.trans inactive
    omega

end Zkc.Realization.QueryWork

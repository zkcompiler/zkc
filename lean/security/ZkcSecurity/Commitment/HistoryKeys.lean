module

public import ZkcSecurity.Oracle.Keys
public import ZkcSecurity.Commitment.Experiment

@[expose] public section

/-! # Commitment keys as histories

The joint oracle of the commitment bridge keys a transcript query by the pair of the absorbed
history before it, committed roots included, and its occurrence (`TranscriptKey`), and keeps a
separate summand for hash calls (`JointKey`). A transcript provider keys the transcript by
histories. The history form of the joint oracle (`HistoryKey`, `HistoryRange`) keys a transcript
cell by the absorbed history ending with the occurrence. A history that ends with an absorbed
event is answered in that event's raw type; the empty history and a history ending with a root
are answered in `Unit`, since no transcript query reaches them. Hash calls keep their own summand
and are answered alike in both forms.

Two renamings relate the forms (`ZkcSecurity.Oracle.Renaming`):

- `jointToHistory` sends a pair `(preceding, occurrence)` to the history
  `preceding ++ [.event occurrence]` and every hash call to itself;
- `historyToJoint` sends a history ending with an absorbed event to the pair of its prefix and that
  event, and every hash call to itself; it answers the empty history and every history ending with
  a root locally (`historyCell_nil`, `historyCell_root`), whatever the adversary asks there.

Through either renaming the lazily sampled executions have the same law
(`Renaming.evalDistEq_translate`; for the bridge's joint games `prEvent_jointToHistory`), queries
transport unchanged (`Renaming.translate_queryBound`), and charges transport through the weights:
the history charge of a joint charge (`historyCharge`) weighs a pair as the joint charge does
(`jointToHistory_weight`, `jointToHistory_costBound`), and the joint charge weighs a history as
the history charge does (`historyToJoint_weight`, `historyToJoint_costBound`).

**Logs and checkpoints.** Against a history table, the translated game of a pair-keyed game asks
the images of the game's keys against the table read back, in order
(`Renaming.tableQueryLog_translate`), and the hash calls before the first query of a transcript
key's history image are the hash calls before the key's first query in the pair-keyed run
(`checkpoint_jointToHistory`). So the checkpoint extraction of every transcript key is the same in
both forms.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment
open OracleComp OracleSpec ZkcSecurity.Oracle

variable {E Shape Y Query α : Type} (Raw : E → Type)

/-- Keys of the joint oracle in history form: absorbed histories and hash calls. -/
abbrev HistoryKey (E Shape Y Query : Type) := List (Absorbed E Shape Y) ⊕ Query

/-- The event an absorbed entry carries, if it is not a root. -/
def Absorbed.eventOf : Absorbed E Shape Y → Option E
  | .event occurrence => some occurrence
  | .root _ _ => none

/-- The event of an absorbed history's last entry: none for the empty history and for a history
ending with a root. -/
def lastEvent (history : List (Absorbed E Shape Y)) : Option E :=
  history.getLast?.bind Absorbed.eventOf

theorem lastEvent_append_event (history : List (Absorbed E Shape Y)) (event : E) :
    lastEvent (history ++ [.event event]) = some event := by
  simp [lastEvent, Absorbed.eventOf]

theorem eq_of_lastEvent {history : List (Absorbed E Shape Y)} {event : E}
    (last : lastEvent history = some event) : history = history.dropLast ++ [.event event] := by
  obtain ⟨entry, found, carries⟩ := Option.bind_eq_some_iff.mp last
  have entryIs : entry = .event event := by
    cases entry with
    | event other =>
        simp only [Absorbed.eventOf, Option.some.injEq] at carries
        rw [carries]
    | root _ _ => cases carries
  rw [entryIs] at found
  exact (Oracle.dropLast_append_of_getLast? found).symm

/-- The answer type after an event, `Unit` without one. -/
def EventRange : Option E → Type
  | some event => Raw event
  | none => Unit

/-- Answers of the joint oracle in history form: a history in the raw type of its last absorbed
event, `Unit` for the empty history and after a root; a hash call in `Y`. -/
def HistoryRange (Shape Y Query : Type) : HistoryKey E Shape Y Query → Type
  | .inl history => EventRange Raw (lastEvent history)
  | .inr _ => Y

instance EventRange.sampleable [∀ event, SampleableType (Raw event)] :
    ∀ last : Option E, SampleableType (EventRange Raw last)
  | some event => inferInstanceAs (SampleableType (Raw event))
  | none => inferInstanceAs (SampleableType Unit)

instance historySampleable [∀ event, SampleableType (Raw event)] [SampleableType Y] :
    ∀ key, SampleableType (HistoryRange Raw Shape Y Query key)
  | .inl history => EventRange.sampleable Raw (lastEvent history)
  | .inr _ => inferInstanceAs (SampleableType Y)

variable {Raw}

/-- The history image of a joint key. -/
def pairCell : JointKey E Shape Y Query → HistoryKey E Shape Y Query
  | .inl key => .inl (key.1 ++ [.event key.2])
  | .inr query => .inr query

theorem pairCell_injective : Function.Injective (pairCell (E := E) (Shape := Shape) (Y := Y)
    (Query := Query)) := by
  intro first second same
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          simp only [pairCell, Sum.inl.injEq] at same
          obtain ⟨prefixes, lasts⟩ := List.append_inj' same rfl
          simp only [List.singleton_inj, Absorbed.event.injEq] at lasts
          exact congrArg Sum.inl (Prod.ext prefixes lasts)
      | inr _ => cases same
  | inr first =>
      cases second with
      | inl _ => cases same
      | inr second =>
          simp only [pairCell, Sum.inr.injEq] at same
          rw [same]

variable (Raw)

/-- Pair keys rename into histories: `(preceding, occurrence)` is the history
`preceding ++ [.event occurrence]`, and a hash call is itself. -/
def jointToHistory : Renaming (JointRange Raw Shape Y Query) (HistoryRange Raw Shape Y Query) where
  cell key := some (pairCell key)
  injective first second target found other :=
    pairCell_injective ((Option.some.inj found).trans (Option.some.inj other).symm)
  read key target found := by
    obtain rfl := Option.some.inj found
    cases key with
    | inl key =>
        exact Equiv.cast (by simp only [pairCell, HistoryRange, lastEvent_append_event, EventRange,
          JointRange])
    | inr query => exact Equiv.refl Y
  single _ found := by cases found

variable {Raw}

/-- The joint key of a history: a history ending with an absorbed event is the pair of its prefix
and that event; the empty history and histories ending with a root have none. -/
def historyCell : HistoryKey E Shape Y Query → Option (JointKey E Shape Y Query)
  | .inl history => (lastEvent history).map fun event => .inl (history.dropLast, event)
  | .inr query => some (.inr query)

theorem historyCell_inl_some {history : List (Absorbed E Shape Y)} {key : JointKey E Shape Y Query}
    (found : historyCell (.inl history) = some key) :
    ∃ event, lastEvent history = some event ∧ key = .inl (history.dropLast, event) := by
  obtain ⟨event, last, same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨event, last, same.symm⟩

variable (Raw)

/-- Histories rename into pairs: a history ending with an absorbed event is the pair of its
prefix and that event; the empty history and histories ending with a root, whose answer type is
`Unit`, are answered locally; a hash call is itself. -/
def historyToJoint : Renaming (HistoryRange Raw Shape Y Query) (JointRange Raw Shape Y Query) where
  cell := historyCell
  injective first second target found other := by
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            obtain ⟨event, last, rfl⟩ := historyCell_inl_some found
            obtain ⟨event', last', same⟩ := historyCell_inl_some other
            simp only [Sum.inl.injEq, Prod.mk.injEq] at same
            obtain ⟨prefixes, rfl⟩ := same
            rw [eq_of_lastEvent last, eq_of_lastEvent last', prefixes]
        | inr _ =>
            obtain ⟨event, _, rfl⟩ := historyCell_inl_some found
            simp [historyCell] at other
    | inr first =>
        cases second with
        | inl second =>
            obtain ⟨event, _, rfl⟩ := historyCell_inl_some other
            simp [historyCell] at found
        | inr second =>
            simp only [historyCell, Option.some.injEq] at found other
            rw [← found] at other
            exact congrArg Sum.inr (Sum.inr.inj other).symm
  read key target found := by
    cases key with
    | inl history =>
        cases last : lastEvent history with
        | none =>
            simp only [historyCell, last, Option.map_none] at found
            cases found
        | some event =>
            simp only [historyCell, last, Option.map_some, Option.some.injEq] at found
            subst found
            exact Equiv.cast (by simp only [HistoryRange, last, EventRange, JointRange])
    | inr query =>
        obtain rfl := (Option.some.inj found).symm
        exact Equiv.refl Y
  single key found := by
    cases key with
    | inl history =>
        have none : lastEvent history = none := Option.map_eq_none_iff.mp found
        exact Equiv.cast (by simp only [HistoryRange, none, EventRange])
    | inr query => cases found

variable {Raw}

/-- The charge of a history key from a joint charge: a history ending with an absorbed event is
charged at its prefix and that event, any other history nothing, and a hash call `hashError`. -/
def historyCharge (charge : List (Absorbed E Shape Y) → E → ENNReal) (hashError : ENNReal) :
    HistoryKey E Shape Y Query → ENNReal
  | .inl history => (lastEvent history).elim 0 (charge history.dropLast)
  | .inr _ => hashError

/-- A pair key weighs, through its history image, what the joint charge charges it. -/
theorem jointToHistory_weight (charge : List (Absorbed E Shape Y) → E → ENNReal)
    (hashError : ENNReal) :
    (jointToHistory (Shape := Shape) (Y := Y) (Query := Query) Raw).weight
        (historyCharge charge hashError) = jointCharge charge hashError := by
  funext key
  cases key with
  | inl key =>
      simp [Renaming.weight, jointToHistory, pairCell, historyCharge, jointCharge,
        lastEvent_append_event]
  | inr query => rfl

/-- A history key weighs, through its joint key, what the history charge charges it. -/
theorem historyToJoint_weight (charge : List (Absorbed E Shape Y) → E → ENNReal)
    (hashError : ENNReal) :
    (historyToJoint (Shape := Shape) (Y := Y) (Query := Query) Raw).weight
        (jointCharge charge hashError) = historyCharge charge hashError := by
  funext key
  cases key with
  | inl history =>
      simp only [Renaming.weight, historyToJoint, historyCell, historyCharge]
      cases lastEvent history <;> rfl
  | inr query => rfl

/-- The empty history is answered locally. -/
theorem historyCell_nil : historyCell (E := E) (Shape := Shape) (Y := Y) (Query := Query) (.inl []) =
    none := rfl

/-- A history ending with a root is answered locally. -/
theorem historyCell_root (history : List (Absorbed E Shape Y)) (shape : Shape) (root : Y) :
    historyCell (Query := Query) (.inl (history ++ [.root shape root])) = none := by
  simp [historyCell, lastEvent, Absorbed.eventOf]

section Transport
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ event, SampleableType (Raw event)] [SampleableType Y]

/-- Sampling transport: every event of a pair-keyed game has the probability of the same event of
its translation to history keys. -/
theorem prEvent_jointToHistory (game : OracleComp (joint Raw Shape Y Query) α) (event : α → Prop) :
    Pr{let result ← (simulateQ randomOracle ((jointToHistory Raw).translate game)).run' ∅}[
      event result] =
      Pr{let result ← (simulateQ randomOracle game).run' ∅}[event result] :=
  (jointToHistory Raw).prEvent_translate game event

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query] in
/-- Budget transport: a pair-keyed game's joint charge bounds its translation's history charge. -/
theorem jointToHistory_costBound (charge : List (Absorbed E Shape Y) → E → ENNReal)
    (hashError : ENNReal) (game : OracleComp (joint Raw Shape Y Query) α) (cost : ENNReal)
    (bounded : WorstCaseCostBound game ⟨jointCharge charge hashError⟩ cost) :
    WorstCaseCostBound ((jointToHistory Raw).translate game) ⟨historyCharge charge hashError⟩
      cost :=
  (jointToHistory Raw).translate_costBound _ game cost (by rwa [jointToHistory_weight])

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query] in
/-- Budget transport: a history-keyed game's history charge bounds its translation's joint
charge. -/
theorem historyToJoint_costBound (charge : List (Absorbed E Shape Y) → E → ENNReal)
    (hashError : ENNReal)
    (game : OracleComp (OracleSpec.ofFn (HistoryRange Raw Shape Y Query)) α) (cost : ENNReal)
    (bounded : WorstCaseCostBound game ⟨historyCharge charge hashError⟩ cost) :
    WorstCaseCostBound ((historyToJoint Raw).translate game) ⟨jointCharge charge hashError⟩ cost :=
  (historyToJoint Raw).translate_costBound _ game cost (by rwa [historyToJoint_weight])

end Transport

/-- The hash calls of a history-keyed key list, with their answers in a table. -/
def historyHashLog (table : (key : HistoryKey E Shape Y Query) → HistoryRange Raw Shape Y Query key)
    (keys : List (HistoryKey E Shape Y Query)) : HashLog Query Y :=
  keys.filterMap fun key =>
    match key with
    | .inr query => some (⟨query, table (.inr query)⟩ : (_ : Query) × Y)
    | .inl _ => none

theorem takeWhile_map_pairCell [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
    [DecidableEq Query] (key : JointKey E Shape Y Query) :
    ∀ keys : List (JointKey E Shape Y Query),
      (keys.map pairCell).takeWhile (fun other => decide (other ≠ pairCell key)) =
        (keys.takeWhile fun other => decide (other ≠ key)).map pairCell
  | [] => rfl
  | head :: tail => by
      by_cases same : head = key
      · subst same
        simp
      · have different : pairCell head ≠ pairCell key := fun equal => same (pairCell_injective equal)
        have keepImage : decide (pairCell head ≠ pairCell key) = true := by simpa using different
        have keep : decide (head ≠ key) = true := by simpa using same
        simp only [List.map_cons, List.takeWhile_cons, keepImage, keep, ↓reduceIte,
          takeWhile_map_pairCell key tail]

theorem historyHashLog_map_pairCell
    (table : (key : HistoryKey E Shape Y Query) → HistoryRange Raw Shape Y Query key) :
    ∀ keys : List (JointKey E Shape Y Query),
      historyHashLog table (keys.map pairCell) = hashLog ((jointToHistory Raw).pullback table) keys
  | [] => rfl
  | .inl _ :: tail => by
      simp only [List.map_cons, historyHashLog, hashLog, pairCell, List.filterMap_cons]
      exact historyHashLog_map_pairCell table tail
  | .inr query :: tail => by
      simp only [List.map_cons, historyHashLog, hashLog, pairCell, List.filterMap_cons]
      rw [Renaming.pullback_some _ table
        (show (jointToHistory Raw).cell (.inr query) = some (.inr query) from rfl)]
      exact congrArg _ (historyHashLog_map_pairCell table tail)

/-- The log/checkpoint correspondence: against a history table, the hash calls the translated game
asks before the first query of a transcript key's history image are those the pair-keyed game asks
before the key's first query, against the table read back. -/
theorem checkpoint_jointToHistory [DecidableEq E] [DecidableEq Shape] [DecidableEq Y]
    [DecidableEq Query] (game : OracleComp (joint Raw Shape Y Query) α)
    (table : (key : HistoryKey E Shape Y Query) → HistoryRange Raw Shape Y Query key)
    (key : TranscriptKey E Shape Y) :
    historyHashLog table
        (((tableQueryLog ((jointToHistory Raw).translate game) table).map Sigma.fst).takeWhile
          fun other => decide (other ≠ pairCell (.inl key))) =
      hashLog ((jointToHistory Raw).pullback table) (beforeFirstKey (.inl key)
        ((tableQueryLog game ((jointToHistory Raw).pullback table)).map Sigma.fst)) := by
  rw [Renaming.tableQueryLog_translate]
  have total : ∀ keys : List (JointKey E Shape Y Query),
      keys.filterMap (jointToHistory (Shape := Shape) (Y := Y) (Query := Query) Raw).cell =
        keys.map pairCell := by
    intro keys
    simp [jointToHistory]
  rw [total, takeWhile_map_pairCell, historyHashLog_map_pairCell]
  rfl

end ZkcSecurity.Commitment

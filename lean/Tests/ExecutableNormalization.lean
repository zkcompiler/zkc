import ZkcExamples.Executable.SchnorrProof
import ZkcExamples.Executable.SumcheckProof
import Mathlib.Algebra.Field.ZMod

/-! Controls for checked normalization of pure total calculations.

Small programs exercise `checkNormalized` directly. Accepted are a calculation
deferred past the transcript operations before its first consumer (the schedule
the compiler's calculation batching produces), independent calculations
reordered, a repeated term shared, a dead term dropped and a value moved across
a loop. Refused, each with its named reason, are a calculation that can stop,
a helper call, a guard or a transcript operation moved across another anchor, a
pure value scheduled after the observation that absorbs it with that operand
retargeted, changed arithmetic, a deleted or duplicated guard, work moved into a
loop body and an ill-sorted calculation. The actual Schnorr and Sumcheck
programs take the exact-equality fast path.

Two counterexamples show that the refused moves are unsound, not merely
unrecognized: moving a calculation that stops, or a rejecting guard, after a
challenge makes the program query the challenge function where the export never
does. -/

namespace Tests.ExecutableNormalization
open Zkc.Construction Zkc.Executable Zkc.Source

/-! ## Programs -/

abbrev fr : String := "fr"
abbrev suite : String := "suite"
abbrev field : ValueSort := .data (.field fr)
abbrev boolean : ValueSort := .data .boolean
abbrev transcript : ValueSort := .transcript suite

/-- A challenge drawn from the transcript. -/
def drawTemplate : Template := ⟨"entry", [], ["query", "entry", "challenge", "service", "draw", "draw", "value"]⟩

/-- A message absorbed into the transcript at `site`. -/
def messageTemplate (site : String) : Template := ⟨"entry", [], ["message", "entry", site, site, "prover", "verifier"]⟩

def calculation (operation : Calculation) (operands : List Nat) (sort : ValueSort) : Instruction :=
  ⟨.calculate operation, operands, [sort], []⟩

def multiply (left right : Nat) : Instruction := calculation (.fieldMultiply fr) [left, right] field
def add (left right : Nat) : Instruction := calculation (.fieldAdd fr) [left, right] field
def subtract (left right : Nat) : Instruction := calculation (.fieldSubtract fr) [left, right] field
def equal (left right : Nat) : Instruction := calculation (.fieldEqual fr) [left, right] boolean
def constant (value : Nat) : Instruction := calculation (.fieldConstant fr value) [] field
def element (vector index : Nat) : Instruction := calculation (.boundedAt fr) [vector, index] field
def coordinates : Instruction := ⟨.indicesEmpty, [], [.indices], []⟩
def observe (state value occurrence : Nat) (site : String) : Instruction :=
  ⟨.observe suite (messageTemplate site), [state, value, occurrence], [transcript], []⟩
def draw (state occurrence : Nat) : Instruction :=
  ⟨.challenge suite fr drawTemplate, [state, occurrence], [field, transcript], []⟩
def guard (condition : Nat) : Instruction := ⟨.guard "check", [condition], [], []⟩
def helper (argument : Nat) : Instruction := ⟨.call "helper", [argument], [field], []⟩

/-- A loop over `count` with one carried field value. -/
def loop (count initial : Nat) (yielded : List Nat) (body : List Instruction) : Instruction :=
  ⟨.loop "rounds" 2 yielded, [count, initial], [field], body⟩

/-- The check's verdict: `none` when it accepts. -/
def verdict (inputs : List ValueSort) (exported : List Instruction) (exportedReturned : List Nat)
    (reading : List Instruction) (readingReturned : List Nat) : Option Refusal :=
  match checkNormalized inputs exported exportedReturned reading readingReturned with
  | .ok _ => none
  | .error refusal => some refusal

theorem accepted_of_verdict {inputs : List ValueSort} {exported : List Instruction} {exportedReturned : List Nat}
    {reading : List Instruction} {readingReturned : List Nat}
    (accepted : verdict inputs exported exportedReturned reading readingReturned = none) :
    ∃ result, checkNormalized inputs exported exportedReturned reading readingReturned = .ok result := by
  unfold verdict at accepted
  split at accepted
  · exact ⟨_, ‹_›⟩
  · cases accepted

/-! ## Accepted schedules -/

/-- Two rounds: each draws a challenge, and the claim `a₀·r₀ + a₁·r₁` is
compared with a point. The export computes `a₀·r₀` where the source does,
after the first draw. -/
def rounds : List Instruction :=
  [coordinates, draw 0 4, multiply 1 5, coordinates, draw 6 8, multiply 2 9, add 7 11, equal 12 3]

/-- The schedule calculation batching produces: every calculation after the
last draw, the second product first, one shared coordinate value. -/
def roundsBatched : List Instruction :=
  [coordinates, draw 0 4, draw 6 4, multiply 2 7, multiply 1 5, add 10 9, equal 11 3]

abbrev roundsInputs : List ValueSort := [transcript, field, field, field]

theorem rounds_accepted : verdict roundsInputs rounds [13, 10] roundsBatched [12, 8] = none := by
  decide +kernel

/-- The batched schedule has the export's ideal meaning, in every monad and for
every challenge function. -/
theorem rounds_same {m : Type → Type} [Monad m] {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G]
    [Module F G] [DecidableEq G] (context : Context) (challenge : History F G → m F)
    (helpers : Structured.Evaluation.Meanings F G Structured.closedInterface) (env : List (Value F G))
    (sorted : SortedValues env roundsInputs) (proof : Proof F G) :
    ideal context challenge helpers [12, 8] roundsBatched env proof =
      ideal context challenge helpers [13, 10] rounds env proof := by
  obtain ⟨result, accepted⟩ := accepted_of_verdict rounds_accepted
  have calls : Instruction.callList rounds = [] := by decide +kernel
  exact checkNormalized_sound context challenge helpers accepted (by simp [calls]) env sorted proof

/-- A repeated product is shared. -/
theorem shared_accepted :
    verdict [transcript, field, field] [multiply 1 2, multiply 1 2, add 3 4] [5]
      [multiply 1 2, add 3 3] [4] = none := by
  decide +kernel

/-- A product no anchor and no returned value uses is dropped. -/
theorem dead_accepted :
    verdict [transcript, field, field] [multiply 1 1, add 1 2] [4] [add 1 2] [3] = none := by
  decide +kernel

/-- A value computed before a loop and used only after it is computed after
the loop; the loop bodies number their positions differently. -/
theorem acrossLoop_accepted :
    verdict [transcript, field, .data .index]
      [multiply 1 1, loop 2 1 [6] [add 5 5], add 3 4] [5]
      [loop 2 1 [5] [add 4 4], multiply 1 1, add 4 3] [5] = none := by
  decide +kernel

/-! ## Refused moves and changes -/

/-- A calculation that can stop is an anchor: moving `boundedAt` across a draw
changes the anchor sequence. -/
theorem stoppingMoved_refused :
    verdict [transcript, .data (.vector fr), .data .index]
      [coordinates, element 1 2, draw 0 3] [4, 6]
      [coordinates, draw 0 3, element 1 2] [6, 5] = some (.anchor 0) := by
  decide +kernel

/-- A helper call moved across an observation. -/
theorem helperMoved_refused :
    verdict [transcript, field]
      [coordinates, helper 1, observe 0 1 2 "message"] [3, 4]
      [coordinates, observe 0 1 2 "message", helper 1] [4, 3] = some (.anchor 0) := by
  decide +kernel

/-- A guard moved across an observation. -/
theorem guardMoved_refused :
    verdict [transcript, field, boolean]
      [coordinates, guard 2, observe 0 1 3 "message"] [4]
      [coordinates, observe 0 1 3 "message", guard 2] [4] = some (.anchor 0) := by
  decide +kernel

/-- Two observations swapped. -/
theorem observationsSwapped_refused :
    verdict [transcript, field, field]
      [coordinates, observe 0 1 3 "first", observe 4 2 3 "second"] [5]
      [coordinates, observe 0 2 3 "second", observe 4 1 3 "first"] [5] = some (.anchor 0) := by
  decide +kernel

/-- An observation moved past a draw. -/
theorem observationMoved_refused :
    verdict [transcript, field]
      [coordinates, observe 0 1 2 "message", draw 3 2] [5]
      [coordinates, draw 0 2, observe 4 1 2 "message"] [5] = some (.anchor 0) := by
  decide +kernel

/-- A product scheduled after the observation that absorbs it, with the
observation retargeted to another field value. -/
theorem absorbedLater_refused :
    verdict [transcript, field, field]
      [coordinates, multiply 1 2, observe 0 4 3 "message"] [5]
      [coordinates, observe 0 1 3 "message", multiply 1 2] [4] = some (.anchorOperand 0 1) := by
  decide +kernel

/-- A difference with its operands swapped. -/
theorem subtractionSwapped_refused :
    verdict [transcript, field, field]
      [coordinates, subtract 1 2, observe 0 4 3 "message"] [5]
      [coordinates, subtract 2 1, observe 0 4 3 "message"] [5] = some (.anchorOperand 0 1) := by
  decide +kernel

/-- A changed constant. -/
theorem constantChanged_refused :
    verdict [transcript, field]
      [coordinates, constant 1, add 1 3, observe 0 4 2 "message"] [5]
      [coordinates, constant 2, add 1 3, observe 0 4 2 "message"] [5] = some (.anchorOperand 0 1) := by
  decide +kernel

/-- An addition replaced by a multiplication. -/
theorem operationChanged_refused :
    verdict [transcript, field, field]
      [coordinates, add 1 2, observe 0 4 3 "message"] [5]
      [coordinates, multiply 1 2, observe 0 4 3 "message"] [5] = some (.anchorOperand 0 1) := by
  decide +kernel

/-- A deleted guard. -/
theorem guardDeleted_refused :
    verdict [transcript, field, boolean]
      [coordinates, observe 0 1 3 "message", guard 2] [4]
      [coordinates, observe 0 1 3 "message"] [4] = some (.anchor 1) := by
  decide +kernel

/-- A duplicated guard. -/
theorem guardDuplicated_refused :
    verdict [transcript, field, boolean]
      [coordinates, observe 0 1 3 "message", guard 2] [4]
      [coordinates, observe 0 1 3 "message", guard 2, guard 2] [4] = some (.anchor 2) := by
  decide +kernel

/-- A product computed before the loop in the export is computed inside the
loop body: the body's yield denotes another term in its own table. -/
theorem intoLoop_refused :
    verdict [transcript, field, .data .index]
      [multiply 1 1, loop 2 1 [6] [add 5 3]] [4]
      [loop 2 1 [6] [multiply 1 1, add 4 5]] [3] = some (.yielded 0) := by
  decide +kernel

/-- A product of a transcript and a field value. -/
theorem illSorted_refused :
    verdict [transcript, field] [multiply 0 1] [2] [multiply 0 1] [2] = some (.sort 0) := by
  decide +kernel

/-! ## The actual programs take the fast path -/

set_option maxRecDepth 20000 in
theorem schnorr_exact :
    Code.instructionList ZkcExamples.Executable.SchnorrProof.lowered.code =
        ZkcExamples.Construction.SchnorrProof.participant.instructions ∧
      ZkcExamples.Executable.SchnorrProof.lowered.returned =
        ZkcExamples.Construction.SchnorrProof.participant.returned := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem sumcheck_exact :
    Code.instructionList ZkcExamples.Executable.SumcheckProof.lowered.code =
        ZkcExamples.Construction.SumcheckProof.participant.instructions ∧
      ZkcExamples.Executable.SumcheckProof.lowered.returned =
        ZkcExamples.Construction.SumcheckProof.participant.returned := by
  decide +kernel

/-! ## Refused moves change the interaction -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

def context : Context := ⟨"entry", ["prover", "verifier"], 0, 1, 2, "contract", suite, []⟩

/-- A challenge function that counts its queries. -/
def counting (_ : History F G) : StateM Nat F := do
  modify (· + 1)
  pure 0

/-- The number of challenge queries of a run. -/
def queries (run : StateM Nat (PIR.Outcome (List (Value F G)) × Proof F G)) : Nat := (run.run 0).2

/-- A transcript, an empty vector and the index `0`. -/
def outOfRange : List (Value F G) := [.transcript [], .vector fr [], .index 0]

/-- An out-of-range element access stops before the draw in the export; moved
after the draw, it stops only after the challenge function was queried. Both
stop with the same reason, so only the interaction tells them apart. -/
theorem moved_stop_changes_interaction :
    queries (ideal context counting [] [4, 6] [coordinates, element 1 2, draw 0 3] outOfRange []) = 0 ∧
      queries (ideal context counting [] [6, 5] [coordinates, draw 0 3, element 1 2] outOfRange []) = 1 ∧
      (ideal context counting [] [4, 6] [coordinates, element 1 2, draw 0 3] outOfRange [] |>.run 0).1 =
        (ideal context counting [] [6, 5] [coordinates, draw 0 3, element 1 2] outOfRange [] |>.run 0).1 := by
  decide +kernel

/-- A transcript and a false condition. -/
def rejecting : List (Value F G) := [.transcript [], .data (.boolean false)]

/-- A rejecting guard stops the export before it draws; moved after the draw,
the program queries the challenge function first. Both stop with the same
reason. -/
theorem moved_guard_changes_interaction :
    queries (ideal context counting [] [3] [coordinates, guard 1, draw 0 2] rejecting []) = 0 ∧
      queries (ideal context counting [] [3] [coordinates, draw 0 2, guard 1] rejecting []) = 1 ∧
      (ideal context counting [] [3] [coordinates, guard 1, draw 0 2] rejecting [] |>.run 0).1 =
        (ideal context counting [] [3] [coordinates, draw 0 2, guard 1] rejecting [] |>.run 0).1 := by
  decide +kernel

end Tests.ExecutableNormalization

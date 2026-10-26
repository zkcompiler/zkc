import Zkc.Executable.DomainNormalizationSoundness

/-! Kernel-reduced finite positive/refusal controls for canonical normalization.
The semantic controls below apply the reusable theorem, including loops. -/

namespace Tests.CanonicalNormalization
open Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Executable.CanonicalNormalization

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

def verdict (inputs : List ValueSort) (exported : List Instruction) (exportedReturned : List Nat)
    (reading : List Instruction) (readingReturned : List Nat) : Option Refusal :=
  match Zkc.Executable.CanonicalNormalization.checkNormalized inputs exported exportedReturned reading readingReturned with
  | .ok _ => none
  | .error refusal => some refusal

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


def badEmpty : Instruction := ⟨.indicesEmpty, [], [], []⟩
def badAppend : Instruction := ⟨.indicesAppend, [0, 0], [.indices], []⟩
def receive : Instruction := ⟨.receive "message" "message" "prover" .boolean, [], [boolean], []⟩
def badReceive : Instruction := { receive with body := [coordinates] }

theorem badEmpty_refused : verdict [] [badEmpty] [] [] [] = some (.sort 0) := by decide +kernel

theorem badAppend_refused : verdict [boolean] [badAppend] [0] [] [0] = some (.sort 0) := by decide +kernel

theorem badReceive_refused : verdict [] [badReceive] [0] [receive] [0] = some (.anchor 0) := by decide +kernel

theorem badCalculationDeclaration_refused :
    verdict [] [⟨.calculate (.booleanConstant true), [], [], []⟩] [] [] [] = some (.sort 0) := by decide +kernel

theorem outputSchema_refused :
    (check [field] [boolean] [] [0] [] [0]).toOption.isSome = false := by decide +kernel

theorem outputSchema_accepted :
    (check [field] [field] [] [0] [] [0]).toOption.isSome = true := by decide +kernel

def service : Instruction :=
  ⟨.localService ⟨"local", "verifier", 0, 0, "random.fr/0"⟩ (.draw fr) drawTemplate [0], [], [field], []⟩

theorem embeddedReferences_refused :
    verdict [.data .index] [service] [] [service] [] = some (.anchor 0) := by decide +kernel

/-- Total work crosses unchanged receives, actual helper calls and guards.
All of those anchors retain their original order, metadata and operands. -/
theorem anchors_accepted :
    verdict [field, boolean]
      [multiply 0 0, receive, helper 0, guard 1, add 2 4] [5, 3]
      [receive, helper 0, guard 1, multiply 0 0, add 4 3] [5, 2] = none := by
  decide +kernel

/-- Nested loop bodies keep separate outer/index/carried scopes. -/
theorem nestedLoops_accepted :
    verdict [transcript, field, .data .index]
      [loop 2 1 [7]
        [multiply 4 4, loop 2 4 [8] [add 7 7], add 5 6]] [3]
      [loop 2 1 [7]
        [loop 2 4 [7] [add 6 6], multiply 4 4, add 6 5]] [3] = none := by
  decide +kernel

/-- A changed carried/result schema cannot be hidden by an unused loop result. -/
theorem badLoopResults_refused :
    verdict [.data .index, field]
      [⟨.loop "rounds" 2 [3], [0, 1], [], []⟩] []
      [⟨.loop "rounds" 2 [3], [0, 1], [], []⟩] [] = some (.sort 0) := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable (program : Structured.Program) (context : Context)

/-- The same two-level loop test as the finite control, for every count, field
value, transcript and possible body effect reply, including oversize refusal. -/
theorem acrossLoop_sound (env : List (Zkc.Executable.CanonicalNormalization.Value F G))
    (schema : env.map Domain.Value.sort = [transcript, field, .data .index]) :
    DomainVM.observation program context
      [loop 2 1 [5] [add 4 4], multiply 1 1, add 4 3] [5] env =
    DomainVM.observation program context
      [multiply 1 1, loop 2 1 [6] [add 5 5], add 3 4] [5] env := by
  apply accepted_sound program context (inputs := [transcript, field, .data .index])
    (outputs := [field]) (env := env) (schema := schema)
  decide +kernel

/-- Sharing and dead total work are justified by canonical execution. -/
theorem sharing_sound (env : List (Zkc.Executable.CanonicalNormalization.Value F G))
    (schema : env.map Domain.Value.sort = [transcript, field, field]) :
    DomainVM.observation program context [multiply 1 2, add 3 3] [4] env =
    DomainVM.observation program context [multiply 1 2, multiply 1 2, add 3 4] [5] env := by
  apply accepted_sound program context (inputs := [transcript, field, field])
    (outputs := [field]) (env := env) (schema := schema)
  decide +kernel

theorem dead_sound (env : List (Zkc.Executable.CanonicalNormalization.Value F G))
    (schema : env.map Domain.Value.sort = [transcript, field, field]) :
    DomainVM.observation program context [add 1 2] [3] env =
    DomainVM.observation program context [multiply 1 1, add 1 2] [4] env := by
  apply accepted_sound program context (inputs := [transcript, field, field])
    (outputs := [field]) (env := env) (schema := schema)
  decide +kernel

/-- Actual helper admission and all replies are handled by Domain itself.
The normalization premise does not assume helper success or a helper table. -/
theorem anchors_sound (env : List (Zkc.Executable.CanonicalNormalization.Value F G))
    (schema : env.map Domain.Value.sort = [field, boolean]) :
    DomainVM.observation program context
      [receive, helper 0, guard 1, multiply 0 0, add 4 3] [5, 2] env =
    DomainVM.observation program context
      [multiply 0 0, receive, helper 0, guard 1, add 2 4] [5, 3] env := by
  apply accepted_sound program context (inputs := [field, boolean])
    (outputs := [field, boolean]) (env := env) (schema := schema)
  decide +kernel

theorem nestedLoops_sound (env : List (Zkc.Executable.CanonicalNormalization.Value F G))
    (schema : env.map Domain.Value.sort = [transcript, field, .data .index]) :
    DomainVM.observation program context
      [loop 2 1 [7] [loop 2 4 [7] [add 6 6], multiply 4 4, add 6 5]] [3] env =
    DomainVM.observation program context
      [loop 2 1 [7] [multiply 4 4, loop 2 4 [8] [add 7 7], add 5 6]] [3] env := by
  apply accepted_sound program context (inputs := [transcript, field, .data .index])
    (outputs := [field]) (env := env) (schema := schema)
  decide +kernel

end Tests.CanonicalNormalization

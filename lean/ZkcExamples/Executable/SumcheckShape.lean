module

public import Zkc.Executable.Code

@[expose] public section

/-! The shape of a compiled Sumcheck proof validator.

Every compiled Sumcheck validator of this family has the same constructed
instructions up to its names (`Names`): Pending construction and opening, a
loop over the round count bounded by the Entry's static maximum, and the
pending-claim wrapper and terminal check as helper calls. A round receives its two message coordinates
and absorbs each, checks the round sum, draws the challenge and delivers it,
extends the point by a helper call and updates the claim (`roundBody`). The
executable reads a round with the charges of the transparent calls that compute
it (`roundCode`). `Names.of` reads the names off a constructed validator, so an
artifact of this shape is recognized by evaluating
`instructions (Names.of instructions) maximum = instructions` in the kernel.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckShape
open Zkc.Construction Zkc.Executable

/-- What distinguishes one compiled Sumcheck validator from another: the scalar
field, the transcript suite, the helpers it calls by name, its sites and the
occurrence templates of its transcript operations. -/
structure Names where
  scalar : String
  suite : String
  pendingHelper : String
  openClaimHelper : String
  atPrefixHelper : String
  appendHelper : String
  checkHelper : String
  loopSite : String
  firstReceive : String × String × String
  secondReceive : String × String × String
  guardSite : String
  firstMessage : Template
  secondMessage : Template
  draw : Template
  delivery : Template
  deriving DecidableEq, Repr

/-- The constructed instructions of one round. Positions count from the eight
values before the loop (the data inputs, transcript, and both Pending pairs), then the round index and the carried point, claim and transcript. -/
def roundBody (n : Names) : List Instruction := [
  ⟨.receive n.firstReceive.1 n.firstReceive.2.1 n.firstReceive.2.2 (.field n.scalar), [], [.data (.field n.scalar)], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [13, 8], [.indices], []⟩,
  ⟨.observe n.suite n.firstMessage, [11, 12, 14], [.transcript n.suite], []⟩,
  ⟨.receive n.secondReceive.1 n.secondReceive.2.1 n.secondReceive.2.2 (.field n.scalar), [], [.data (.field n.scalar)],
    []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [17, 8], [.indices], []⟩,
  ⟨.observe n.suite n.secondMessage, [15, 16, 18], [.transcript n.suite], []⟩,
  ⟨.calculate (.fieldAdd n.scalar), [12, 16], [.data (.field n.scalar)], []⟩,
  ⟨.calculate (.fieldEqual n.scalar), [10, 20], [.data .boolean], []⟩,
  ⟨.guard n.guardSite, [21], [], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [22, 8], [.indices], []⟩,
  ⟨.challenge n.suite n.scalar n.draw, [19, 23], [.data (.field n.scalar), .transcript n.suite], []⟩,
  ⟨.indicesEmpty, [], [.indices], []⟩,
  ⟨.indicesAppend, [26, 8], [.indices], []⟩,
  ⟨.observe n.suite n.delivery, [25, 24, 27], [.transcript n.suite], []⟩,
  ⟨.call n.appendHelper, [9, 24], [.data (.vector n.scalar)], []⟩,
  ⟨.calculate (.fieldConstant n.scalar 1), [], [.data (.field n.scalar)], []⟩,
  ⟨.calculate (.fieldSubtract n.scalar), [30, 24], [.data (.field n.scalar)], []⟩,
  ⟨.calculate (.fieldMultiply n.scalar), [31, 12], [.data (.field n.scalar)], []⟩,
  ⟨.calculate (.fieldMultiply n.scalar), [24, 16], [.data (.field n.scalar)], []⟩,
  ⟨.calculate (.fieldAdd n.scalar), [32, 33], [.data (.field n.scalar)], []⟩]

/-- Where a round leaves the next point, claim and transcript. -/
abbrev yielded : List Nat := [29, 34, 28]

/-- The sorts the round loop carries. -/
def carriedSorts (n : Names) : List ValueSort := [.data (.vector n.scalar), .data (.field n.scalar), .transcript n.suite]

/-- Construct Pending from the published scalar, then consume its components. -/
def pendingCall (n : Names) : Instruction :=
  ⟨.call n.pendingHelper, [1], [.data (.vector n.scalar), .data (.field n.scalar)], []⟩

def openClaimCall (n : Names) : Instruction :=
  ⟨.call n.openClaimHelper, [4, 5], [.data (.vector n.scalar), .data (.field n.scalar)], []⟩

/-- Consume the loop's complete pending claim before checking it. -/
def atPrefixCall (n : Names) : Instruction :=
  ⟨.call n.atPrefixHelper, [8, 9], [.data (.vector n.scalar), .data (.field n.scalar)], []⟩

def checkCall (n : Names) : Instruction := ⟨.call n.checkHelper, [0, 11, 12], [.data .boolean], []⟩

/-- The current five-step constructed validator, including both consuming wrappers. -/
def instructions (n : Names) (maximum : Nat) : List Instruction :=
  [pendingCall n, openClaimCall n,
    ⟨.loop n.loopSite maximum yielded, [2, 6, 7, 3], carriedSorts n, roundBody n⟩,
    atPrefixCall n, checkCall n]

/-- The executable's reading of a round: each constructed instruction with what
it charges itself, and the entries and returns of the transparent calls that
compute them. -/
def roundCode (n : Names) : List Code :=
  let i := fun index => (roundBody n).getD index ⟨.unsupported "", [], [], []⟩
  [.step (i 0) 1, .charge 1, .step (i 1) 1, .step (i 2) 1, .step (i 3) 1, .charge 1,
    .step (i 4) 1, .charge 1, .step (i 5) 1, .step (i 6) 1, .step (i 7) 1, .charge 1,
    .charge 1, .step (i 8) 1, .step (i 9) 1, .step (i 10) 2, .charge 1,
    .charge 1, .step (i 11) 1, .step (i 12) 1, .step (i 13) 1, .charge 1,
    .charge 1, .step (i 14) 1, .step (i 15) 1, .step (i 16) 1, .charge 1,
    .helper (i 17),
    .charge 1, .step (i 18) 1, .step (i 19) 1, .step (i 20) 1, .step (i 21) 1, .step (i 22) 1, .charge 1]

/-- The executable's reading of a validator. -/
def code (n : Names) (maximum : Nat) : List Code :=
  [.helper (pendingCall n), .helper (openClaimCall n),
    .loop n.loopSite maximum yielded [2, 6, 7, 3] (carriedSorts n) (roundCode n),
    .helper (atPrefixCall n), .helper (checkCall n)]

theorem roundCode_instructions (n : Names) : Code.instructions (roundCode n) = roundBody n := by
  rw [← Code.instructionList_eq]
  rfl

/-- The operation of an instruction at a position, if any. -/
def operationAt (instructions : List Instruction) (index : Nat) : Operation :=
  (instructions.getD index ⟨.unsupported "", [], [], []⟩).operation

/-- The round body of a loop at position two. -/
def loopBody (instructions : List Instruction) : List Instruction :=
  (instructions.getD 2 ⟨.unsupported "", [], [], []⟩).body

/-- The loop's static maximum. -/
def maximumOf (instructions : List Instruction) : Nat :=
  match operationAt instructions 2 with
  | .loop _ maximum _ => maximum
  | _ => 0

/-- The names of a validator of this shape, read off its instructions. -/
def Names.of (instructions : List Instruction) : Names :=
  let body := loopBody instructions
  let receiveAt := fun index => match operationAt body index with
    | .receive site schema peer _ => (site, schema, peer)
    | _ => ("", "", "")
  let templateAt := fun index => match operationAt body index with
    | .observe _ template => template
    | .challenge _ _ template => template
    | _ => ⟨"", [], []⟩
  { scalar := match operationAt body 0 with | .receive _ _ _ (.field domain) => domain | _ => ""
    suite := match operationAt body 3 with | .observe suite _ => suite | _ => ""
    pendingHelper := match operationAt instructions 0 with | .call name => name | _ => ""
    openClaimHelper := match operationAt instructions 1 with | .call name => name | _ => ""
    atPrefixHelper := match operationAt instructions 3 with | .call name => name | _ => ""
    appendHelper := match operationAt body 17 with | .call name => name | _ => ""
    checkHelper := match operationAt instructions 4 with | .call name => name | _ => ""
    loopSite := match operationAt instructions 2 with | .loop site _ _ => site | _ => ""
    firstReceive := receiveAt 0
    secondReceive := receiveAt 4
    guardSite := match operationAt body 10 with | .guard site => site | _ => ""
    firstMessage := templateAt 3
    secondMessage := templateAt 7
    draw := templateAt 13
    delivery := templateAt 16 }

end ZkcExamples.Executable.SumcheckShape

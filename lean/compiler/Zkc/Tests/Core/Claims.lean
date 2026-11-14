import Zkc.Core.Admission

/-! What a producer states beside a raw package, checked by admission.

- The keys of the sites: one per site, no key twice.
- The sites of a protocol in the order of its body.
- Whether each function can stop: a function with a guard can; one that calls it can; one
  that only computes cannot.
- The data of a literal of a nominal type: a number below the order of a field.
- The rows: stated to be the vocabulary's, a row under a name of the vocabulary with other
  inputs, or at static arguments for which the vocabulary has no row, is refused; not stated,
  it is not looked at. A row under a name that the vocabulary does not have is a row of an
  extension (`Vocabulary.extensions`): it is not refused, and a package with one is not a
  package of the vocabulary alone.
- The maximum of a loop of a protocol: at least the largest count that its participants can
  have. The maxima are written from the facts in the order of the body, also past an
  application that is not justified and for a participant whose code never runs.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ClaimsTests

def base : Raw.Package :=
  { types := [], records := [], variants := [], operations := [], functions := [], protocols := [],
    names := none }

/-- The refusals of admission, each by its kind. -/
def kinds (package : Raw.Package) (claims : Admission.Claims := {}) : List String :=
  match admit package claims with
  | .ok _ => []
  | .error refusals => refusals.map fun
    | .elaboration _ => "elaboration"
    | .facts .. => "facts"
    | .copies .. => "copies"
    | .sites _ => "sites"
    | .keys _ => "keys"
    | .stops number => s!"stops {number}"
    | .row _ => "row"
    | .literal .. => "literal"

/-- Role 0 sends two numbers to role 1. -/
def twoSends (first second : Nat) : Raw.Package :=
  { base with protocols := [⟨false, 2, [⟨.nat, 0⟩], [], [],
      .step (.exchange 0 1 first 0) <| .step (.exchange 0 1 second 0) (.ret [])⟩] }

def key (event : Nat) : SiteKey := ⟨event, "message", []⟩

#guard kinds (twoSends 0 1) { keys := some [[key 0, key 1]] } == []
#guard kinds (twoSends 0 1) { keys := some [[key 0, key 0]] } == ["keys"]
#guard kinds (twoSends 0 1) { keys := some [[key 0]] } == ["keys"]
#guard kinds (twoSends 1 0) == ["sites"]

/-- `guarded` has a guard, `calls` calls it, `plain` adds. -/
def functions : Raw.Package :=
  { base with functions := [
      ⟨false, [.bool], [], some (.step (.guard .reject 0) (.ret []))⟩,
      ⟨false, [.bool], [], some (.step (.call 0 [0]) (.ret []))⟩,
      ⟨false, [.nat], [.nat], some (.step (.builtin .natAdd [0, 0]) (.ret [1]))⟩] }

#guard kinds functions { stops := some [true, true, false] } == []
#guard kinds functions { stops := some [true, false, false] } == ["stops 1"]
#guard kinds functions { stops := some [true, true, true] } == ["stops 2"]

/-- A loop of roles 0 and 1 over a count that both hold under an agreement, guarded to be at
most `bound` by each, with the stated maximum. -/
def looping (bound maximum : Nat) : Raw.Package :=
  { base with protocols := [⟨false, 2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [], [⟨false, [0, 1]⟩],
      .step (.at 0 (.literal (.nat bound))) <|            -- 2
      .step (.at 0 (.builtin .natLess [0, 2])) <|          -- 3
      .step (.at 0 (.guard .reject 3)) <|
      .step (.at 1 (.literal (.nat bound))) <|            -- 4
      .step (.at 1 (.builtin .natLess [1, 4])) <|          -- 5
      .step (.at 1 (.guard .reject 5)) <|
      .step (.repeat [0, 1] (.runtime maximum [0, 1]) [] [] [] (.ret [])) (.ret [])⟩] }

-- `count < 5` leaves at most 4
#guard kinds (looping 5 4) == []
#guard kinds (looping 5 3) == ["facts"]
#guard (fillMaxima (looping 5 0)).protocols.map (fun protocol =>
    (admit { base with protocols := [protocol] }).isOk) == [true]

/-- The requirements that admission finds unmet, in the order of the refusals. -/
def unmet (package : Raw.Package) : List Requirement :=
  match admit package with
  | .ok _ => []
  | .error refusals => refusals.filterMap fun
    | .facts _ unjustified => some unjustified.requirement
    | _ => none

/-- The maxima of the loops over a value of a region, in the order of the body. -/
partial def maxima : Raw.ProtocolRegion → List Nat
  | .ret _ | .stop _ => []
  | .block _ body next => maxima body ++ maxima next
  | .step (.repeat _ count _ _ _ body) next =>
      (match count with
        | .runtime maximum _ => [maximum]
        | .static _ => []) ++ maxima body ++ maxima next
  | .step (.choose _ _ _ _ _ arms) next => arms.toList.flatMap maxima ++ maxima next
  | .step _ next => maxima next

/-- The roles guard an agreed count below 5 and loop on it; afterwards role 0 reads `xs[i]`
without a guard. -/
def readAfterLoop (maximum : Nat) : Raw.Package :=
  { base with protocols := [⟨false, 2, [⟨.nat, 0⟩, ⟨.nat, 1⟩, ⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩],
      [⟨.nat, 0⟩], [⟨false, [0, 1]⟩],
      .step (.at 0 (.literal (.nat 5))) <|            -- 4
      .step (.at 0 (.builtin .natLess [0, 4])) <|      -- 5
      .step (.at 0 (.guard .reject 5)) <|
      .step (.at 1 (.literal (.nat 5))) <|            -- 6
      .step (.at 1 (.builtin .natLess [1, 6])) <|      -- 7
      .step (.at 1 (.guard .reject 7)) <|
      .step (.repeat [0, 1] (.runtime maximum [0, 1]) [] [] [] (.ret [])) <|
      .step (.at 0 (.builtin (.seqAt .nat none) [2, 3])) <|   -- 8
      .ret [8]⟩] }

-- the maximum is written although a later application is not justified, so that admission
-- reports that application and not the loop
#guard unmet (readAfterLoop 4) == [.position]
#guard unmet (fillMaxima (readAfterLoop 0)) == [.position]

/-- Role 0 holds a value of a variant without alternatives, so nothing it does runs; role 1
guards its copy of the count below 10. -/
def deadParticipant (maximum : Nat) : Raw.Package :=
  { base with
    variants := [⟨[]⟩]
    protocols := [⟨false, 2, [⟨.variant 0 [], 0⟩, ⟨.nat, 0⟩, ⟨.nat, 1⟩], [], [⟨false, [1, 2]⟩],
      .step (.at 1 (.literal (.nat 10))) <|
      .step (.at 1 (.builtin .natLess [2, 3])) <|
      .step (.at 1 (.guard .reject 4)) <|
      .step (.repeat [0, 1] (.runtime maximum [1, 2]) [] [] [] (.ret [])) <|
      .ret []⟩] }

#guard kinds (deadParticipant 9) == []
#guard (fillMaxima (deadParticipant 0)).protocols.map (maxima ·.body) == [[9]]
#guard kinds (fillMaxima (deadParticipant 0)) == []

/-- A loop on a count below 5 whose body loops on another count below 3. -/
def nestedLoops : Raw.Package :=
  { base with protocols := [⟨false, 2, [⟨.nat, 0⟩, ⟨.nat, 1⟩, ⟨.nat, 0⟩, ⟨.nat, 1⟩], [],
      [⟨false, [0, 1]⟩, ⟨false, [2, 3]⟩],
      .step (.at 0 (.literal (.nat 5))) <|            -- 4
      .step (.at 0 (.builtin .natLess [0, 4])) <|      -- 5
      .step (.at 0 (.guard .reject 5)) <|
      .step (.at 1 (.literal (.nat 5))) <|            -- 6
      .step (.at 1 (.builtin .natLess [1, 6])) <|      -- 7
      .step (.at 1 (.guard .reject 7)) <|
      .step (.at 0 (.literal (.nat 3))) <|            -- 8
      .step (.at 0 (.builtin .natLess [2, 8])) <|      -- 9
      .step (.at 0 (.guard .reject 9)) <|
      .step (.at 1 (.literal (.nat 3))) <|            -- 10
      .step (.at 1 (.builtin .natLess [3, 10])) <|     -- 11
      .step (.at 1 (.guard .reject 11)) <|
      .step (.repeat [0, 1] (.runtime 0 [0, 1]) [] [2, 3] []
        -- the iteration number at each role (0, 1), then the captures (2, 3)
        (.step (.repeat [0, 1] (.runtime 0 [2, 3]) [] [] [] (.ret [])) (.ret []))) <|
      .ret []⟩] }

-- the bounds are written in the order of the body: the outer loop, then the loop in it
#guard (fillMaxima nestedLoops).protocols.map (maxima ·.body) == [[4, 2]]
#guard kinds (fillMaxima nestedLoops) == []

/-- A package with one row at the scalar field of BLS12-381, at a signature. -/
def withRow (name : String) (inputs outputs : List Ty) : Raw.Package :=
  { base with types := [⟨Name.ofString "bls12-381.fr", []⟩]
              operations := [{ identity := ⟨Name.ofString name, [.type (.nominal 0)]⟩
                               signature := ⟨inputs, outputs, .pure⟩ }] }

def scalar : Ty := .nominal 0

#guard kinds (withRow "field.add" [scalar, scalar] [scalar]) { rows := some Vocabulary.table } == []
-- the vocabulary's row with one input: refused when the rows are stated, not looked at otherwise
#guard kinds (withRow "field.add" [scalar] [scalar]) { rows := some Vocabulary.table } == ["row"]
#guard kinds (withRow "field.add" [scalar] [scalar]) == []
-- a row under a name that the vocabulary does not have is a row of an extension: admitted
#guard kinds (withRow "field.unknown" [scalar] [scalar]) { rows := some Vocabulary.table } == []
#guard Vocabulary.extensions Vocabulary.table (withRow "field.add" [scalar] [scalar]) == []
#guard Vocabulary.extensions Vocabulary.table (withRow "field.unknown" [scalar] [scalar]) ==
  ["field.unknown"]
-- a name of the vocabulary at static arguments for which it has no row is no extension
#guard kinds { withRow "field.add" [scalar, scalar] [scalar] with
    operations := [{ identity := ⟨Name.ofString "field.add", []⟩
                     signature := ⟨[scalar, scalar], [scalar], .pure⟩ }] }
  { rows := some Vocabulary.table } == ["row"]

end ClaimsTests

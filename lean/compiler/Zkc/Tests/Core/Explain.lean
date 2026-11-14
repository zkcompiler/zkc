import Zkc.Core.Explain

/-! The explanation of a refusal of the check of facts.

- Every application that is not justified is reported, not only the first, each at its path as
  written and with what was known of its operands.
- A slice says which of its conditions is not met.
- In a protocol body an application is reported with the role whose copy it is; a copy of the
  same code at a role that has the fact is not reported.
- A loop over a value that a participant does not know to be bounded is reported with that
  participant.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ExplainTests

def base : Raw.Package :=
  { types := [], records := [], variants := [], operations := [], functions := [], protocols := [],
    names := none }

/-- What is explained of a package: the path, the role, the requirement, the condition, and
the upper end of each operand. -/
def explained (package : Raw.Package) :
    List (List Nat × Option Nat × Requirement × Explain.Condition × List (Option Nat)) :=
  match elaborate package with
  | .ok typed => typed.explain.map fun (_, found) =>
      (found.path, found.role, found.requirement, found.condition, found.operands.map (·.hi))
  | .error _ => []

/-- `xs[i]` on a collection of 4 with `i` a natural, then `a - b`, then `xs[j]` after
`guard j < 9`. -/
def threeReads : Raw.Package :=
  { base with functions := [⟨false, [.seq .nat (some 4), .nat, .nat, .nat, .nat], [.nat], some <|
      .step (.builtin (.seqAt .nat (some 4)) [0, 1]) <|        -- 5
      .step (.builtin .natSub [2, 3]) <|                       -- 6
      .step (.literal (.nat 9)) <|                             -- 7
      .step (.builtin .natLess [4, 7]) <|                      -- 8
      .step (.guard .reject 8) <|
      .step (.builtin (.seqAt .nat (some 4)) [0, 4]) <|        -- 9
      .ret [9]⟩] }

#guard explained threeReads ==
  [([0], none, .position, .whole, [none, none]),
   ([1], none, .ordered, .whole, [none, none]),
   ([5], none, .position, .whole, [none, some 8])]

/-- Slices of a collection of 8: bounds not in order; an upper bound that can be 9; and
bounds in order within the size into a result of another size. -/
def slices : Raw.Package :=
  { base with functions := [⟨false, [.seq .nat (some 8), .nat, .nat], [], some <|
      .step (.builtin (.seqSlice .nat (some 8) none) [0, 2, 1]) <|     -- 3
      .step (.literal (.nat 10)) <|                                    -- 4
      .step (.builtin .natLess [2, 4]) <|                              -- 5
      .step (.guard .reject 5) <|
      .step (.builtin .natLess [1, 2]) <|                              -- 6
      .step (.guard .reject 6) <|
      .step (.builtin (.seqSlice .nat (some 8) none) [0, 1, 2]) <|     -- 7
      .step (.literal (.nat 8)) <|                                     -- 8
      .step (.builtin .natLess [2, 8]) <|                              -- 9
      .step (.guard .reject 9) <|
      .step (.builtin (.seqSlice .nat (some 8) (some 3)) [0, 1, 2]) <| -- 10
      .ret []⟩] }

#guard (explained slices).map (fun (path, _, requirement, condition, _) => (path, requirement, condition)) ==
  [([0], .slice, .order), ([6], .slice, .upperSize), ([10], .slice, .resultSize)]

/-- Role 0 guards `i < 4` and reads `xs[i]`; role 1 reads its copy without a guard. -/
def twoReaders : Raw.Package :=
  { base with protocols := [⟨false, 2,
      [⟨.seq .nat (some 4), 0⟩, ⟨.seq .nat (some 4), 1⟩, ⟨.nat, 0⟩, ⟨.nat, 1⟩], [],
      [⟨false, [0, 1]⟩, ⟨false, [2, 3]⟩],
      .step (.at 0 (.literal (.nat 4))) <|                       -- 4
      .step (.at 0 (.builtin .natLess [2, 4])) <|                 -- 5
      .step (.at 0 (.guard .reject 5)) <|
      .step (.at 0 (.builtin (.seqAt .nat (some 4)) [0, 2])) <|   -- 6
      .step (.at 1 (.builtin (.seqAt .nat (some 4)) [1, 3])) <|   -- 7
      .ret []⟩] }

#guard explained twoReaders == [([4], some 1, .position, .whole, [none, none])]

/-- Role 0 guards the count below 5; role 1 does not. -/
def unboundedLoop : Raw.Package :=
  { base with protocols := [⟨false, 2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [], [⟨false, [0, 1]⟩],
      .step (.at 0 (.literal (.nat 5))) <|            -- 2
      .step (.at 0 (.builtin .natLess [0, 2])) <|      -- 3
      .step (.at 0 (.guard .reject 3)) <|
      .step (.repeat [0, 1] (.runtime 4 [0, 1]) [] [] [] (.ret [])) (.ret [])⟩] }

#guard explained unboundedLoop == [([3], some 1, .maximum, .whole, [none])]

end ExplainTests

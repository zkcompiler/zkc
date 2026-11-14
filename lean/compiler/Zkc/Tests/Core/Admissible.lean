import Zkc.Core.Admissible
import Zkc.Tests.Core.Facts
import Zkc.Tests.Core.RoleFacts

/-! The check of facts on the normal form, evaluated by the kernel.

- The packages that pass the check of facts as written pass it in normal form, and the ones
  that are refused as written for a missing guard are refused in normal form: the normal form
  adds no fact.
- Five functions are refused as written and pass in normal form. `twice` computes a guarded
  sum a second time. `across` guards a sum and computes it again inside an `if` that captures
  only the addends. `unread` guards a position against the length of a sequence and reads the
  sequence inside an `if` that captures the sequence and the position, not the length.
  `looped` is the same with a loop. `unguarded` is `unread` without the guard, and is refused
  in both forms.
- `conjunction` passes in both forms: a `bool` literal is not shared, so the form that the
  check reads for `a and b` stays.
- Two protocols are refused as written and pass in normal form: a role guards a position and
  reads it inside a `choose`, whose regions capture the sequence and the position; and a role
  guards a position and reads it inside a local `if`.
- A block inside a local region of a role is removed: a guard in it justifies a read after it,
  and a refusal after it is placed at the path of the instruction as written.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace AdmissibleTests

kernel_refl facts_admissible : Facts.typed.program.admissible equals true
kernel_refl facts_unguarded : Facts.unguardedTyped.program.admissible equals false
kernel_refl role_facts_admissible : RoleFacts.typed.program.admissible equals true
kernel_refl role_facts_unguarded : RoleFacts.unguardedTyped.program.admissible equals false

def base : Raw.Package :=
  { types := [], records := [], variants := [], operations := [], functions := [], protocols := [],
    names := none }

def function (inputs : List Ty) (body : Raw.LocalRegion) : Raw.Package :=
  { base with functions := [⟨false, inputs, [.nat], some body⟩] }

/-- Whether a package elaborates and passes the check of facts, as written and in normal
form. -/
def verdicts (package : Raw.Package) : Option (Bool × Bool) :=
  match elaborate package with
  | .ok typed => some (typed.program.justified, typed.program.admissible)
  | .error _ => none

/-- `s = a + b; guard c < s; s' = a + b; s' - c` -/
def twice : Raw.Package := function [.nat, .nat, .nat] <|
  .step (.builtin .natAdd [0, 1]) <|
  .step (.builtin .natLess [2, 3]) <|
  .step (.guard .reject 4) <|
  .step (.builtin .natAdd [0, 1]) <|
  .step (.builtin .natSub [5, 2]) (.ret [6])

/-- `guard c < a + b; if cond then (a + b) - c else 0`, the `if` capturing `a`, `b`, `c`. -/
def across : Raw.Package := function [.nat, .nat, .nat, .bool] <|
  .step (.builtin .natAdd [0, 1]) <|
  .step (.builtin .natLess [2, 4]) <|
  .step (.guard .reject 5) <|
  .step (.conditional 3 [0, 1, 2] [.nat]
    (.step (.builtin .natAdd [0, 1]) <| .step (.builtin .natSub [3, 2]) (.ret [4]))
    (.step (.literal (.nat 0)) (.ret [3]))) <|
  .ret [6]

/-- `guard i < length(xs); if cond then xs[i] else 0`, the `if` capturing `xs` and `i`. -/
def unread : Raw.Package := function [.seq .nat none, .nat, .bool] <|
  .step (.builtin (.seqLength .nat none) [0]) <|
  .step (.builtin .natLess [1, 3]) <|
  .step (.guard .reject 4) <|
  .step (.conditional 2 [0, 1] [.nat]
    (.step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2]))
    (.step (.literal (.nat 0)) (.ret [2]))) <|
  .ret [5]

/-- The same without the guard. -/
def unguarded : Raw.Package := function [.seq .nat none, .nat, .bool] <|
  .step (.conditional 2 [0, 1] [.nat]
    (.step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2]))
    (.step (.literal (.nat 0)) (.ret [2]))) <|
  .ret [3]

/-- `guard i < length(xs); for _ in 0..3: xs[i]`, the loop capturing `xs` and `i`. -/
def looped : Raw.Package := function [.seq .nat none, .nat] <|
  .step (.builtin (.seqLength .nat none) [0]) <|
  .step (.builtin .natLess [1, 2]) <|
  .step (.guard .reject 3) <|
  .step (.loop (.static 3) [] [0, 1] [.nat]
    (.step (.builtin (.seqAt .nat none) [1, 2]) (.ret [3]))) <|
  .step (.literal (.nat 0)) (.ret [5])

/-- `r = if i < length(xs) then b else false; guard r; xs[i]`, after a literal `false`. The
check of facts reads the second region of the `if` as the literal `false` and a return, so a
`bool` literal is not shared. -/
def conjunction : Raw.Package := function [.seq .nat none, .nat, .bool] <|
  .step (.literal (.bool false)) <|
  .step (.builtin (.seqLength .nat none) [0]) <|
  .step (.builtin .natLess [1, 4]) <|
  .step (.conditional 5 [2] [.bool]
    (.ret [0])
    (.step (.literal (.bool false)) (.ret [1]))) <|
  .step (.guard .reject 6) <|
  .step (.builtin (.seqAt .nat none) [0, 1]) <|
  .ret [7]

kernel_refl conjunction_verdicts : verdicts conjunction equals some (true, true)
kernel_refl twice_verdicts : verdicts twice equals some (false, true)
kernel_refl across_verdicts : verdicts across equals some (false, true)
kernel_refl unread_verdicts : verdicts unread equals some (false, true)
kernel_refl unguarded_verdicts : verdicts unguarded equals some (false, false)
kernel_refl looped_verdicts : verdicts looped equals some (false, true)

/-! ## The place of a refusal

The normal form drops a shared application and has no block, so its paths are not those of
the body. A refusal is placed in the body as written. -/

/-- `a + b` twice, then `xs[i]` without a guard: the third instruction as written, the second
of the normal form. -/
def afterShared : Raw.Package := function [.seq .nat none, .nat, .nat] <|
  .step (.builtin .natAdd [1, 2]) <|
  .step (.builtin .natAdd [1, 2]) <|
  .step (.builtin (.seqAt .nat none) [0, 1]) <|
  .ret [5]

/-- The same read inside a block, after a shared sum inside it, and inside an `if`. -/
def inBlock : Raw.Package := function [.seq .nat none, .nat, .bool] <|
  .step (.builtin .natAdd [1, 1]) <|
  .block [.nat]
    (.step (.builtin .natAdd [1, 1]) <|
     .step (.conditional 2 [0, 1] [.nat]
       (.step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2]))
       (.step (.literal (.nat 0)) (.ret [2]))) <|
     .ret [5]) <|
  .ret [4]

/-- The refusals of a package, as admission places them. -/
def refusalsOf (package : Raw.Package) : Option (List (Nat × Unjustified)) :=
  match elaborate package with
  | .ok typed => some typed.program.functions.inadmissible
  | .error _ => none

kernel_refl after_shared : refusalsOf afterShared equals some [(0, ⟨[2], .position⟩)]
kernel_refl in_block : refusalsOf inBlock equals some [(0, ⟨[1, 1, 0, 0], .position⟩)]

def protocol (inputs outputs : List Located) (body : Raw.ProtocolRegion) : Raw.Package :=
  { base with
    protocols := [⟨false, 2, inputs, outputs, [], body⟩] }

/-- Role 0 holds `xs`, `i` and a condition, role 1 a copy of the condition. Role 0 guards
`i < length(xs)`; inside a `choose` of both roles, whose regions capture `xs` and `i`, it reads
`xs[i]`. -/
def chosen : Raw.Package :=
  protocol [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩, ⟨.bool, 1⟩] [⟨.nat, 0⟩] <|
  .step (.at 0 (.builtin (.seqLength .nat none) [0])) <|
  .step (.at 0 (.builtin .natLess [1, 4])) <|
  .step (.at 0 (.guard .reject 5)) <|
  .step (.choose [0, 1] [2, 3] .condition [0, 1] [⟨.nat, 0⟩]
    (.ofList
      [.step (.at 0 (.literal (.nat 0))) (.ret [2]),
       .step (.at 0 (.builtin (.seqAt .nat none) [0, 1])) (.ret [2])])) <|
  .ret [6]

/-- Role 0 guards `i < length(xs)` and reads `xs[i]` inside a local `if` that captures `xs`
and `i`. -/
def local_ : Raw.Package :=
  protocol [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩, ⟨.bool, 1⟩] [⟨.nat, 0⟩] <|
  .step (.at 0 (.builtin (.seqLength .nat none) [0])) <|
  .step (.at 0 (.builtin .natLess [1, 4])) <|
  .step (.at 0 (.guard .reject 5)) <|
  .step (.at 0 (.conditional 2 [0, 1] [.nat]
    (.step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2]))
    (.step (.literal (.nat 0)) (.ret [2])))) <|
  .ret [6]

/-- Role 0 reads `xs[i]` without a guard inside a local `if`, after a literal that both roles
make: the fourth instruction as written, inside the first region of the `if`. -/
def localUnguarded : Raw.Package :=
  protocol [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩, ⟨.bool, 1⟩] [⟨.nat, 0⟩] <|
  .step (.at 0 (.literal (.nat 1))) <|
  .step (.at 0 (.literal (.nat 1))) <|
  .step (.at 1 (.literal (.nat 1))) <|
  .step (.at 0 (.conditional 2 [0, 1] [.nat]
    (.step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2]))
    (.step (.literal (.nat 0)) (.ret [2])))) <|
  .ret [7]

def protocolRefusalsOf (package : Raw.Package) : Option (List (Nat × Unjustified)) :=
  match elaborate package with
  | .ok typed => some typed.program.protocols.inadmissible
  | .error _ => none

kernel_refl local_unguarded :
    protocolRefusalsOf localUnguarded equals some [(0, ⟨[3, 0, 0], .position⟩)]
kernel_refl chosen_verdicts : verdicts chosen equals some (false, true)
kernel_refl local_verdicts : verdicts local_ equals some (false, true)

/-- The region of `true` of a local `if`: `{ guard i < length(xs) }; xs[i]`, the guard inside
a block. -/
def guardedInBlock : Raw.LocalRegion :=
  .block []
    (.step (.builtin (.seqLength .nat none) [0]) <|
     .step (.builtin .natLess [1, 2]) <|
     .step (.guard .reject 3) (.ret [])) <|
  .step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2])

/-- The same region with the block computing the length twice in place of the guard. -/
def unguardedInBlock : Raw.LocalRegion :=
  .block []
    (.step (.builtin (.seqLength .nat none) [0]) <|
     .step (.builtin (.seqLength .nat none) [0]) (.ret [])) <|
  .step (.builtin (.seqAt .nat none) [0, 1]) (.ret [2])

/-- A role's local `if` whose region of `true` is given. -/
def blockInRole (onTrue : Raw.LocalRegion) : Raw.Package :=
  protocol [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩, ⟨.bool, 0⟩] [⟨.nat, 0⟩] <|
  .step (.at 0 (.conditional 2 [0, 1] [.nat] onTrue (.step (.literal (.nat 0)) (.ret [2])))) <|
  .ret [3]

-- a block of a local region of a role is removed like any other: its guard justifies the
-- read after it, and a refusal after it is placed at the instruction as written
kernel_refl block_in_role_verdicts : verdicts (blockInRole guardedInBlock) equals some (false, true)
kernel_refl block_in_role_placed :
    protocolRefusalsOf (blockInRole unguardedInBlock) equals some [(0, ⟨[0, 0, 1], .position⟩)]

#print axioms across_verdicts
#print axioms Zkc.Core.Program.role_never_undefined_of_admissible

end AdmissibleTests

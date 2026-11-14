import Zkc.Core.Digest
import Zkc.Tests.Core.Lowering

/-! The digest of a role.

The digest is the comparison by which a producer's change is judged, so it is tested the way a
check is: by changing a program and seeing that the digest sees it.

- It does not see what a role cannot tell: other names, a computation without effect made in
  another order or twice, a block.
- It sees a role that no longer computes a guard, two operands of an application exchanged, a
  participant dropped from a choice, another value sent, another site, another callee role.
-/

set_option autoImplicit false

open Zkc.Core Zkc.Core.Named

namespace DigestTests

open LoweringTests (cmp site emptyPackage)

/-- Roles P = 0 and V = 1. P holds `x`; both hold `c`. P computes `x + x`, guards `c`, and
sends the sum; V guards `c` and returns what it received. -/
def base (instructions : List ProtocolInstruction) : Named.Package :=
  { emptyPackage with
    protocols := [{ specificationOnly := false, roles := 2
                    inputs := [⟨.nat, [0]⟩, ⟨.bool, [0, 1]⟩], outputs := [⟨.nat, [1]⟩]
                    body := .mk [0, 1] instructions (.ret [20]) }]
    protocolNames := ["main"], roleNames := [["P", "V"]] }

def written : List ProtocolInstruction :=
  [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
   cmp 2 [0, 1] [] (.guard .reject 1),
   .mk 3 [20] (.exchange 0 1 (site 3 "m") 10)]

/-- The digests of the two roles. -/
def digests (instructions : List ProtocolInstruction) : List (Array String) :=
  (base instructions).digests.map (·.2)

-- other names
#guard digests written ==
  digests [cmp 1 [0] [77] (.builtin .natAdd [0, 0]),
           cmp 2 [0, 1] [] (.guard .reject 1),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 77)]

-- the sum computed after the guard, and computed twice
#guard digests written ==
  digests [cmp 2 [0, 1] [] (.guard .reject 1),
           cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           cmp 1 [0] [11] (.builtin .natAdd [0, 0]),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 11)]

-- the guard of each role as a `compute` of its own
#guard digests written ==
  digests [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           cmp 2 [1] [] (.guard .reject 1),
           cmp 2 [0] [] (.guard .reject 1),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 10)]

-- V no longer guards
#guard digests written !=
  digests [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           cmp 2 [0] [] (.guard .reject 1),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 10)]

-- another value is sent
#guard digests written !=
  digests [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           cmp 2 [0, 1] [] (.guard .reject 1),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 0)]

-- another site
#guard digests written !=
  digests [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           cmp 2 [0, 1] [] (.guard .reject 1),
           .mk 3 [20] (.exchange 0 1 (site 4 "m") 10)]

-- the guard after the send: the order of what a role does
#guard digests written !=
  digests [cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
           .mk 3 [20] (.exchange 0 1 (site 3 "m") 10),
           cmp 2 [0, 1] [] (.guard .reject 1)]

/-- A callee of two roles with two ports held by its first role, and a caller that applies it
on two values. -/
def applying (operands : List ValueName) (roleMap : List Nat) : Named.Package :=
  { emptyPackage with
    protocols := [
      { specificationOnly := false, roles := 2
        inputs := [⟨.nat, [0]⟩, ⟨.nat, [0]⟩], outputs := [⟨.nat, [0]⟩]
        body := .mk [0, 1] [cmp 1 [0] [2] (.builtin .natSub [0, 1])] (.ret [2]) },
      { specificationOnly := false, roles := 2
        inputs := [⟨.nat, [0]⟩, ⟨.nat, [0]⟩], outputs := [⟨.nat, [0]⟩]
        body := .mk [0, 1] [.mk 5 [2] (.apply 0 roleMap (site 5 "call") operands)] (.ret [2]) }]
    protocolNames := ["callee", "main"], roleNames := [["A", "B"], ["P", "V"]] }

-- two operands of an application exchanged
#guard (applying [0, 1] [0, 1]).digests != (applying [1, 0] [0, 1]).digests

/-- A choice of the participants given on the flag that both hold; P guards in the arm of
`true`. -/
def choosing (participants : List Nat) : Named.Package :=
  base [.mk 4 [] (.choose participants 1 .condition []
          [.mk [] [cmp 5 [0] [] (.guard .reject 1)] (.ret []), .mk [] [] (.ret [])]),
        cmp 1 [0] [10] (.builtin .natAdd [0, 0]),
        .mk 3 [20] (.exchange 0 1 (site 3 "m") 10)]

-- a participant dropped from a choice
#guard (choosing [0, 1]).digests != (choosing [0]).digests

/-- The instructions of `written` with the sum inside a block of a loop in sequence. -/
def blocked : List ProtocolInstruction :=
  [.mk 9 [10] (.block ⟨0, [0]⟩ [⟨.nat, [0]⟩]
     (.mk [] [cmp 1 [0] [11] (.builtin .natAdd [0, 0])] (.ret [11]))),
   cmp 2 [0, 1] [] (.guard .reject 1),
   .mk 3 [20] (.exchange 0 1 (site 3 "m") 10)]

-- a block does nothing
#guard digests written == digests blocked

end DigestTests

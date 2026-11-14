import Zkc.Core.Copies
import Zkc.Tests.Core.Check

/-! The check of copies, evaluated by the kernel.

- `agreedChoice`: two roles choose on an input that both hold under an agreement. It passes,
  and its one requirement is the two tags, each with the support of its holder.
- `apartChoice`: the two tags are inputs under no agreement. Refused: the tags are not one
  class.
- `computedChoice`: each role computes its tag by the same code from copies of one input.
  It passes: the same code on copies of the same values gives copies.
- `otherCode`: one role negates. Refused.
- `fanOut`: role 0 sends a number to role 1 and to role 2, and the two received copies are
  the outputs under one agreement. It passes: the copies are one class. The side of roles 1
  and 2 does not support the requirement, because the support of each copy contains the
  sender; the side of all roles does, and so does a side of one role.
- `relayed`: role 0 binds 5 and sends it to role 1; role 2 binds its own 5; roles 1 and 2 loop
  on those counts. The copies are one class (the literal), and the support of the received
  copy contains the sender: the side of roles 1 and 2 does not support the requirement.
- `drifting`: a loop of two roles carries a value per role; role 0 adds 1 in each iteration
  and role 1 adds 2. After the loop the two are the tags of a choice. Refused: the body does
  not keep the two carried values one class.
- `steady`: both roles add 1. It passes.
- `afterBlock`: one role negates the agreed flag inside a block and the other after it. It
  passes: a block runs to its end, so what it computes is computed for what follows.
- `passedThrough`: a loop carries one role's copy of the agreed flag and returns it as it
  entered. It passes: no iteration changes the value.
- `sameInEveryArm`: both arms of a choice return the agreed flag from around it. It passes:
  the output is that value.
- `twoApplications`: the results of two applications of one callee on the same copies are not
  one class. Refused: a callee may draw, so two applications of it give two values.
- `drawn`: role 0 draws and role 1 hears the coin; the two copies are the outputs under one
  agreement. It passes: the copies of a draw are one class, and the receiver's copy has the
  owner in its support. `drawnTwice`: the coins of two draws are two values. Refused.
- `swappedCallee`: a callee with an agreed input, applied with its roles exchanged. On the
  agreed copies it passes, and its requirements are the callee's in the caller's roles; on a
  copy outside the agreement it is refused: the operands are not one class.
- `collectingSame`: each role collects its iteration number, and the two sequences are the
  outputs under one agreement. It passes: the collections are one class when the values
  collected are. `collectingOther`: the second role collects a sum. Refused.
- `payloads`: a choice on a variant that both roles hold under an agreement; each arm chooses
  on the payloads. It passes: the payloads of the participants are one class.
- `chain`: a loop whose carried values move one place per iteration, so that the partition
  that the body keeps is found after as many rounds as there are values. It passes: the
  search settles within its fuel.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace CopiesTests

def base : Raw.Package :=
  { types := [], records := [], variants := [], operations := [], functions := [], protocols := [],
    names := none }

def protocol (roles : Nat) (inputs outputs : List Located) (agreements : List Raw.Agreement)
    (body : Raw.ProtocolRegion) : Raw.Package :=
  { base with protocols := [⟨false, roles, inputs, outputs, agreements, body⟩] }

/-- The requirements of the protocols of a package, the most recent first, and the refusals. -/
def copiesOf (package : Raw.Package) :
    Option (List (List Copies.Requirement) × List (Nat × Copies.Refusal)) :=
  match elaborate package with
  | .ok typed => some typed.program.protocols.copies
  | .error _ => none

/-- Whether a side supports the requirements of the last protocol of a package. -/
def supported (package : Raw.Package) (members : List Nat) : Option Bool :=
  (copiesOf package).map fun found =>
    Side.supports (fun role => members.contains role) (found.1.headD [])

def choice (tags : List Nat) : Raw.ProtocolStep :=
  .choose [0, 1] tags .condition [] []
    (.ofList [.ret [], .ret []])

def agreedChoice : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [⟨false, [0, 1]⟩] <|
  .step (choice [0, 1]) (.ret [])

def apartChoice : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [] <|
  .step (choice [0, 1]) (.ret [])

def computedChoice : Raw.Package :=
  protocol 2 [⟨.nat, 0⟩, ⟨.nat, 1⟩] [] [⟨false, [0, 1]⟩] <|
  .step (.at 0 (.builtin .natLess [0, 0])) <|
  .step (.at 1 (.builtin .natLess [1, 1])) <|
  .step (choice [2, 3]) (.ret [])

def otherCode : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [⟨false, [0, 1]⟩] <|
  .step (.at 0 (.builtin .boolNot [0])) <|
  .step (choice [2, 1]) (.ret [])

def fanOut : Raw.Package :=
  protocol 3 [⟨.nat, 0⟩] [⟨.nat, 1⟩, ⟨.nat, 2⟩] [⟨true, [0, 1]⟩] <|
  .step (.exchange 0 1 0 0) <|
  .step (.exchange 0 2 1 0) <|
  .ret [1, 2]

def loopOf (counts : List Nat) : Raw.ProtocolStep :=
  .repeat [1, 2] (.runtime 8 counts) [] [] [] (.ret [])

def relayed : Raw.Package :=
  protocol 3 [] [] [] <|
  .step (.at 0 (.literal (.nat 5))) <|
  .step (.exchange 0 1 0 0) <|
  .step (.at 2 (.literal (.nat 5))) <|
  .step (loopOf [1, 2]) (.ret [])

/-- A loop of roles 0 and 1 over three iterations that carries a flag per role, from two
copies of an agreed input; each role applies `step` to its flag. The flags after the loop are
the tags of a choice. -/
def carrying (first second : Raw.Builtin) : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [⟨false, [0, 1]⟩] <|
  .step (.repeat [0, 1] (.static 3) [0, 1] [] []
    -- inputs: the iteration number at 0 and at 1, then the carried flag at 0 and at 1
    (.step (.at 0 (.builtin first [2, 2])) <|
     .step (.at 1 (.builtin second [3, 3])) <|
     .ret [4, 5])) <|
  .step (choice [2, 3]) (.ret [])

def drifting : Raw.Package := carrying .boolAnd .boolOr
def steady : Raw.Package := carrying .boolAnd .boolAnd

kernel_refl agreed_choice : copiesOf agreedChoice equals
  some ([[[(0, [0]), (1, [1])]]], [])
kernel_refl apart_choice : (copiesOf apartChoice).map (·.2) equals some [(0, ⟨[0], .tags⟩)]
kernel_refl computed_choice : (copiesOf computedChoice).map (·.2) equals some []
kernel_refl other_code : (copiesOf otherCode).map (·.2) equals some [(0, ⟨[1], .tags⟩)]

kernel_refl fan_out : copiesOf fanOut equals some ([[[(1, [1, 0]), (2, [2, 0])]]], [])
kernel_refl fan_out_receivers : supported fanOut [1, 2] equals some false
kernel_refl fan_out_all : supported fanOut [0, 1, 2] equals some true
kernel_refl fan_out_one : supported fanOut [1] equals some true

kernel_refl relayed_passes : (copiesOf relayed).map (·.2) equals some []
kernel_refl relayed_receivers : supported relayed [1, 2] equals some false
kernel_refl relayed_all : supported relayed [0, 1, 2] equals some true

kernel_refl drifting_refused : (copiesOf drifting).map (·.2) equals some [(0, ⟨[1], .tags⟩)]
kernel_refl steady_passes : (copiesOf steady).map (·.2) equals some []

/-- Two roles with an input that both hold under an agreement. -/
def twoRoles (body : Raw.ProtocolRegion) : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [⟨false, [0, 1]⟩] body

def afterBlock : Raw.Package := twoRoles <|
  .block [⟨.bool, 0⟩] (.step (.at 0 (.builtin .boolNot [0])) (.ret [2])) <|   -- 2
  .step (.at 1 (.builtin .boolNot [1])) <|                                     -- 3
  .step (choice [2, 3]) (.ret [])

def passedThrough : Raw.Package := twoRoles <|
  -- the region: the iteration number at each role, then the carried flag of role 0
  .step (.repeat [0, 1] (.static 2) [0] [] [] (.ret [2])) <|                   -- 2
  .step (choice [2, 1]) (.ret [])

def sameInEveryArm : Raw.Package := twoRoles <|
  .step (.choose [0, 1] [0, 1] .condition [0] [⟨.bool, 0⟩] (.ofList [.ret [0], .ret [0]])) <|  -- 2
  .step (choice [2, 1]) (.ret [])

/-- A callee that returns its agreed input, applied twice; the tags are a result of each
application. -/
def twoApplications : Raw.Package :=
  { base with protocols := [
      ⟨false, 2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [⟨.bool, 0⟩, ⟨.bool, 1⟩],
        [⟨false, [0, 1]⟩, ⟨true, [0, 1]⟩], .ret [0, 1]⟩,
      ⟨false, 2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [], [⟨false, [0, 1]⟩],
        .step (.apply 0 [0, 1] 0 [0, 1]) <|   -- 2, 3
        .step (.apply 0 [0, 1] 1 [0, 1]) <|   -- 4, 5
        .step (choice [2, 5]) (.ret [])⟩] }

kernel_refl after_block_passes : (copiesOf afterBlock).map (·.2) equals some []
kernel_refl passed_through_passes : (copiesOf passedThrough).map (·.2) equals some []
kernel_refl same_in_every_arm_passes : (copiesOf sameInEveryArm).map (·.2) equals some []
kernel_refl two_applications_refused :
    (copiesOf twoApplications).map (·.2) equals some [(1, ⟨[2], .tags⟩)]

def law : Operation :=
  ⟨⟨Name.ofString "law.uniform", [.type (.nominal 0)]⟩, ⟨[], [.nominal 0], .sampling⟩⟩

/-- A package with the type `bls12-381.fr` and its law. -/
def withLaw (protocols : List Raw.Protocol) : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩], [], [], [law], [], protocols, none⟩

def drawn : Raw.Package := withLaw
  [⟨false, 2, [], [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩], [⟨true, [0, 1]⟩],
    .step (.draw 0 [1] 0 0 []) (.ret [0, 1])⟩]

def drawnTwice : Raw.Package := withLaw
  [⟨false, 2, [], [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩], [⟨true, [0, 1]⟩],
    .step (.draw 0 [1] 0 0 []) (.step (.draw 0 [1] 1 0 []) (.ret [0, 3]))⟩]

/-- A callee that chooses on its agreed input, applied with the two roles exchanged; the
caller has a third flag, at role 0, under no agreement. -/
def swappedCallee (operands : List Nat) : Raw.Package :=
  { base with protocols := [
      ⟨false, 2, [⟨.bool, 0⟩, ⟨.bool, 1⟩], [], [⟨false, [0, 1]⟩],
        .step (choice [0, 1]) (.ret [])⟩,
      ⟨false, 2, [⟨.bool, 0⟩, ⟨.bool, 1⟩, ⟨.bool, 0⟩], [], [⟨false, [0, 1]⟩],
        .step (.apply 0 [1, 0] 0 operands) (.ret [])⟩] }

/-- A loop of three iterations in which each role collects a value; the region's inputs are
the iteration numbers of the two roles. -/
def collecting (body : Raw.ProtocolRegion) : Raw.Package :=
  protocol 2 [] [⟨.seq .nat (some 3), 0⟩, ⟨.seq .nat (some 3), 1⟩] [⟨true, [0, 1]⟩] <|
  .step (.repeat [0, 1] (.static 3) [] [] [⟨.nat, 0⟩, ⟨.nat, 1⟩] body) <|
  .ret [0, 1]

def collectingSame : Raw.Package := collecting (.ret [0, 1])
def collectingOther : Raw.Package :=
  collecting (.step (.at 1 (.builtin .natAdd [1, 1])) (.ret [0, 2]))

def payloads : Raw.Package :=
  ⟨[], [], [⟨[.bool, .bool]⟩], [], [],
    [⟨false, 2, [⟨.variant 0 [.bool, .bool], 0⟩, ⟨.variant 0 [.bool, .bool], 1⟩], [],
      [⟨false, [0, 1]⟩],
      .step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.ofList [.step (choice [0, 1]) (.ret []), .step (choice [0, 1]) (.ret [])])) (.ret [])⟩],
    none⟩

def chain : Raw.Package :=
  protocol 2 [⟨.bool, 0⟩, ⟨.bool, 1⟩] [] [⟨false, [0, 1]⟩] <|
  .step (.repeat [0, 1] (.static 5) [0, 0, 0, 0, 1] [] []
    -- inputs: the iteration numbers, four carried flags of role 0 and one of role 1
    (.step (.at 0 (.builtin .boolNot [2])) (.ret [7, 2, 3, 4, 6]))) <|
  .step (choice [0, 1]) (.ret [])

kernel_refl drawn_passes : copiesOf drawn equals some ([[[(0, [0]), (1, [1, 0])]]], [])
kernel_refl drawn_twice_refused :
    (copiesOf drawnTwice).map (·.2) equals some [(0, ⟨[], .outputs⟩)]
kernel_refl swapped_passes : copiesOf (swappedCallee [1, 0]) equals
  some ([[[(1, [1]), (0, [0])], [(1, [1]), (0, [0])]], [[(0, [0]), (1, [1])]]], [])
kernel_refl swapped_refused :
    (copiesOf (swappedCallee [1, 2])).map (·.2) equals some [(1, ⟨[0], .operands⟩)]
kernel_refl collecting_same_passes : copiesOf collectingSame equals
  some ([[[], [(0, [0]), (1, [1])]]], [])
kernel_refl collecting_other_refused :
    (copiesOf collectingOther).map (·.2) equals some [(0, ⟨[], .outputs⟩)]
kernel_refl payloads_pass : copiesOf payloads equals
  some ([[[(0, [0]), (1, [1])], [(0, [0]), (1, [1])], [(0, [0]), (1, [1])]]], [])
kernel_refl chain_settles : copiesOf chain equals some ([[[], [(0, [0]), (1, [1])]]], [])

end CopiesTests

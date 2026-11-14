import Zkc.Tests.Core.Check
import Zkc.Core.RoundTrip

/-! Kernel checks for the place of a refusal of elaboration.

A refusal names the function or the protocol it is in, by its number among the definitions
of its kind, and the path of the instruction, numbered as the check of facts numbers an
application that is not justified. The packages here are refused in a second function, in
a nested region of an `if`, of a `match` and of a `loop`, in the body of a block, at the
values a body returns, in a local region under an `at` of a second protocol, in a header,
in an agreement, in the tables and in the names.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Refusals

/-- The refusal of a package. -/
abbrev refusalOf (package : Raw.Package) : Option Refusal :=
  match elaborate package with
  | .error refusal => some refusal
  | .ok _ => none

/-- A package of functions. -/
abbrev functions (definitions : List Raw.Function) : Raw.Package :=
  ⟨[], [], [⟨[.nat, .bool]⟩], [], definitions, [], none⟩

/-- A function without inputs and outputs that returns. -/
abbrev idle : Raw.Function := ⟨false, [], [], some (.ret [])⟩

/-! ## In a function -/

-- The second function, its third instruction, the second region of the `if`, the first
-- instruction there: `bool.not` of a `nat`.
kernel_refl second_region :
    refusalOf (functions [idle, ⟨false, [.bool, .nat], [], some
      (.step (.literal (.nat 1))
        (.step (.builtin .natAdd [1, 2])
          (.step (.conditional 0 [1] [] (.ret []) (.step (.builtin .boolNot [0]) (.ret [])))
            (.ret []))))⟩]) equals
      some ⟨.operand, some (.function 1), [2, 1, 0]⟩

-- A call of a function that the package does not have, in the region of a loop that is the
-- second instruction of the first region of an `if`.
kernel_refl loop_in_region :
    refusalOf (functions [⟨false, [.bool], [], some
      (.step (.conditional 0 [] []
          (.step (.literal (.nat 0))
            (.step (.loop (.static 2) [] [] [] (.step (.call 7 []) (.ret []))) (.ret [])))
          (.ret []))
        (.ret []))⟩]) equals
      some ⟨.dangling, some (.function 0), [0, 0, 1, 0, 0]⟩

-- The region of the second alternative of a `match`: its payload is a `bool`.
kernel_refl second_alternative :
    refusalOf (functions [⟨false, [.variant 0 []], [], some
      (.step (.match 0 0 [] []
          (.arm (.ret []) (.arm (.step (.builtin .natAdd [0, 0]) (.ret [])) .none)))
        (.ret []))⟩]) equals
      some ⟨.operand, some (.function 0), [0, 1, 0]⟩

-- A literal outside its type in the body of a block that is the second instruction: the
-- body of a block has no region number.
kernel_refl block_body :
    refusalOf (functions [⟨false, [], [], some
      (.step (.literal (.nat 0))
        (.block [.nat] (.step (.literal (.fin 2 5)) (.ret [1])) (.ret [])))⟩]) equals
      some ⟨.literal, some (.function 0), [1, 0]⟩

-- A block whose output names an undeclared record: at the block.
kernel_refl block_outputs :
    refusalOf (functions [⟨false, [], [], some
      (.block [.record 9 .free []] (.ret []) (.ret []))⟩]) equals
      some ⟨.declaration, some (.function 0), [0]⟩

-- The values that a body returns, after its two instructions.
kernel_refl returned_values :
    refusalOf (functions [⟨false, [], [.nat], some
      (.step (.literal (.nat 0)) (.step (.literal (.nat 1)) (.ret [5])))⟩]) equals
      some ⟨.operand, some (.function 0), [2]⟩

-- An instruction after the first: an operand that is no value.
kernel_refl later_instruction :
    refusalOf (functions [idle, idle, ⟨false, [], [], some
      (.step (.literal (.nat 0)) (.step (.guard .reject 4) (.ret [])))⟩]) equals
      some ⟨.operand, some (.function 2), [1]⟩

-- The header of the third function names an undeclared variant: no path.
kernel_refl header :
    refusalOf (functions [idle, idle, ⟨false, [.variant 4 []], [], some (.ret [])⟩]) equals
      some ⟨.declaration, some (.function 2), []⟩

-- A function known by its header whose input names a nominal row that the package does not
-- have: a residual condition of the definition, without a path.
kernel_refl opaque_header :
    refusalOf (functions [idle, ⟨false, [.nominal 4], [], none⟩]) equals
      some ⟨.residual .nominalRow, some (.function 1), []⟩

-- A stop with the reserved reason, a residual condition of the body.
kernel_refl residual_body :
    refusalOf (functions [idle, ⟨false, [], [], some (.stop .undefined)⟩]) equals
      some ⟨.residual .reservedReason, some (.function 1), []⟩

/-! ## In a protocol -/

/-- A package of two functions and protocols. -/
abbrev protocols (definitions : List Raw.Protocol) : Raw.Package :=
  ⟨[], [], [], [], [idle, idle], definitions, none⟩

/-- A protocol of two roles without inputs and outputs that returns. -/
abbrev quiet : Raw.Protocol := ⟨false, 2, [], [], [], .ret []⟩

-- The second protocol, numbered among the protocols: a row that the table does not have,
-- in the second region of an `if` that the first role performs.
kernel_refl local_region :
    refusalOf (protocols [quiet, ⟨false, 2, [⟨.bool, 0⟩], [], [],
      .step (.at 0 (.conditional 0 [] [] (.ret []) (.step (.op 3 []) (.ret []))))
        (.ret [])⟩]) equals
      some ⟨.dangling, some (.protocol 1), [0, 1, 0]⟩

-- An application of a protocol that is not an earlier one, after an instruction.
kernel_refl later_application :
    refusalOf (protocols [quiet, ⟨false, 2, [], [], [],
      .step (.at 0 (.literal (.nat 0))) (.step (.apply 1 [0, 1] 0 []) (.ret []))⟩]) equals
      some ⟨.dangling, some (.protocol 1), [1]⟩

-- An agreement without a port: no path.
kernel_refl agreement :
    refusalOf (protocols [quiet, quiet, ⟨false, 2, [⟨.nat, 0⟩], [], [⟨false, []⟩], .ret []⟩])
      equals some ⟨.agreement, some (.protocol 2), []⟩

/-! ## In the tables and the names -/

-- A name table with two function names for one function: no definition.
kernel_refl names :
    refusalOf ⟨[], [], [], [], [idle], [], some ⟨["first", "second"], [], [], []⟩⟩ equals
      some ⟨.residual .nameTable, none, []⟩

-- A row with an input of a nominal type that the package does not have.
kernel_refl tables :
    refusalOf ⟨[], [], [], [⟨⟨Name.ofString "test.row", []⟩, ⟨[.nominal 2], [], .pure⟩⟩],
      [idle], [], none⟩ equals
      some ⟨.residual .nominalRow, none, []⟩

end Refusals

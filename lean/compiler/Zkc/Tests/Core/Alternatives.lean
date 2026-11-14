import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Tests.Core.Builtins
import Zkc.Core.RoundTrip
import Zkc.Core.RoleSyntax
import Zkc.Core.Laws
import Zkc.Tests.Core.Runs

/-! Kernel checks for `choose` on a variant: the participants agree on the alternative
that their copies are, and the region of that alternative takes the payload of each.

- `fixtures/alternatives.json` declares a variant of two alternatives with a `nat` and a
  `bool` payload, and a variant without alternatives. In `decide` both roles hold a value of
  the first variant and choose on it. In the region of the first alternative the first role
  doubles its payload and sends the result, and the second adds its own payload to what it
  receives; in the region of the second each role reads its own `bool`. `never` chooses on
  the variant without alternatives and has no region. `swapped` applies `decide` with the
  two roles exchanged. The package elaborates, its typed package unelaborates to it, and its
  printed JSON reads back to it.
- For an arbitrary model the kernel evaluates `decide` for the side of both roles and for
  the side of each: a role alone runs the region of its own alternative on its own payload,
  and sends or receives; two different alternatives in one side stop `incomplete`, and two
  different payloads of one alternative do not; a side without a participant does nothing.
- The meaning of a `choose` on a condition and on an arm number, stated with equal regions
  over the captures, holds by computation.
- Refusals: a variant that is not declared, fewer regions than alternatives, a region that
  uses its payload at another type, and one that uses the payload of the other role.
- The executor runs the grouped meaning and the two role programs against each other under
  the model of the vocabulary's rows (Lean's interpreter, not the kernel).
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Alternatives

raw_package raw from file "fixtures/alternatives.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl declared :
    raw.variants equals ([⟨[.nat, .bool]⟩, ⟨[]⟩] : List VariantDeclaration)
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/alternatives.json"

kernel_refl reprinted_eq : reprinted equals raw

-- The raw bodies of `never` and of `swapped`: the tag names the variant by its declaration,
-- and a choice on a variant without alternatives has no region.
kernel_refl bodies : ((raw.protocols.drop 1).map (·.body)) equals
  [.step (.choose [0, 1] [0, 1] (.alternative 1 []) [2] [⟨.nat, 0⟩] .none) (.ret [3]),
   .step (.apply 0 [1, 0] 0 [1, 0]) (.ret [2, 3])]

-- The region of the first alternative of `decide`: its first values are the payloads of
-- the two roles.
kernel_refl first_region :
    (raw.protocols.head?.map fun protocol =>
      match protocol.body with
      | .step (.choose participants tags tag captures outputs (.arm region _)) _ =>
          some (participants, tags, tag, captures, outputs, region)
      | _ => none) equals
  some (some ([0, 1], [0, 1], .alternative 0 [], [], [⟨.nat, 1⟩, ⟨.nat, 0⟩],
    .step (.at 0 (.builtin .natAdd [0, 0]))
      (.step (.exchange 0 1 0 2)
        (.step (.at 1 (.builtin .natAdd [3, 1])) (.ret [4, 2])))))

/-- The variant of the package: a `nat` or a `bool`. -/
abbrev choice : Ty := .variant 0 [.nat, .bool]

abbrev decide :
    Var typed.protocols ⟨2, [⟨choice, 0⟩, ⟨choice, 1⟩], [⟨.nat, 1⟩, ⟨.nat, 0⟩], .none, false⟩ :=
  ⟨2, rfl⟩

abbrev never :
    Var typed.protocols
      ⟨2, [⟨.variant 1 [], 0⟩, ⟨.variant 1 [], 1⟩, ⟨.nat, 0⟩], [⟨.nat, 0⟩], .none, false⟩ :=
  ⟨1, rfl⟩

abbrev swapped :
    Var typed.protocols ⟨2, [⟨choice, 0⟩, ⟨choice, 1⟩], [⟨.nat, 0⟩, ⟨.nat, 1⟩], .none, false⟩ :=
  ⟨0, rfl⟩

/-- The meaning of a protocol of the package for a side. -/
noncomputable abbrev meaning (model : Model) {header : ProtocolHeader}
    (protocol : Var typed.protocols header) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get protocol []

abbrev both : Side := fun _ => true
abbrev left : Side := fun role => Nat.beq role 0
abbrev right : Side := fun role => Nat.beq role 1

/-- Both roles hold the first alternative: the first doubles its payload, and the second
adds its own to what the first sent. -/
theorem both_first (model : Model) :
    meaning model decide both (.cons (.inl (3 : Nat)) (.cons (.inl (4 : Nat)) .nil)) =
      .done (.cons (10 : Nat) (.cons (6 : Nat) .nil)) := kernel_rfl%

/-- Both roles hold the second alternative: each reads its own `bool`. -/
theorem both_second (model : Model) :
    meaning model decide both (.cons (.inr (.inl true)) (.cons (.inr (.inl false)) .nil)) =
      .done (.cons (21 : Nat) (.cons (1 : Nat) .nil)) := kernel_rfl%

/-- Two different alternatives in one side stop `incomplete`. -/
theorem both_disagree (model : Model) :
    meaning model decide both (.cons (.inl (3 : Nat)) (.cons (.inr (.inl true)) .nil)) =
      .halt .incomplete := kernel_rfl%

theorem both_disagree_other (model : Model) :
    meaning model decide both (.cons (.inr (.inl true)) (.cons (.inl (3 : Nat)) .nil)) =
      .halt .incomplete := kernel_rfl%

/-- The first role alone, with the first alternative: it doubles its payload and sends the
result. It holds nothing of the second role. -/
theorem left_first (model : Model) :
    meaning model decide left (.cons (.inl (3 : Nat)) (.cons PUnit.unit .nil)) =
      .call (.send ⟨[], 0, 0⟩ .nat (6 : Nat)) fun _ =>
        .done (.cons PUnit.unit (.cons (6 : Nat) .nil)) := kernel_rfl%

/-- The second role alone, with the first alternative: it receives and adds its payload. -/
theorem right_first (model : Model) :
    meaning model decide right (.cons PUnit.unit (.cons (.inl (4 : Nat)) .nil)) =
      .call (.receive ⟨[], 0, 0⟩ .nat) fun reply =>
        .done (.cons (reply + 4 : Nat) (.cons PUnit.unit .nil)) := kernel_rfl%

/-- The first role alone, with the second alternative: the region of that alternative, on
its own `bool`, at the site of that region. -/
theorem left_second (model : Model) :
    meaning model decide left (.cons (.inr (.inl true)) (.cons PUnit.unit .nil)) =
      .call (.send ⟨[], 0, 1⟩ .nat (1 : Nat)) fun _ =>
        .done (.cons PUnit.unit (.cons (1 : Nat) .nil)) := kernel_rfl%

theorem right_second (model : Model) :
    meaning model decide right (.cons PUnit.unit (.cons (.inr (.inl false)) .nil)) =
      .call (.receive ⟨[], 0, 1⟩ .nat) fun reply =>
        .done (.cons (reply + 20 : Nat) (.cons PUnit.unit .nil)) := kernel_rfl%

/-- A side without a participant does nothing and holds nothing. -/
theorem neither (model : Model) :
    meaning model decide (fun _ => false) (.cons PUnit.unit (.cons PUnit.unit .nil)) =
      .done (.cons PUnit.unit (.cons PUnit.unit .nil)) := kernel_rfl%

/-- A choice on a variant without alternatives, for a side without a participant. A side
with one holds a value of a type that has none. -/
theorem never_outside (model : Model) :
    meaning model never (fun _ => false)
        (.cons PUnit.unit (.cons PUnit.unit (.cons PUnit.unit .nil))) =
      .done (.cons PUnit.unit .nil) := kernel_rfl%

/-- The application with the roles exchanged: the second role doubles, the first adds. -/
theorem swapped_first (model : Model) :
    meaning model swapped both (.cons (.inl (3 : Nat)) (.cons (.inl (4 : Nat)) .nil)) =
      .done (.cons (11 : Nat) (.cons (8 : Nat) .nil)) := kernel_rfl%

#print axioms elaborate_eq
#print axioms reprinted_eq
#print axioms both_first
#print axioms both_second
#print axioms both_disagree
#print axioms left_first
#print axioms right_first
#print axioms left_second
#print axioms neither
#print axioms never_outside
#print axioms swapped_first

/-! ## A condition and an arm number

The regions of a `choose` and the region that an agreed tag selects are functions of the
tag. For a condition and for an arm number they are, by computation, equal regions over the
captures and the region with the number that the tag selects. -/

section Earlier

variable {model : Model} {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {side : Side} {label : Nat → Site}

theorem condition_meaning {participants : List Nat} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    (arguments : Values (SideValue model side) (Located.ofRoles .bool participants ++ captures))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (List.replicate 2 (captures, outputs))) :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.choose participants .condition captures outputs covered)
        arguments regions =
      agreed (ChoiceTag.same model.Carrier .condition) side
        (fun value => selectArm (captures, outputs) 2 regions
          (ChoiceTag.select model.Carrier .condition value)
          (arguments.split (Located.ofRoles .bool participants)).2)
        (.halt .incomplete) participants
        (unmapValues (F := SideValue model side) (fun role => ⟨.bool, role⟩) participants
          (arguments.split (Located.ofRoles .bool participants)).1)
        fun none => .done (absentOutputs model side outputs fun _ member =>
          not_held_of_heldBy covered none member) := rfl

theorem arm_meaning {participants : List Nat} {count : Nat} {captures outputs : List Located}
    {covered : Located.heldBy participants outputs = true}
    (arguments : Values (SideValue model side)
      (Located.ofRoles (.fin count) participants ++ captures))
    (regions : Values (RegionFunction (SideValue model side) (Effects model))
      (List.replicate count (captures, outputs))) :
    labelledOperation model label functionTable table side (operations := operations)
        (deployed := deployed) (.choose participants (.arm count) captures outputs covered)
        arguments regions =
      agreed (ChoiceTag.same model.Carrier (.arm count)) side
        (fun value => selectArm (captures, outputs) count regions
          (ChoiceTag.select model.Carrier (.arm count) value)
          (arguments.split (Located.ofRoles (.fin count) participants)).2)
        (.halt .incomplete) participants
        (unmapValues (F := SideValue model side) (fun role => ⟨.fin count, role⟩) participants
          (arguments.split (Located.ofRoles (.fin count) participants)).1)
        fun none => .done (absentOutputs model side outputs fun _ member =>
          not_held_of_heldBy covered none member) := rfl

/-- Two copies of an arm number are the same tag when they are equal. -/
theorem arm_same (count : Nat) (first second : Fin count) :
    ChoiceTag.same model.Carrier (.arm count) first second = true ↔ first = second :=
  ChoiceTag.same_decides model.Carrier (.arm count) first second

/-- Two copies of a variant are the same tag when they are the same alternative: two
different payloads of one alternative agree. -/
theorem payloads_agree :
    ChoiceTag.same model.Carrier (.alternative 0 [.nat, .bool]) (.inl (3 : Nat)) (.inl (4 : Nat)) =
      true := rfl

theorem alternatives_differ :
    ChoiceTag.same model.Carrier (.alternative 0 [.nat, .bool]) (.inl (3 : Nat))
      (.inr (.inl true)) = false := rfl

end Earlier

/-! ## Refusals -/

/-- The refusal of a package with the variant of a `nat` or a `bool` and one protocol of two
roles that both hold a value of it. -/
abbrev refusalOf (outputs : List Located) (body : Raw.ProtocolRegion) : Option Refusal :=
  match elaborate ⟨[], [], [⟨[.nat, .bool]⟩], [], [],
      [⟨false, 2, [⟨.variant 0 [], 0⟩, ⟨.variant 0 [], 1⟩], outputs, [], body⟩], none⟩ with
  | .error refusal => some refusal
  | .ok _ => none

-- A choice whose regions return their own payloads.
kernel_refl choice_accepted :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.arm (.ret []) (.arm (.ret []) .none))) (.ret [])) equals none

-- A variant that is not declared.
kernel_refl undeclared :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 3 []) [] []
        (.arm (.ret []) (.arm (.ret []) .none))) (.ret [])) equals
      some ⟨.declaration, some (.protocol 0), [0]⟩

-- One region for a variant of two alternatives.
kernel_refl one_region :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] [] (.arm (.ret []) .none))
        (.ret [])) equals some ⟨.operand, some (.protocol 0), [0]⟩

-- Three regions for a variant of two alternatives.
kernel_refl three_regions :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.arm (.ret []) (.arm (.ret []) (.arm (.ret []) .none)))) (.ret [])) equals
      some ⟨.operand, some (.protocol 0), [0]⟩

-- The payload of the second alternative is a `bool`: its region does not add it. The
-- refusal is at the first instruction of the second region of the first instruction.
kernel_refl other_type :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.arm (.ret [])
          (.arm (.step (.at 0 (.builtin .natAdd [0, 0])) (.ret [])) .none))) (.ret [])) equals
      some ⟨.operand, some (.protocol 0), [0, 1, 0]⟩

-- The first payload of a region is the first role's: the second role does not compute
-- with it.
kernel_refl other_holder :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.arm (.step (.at 1 (.builtin .natAdd [0, 0])) (.ret [])) (.arm (.ret []) .none)))
        (.ret [])) equals some ⟨.operand, some (.protocol 0), [0, 0, 0]⟩

-- The same region, with the payload of the role that computes.
kernel_refl own_holder :
    refusalOf []
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
        (.arm (.step (.at 1 (.builtin .natAdd [1, 1])) (.ret [])) (.arm (.ret []) .none)))
        (.ret [])) equals none

-- A region returns the payload of the role that holds the output, and no other.
kernel_refl returned_payload :
    refusalOf [⟨.nat, 1⟩]
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] [⟨.nat, 1⟩]
        (.arm (.ret [1]) (.arm (.step (.at 1 (.literal (.nat 0))) (.ret [2])) .none)))
        (.ret [2])) equals none

kernel_refl returned_other :
    refusalOf [⟨.nat, 1⟩]
      (.step (.choose [0, 1] [0, 1] (.alternative 0 []) [] [⟨.nat, 1⟩]
        (.arm (.ret [0]) (.arm (.step (.at 1 (.literal (.nat 0))) (.ret [2])) .none)))
        (.ret [2])) equals some ⟨.operand, some (.protocol 0), [0, 0, 0]⟩

-- A tag of another type than the variant.
kernel_refl other_tag :
    (match elaborate ⟨[], [], [⟨[.nat, .bool]⟩], [], [],
        [⟨false, 2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [], [],
          .step (.choose [0, 1] [0, 1] (.alternative 0 []) [] []
            (.arm (.ret []) (.arm (.ret []) .none))) (.ret [])⟩], none⟩ with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.operand, some (.protocol 0), [0]⟩

end Alternatives

/-! ## The JSON text -/

-- The JSON of a choice on a variant, and the tag of the choice of a role.
#eval show IO Unit from do
  let parse (text : String) : IO Zkc.Json := match Zkc.Json.parse text with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  let region := "[[], []]"
  match Raw.readProtocolStep #[]
      (← parse s!"[\"case\", 4, [[0, 1], [1, 2]], [3], [{region}, {region}], []]") with
  | .ok (.choose [0, 1] [1, 2] (.alternative 4 []) [3] [] _) => pure ()
  | .ok _ => throw (IO.userError "the choice is read as another instruction")
  | .error message => throw (IO.userError message)
  match Raw.readRoleStep #[]
      (← parse s!"[\"choose\", [\"variant\", 4], 0, [3], [{region}, {region}], []]") with
  | .ok (.choose (.alternative 4 []) 0 [3] [] _) => pure ()
  | .ok _ => throw (IO.userError "the choice of a role is read as another instruction")
  | .error message => throw (IO.userError message)

/-! ## The executor -/

namespace Alternatives.Run

open Zkc.Core.Concrete Zkc.Core.Execute Builtins.Run

#eval show IO Unit from do
  let raw ← match Raw.parsePackage (← IO.FS.readFile (package_file "fixtures/alternatives.json")) with
    | .ok raw => pure raw
    | .error message => throw (IO.userError message)
  let typed ← match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let expect (inputs : List Datum) (expected : String) : IO Unit := do
    let run ← IO.ofExcept (Zkc.Core.Runs.interactive typed inputs [] 0 1)
    unless run.agrees && run.grouped.describe == expected do
      throw (IO.userError s!"{run.grouped.describe}, not {expected}")
  -- The entry applies `decide` with the roles exchanged. The grouped meaning and the two
  -- role programs, run against each other, end alike: each role program matches on its own
  -- copy and computes with its own payload.
  expect [.sequence [.number 0, .number 3], .sequence [.number 0, .number 4]] "returned 11, 8"
  expect [.sequence [.number 1, .number 1], .sequence [.number 1, .number 0]] "returned 10, 0"
  expect [.sequence [.number 1, .number 0], .sequence [.number 1, .number 1]] "returned 21, 1"

end Alternatives.Run

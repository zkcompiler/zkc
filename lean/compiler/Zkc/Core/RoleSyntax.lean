module

public import Zkc.Core.Package
public import Zkc.Core.Unelaborate
public import Zkc.Core.ProjectProgram

public section

/-! Raw positional syntax of role programs, and its text.

A role program is printed from its raw syntax, which is computed from the typed program
by structural recursion, like `unelaborate`. The kernel evaluates the same function, so a
per-package check compares the kernel's raw syntax of a role program with the one the
compiled tool printed.

A value is named by its number in its region, a function by its position among the
functions, and a called role program by its position among the role programs. A type
names a declared record or variant by its number only, as in a raw package.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

namespace Raw

/-- How the count of the loop of a role is given: a number of the instruction, or the
maximum and the number of the value that holds the role's count. -/
inductive RoleCount where
  | static (count : Nat)
  | runtime (maximum value : Nat)
  deriving Repr, Inhabited, DecidableEq

mutual
  /-- One instruction of a role program. -/
  inductive RoleStep where
    | perform (instruction : LocalStep)
    | send (site value : Nat)
    | receive (site : Nat) (type : Ty)
    | draw (site law : Nat) (operands : List Nat)
    | sample (site law : Nat) (operands : List Nat)
    /-- The role's loop: the count, the carried values, the captures, the types of the
    values that each iteration collects, and the region. -/
    | repeat (count : RoleCount) (carried captures : List Nat) (collected : List Ty)
        (body : RoleRegion)
    /-- The role's choice: the tag, the value that holds the role's copy, the captures, the
    outputs and one region per value of the tag. A tag that is a variant names its
    declaration by its number only. -/
    | choose (tag : ChoiceTag) (copy : Nat) (captures : List Nat) (outputs : List Ty)
        (arms : RoleArms)
    | call (callee site : Nat) (operands : List Nat)

  inductive RoleRegion where
    | ret (values : List Nat)
    | stop (reason : PIR.Stop)
    | step (instruction : RoleStep) (next : RoleRegion)
    | block (outputs : List Ty) (body next : RoleRegion)

  /-- The regions of a choice, one per arm. -/
  inductive RoleArms where
    | none
    | arm (region : RoleRegion) (rest : RoleArms)
end

/-- The program of one role of one protocol. -/
structure RoleProgram where
  definition : Nat
  role : Nat
  inputs : List Ty
  outputs : List Ty
  body : RoleRegion

end Raw

section Unelaborate

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {programs : List RoleHeader} {deployed : Bool}

/-- The arms with the given regions. -/
def Raw.RoleArms.ofList : List Raw.RoleRegion → Raw.RoleArms
  | [] => .none
  | region :: rest => .arm region (ofList rest)

/-- A role operation with the numbers of its operands and its nested raw regions.
`programCount` is the number of role programs the operation may call. -/
def unelaborateRoleStep (functionCount programCount : Nat) :
    RoleOp operations functions programs deployed → List Nat → List Raw.RoleRegion → Raw.RoleStep
  | .perform op bodies, operands, _ =>
      .perform (unelaborateLocalStep functionCount op operands
        (unelaborateLocalRegions functionCount bodies))
  | .send site _, [value], _ => .send site value
  | .receive site type, _, _ => .receive site type.strip
  | .draw site law _, operands, _ => .draw site law.index operands
  | .sample site law _, operands, _ => .sample site law.index operands
  | .repeat (.static number) carried collected _, operands, [body] =>
      .repeat (.static number) (operands.take carried.length) (operands.drop carried.length)
        (Ty.stripAll collected) body
  | .repeat (.runtime maximum) carried collected _, count :: rest, [body] =>
      .repeat (.runtime maximum count) (rest.take carried.length) (rest.drop carried.length)
        (Ty.stripAll collected) body
  | .choose tag _ outputs, copy :: captures, arms =>
      .choose tag.strip copy captures (Ty.stripAll outputs) (.ofList arms)
  | .call site callee, operands, _ => .call (Scope.number programCount callee) site operands
  | _, _, _ => .send 0 0

mutual
  def unelaborateRoleRegion (functionCount programCount : Nat) {Γ out : List Ty} (depth : Nat) :
      Region (RoleDialect operations functions programs deployed) Γ out → Raw.RoleRegion
    | .ret values => .ret (Scope.numbers depth values)
    | .stop reason => .stop reason
    | .letOp op arguments bodies rest =>
        .step (unelaborateRoleStep functionCount programCount op (Scope.numbers depth arguments)
            (unelaborateRoleRegions functionCount programCount bodies))
          (unelaborateRoleRegion functionCount programCount (depth + (RoleOp.results op).length) rest)
    | .bind (mid := mid) body rest =>
        .block (Ty.stripAll mid) (unelaborateRoleRegion functionCount programCount depth body)
          (unelaborateRoleRegion functionCount programCount (depth + mid.length) rest)

  def unelaborateRoleRegions (functionCount programCount : Nat)
      {signatures : List (List Ty × List Ty)} :
      Regions (RoleDialect operations functions programs deployed) signatures → List Raw.RoleRegion
    | .nil => []
    | .cons (inputs := inputs) body tail =>
        unelaborateRoleRegion functionCount programCount inputs.length body ::
          unelaborateRoleRegions functionCount programCount tail
end

/-- The raw syntax of one role program. -/
def unelaborateRoleProgram (functionCount programCount definition role : Nat) {header : RoleHeader}
    (program : RoleProgram operations functions programs header) : Raw.RoleProgram :=
  ⟨definition, role, Ty.stripAll header.inputs, Ty.stripAll header.outputs,
    unelaborateRoleRegion functionCount programCount header.inputs.length program.body⟩

/-- The raw role programs of a program, oldest first, before `later`. `count` is the
number of the role programs. -/
def unelaborateRolePrograms (functionCount : Nat) :
    {programs : List RoleHeader} → (count : Nat) → RolePrograms operations functions programs →
      List Raw.RoleProgram → List Raw.RoleProgram
  | _, _, .nil, later => later
  | _, count, .snoc earlier definition role program, later =>
      unelaborateRolePrograms functionCount (count - 1) earlier
        (unelaborateRoleProgram functionCount (count - 1) definition role program :: later)

end Unelaborate

/-! ## Text -/

namespace Raw

mutual
  partial def printRoleStep : RoleStep → Json
    | .perform instruction => printLocalStep instruction
    | .send site value => .arr #["send", site, value]
    | .receive site type => .arr #["receive", site, printType type]
    | .draw site law operands => .arr #["draw", site, law, nats operands]
    | .sample site law operands => .arr #["sample", site, law, nats operands]
    | .repeat count carried captures collected body =>
        -- As a local loop: a loop that collects nothing has no list of collected types.
        let (bound, value) : Json × Json := match count with
          | .static count => ("static", count)
          | .runtime maximum count => (maximum, count)
        let parts : Array Json := #["repeat", bound, value, nats carried, nats captures,
          printRoleRegion body]
        .arr (if collected.isEmpty then parts else parts.push (printTypes collected))
    | .choose tag copy captures outputs arms =>
        let form : Json := match tag with
          | .condition => .arr #[]
          | .arm count => .arr #[count]
          | .alternative declaration _ => .arr #["variant", declaration]
        .arr #["choose", form, copy, nats captures, .arr (printRoleArms arms).toArray,
          printTypes outputs]
    | .call callee site operands => .arr #["call_role", callee, site, nats operands]

  partial def printRoleRegion (region : RoleRegion) : Json := Id.run do
    let mut instructions := #[]
    let mut current := region
    repeat
      match current with
      | .ret values => return .arr #[.arr instructions, nats values]
      | .stop reason => return .arr #[.arr (instructions.push (.arr #["stop", printStop reason])), nats []]
      | .step instruction next =>
          instructions := instructions.push (printRoleStep instruction)
          current := next
      | .block outputs body next =>
          instructions := instructions.push (.arr #["block", printTypes outputs, printRoleRegion body])
          current := next
    return .null

  partial def printRoleArms : RoleArms → List Json
    | .none => []
    | .arm region rest => printRoleRegion region :: printRoleArms rest
end

def printRoleProgram (program : RoleProgram) : Json :=
  .arr #["role", program.definition, program.role, printTypes program.inputs,
    printTypes program.outputs, printRoleRegion program.body]

def printRolePrograms (programs : List RoleProgram) : Json :=
  .arr (programs.map printRoleProgram).toArray

/-- The count of the loop of a role from the two positions after the instruction's name,
as for a local loop: with `"static"` the second is the count itself; otherwise it is the
value that holds the count, and the first is its maximum. -/
def readRoleCount (bound count : Json) : Read RoleCount := do
  match bound with
  | .str "static" => return .static (← readNat "count" count)
  | maximum => return .runtime (← readNat "maximum" maximum) (← readNat "count" count)

mutual
  partial def readRoleStep (kinds : Kinds) (json : Json) : Read RoleStep := do
    match json with
    | .arr #[.str "send", site, value] => return .send (← readNat "site" site) (← readNat "value" value)
    | .arr #[.str "receive", site, type] => return .receive (← readNat "site" site) (← readType type)
    | .arr #[.str "draw", site, law, operands] =>
        return .draw (← readNat "site" site) (← readNat "law" law) (← readNats "operands" operands)
    | .arr #[.str "sample", site, law, operands] =>
        return .sample (← readNat "site" site) (← readNat "law" law) (← readNats "operands" operands)
    | .arr #[.str "repeat", bound, count, carried, captures, body] =>
        return .repeat (← readRoleCount bound count) (← readNats "carried" carried)
          (← readNats "captures" captures) [] (← readRoleRegion kinds body)
    | .arr #[.str "repeat", bound, count, carried, captures, body, collected] =>
        let collected ← readTypes "collected" collected
        if collected.isEmpty then
          throw "repeat: a repeat that collects nothing does not list collected types"
        return .repeat (← readRoleCount bound count) (← readNats "carried" carried)
          (← readNats "captures" captures) collected (← readRoleRegion kinds body)
    | .arr #[.str "choose", tag, copy, captures, arms, outputs] =>
        let tag ← match tag with
          | .arr #[] => pure ChoiceTag.condition
          | .arr #[count] => pure (ChoiceTag.arm (← readNat "arm count" count))
          | .arr #[.str "variant", declaration] =>
              pure (ChoiceTag.alternative (← readNat "variant declaration" declaration) [])
          | _ => throw "malformed tag"
        let arms ← (← readArray "arms" arms).toList.mapM (readRoleRegion kinds)
        return .choose tag (← readNat "tag" copy) (← readNats "captures" captures)
          (← readTypes "outputs" outputs) (.ofList arms)
    | .arr #[.str "call_role", callee, site, operands] =>
        return .call (← readNat "callee" callee) (← readNat "site" site)
          (← readNats "operands" operands)
    | other => return .perform (← readLocalStep kinds other)

  partial def readRoleRegion (kinds : Kinds) (json : Json) : Read RoleRegion := do
    let (instructions, results) ← regionParts json
    let mut region : RoleRegion := .ret results
    for instruction in instructions.reverse do
      match instruction with
      | .arr #[.str "stop", reason] => region := .stop (← readStop reason)
      | .arr #[.str "block", outputs, body] =>
          region := .block (← readTypes "outputs" outputs) (← readRoleRegion kinds body) region
      | other => region := .step (← readRoleStep kinds other) region
    return region
end

def readRoleProgram (json : Json) : Read RoleProgram := do
  match json with
  | .arr #[.str "role", definition, role, inputs, outputs, body] =>
      return ⟨← readNat "definition" definition, ← readNat "role" role, ← readTypes "inputs" inputs,
        ← readTypes "outputs" outputs, ← readRoleRegion #[] body⟩
  | _ => throw "malformed role program"

/-- The role programs of a text that the tool printed. -/
def parseRolePrograms (source : String) : Read (List RoleProgram) := do
  (← readArray "role programs" (← Json.parse source)).toList.mapM readRoleProgram

end Raw

end Zkc.Core

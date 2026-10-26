module

public import Zkc.Executable.Program
public import Zkc.Construction.Scalar

@[expose] public section

/-! The executable reading and its instruction-charge schedule. Code and
receive plans are stage syntax and contain no execution interpreter. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source

/-- A constructed instruction and where the executable charges instructions.
`charge` is executable work with no constructed instruction (a transparent
call's entry or return); `step` is a constructed instruction with the
instructions it charges itself; `helper` is a helper call, charging its call and
its body's work; `loop` is a constructed loop, charging one instruction to start
and one to end each iteration. -/
inductive Code where
  | charge (count : Nat)
  | step (instruction : Instruction) (charged : Nat)
  | helper (instruction : Instruction)
  | loop (site : String) (maximum : Nat) (yielded operands : List Nat) (results : List ValueSort)
      (body : List Code)
  deriving Repr

mutual
/-- Decide equality of code items, so that the kernel can compare readings. -/
def Code.decide : (left right : Code) → Decidable (left = right)
  | .charge count, .charge count' =>
      decidable_of_iff (count = count') (by simp only [Code.charge.injEq])
  | .step instruction charged, .step instruction' charged' =>
      decidable_of_iff (instruction = instruction' ∧ charged = charged')
        (by simp only [Code.step.injEq])
  | .helper instruction, .helper instruction' =>
      decidable_of_iff (instruction = instruction') (by simp only [Code.helper.injEq])
  | .loop site maximum yielded operands results body, .loop site' maximum' yielded' operands' results' body' =>
      letI := Code.decideList body body'
      decidable_of_iff (site = site' ∧ maximum = maximum' ∧ yielded = yielded' ∧
        operands = operands' ∧ results = results' ∧ body = body')
        (by simp only [Code.loop.injEq])
  | .charge _, .step _ _ | .charge _, .helper _ | .charge _, .loop _ _ _ _ _ _
  | .step _ _, .charge _ | .step _ _, .helper _ | .step _ _, .loop _ _ _ _ _ _
  | .helper _, .charge _ | .helper _, .step _ _ | .helper _, .loop _ _ _ _ _ _
  | .loop _ _ _ _ _ _, .charge _ | .loop _ _ _ _ _ _, .step _ _ | .loop _ _ _ _ _ _, .helper _ =>
      isFalse (by intro equal; cases equal)

def Code.decideList : (left right : List Code) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      letI := Code.decide head head'
      letI := Code.decideList tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp only [List.cons.injEq])
end

instance : DecidableEq Code := Code.decide

/-- The constructed instructions of a reading. -/
def Code.instructions : List Code → List Instruction
  | [] => []
  | .charge _ :: rest => Code.instructions rest
  | .step instruction _ :: rest => instruction :: Code.instructions rest
  | .helper instruction :: rest => instruction :: Code.instructions rest
  | .loop site maximum yielded operands results body :: rest =>
      ⟨.loop site maximum yielded, operands, results, Code.instructions body⟩ :: Code.instructions rest

mutual
/-- `Code.instructions` by structural recursion, which the kernel evaluates. -/
def Code.instructionList : List Code → List Instruction
  | [] => []
  | code :: rest => Code.instructionsOf code ++ Code.instructionList rest

/-- The constructed instructions of one code item. -/
def Code.instructionsOf : Code → List Instruction
  | .charge _ => []
  | .step instruction _ => [instruction]
  | .helper instruction => [instruction]
  | .loop site maximum yielded operands results body =>
      [⟨.loop site maximum yielded, operands, results, Code.instructionList body⟩]
end

theorem Code.instructionList_eq : ∀ code : List Code, Code.instructionList code = Code.instructions code
  | [] => by simp [Code.instructionList, Code.instructions]
  | .charge _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .step _ _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .helper _ :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq rest]
  | .loop _ _ _ _ _ body :: rest => by
      simp [Code.instructionList, Code.instructionsOf, Code.instructions, Code.instructionList_eq body,
        Code.instructionList_eq rest]

/-- The receives of a reading: a receive at a physical type, or a loop whose
count is the data input at position `count`, run at most `maximum` times. -/
inductive Plan where
  | receive (type : PhysicalType)
  | loop (count maximum : Nat) (body : List Plan)
  deriving Repr

mutual
def Plan.decide : (left right : Plan) → Decidable (left = right)
  | .receive type, .receive type' =>
      decidable_of_iff (type = type') (by simp only [Plan.receive.injEq])
  | .loop count maximum body, .loop count' maximum' body' =>
      letI := Plan.decideList body body'
      decidable_of_iff (count = count' ∧ maximum = maximum' ∧ body = body')
        (by simp only [Plan.loop.injEq])
  | .receive _, .loop _ _ _ => isFalse (by intro equal; cases equal)
  | .loop _ _ _, .receive _ => isFalse (by intro equal; cases equal)

def Plan.decideList : (left right : List Plan) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | head :: tail, head' :: tail' =>
      letI := Plan.decide head head'
      letI := Plan.decideList tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp only [List.cons.injEq])

end

instance : DecidableEq Plan := Plan.decide

/-- The receive types of a run on the given data inputs, in order. -/
def Plan.types {F G : Type} (data : List (Value F G)) : List Plan → List PhysicalType
  | [] => []
  | .receive type :: rest => type :: Plan.types data rest
  | .loop count maximum body :: rest =>
      (match data[count]? with
        | some (.index bound) =>
            if bound ≤ maximum then (List.replicate bound (Plan.types data body)).flatten else []
        | _ => []) ++ Plan.types data rest

/-- The receive types of a plan without loops, which do not depend on the
data inputs. -/
def Plan.static : List Plan → Option (List PhysicalType)
  | [] => some []
  | .receive type :: rest => (Plan.static rest).map (type :: ·)
  | .loop _ _ _ :: _ => none

theorem Plan.types_static {F G : Type} (data : List (Value F G)) :
    ∀ {plan : List Plan} {types : List PhysicalType}, Plan.static plan = some types →
      Plan.types data plan = types
  | [], types, static => by
      simp only [Plan.static, Option.some.injEq] at static
      subst static
      simp only [Plan.types]
  | .receive type :: rest, types, static => by
      simp only [Plan.static] at static
      cases restStatic : Plan.static rest with
      | none => simp [restStatic] at static
      | some restTypes =>
          simp only [restStatic, Option.map_some, Option.some.injEq] at static
          subst static
          simp only [Plan.types, Plan.types_static data restStatic]
  | .loop _ _ _ :: _, _, static => by simp [Plan.static] at static

/-- The reading of a validator: its constructed instructions with their
charges, the returned references and the receive plan. -/
structure Lowered where
  code : List Code
  returned : List Nat
  plan : List Plan
  deriving Repr


/-- The instructions a reading without loops and helper calls charges before
its return. -/
def Code.static : List Code → Option Nat
  | [] => some 0
  | .charge count :: rest => (Code.static rest).map (count + ·)
  | .step _ charged :: rest => (Code.static rest).map (charged + ·)
  | _ :: _ => none

/-- The instructions a complete run of a reading without loops and helper
calls charges, its return included. -/
def Lowered.total? (lowered : Lowered) : Option Nat := (Code.static lowered.code).map (· + 1)


/-- What code without loops charges: the instructions its items charge, a helper
call its call and at most `bound` for its body; `none` for code with a loop or a
helper without a bound. -/
def Code.charges (bound : String → Option Nat) : List Code → Option Nat
  | [] => some 0
  | .charge count :: rest => (Code.charges bound rest).map (count + ·)
  | .step _ charged :: rest => (Code.charges bound rest).map (charged + ·)
  | .helper instruction :: rest =>
      match instruction.operation with
      | .call name =>
          match bound name, Code.charges bound rest with
          | some most, some others => some (1 + most + others)
          | _, _ => none
      | _ => none
  | .loop .. :: _ => none

end Zkc.Executable

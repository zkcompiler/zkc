import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Zkc.Semantics.Relation

/-! A bounded accumulator machine and an integer trace-column encoding.
Words wrap modulo W, addresses are static and bounded, and one private advice
word is reusable. Instruction fetch is bound to the public program. This is
an explicitly new test machine, not a RISC-V correspondence or a field AIR. -/

set_option autoImplicit false

namespace Composition.Machine

inductive Instruction (W M : Nat) where
  | add : Fin W → Instruction W M
  | load : Fin M → Instruction W M
  | store : Fin M → Instruction W M
  | branchZero : Nat → Instruction W M
  | advice
  | halt
  deriving DecidableEq, Repr

structure State (W M : Nat) where
  pc : Nat
  acc : Fin W
  memory : Fin M → Fin W
  deriving DecidableEq

variable {W M : Nat}

/-- One instruction; invalid fetch and halt have no outgoing transition. -/
def step (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W)
    (state : State W M) : Option (State W M) :=
  match program[state.pc]? with
  | some (.add imm) => some { state with
      pc := state.pc + 1
      acc := ⟨(state.acc.val + imm.val) % W, Nat.mod_lt _ positive⟩ }
  | some (.load address) => some { state with pc := state.pc + 1, acc := state.memory address }
  | some (.store address) => some { state with
      pc := state.pc + 1
      memory := Function.update state.memory address state.acc }
  | some (.branchZero target) => some { state with pc := if state.acc.val = 0 then target else state.pc + 1 }
  | some .advice => some { state with pc := state.pc + 1, acc := secret }
  | some .halt | none => none

/-- Exactly k executed instructions, with successful completion at halt.
Exhaustion and invalid fetch cannot witness this relation. -/
inductive Executes (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W) :
    Nat → State W M → State W M → Prop where
  | done {state : State W M} : program[state.pc]? = some .halt → Executes positive program secret 0 state state
  | next {k : Nat} {state next final : State W M} : step positive program secret state = some next →
      Executes positive program secret k next final → Executes positive program secret (k + 1) state final

structure Statement (W M : Nat) where
  program : List (Instruction W M)
  bound : Nat
  input : Fin W
  initialMemory : Fin M → Fin W
  output : Fin W
  finalMemory : Fin M → Fin W

def initial (statement : Statement W M) : State W M :=
  ⟨0, statement.input, statement.initialMemory⟩

structure Witness (W M : Nat) where
  secret : Fin W
  steps : Nat
  final : State W M

def ValidExecution (positive : 0 < W) (statement : Statement W M) (witness : Witness W M) : Prop :=
  witness.steps ≤ statement.bound ∧
  Executes positive statement.program witness.secret witness.steps (initial statement) witness.final ∧
  witness.final.acc = statement.output ∧ witness.final.memory = statement.finalMemory

/-- Raw untrusted columns. Range is a constraint, not silently a field type. -/
structure Row (M : Nat) where
  pc : Nat
  acc : Nat
  memory : Fin M → Nat
  deriving DecidableEq

def encode (state : State W M) : Row M := ⟨state.pc, state.acc.val, fun a => (state.memory a).val⟩

def InRange (row : Row M) : Prop := row.acc < W ∧ ∀ a, row.memory a < W

def decode (row : Row M) (range : InRange (W := W) row) : State W M :=
  ⟨row.pc, ⟨row.acc, range.1⟩, fun a => ⟨row.memory a, range.2 a⟩⟩

theorem encode_range (state : State W M) : InRange (W := W) (encode state) :=
  ⟨state.acc.isLt, fun a => (state.memory a).isLt⟩

theorem encode_decode (row : Row M) (range : InRange (W := W) row) : encode (decode row range) = row := rfl

theorem encode_injective : Function.Injective (encode (W := W) (M := M)) := by
  intro a b same
  cases a with | mk pc acc memory =>
    cases b with | mk pc' acc' memory' =>
      simp only [encode, Row.mk.injEq] at same
      obtain ⟨rfl, hacc, hmem⟩ := same
      have hacc' : acc = acc' := Fin.ext hacc
      have hmem' : memory = memory' := funext (fun a => Fin.ext (congrFun hmem a))
      cases hacc'; cases hmem'; rfl

/-- Integer local constraints: wrapping addition has an explicit Boolean carry.
The opcode and operands come from public fetch, never from prover selectors. -/
def Local (program : List (Instruction W M)) (secret : Nat) (row next : Row M) : Prop :=
  match program[row.pc]? with
  | some (.add imm) => next.pc = row.pc + 1 ∧ next.memory = row.memory ∧
      ∃ carry : Nat, carry ≤ 1 ∧ row.acc + imm.val = next.acc + W * carry
  | some (.load address) => next.pc = row.pc + 1 ∧ next.memory = row.memory ∧ next.acc = row.memory address
  | some (.store address) => next.pc = row.pc + 1 ∧ next.acc = row.acc ∧
      next.memory = Function.update row.memory address row.acc
  | some (.branchZero target) => next.pc = (if row.acc = 0 then target else row.pc + 1) ∧
      next.acc = row.acc ∧ next.memory = row.memory
  | some .advice => next.pc = row.pc + 1 ∧ next.acc = secret ∧ next.memory = row.memory
  | some .halt | none => False

theorem wrap_iff (positive : 0 < W) (a b c : Nat) (ha : a < W) (hb : b < W) (hc : c < W) :
    c = (a + b) % W ↔ ∃ carry : Nat, carry ≤ 1 ∧ a + b = c + W * carry := by
  constructor
  · intro same
    refine ⟨(a + b) / W, ?_, ?_⟩
    · have := (Nat.div_lt_iff_lt_mul positive).mpr (show a + b < 2 * W by omega)
      omega
    · rw [same]; exact (Nat.mod_add_div (a + b) W).symm
  · rintro ⟨carry, _, equation⟩
    have reduced := congrArg (fun value => value % W) equation
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hc] using reduced.symm

/-- Only the addition equation is arithmetized here. Range and carry bounds
remain integer premises; a full AIR must enforce them and its other columns.
The sufficient modulus bound prevents an extra wrap in the constraint field. -/
theorem field_add_iff (P a b c carry : Nat) (large : 2 * W ≤ P)
    (ha : a < W) (hb : b < W) (hc : c < W) (hcarry : carry ≤ 1) :
    (a : ZMod P) + b = c + (W : ZMod P) * carry ↔ a + b = c + W * carry := by
  have leftBound : a + b < P := by omega
  have rightBound : c + W * carry < P := by
    have : carry = 0 ∨ carry = 1 := by omega
    rcases this with rfl | rfl <;> simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] <;> omega
  rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]

theorem encode_update (memory : Fin M → Fin W) (address : Fin M) (value : Fin W) :
    (fun a => ((Function.update memory address value) a).val) =
      Function.update (fun a => (memory a).val) address value.val := by
  funext a
  by_cases h : a = address <;> simp [h]

/-- All typed predecessor/successor states; not merely honest executions. -/
theorem local_iff_step (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W)
    (state next : State W M) :
    Local program secret.val (encode state) (encode next) ↔ step positive program secret state = some next := by
  cases fetch : program[state.pc]? with
  | none => simp [Local, step, encode, fetch]
  | some op =>
      cases op with
      | add imm =>
          simp only [Local, encode, fetch, step, Option.some.injEq]
          rw [← wrap_iff positive state.acc.val imm.val next.acc.val state.acc.isLt imm.isLt next.acc.isLt]
          constructor
          · rintro ⟨hpc, hmem, hacc⟩
            apply encode_injective
            simp only [encode, Row.mk.injEq]
            exact ⟨hpc.symm, hacc.symm, hmem.symm⟩
          · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      | load address =>
          simp only [Local, encode, fetch, step, Option.some.injEq]
          constructor
          · rintro ⟨hpc, hmem, hacc⟩
            apply encode_injective
            simp only [encode, Row.mk.injEq]
            exact ⟨hpc.symm, hacc.symm, hmem.symm⟩
          · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      | store address =>
          simp only [Local, encode, fetch, step, Option.some.injEq]
          constructor
          · rintro ⟨hpc, hacc, hmem⟩
            apply encode_injective
            simp only [encode, encode_update, Row.mk.injEq]
            exact ⟨hpc.symm, hacc.symm, hmem.symm⟩
          · intro h; cases h; exact ⟨rfl, rfl, encode_update _ _ _⟩
      | branchZero target =>
          simp only [Local, encode, fetch, step, Option.some.injEq]
          constructor
          · rintro ⟨hpc, hacc, hmem⟩
            apply encode_injective
            simp only [encode, Row.mk.injEq]
            exact ⟨hpc.symm, hacc.symm, hmem.symm⟩
          · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      | advice =>
          simp only [Local, encode, fetch, step, Option.some.injEq]
          constructor
          · rintro ⟨hpc, hacc, hmem⟩
            apply encode_injective
            simp only [encode, Row.mk.injEq]
            exact ⟨hpc.symm, hacc.symm, hmem.symm⟩
          · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      | halt => simp [Local, step, encode, fetch]

/-- Decode arbitrary range-valid raw rows, then establish machine semantics. -/
theorem local_decode (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W)
    (row next : Row M) (hr : InRange (W := W) row) (hn : InRange (W := W) next)
    (constraints : Local program secret.val row next) :
    step positive program secret (decode row hr) = some (decode next hn) :=
  (local_iff_step positive program secret _ _).mp constraints

def lastRow (first : Row M) : List (Row M) → Row M
  | [] => first
  | row :: tail => lastRow row tail

theorem lastRow_mem (first : Row M) (tail : List (Row M)) : lastRow first tail ∈ first :: tail := by
  induction tail generalizing first with
  | nil => simp [lastRow]
  | cons row tail ih => exact List.mem_cons_of_mem first (ih row)

structure EncodedWitness (M : Nat) where
  secret : Nat
  first : Row M
  tail : List (Row M)

/-- The public statement map is identity: the same program, bound, inputs and
both memory boundaries are checked. No witness-chosen program is admitted. -/
structure Constraints (statement : Statement W M) (witness : EncodedWitness M) : Prop where
  secret_range : witness.secret < W
  initial : witness.first = encode (Machine.initial statement)
  bound : witness.tail.length ≤ statement.bound
  ranges : ∀ row ∈ witness.first :: witness.tail, InRange (W := W) row
  transitions : List.IsChain (Local statement.program witness.secret) (witness.first :: witness.tail)
  halt : statement.program[(lastRow witness.first witness.tail).pc]? = some .halt
  output : (lastRow witness.first witness.tail).acc = statement.output.val
  memory : (lastRow witness.first witness.tail).memory = fun a => (statement.finalMemory a).val

theorem trace_decode (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W)
    (first : Row M) (tail : List (Row M))
    (ranges : ∀ row ∈ first :: tail, InRange (W := W) row)
    (transitions : List.IsChain (Local program secret.val) (first :: tail))
    (halt : program[(lastRow first tail).pc]? = some .halt) :
    Executes positive program secret tail.length (decode first (ranges first (by simp)))
      (decode (lastRow first tail) (ranges _ (lastRow_mem first tail))) := by
  induction tail generalizing first with
  | nil => exact .done halt
  | cons next tail ih =>
      obtain ⟨edge, rest⟩ := List.isChain_cons_cons.mp transitions
      have ranges' : ∀ row ∈ next :: tail, InRange (W := W) row :=
        fun row member => ranges row (List.mem_cons_of_mem first member)
      exact .next (local_decode positive program secret first next _ _ edge)
        (ih next ranges' rest halt)

theorem encoding_soundness (positive : 0 < W) (statement : Statement W M)
    (encoded : EncodedWitness M) (constraints : Constraints statement encoded) :
    ∃ witness, ValidExecution positive statement witness := by
  let secret : Fin W := ⟨encoded.secret, constraints.secret_range⟩
  let final := decode (lastRow encoded.first encoded.tail)
    (constraints.ranges _ (lastRow_mem _ _))
  refine ⟨⟨secret, encoded.tail.length, final⟩, constraints.bound, ?_, ?_, ?_⟩
  · have execution := trace_decode positive statement.program secret encoded.first encoded.tail
      constraints.ranges constraints.transitions constraints.halt
    have start : decode encoded.first (constraints.ranges _ (by simp)) = initial statement :=
      encode_injective constraints.initial
    rw [start] at execution
    exact execution
  · exact Fin.ext constraints.output
  · exact funext (fun a => Fin.ext (congrFun constraints.memory a))

theorem execution_rows (positive : 0 < W) (program : List (Instruction W M)) (secret : Fin W)
    {k : Nat} {state final : State W M} (execution : Executes positive program secret k state final) :
    ∃ tail : List (Row M), tail.length = k ∧
      (∀ row ∈ encode state :: tail, InRange (W := W) row) ∧
      List.IsChain (Local program secret.val) (encode state :: tail) ∧
      lastRow (encode state) tail = encode final ∧ program[final.pc]? = some .halt := by
  induction execution with
  | done halt =>
      refine ⟨[], rfl, ?_, .singleton _, rfl, halt⟩
      intro row member
      rw [List.mem_singleton] at member
      subst row
      exact encode_range _
  | @next k state next final step rest ih =>
      obtain ⟨tail, length, ranges, transitions, last, halt⟩ := ih
      refine ⟨encode next :: tail, by simp [length], ?_, ?_, last, halt⟩
      · intro row member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ encode_range state
        · exact ranges row member
      · exact List.isChain_cons_cons.mpr
          ⟨(local_iff_step positive program secret state next).mpr step, transitions⟩

theorem encoding_completeness (positive : 0 < W) (statement : Statement W M)
    (witness : Witness W M) (valid : ValidExecution positive statement witness) :
    ∃ encoded, Constraints statement encoded := by
  obtain ⟨bound, execution, output, memory⟩ := valid
  obtain ⟨tail, length, ranges, transitions, last, halt⟩ := execution_rows positive _ _ execution
  refine ⟨⟨witness.secret.val, encode (initial statement), tail⟩, witness.secret.isLt, rfl,
    length ▸ bound, ranges, transitions, ?_, ?_, ?_⟩
  · change statement.program[(lastRow (encode (initial statement)) tail).pc]? = _
    rw [last]; exact halt
  · change (lastRow (encode (initial statement)) tail).acc = _
    rw [last]; exact congrArg Fin.val output
  · change (lastRow (encode (initial statement)) tail).memory = _
    rw [last]; exact congrArg (fun m => fun a => (m a).val) memory

theorem encoding_adequacy (positive : 0 < W) (statement : Statement W M) :
    (∃ encoded, Constraints statement encoded) ↔ ∃ witness, ValidExecution positive statement witness :=
  ⟨fun ⟨encoded, h⟩ => encoding_soundness positive statement encoded h,
    fun ⟨witness, h⟩ => encoding_completeness positive statement witness h⟩

theorem encoding_reduction (positive : 0 < W) (statement : Statement W M) :
    PIR.Relation.ReductionContract
      (fun s => ∃ witness, ValidExecution positive s witness)
      (fun s => ∃ encoded, Constraints s encoded) statement statement False :=
  ⟨fun satisfying => Or.inl ((encoding_adequacy positive statement).mp satisfying)⟩

end Composition.Machine

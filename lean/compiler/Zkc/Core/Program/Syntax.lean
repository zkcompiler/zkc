module

public import Zkc.Core.Program.Identity

@[expose] public section

/-!
The program by names, for any operations and any performers: the form of what a frontend gives
to the core.

One first-order syntax, generic in the operation and in who performs. A region is a list of
instructions and an exit. An instruction is an operation (its results, the operation, its
operands) or one of the forms of control (a guard, a choice, a case analysis, a loop, a
block, an attempt), each with its key and its nested regions; the control is written once here, and a
dialect lists only its operations. The key is the producer's: it is the key of the event, the
block or the application that the instruction is. A name is a number; a definition binds each of
its names at one place, and a use refers to that place. A nested region sees the names around it.
Instructions and regions by names are decided equal part by part (`Instruction.decideEq`,
`Region.decideEq`), so that stored programs are compared whole. Nothing here is about a dialect or
the vocabulary: the operations of the three dialects by names and the program by names of them
are in `Program/NamedProgram.lean`.
-/

namespace Zkc.Core

/-- How often a loop runs, by names: a written number of times, or as often as the value of a
name says. -/
inductive Repeat where
  | fixed (n : Nat)
  | count (name : Name)
deriving DecidableEq, Repr

mutual
  /-- An instruction by names. `Who` is who performs a form of control: nobody in a function,
  roles in a protocol or a role program. The region of a loop has the iteration number and
  the carried values as its inputs, and exits with the carried values and one value of each
  collected type; the loop's results are the last carried values and the collections. -/
  inductive Instruction (Op Who : Type) where
    | op (key : Key) (results : List Name) (o : Op) (operands : List Name)
    | guard (key : Key) (who : Who) (condition : Name) (why : Reason)
    | choose (key : Key) (who : Who) (condition : Name) (results : List Name)
        (onTrue onFalse : Region Op Who)
    | cases (key : Key) (who : Who) (subject : Name) (results : List Name)
        (arms : List (Region Op Who))
    | loop (key : Key) (who : Who) (times : Repeat) (carried : List Name) (results : List Name)
        (body : Region Op Who)
    | block (key : Key) (number : Nat) (results : List Name) (body : Region Op Who)
    /-- An attempt that `who` own: the input of its body is the number of the attempt; the
    results are what the body exits with. -/
    | attempt (key : Key) (who : Who) (results : List Name) (body : Region Op Who)
  inductive Region (Op Who : Type) where
    | mk (inputs : List Name) (body : List (Instruction Op Who)) (exit : List Name)
end

/-! ## Equality of stored programs

The handler that derives a decision of equality does not apply to instructions and regions,
which are mutual and nested; the decision is written here: two instructions, or two regions, are
compared part by part, and they are equal exactly when they are found the same. -/

section
variable {Op Who : Type} [DecidableEq Op] [DecidableEq Who]

mutual
  /-- Whether two instructions by names are the same, part by part. -/
  def Instruction.same : Instruction Op Who → Instruction Op Who → Bool
    | .op key results o operands, .op key' results' o' operands' =>
        decide (key = key') && decide (results = results') && decide (o = o') &&
          decide (operands = operands')
    | .guard key who condition why, .guard key' who' condition' why' =>
        decide (key = key') && decide (who = who') && decide (condition = condition') &&
          decide (why = why')
    | .choose key who condition results onTrue onFalse,
        .choose key' who' condition' results' onTrue' onFalse' =>
        decide (key = key') && decide (who = who') && decide (condition = condition') &&
          decide (results = results') && Region.same onTrue onTrue' &&
          Region.same onFalse onFalse'
    | .cases key who subject results arms, .cases key' who' subject' results' arms' =>
        decide (key = key') && decide (who = who') && decide (subject = subject') &&
          decide (results = results') && Region.sameAll arms arms'
    | .loop key who times carried results body, .loop key' who' times' carried' results' body' =>
        decide (key = key') && decide (who = who') && decide (times = times') &&
          decide (carried = carried') && decide (results = results') && Region.same body body'
    | .block key number results body, .block key' number' results' body' =>
        decide (key = key') && decide (number = number') && decide (results = results') &&
          Region.same body body'
    | .attempt key who results body, .attempt key' who' results' body' =>
        decide (key = key') && decide (who = who') && decide (results = results') &&
          Region.same body body'
    | _, _ => false
  /-- Whether two lists of instructions are the same, instruction by instruction. -/
  def Instruction.sameAll : List (Instruction Op Who) → List (Instruction Op Who) → Bool
    | [], [] => true
    | i :: is, i' :: is' => Instruction.same i i' && Instruction.sameAll is is'
    | _, _ => false
  /-- Whether two regions by names are the same, part by part. -/
  def Region.same : Region Op Who → Region Op Who → Bool
    | .mk inputs body exit, .mk inputs' body' exit' =>
        decide (inputs = inputs') && Instruction.sameAll body body' && decide (exit = exit')
  /-- Whether two lists of regions are the same, region by region. -/
  def Region.sameAll : List (Region Op Who) → List (Region Op Who) → Bool
    | [], [] => true
    | r :: rs, r' :: rs' => Region.same r r' && Region.sameAll rs rs'
    | _, _ => false
end

mutual
  /-- Instructions found the same are equal. -/
  theorem Instruction.eq_of_same :
      ∀ (i i' : Instruction Op Who), Instruction.same i i' = true → i = i'
    | .op .., i', h => by
        cases i' with
        | op =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
            rfl
        | _ => simp [Instruction.same] at h
    | .guard .., i', h => by
        cases i' with
        | guard =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
            rfl
        | _ => simp [Instruction.same] at h
    | .choose _ _ _ _ onTrue onFalse, i', h => by
        cases i' with
        | choose =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, yes⟩, no⟩ := h
            rw [Region.eq_of_same onTrue _ yes, Region.eq_of_same onFalse _ no]
        | _ => simp [Instruction.same] at h
    | .cases _ _ _ _ arms, i', h => by
        cases i' with
        | cases =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, all⟩ := h
            rw [Region.eq_of_sameAll arms _ all]
        | _ => simp [Instruction.same] at h
    | .loop _ _ _ _ _ body, i', h => by
        cases i' with
        | loop =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, inner⟩ := h
            rw [Region.eq_of_same body _ inner]
        | _ => simp [Instruction.same] at h
    | .block _ _ _ body, i', h => by
        cases i' with
        | block =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, inner⟩ := h
            rw [Region.eq_of_same body _ inner]
        | _ => simp [Instruction.same] at h
    | .attempt _ _ _ body, i', h => by
        cases i' with
        | attempt =>
            simp only [Instruction.same, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, inner⟩ := h
            rw [Region.eq_of_same body _ inner]
        | _ => simp [Instruction.same] at h
  /-- Lists of instructions found the same are equal. -/
  theorem Instruction.eq_of_sameAll :
      ∀ (is is' : List (Instruction Op Who)), Instruction.sameAll is is' = true → is = is'
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [Instruction.sameAll] at h
    | _ :: _, [], h => by simp [Instruction.sameAll] at h
    | i :: is, _ :: _, h => by
        simp only [Instruction.sameAll, Bool.and_eq_true] at h
        rw [Instruction.eq_of_same i _ h.1, Instruction.eq_of_sameAll is _ h.2]
  /-- Regions found the same are equal. -/
  theorem Region.eq_of_same : ∀ (r r' : Region Op Who), Region.same r r' = true → r = r'
    | .mk _ body _, .mk _ _ _, h => by
        simp only [Region.same, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, all⟩, rfl⟩ := h
        rw [Instruction.eq_of_sameAll body _ all]
  /-- Lists of regions found the same are equal. -/
  theorem Region.eq_of_sameAll :
      ∀ (rs rs' : List (Region Op Who)), Region.sameAll rs rs' = true → rs = rs'
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [Region.sameAll] at h
    | _ :: _, [], h => by simp [Region.sameAll] at h
    | r :: rs, _ :: _, h => by
        simp only [Region.sameAll, Bool.and_eq_true] at h
        rw [Region.eq_of_same r _ h.1, Region.eq_of_sameAll rs _ h.2]
end

mutual
  /-- An instruction is found the same as itself. -/
  theorem Instruction.same_self : ∀ (i : Instruction Op Who), Instruction.same i i = true
    | .op .. => by simp only [Instruction.same, decide_true, Bool.and_self]
    | .guard .. => by simp only [Instruction.same, decide_true, Bool.and_self]
    | .choose _ _ _ _ onTrue onFalse => by
        simp only [Instruction.same, decide_true, Bool.true_and, Region.same_self onTrue,
          Region.same_self onFalse]
    | .cases _ _ _ _ arms => by
        simp only [Instruction.same, decide_true, Bool.true_and, Region.same_self_all arms]
    | .loop _ _ _ _ _ body => by
        simp only [Instruction.same, decide_true, Bool.true_and, Region.same_self body]
    | .block _ _ _ body => by
        simp only [Instruction.same, decide_true, Bool.true_and, Region.same_self body]
    | .attempt _ _ _ body => by
        simp only [Instruction.same, decide_true, Bool.true_and, Region.same_self body]
  /-- A list of instructions is found the same as itself. -/
  theorem Instruction.same_self_all : ∀ (is : List (Instruction Op Who)),
      Instruction.sameAll is is = true
    | [] => by simp only [Instruction.sameAll]
    | i :: is => by
        simp only [Instruction.sameAll, Instruction.same_self i, Instruction.same_self_all is,
          Bool.and_self]
  /-- A region is found the same as itself. -/
  theorem Region.same_self : ∀ (r : Region Op Who), Region.same r r = true
    | .mk _ body _ => by
        simp only [Region.same, decide_true, Instruction.same_self_all body, Bool.and_self]
  /-- A list of regions is found the same as itself. -/
  theorem Region.same_self_all : ∀ (rs : List (Region Op Who)), Region.sameAll rs rs = true
    | [] => by simp only [Region.sameAll]
    | r :: rs => by
        simp only [Region.sameAll, Region.same_self r, Region.same_self_all rs, Bool.and_self]
end

/-- Instructions by names are equal exactly when they are found the same. -/
instance Instruction.decideEq : DecidableEq (Instruction Op Who) := fun i i' =>
  decidable_of_iff (Instruction.same i i' = true)
    ⟨Instruction.eq_of_same i i', fun same => same ▸ Instruction.same_self i⟩

/-- Regions by names are equal exactly when they are found the same. -/
instance Region.decideEq : DecidableEq (Region Op Who) := fun r r' =>
  decidable_of_iff (Region.same r r' = true)
    ⟨Region.eq_of_same r r', fun same => same ▸ Region.same_self r⟩

end

end Zkc.Core

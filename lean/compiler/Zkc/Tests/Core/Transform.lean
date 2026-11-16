import Zkc.Core.Admission.Programs
import Zkc.Core.Value.Passes
import Zkc.Tests.Core.Facts

/-!
Transformations of functions as checked steps, on functions written by names, run by the kernel.

A function with unused and repeated operations is transformed twice by the untrusted passes:
`removeUnused`, then `shareRepeated` of what it gave. Each stored result is compared whole with
what is expected, `transform` accepts each step, and `transform_then` composes the two. Then the
refusals, each whole: a target that elaboration refuses, a target that the check of facts
refuses (an operation with a domain moved above the guard that justified it), a target that
elaborates and passes the check of facts but is not decided (two guards exchanged), and a
source that is not accepted. A control: a target that computes another result (an operand
replaced by another) is not decided; a target with the operands of a sum exchanged is accepted.

Last, a program of two functions whose first, called by the second, is replaced by what
`removeUnused` gives: the two programs follow one another (`Defs.follows`), and
`Defs.follows_sound` gives that the caller means what it meant. A control: replacing the first
function by one that computes another result, the programs do not follow.
-/

namespace Zkc.Core.TransformTests

open FactsTests (field F plus times fieldRow unjustified place)

-- What a step and the check of facts return are compared whole.
deriving instance DecidableEq for TransformRefusal
deriving instance DecidableEq for Except

/-! ## Stored functions compared whole

The handler that derives a decision of equality does not apply to instructions and regions,
which are mutual and nested; the decision is written here. -/

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

/-- Regions by names are equal exactly when they are found the same. -/
instance Region.decideEq : DecidableEq (Region Op Who) := fun r r' =>
  decidable_of_iff (Region.same r r' = true)
    ⟨Region.eq_of_same r r', fun same => same ▸ Region.same_self r⟩

end

/-- The refusal of a step; nothing when it is accepted. -/
def refusal {fns : List (FnHeader field)} {hdr : FnHeader field} :
    Except (TransformRefusal field) (Transformed field fns hdr) → Option (TransformRefusal field)
  | .ok _ => none
  | .error refused => some refused

/-- What a step accepted; nothing when it refuses. -/
def accepted? {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- A result that something was accepted from is that thing, accepted. -/
theorem ok_of_accepted {ε α : Type} : ∀ {r : Except ε α} (found : (accepted? r).isSome = true),
    r = .ok ((accepted? r).get found)
  | .ok _, _ => rfl
  | .error _, found => nomatch found

/-! ## Two steps -/

/-- A function with the key 1 of two naturals and a truth value, which can stop. -/
def header : FnHeader field := ⟨⟨1⟩, [.nat, .nat, .bool], [.nat], true, none⟩

/-- `x + y`, a product that only an unused product uses, a guard, `x + y` again, a loop that
computes `x + y` again and a square that nothing uses, and the product of `x + y` with what the
loop gives. -/
def source : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .op ⟨1⟩ [10] plus [0, 1],
  .op ⟨2⟩ [11] times [0, 1],
  .guard ⟨3⟩ () 2 .reject,
  .op ⟨4⟩ [12] plus [0, 1],
  .loop ⟨5⟩ () (.fixed 2) [12] [13] (.mk [20, 21] [
    .op ⟨6⟩ [22] plus [0, 1],
    .op ⟨7⟩ [23] times [21, 21],
    .op ⟨8⟩ [24] plus [21, 22]] [24]),
  .op ⟨9⟩ [14] times [10, 13],
  .op ⟨10⟩ [15] times [11, 11]] [14]

/-- What `removeUnused` gives: the unused square inside the loop, the unused product at the end,
and then the product that only it used, are dropped; the guard and the loop are kept. -/
def withoutUnused : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .op ⟨1⟩ [10] plus [0, 1],
  .guard ⟨3⟩ () 2 .reject,
  .op ⟨4⟩ [12] plus [0, 1],
  .loop ⟨5⟩ () (.fixed 2) [12] [13] (.mk [20, 21] [
    .op ⟨6⟩ [22] plus [0, 1],
    .op ⟨8⟩ [24] plus [21, 22]] [24]),
  .op ⟨9⟩ [14] times [10, 13]] [14]

/-- What `shareRepeated` gives of that: `x + y` once, its later computations dropped, after the
guard and inside the loop, their results renamed to its result. -/
def shared : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .op ⟨1⟩ [10] plus [0, 1],
  .guard ⟨3⟩ () 2 .reject,
  .loop ⟨5⟩ () (.fixed 2) [10] [13] (.mk [20, 21] [
    .op ⟨8⟩ [24] plus [21, 10]] [24]),
  .op ⟨9⟩ [14] times [10, 13]] [14]

example : removeUnused [] source = withoutUnused := by decide +kernel

example : shareRepeated [] (removeUnused [] source) = shared := by decide +kernel

/-- The first step, accepted. -/
def firstStep : Transformed field [] header :=
  (accepted? (transform [] header source (removeUnused [] source))).get (by decide +kernel)

/-- The second step, from what the first gave, accepted. -/
def secondStep : Transformed field [] header :=
  (accepted? (transform [] header (removeUnused [] source)
    (shareRepeated [] (removeUnused [] source)))).get (by decide +kernel)

/-- The two steps compose: the target of the first is the source of the second, and the source
of the first means what the target of the second means. -/
example : firstStep.target = secondStep.source ∧ firstStep.source.SameAs secondStep.target :=
  transform_then (ok_of_accepted (by decide +kernel)) (ok_of_accepted (by decide +kernel))

/-! ## Refusals -/

/-- A function with the key 1 of two naturals. -/
def sum : FnHeader field := ⟨⟨1⟩, [.nat, .nat], [.nat], false, none⟩

/-- `x + y`. -/
def sumBody : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10]

/-- A target that elaboration refuses: an operand that is not in scope. -/
example : refusal (transform [] sum sumBody (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 5]] [10])) =
    some (.target [⟨.scope, place 1, .name 5⟩]) := by
  decide +kernel

/-- A function with the key 1 of a field element, which can stop. -/
def inverse : FnHeader field := ⟨⟨1⟩, [F], [F], true, none⟩

/-- A target that the check of facts refuses: the inverse moved above the guard that it is not
zero. -/
example : refusal (transform [] inverse
    (.mk [0] [
      .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
      .guard ⟨2⟩ () 10 .refused,
      .op ⟨3⟩ [11] (fieldRow .inverse) [0]] [11])
    (.mk [0] [
      .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
      .op ⟨3⟩ [11] (fieldRow .inverse) [0],
      .guard ⟨2⟩ () 10 .refused] [11])) =
    some (.target [unjustified 3 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]]) := by
  decide +kernel

/-- A function with the key 1 of two truth values, which can stop. -/
def twoGuards : FnHeader field := ⟨⟨1⟩, [.bool, .bool], [], true, none⟩

/-- A target that elaborates and passes the check of facts, but is not decided: two guards
exchanged, so that which one stops first is another. -/
example : refusal (transform [] twoGuards
    (.mk [0, 1] [.guard ⟨1⟩ () 0 .reject, .guard ⟨2⟩ () 1 .reject] [])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .guard ⟨1⟩ () 0 .reject] [])) =
    some .undecided := by
  decide +kernel

/-- A source that is not accepted: the inverse with nothing known of its operand. The target is
not looked at. -/
example : refusal (transform [] ⟨⟨1⟩, [F], [F], false, none⟩
    (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10])
    (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10])) =
    some (.source [unjustified 1 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]]) := by
  decide +kernel

/-- Control: a target that computes another result, `x + x` for `x + y`, is not decided. -/
example : refusal (transform [] sum sumBody (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 0]] [10])) =
    some .undecided := by
  decide +kernel

/-- A target that writes `y + x` for `x + y` is accepted: addition commutes. -/
example : refusal (transform [] sum sumBody (.mk [0, 1] [.op ⟨1⟩ [10] plus [1, 0]] [10])) =
    none := by
  decide +kernel

/-! ## A program whose called function is replaced -/

/-- The callee, with the key 1: of two naturals. -/
def calleeHeader : FnHeader field := ⟨⟨1⟩, [.nat, .nat], [.nat], false, none⟩

/-- The caller, with the key 2: of one natural. -/
def callerHeader : FnHeader field := ⟨⟨2⟩, [.nat], [.nat], false, none⟩

/-- The callee: `x + y`, with a product that nothing uses. -/
def calleeBody : Region (LocalRaw field) Unit :=
  .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1], .op ⟨2⟩ [11] times [0, 1]] [10]

/-- The caller: the callee on `(x, x)`, plus `x`. -/
def callerBody : Region (LocalRaw field) Unit :=
  .mk [0] [.op ⟨1⟩ [10] (.call ⟨1⟩) [0, 0], .op ⟨2⟩ [11] plus [10, 0]] [11]

/-- A function by names, elaborated against the headers before it; nothing when it does not
elaborate. -/
def typed (fns : List (FnHeader field)) (hdr : FnHeader field)
    (region : Region (LocalRaw field) Unit) :
    Option ((inputs : Names hdr.ins) × (body : Fn field fns hdr inputs) ×' FnConditions body) :=
  match elabFn fns hdr region with
  | .ok elaborated => some elaborated
  | .error _ => none

/-- The callee as written, elaborated. -/
def calleeBefore := (typed [] calleeHeader calleeBody).get (by decide +kernel)

/-- The callee without its unused product, elaborated. -/
def calleeAfter := (typed [] calleeHeader (removeUnused [] calleeBody)).get (by decide +kernel)

/-- A callee that computes another result, `x + x`, elaborated. -/
def calleeOther :=
  (typed [] calleeHeader (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 0]] [10])).get (by decide +kernel)

/-- The caller, elaborated against the callee's header. -/
def caller := (typed [calleeHeader] callerHeader callerBody).get (by decide +kernel)

/-- The program as written. -/
def before : Defs field ⟨[callerHeader, calleeHeader], []⟩ :=
  .fn callerHeader caller.1 caller.2.1 caller.2.2
    (.fn calleeHeader calleeBefore.1 calleeBefore.2.1 calleeBefore.2.2 .nil)

/-- The program with the callee replaced by what `removeUnused` gives. -/
def after : Defs field ⟨[callerHeader, calleeHeader], []⟩ :=
  .fn callerHeader caller.1 caller.2.1 caller.2.2
    (.fn calleeHeader calleeAfter.1 calleeAfter.2.1 calleeAfter.2.2 .nil)

/-- The program with the callee replaced by one that computes another result. -/
def other : Defs field ⟨[callerHeader, calleeHeader], []⟩ :=
  .fn callerHeader caller.1 caller.2.1 caller.2.2
    (.fn calleeHeader calleeOther.1 calleeOther.2.1 calleeOther.2.2 .nil)

example : removeUnused [] calleeBody = .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10] := by
  decide +kernel

/-- The functions of the second program follow those of the first, one by one. -/
example : Defs.follows before after = true := by decide +kernel

/-- The program as written is accepted by the check of facts, with no bound. -/
theorem before_accepted : Defs.Accepted before [] :=
  ⟨[], [], by decide +kernel, ⟨[], [], by decide +kernel, rfl, rfl⟩, rfl⟩

/-- The program with the callee replaced is accepted too. -/
theorem after_accepted : Defs.Accepted after [] :=
  ⟨[], [], by decide +kernel, ⟨[], [], by decide +kernel, rfl, rfl⟩, rfl⟩

/-- The caller means what it meant, on every valid input, in every model: it calls the replaced
callee on valid values, where the callee means the same. -/
example (M : Model field) (ins : HList M.Val callerHeader.ins) (valid : ins.All M.Valid) :
    Defs.fnTable M after callerHeader .head ins = Defs.fnTable M before callerHeader .head ins :=
  Defs.follows_sound before after (by decide +kernel) before_accepted after_accepted
    (by decide +kernel) M callerHeader .head ins valid

/-- Control: a callee replaced by one that computes another result does not follow. -/
example : Defs.follows before other = false := by decide +kernel

end Zkc.Core.TransformTests

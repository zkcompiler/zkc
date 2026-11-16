import Zkc.Core.Admission.Programs
import Zkc.Core.Transform.Passes
import Zkc.Tests.Core.Facts
import Zkc.Tests.Core.Following

/-!
Transformations of functions as checked steps, on functions written by names, run by the kernel.

The controls on meanings run in a model written here, the field of two elements.

A function with unused and repeated operations is transformed twice by the untrusted passes:
`removeUnused`, then `shareRepeated` of what it gave. Each stored result is compared whole with
what is expected, `transform` accepts each step, and `transform_then` composes the two. The two
passes again on a function with a choice, a case analysis and a block, with unused and repeated
operations inside and around them: each stored result compared whole, each step accepted. Then
one function whose loop runs as often as a value with an upper end, and one step from it, with
each theorem applied to them: `checkFacts_sound` and `AcceptedFn.safe` to the function, and
`transform_target_safe`, `transform_target_bounds` (the loop of the target bounded as the step
recorded), `transform_erases` and `transform_both` (with a second step from the same source) to
the step.

Then the refusals, each whole: a target that elaboration refuses. Three targets that follow their
source with no place that differs (`FollowingTests.decided`) and that the analysis refuses while
it follows (`FollowingTests.safelyFollows`), since a value has no place in the skeleton and its
requirements are decided where the target evaluates it: an operation with a domain moved above
the guard that justified it, read before a choice in whose region it was justified, and read
before a loop in whose body a guard justified it; the step refuses each with the target's
refusal. The control on the first: in the field of two elements, on the input zero, that target
stops `undefined`, and the source stops at its guard with its reason. A target that is refused
while it follows and also differs, refused with both. A target that elaborates but differs from
its source (two guards exchanged), refused with the place where it differs, and a source that is
not accepted. A control: a target that computes another result (an operand replaced by another)
differs where it returns; a target with the operands of a sum exchanged is accepted.

Last, a program of two functions whose first, called by the second, is replaced by what
`removeUnused` gives: the functions of the second follow those of the first
(`Defs.functionsFollow`), and `Defs.functionsFollow_sound` gives that the caller means what it
meant. A control: replacing the first function by one that computes another result, the
functions do not follow, and that function's meaning is another on a concrete input.
-/
namespace Zkc.Core.TransformTests

open FactsTests (field F plus times natural element toNat fieldRow natOrTruth unjustified place)
open FollowingTests (noCallees noCallees_callees)

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

/-- A function by names, elaborated against the headers before it; nothing when it does not
elaborate. -/
def typed (fns : List (FnHeader field)) (hdr : FnHeader field)
    (region : Region (LocalRaw field) Unit) :
    Option ((inputs : Names hdr.ins) × (body : Fn field fns hdr inputs) ×' FnConditions body) :=
  match elabFn fns hdr region with
  | .ok elaborated => some elaborated
  | .error _ => none

/-! ## The field of two elements

A model of the vocabulary with a field, in which the controls on meanings run: an element is a
truth value, `true` the element that is not zero. -/

/-- The carriers of the field of two elements: every element is valid, and a literal is its
number modulo two. -/
def twoCarriers : Carriers field where
  Carrier _ := Bool
  valid _ _ := True
  literal _ n := some (n % 2 == 1)

/-- The rows of the field of two elements: equality, addition (exclusive or), multiplication
(and), whether an element is not zero, and the inverse, which is defined only on the element that
is not zero and is that element. -/
def twoApply : (row : FactsTests.FieldRow) → (signature : RowSignature Unit FactsTests.FieldRow) →
    field.row row = some signature → HList (Ty.Val twoCarriers) signature.ins →
    Option (HList (Ty.Val twoCarriers) signature.outs)
  | .equal, _, rfl, .cons x (.cons y .nil) => some (.cons (!(Bool.xor x y)) .nil)
  | .add, _, rfl, .cons x (.cons y .nil) => some (.cons (Bool.xor x y) .nil)
  | .mul, _, rfl, .cons x (.cons y .nil) => some (.cons (Bool.and x y) .nil)
  | .isNonzero, _, rfl, .cons x .nil => some (.cons x .nil)
  | .inverse, _, rfl, .cons x .nil => bif x then some (.cons x .nil) else none

/-- The domains of the rows of the field of two elements: the inverse's is the element that is not
zero; every other row is total. -/
def twoInDomain : (row : FactsTests.FieldRow) →
    (signature : RowSignature Unit FactsTests.FieldRow) → field.row row = some signature →
    HList (Ty.Val twoCarriers) signature.ins → Bool
  | .inverse, _, rfl, .cons x .nil => x
  | .equal, _, _, _ => true
  | .add, _, _, _ => true
  | .mul, _, _, _ => true
  | .isNonzero, _, _, _ => true

/-- The field of two elements. -/
def twoModel : Model field where
  toCarriers := twoCarriers
  apply := twoApply
  inDomain := twoInDomain
  defined row signature known args := by
    cases row <;> cases known
    all_goals first
      | (obtain ⟨x, y, rfl⟩ := HList.two args; cases x <;> cases y <;> rfl)
      | (obtain ⟨x, rfl⟩ := HList.one args; cases x <;> rfl)
  total row signature known args pure := by
    cases row <;> cases known
    all_goals first
      | rfl
      | cases pure
  decides row signature known domain restricted args := by
    cases row <;> cases known <;> cases restricted
    obtain ⟨x, rfl⟩ := HList.one args
    cases x <;> rfl
  keeps row signature known args outs _ applied := by
    cases row <;> cases known
    all_goals first
      | (obtain ⟨x, y, rfl⟩ := HList.two args; cases applied; exact ⟨trivial, trivial⟩)
      | (obtain ⟨x, rfl⟩ := HList.one args; cases x <;> cases applied <;> exact ⟨trivial, trivial⟩)
  literals _ _ _ := ⟨_, rfl, trivial⟩
  support law _ _ _ _ := nomatch law
  supported law _ _ _ _ _ _ := nomatch law

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

/-- The two steps compose: the source of the first means what the target of the second means. -/
example : firstStep.source.SameAs secondStep.target :=
  transform_then (ok_of_accepted (by decide +kernel)) (ok_of_accepted (by decide +kernel))

/-! ## Two steps on a function with regions -/

/-- A function with the key 1 of a truth value, a natural or a truth value, and two naturals. -/
def regionsHeader : FnHeader field := ⟨⟨1⟩, [.bool, natOrTruth, .nat, .nat], [.nat], false, none⟩

/-- `x + y`, and a product that nothing uses; a choice whose first region computes `x + y` again
and a square of it that nothing uses, and whose second gives zero; a case analysis whose first
arm adds the payload to `x + y` and computes `x + y` again, unused, and whose second arm computes
zero, unused, and gives `x + y` computed again; a block that adds what the choice and the case
analysis gave, computes `x + y` again, adds the two, and squares the first sum, unused; then
`x + y` again, added to what the block gave. -/
def regionsSource : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .op ⟨1⟩ [10] plus [2, 3],
  .op ⟨2⟩ [11] times [2, 3],
  .choose ⟨3⟩ () 0 [12]
    (.mk [] [
      .op ⟨4⟩ [20] plus [2, 3],
      .op ⟨5⟩ [21] times [20, 20]] [20])
    (.mk [] [.op ⟨6⟩ [22] (natural 0) []] [22]),
  .cases ⟨7⟩ () 1 [13]
    [.mk [30] [
       .op ⟨8⟩ [31] plus [30, 10],
       .op ⟨9⟩ [32] plus [2, 3]] [31],
     .mk [40] [
       .op ⟨10⟩ [41] (natural 0) [],
       .op ⟨11⟩ [42] plus [2, 3]] [42]],
  .block ⟨12⟩ 0 [14] (.mk [] [
    .op ⟨13⟩ [50] plus [12, 13],
    .op ⟨14⟩ [51] plus [2, 3],
    .op ⟨15⟩ [52] plus [50, 51],
    .op ⟨16⟩ [53] times [50, 50]] [52]),
  .op ⟨17⟩ [15] plus [2, 3],
  .op ⟨18⟩ [16] plus [14, 15]] [16]

/-- What `removeUnused` gives: the unused product before the choice, the unused square in its
first region, the unused `x + y` of the first arm and the unused zero of the second, and the
unused square in the block, are dropped; every region is walked, and the choice, the case
analysis and the block are kept. -/
def regionsWithoutUnused : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .op ⟨1⟩ [10] plus [2, 3],
  .choose ⟨3⟩ () 0 [12]
    (.mk [] [.op ⟨4⟩ [20] plus [2, 3]] [20])
    (.mk [] [.op ⟨6⟩ [22] (natural 0) []] [22]),
  .cases ⟨7⟩ () 1 [13]
    [.mk [30] [.op ⟨8⟩ [31] plus [30, 10]] [31],
     .mk [40] [.op ⟨11⟩ [42] plus [2, 3]] [42]],
  .block ⟨12⟩ 0 [14] (.mk [] [
    .op ⟨13⟩ [50] plus [12, 13],
    .op ⟨14⟩ [51] plus [2, 3],
    .op ⟨15⟩ [52] plus [50, 51]] [52]),
  .op ⟨17⟩ [15] plus [2, 3],
  .op ⟨18⟩ [16] plus [14, 15]] [16]

/-- What `shareRepeated` gives of that: `x + y` once, before the regions; its computations in the
first region of the choice, in the second arm, in the block and after the block are dropped, and
their results renamed to its result, in the regions' exits and in the operands after them. -/
def regionsShared : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .op ⟨1⟩ [10] plus [2, 3],
  .choose ⟨3⟩ () 0 [12]
    (.mk [] [] [10])
    (.mk [] [.op ⟨6⟩ [22] (natural 0) []] [22]),
  .cases ⟨7⟩ () 1 [13]
    [.mk [30] [.op ⟨8⟩ [31] plus [30, 10]] [31],
     .mk [40] [] [10]],
  .block ⟨12⟩ 0 [14] (.mk [] [
    .op ⟨13⟩ [50] plus [12, 13],
    .op ⟨15⟩ [52] plus [50, 10]] [52]),
  .op ⟨18⟩ [16] plus [14, 10]] [16]

example : removeUnused [] regionsSource = regionsWithoutUnused := by decide +kernel

example : shareRepeated [] regionsWithoutUnused = regionsShared := by decide +kernel

/-- The step from the source to what `removeUnused` gives, accepted. -/
example : refusal (transform [] regionsHeader regionsSource (removeUnused [] regionsSource)) =
    none := by
  decide +kernel

/-- The step from that to what `shareRepeated` gives, accepted. -/
example : refusal (transform [] regionsHeader regionsWithoutUnused
    (shareRepeated [] regionsWithoutUnused)) = none := by
  decide +kernel

/-! ## The theorems on one function and one step

One function whose loop runs as often as a value with an upper end, accepted by the check of
facts with that bound, and one step from it to what `removeUnused` gives: each theorem of a step,
and the soundness of the check of facts, applied to them in every model. -/

/-- A function with the key 1 of an index below 4 and a natural. -/
def boundedHeader : FnHeader field := ⟨⟨1⟩, [.fin 4, .nat], [.nat], false, none⟩

/-- `n := index as a natural`, the square of the natural, which nothing uses, and a loop as often
as `n` says, which adds the iteration number to what it carries from the natural. -/
def boundedSource : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 4) [0],
  .op ⟨2⟩ [11] times [1, 1],
  .loop ⟨3⟩ () (.count 10) [1] [12] (.mk [20, 21] [.op ⟨4⟩ [22] plus [21, 20]] [22])] [12]

/-- What `removeUnused` gives: the square dropped. -/
def boundedTarget : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 4) [0],
  .loop ⟨3⟩ () (.count 10) [1] [12] (.mk [20, 21] [.op ⟨4⟩ [22] plus [21, 20]] [22])] [12]

example : removeUnused [] boundedSource = boundedTarget := by decide +kernel

/-- The source with the sum in the loop written with its operands exchanged. -/
def boundedExchanged : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 4) [0],
  .op ⟨2⟩ [11] times [1, 1],
  .loop ⟨3⟩ () (.count 10) [1] [12] (.mk [20, 21] [.op ⟨4⟩ [22] plus [20, 21]] [22])] [12]

/-- The source, accepted by the check of facts. -/
def boundedFn : AcceptedFn field [] boundedHeader :=
  (accepted? (acceptFn [] boundedHeader boundedSource)).get (by decide +kernel)

/-- The step from the source to what `removeUnused` gives, accepted. -/
def boundedStep : Transformed field [] boundedHeader :=
  (accepted? (transform [] boundedHeader boundedSource boundedTarget)).get (by decide +kernel)

/-- The step from the source to the source with the sum exchanged, accepted. -/
def exchangedStep : Transformed field [] boundedHeader :=
  (accepted? (transform [] boundedHeader boundedSource boundedExchanged)).get (by decide +kernel)

/-- What `acceptFn` returned. -/
theorem boundedFn_accepted : acceptFn [] boundedHeader boundedSource = .ok boundedFn :=
  ok_of_accepted (by decide +kernel)

/-- What `transform` returned. -/
theorem boundedStep_accepted :
    transform [] boundedHeader boundedSource boundedTarget = .ok boundedStep :=
  ok_of_accepted (by decide +kernel)

/-- The loop runs at most 3 times, the upper end of the index: the check of facts gives that
bound at the loop, and so does the step for its target, while it follows. -/
example : boundedFn.bounds = [(place 3, 3)] ∧ boundedStep.target.bounds = [(place 3, 3)] := by
  decide +kernel

/-- The soundness of the check of facts, on the accepted function: on valid inputs its loop runs
at most 3 times, and it never stops `undefined` and returns valid values. -/
example (M : Model field) (ins : HList M.Val boundedHeader.ins) (valid : ins.All M.Valid) :
    boundedFn.body.EveryLoop (localSem M [] (noCallees M)) (fun _ _ => True)
        (Annotation.Bounded ⟨[(place 3, 3)]⟩ ⟨1⟩ none) [] []
        (Env.empty.extend boundedFn.inputs ins) ∧
      (boundedFn.body.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend boundedFn.inputs ins)).Every (fun _ _ => True)
        (fun outs => outs.All M.Valid) (· ≠ .undefined) :=
  checkFacts_sound (noCallees_callees M) ⟨1⟩ boundedFn.inputs boundedFn.body
    boundedFn.conditions.distinct
    (acceptFn_ok boundedFn_accepted).2
    [(place 3, 3)] (fun _ _ inside _ _ => by
      rw [show boundedFn.bounds = [(place 3, 3)] by decide +kernel]
      exact inside)
    ins valid

/-- An accepted function is safe (`AcceptedFn.safe`). -/
example (M : Model field) (ins : HList M.Val boundedHeader.ins) (valid : ins.All M.Valid) :
    (boundedFn.meaning M (noCallees M) ins).Every (fun _ _ => True)
      (fun outs => outs.All M.Valid) (· ≠ .undefined) :=
  AcceptedFn.safe boundedFn_accepted M (noCallees M) (noCallees_callees M) ins valid

/-- The target of the step is safe (`transform_target_safe`). -/
example (M : Model field) (ins : HList M.Val boundedHeader.ins) (valid : ins.All M.Valid) :
    (boundedStep.target.meaning M (noCallees M) ins).Every (fun _ _ => True)
      (fun outs => outs.All M.Valid) (· ≠ .undefined) :=
  transform_target_safe boundedStep_accepted M (noCallees M) (noCallees_callees M) ins valid

/-- The loop of the target runs at most as often as the bound that the step recorded for it
(`transform_target_bounds`). -/
example (M : Model field) (ins : HList M.Val boundedHeader.ins) (valid : ins.All M.Valid) :
    boundedStep.target.body.EveryLoop (localSem M [] (noCallees M)) (fun _ _ => True)
      (Annotation.Bounded ⟨[(place 3, 3)]⟩ ⟨1⟩ none) [] []
      (Env.empty.extend boundedStep.target.inputs ins) :=
  transform_target_bounds boundedStep_accepted M (noCallees M) (noCallees_callees M)
    [(place 3, 3)] (fun _ _ inside _ _ => by
      rw [show boundedStep.target.bounds = [(place 3, 3)] by decide +kernel]
      exact inside)
    ins valid

/-- The stored forms of what the step returns are what it was given (`transform_erases`). -/
example : eraseFn boundedStep.source.inputs boundedStep.source.body = boundedSource ∧
    eraseFn boundedStep.target.inputs boundedStep.target.body = boundedTarget :=
  transform_erases boundedStep_accepted

/-- Two steps from the one source: their targets, the source without the square and the source
with the sum exchanged, have the same meaning (`transform_both`). -/
example : boundedStep.target.SameAs exchangedStep.target :=
  transform_both boundedStep_accepted (ok_of_accepted (by decide +kernel))

/-! ## Refusals -/

/-- A function with the key 1 of two naturals. -/
def sum : FnHeader field := ⟨⟨1⟩, [.nat, .nat], [.nat], false, none⟩

/-- `x + y`. -/
def sumBody : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10]

/-- A target that elaboration refuses: an operand that is not in scope. -/
example : refusal (transform [] sum sumBody (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 5]] [10])) =
    some (.target [⟨.scope, place 1, .name 5⟩] []) := by
  decide +kernel

/-! ### A value read before what justifies it

A value has no place in the skeleton, so a target may read an operation with a domain where the
source does not justify it and still follow with no place that differs. The analysis decides the
value's requirements where the target evaluates it, while it follows, and refuses it there. Each
pair is one source and one target: the target follows the source with no place that differs
(`FollowingTests.decided`), the whole verdict of following refuses it
(`FollowingTests.safelyFollows`), and `transform` refuses the target, with its whole refusal. -/

/-- A function with the key 1 of a field element, which can stop. -/
def inverse : FnHeader field := ⟨⟨1⟩, [F], [F], true, none⟩

/-- The inverse after the guard that the element is not zero. -/
def inverseGuarded : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .guard ⟨2⟩ () 10 .refused,
  .op ⟨3⟩ [11] (fieldRow .inverse) [0]] [11]

/-- The inverse moved above that guard. -/
def inverseAboveGuard : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .op ⟨3⟩ [11] (fieldRow .inverse) [0],
  .guard ⟨2⟩ () 10 .refused] [11]

/-- The inverse moved above the guard follows with no place that differs: the guard is the
skeleton's entry, and the inverse a value of the table. The whole verdict refuses it. -/
example : FollowingTests.decided [] [F] [F] true true inverseGuarded inverseAboveGuard =
      some true ∧
    FollowingTests.safelyFollows [] [F] [F] true true inverseGuarded inverseAboveGuard =
      some false := by
  decide +kernel

/-- And the step refuses the target, while it follows: the inverse moved above the guard that it
is not zero. -/
example : refusal (transform [] inverse inverseGuarded inverseAboveGuard) =
    some (.target [unjustified 3 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]] []) := by
  decide +kernel

/-- The inverse after its guard, elaborated. -/
def inverseGuardedTyped := (typed [] inverse inverseGuarded).get (by decide +kernel)

/-- The inverse moved above its guard, elaborated. -/
def inverseAboveGuardTyped := (typed [] inverse inverseAboveGuard).get (by decide +kernel)

/-- Control: what the refusal keeps out. In the field of two elements, on the input zero, the
target stops `undefined`, at the inverse that it reads before its guard... -/
example : inverseAboveGuardTyped.2.1.denote (localSem twoModel [] (noCallees twoModel)) []
    (Env.empty.extend inverseAboveGuardTyped.1 (.cons false .nil)) = .halt .undefined := by
  rfl

/-- ...while the source stops at its guard, with its reason. -/
example : inverseGuardedTyped.2.1.denote (localSem twoModel [] (noCallees twoModel)) []
    (Env.empty.extend inverseGuardedTyped.1 (.cons false .nil)) =
      .halt (.declared .refused ⟨[], ⟨2⟩⟩) := by
  rfl

/-- A target that is refused while it follows and also differs, at a guard with another key: the
refusal gives both, the refusal of the analysis and the place where the target differs. -/
example : refusal (transform [] inverse inverseGuarded (.mk [0] [
    .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
    .op ⟨3⟩ [11] (fieldRow .inverse) [0],
    .guard ⟨4⟩ () 10 .refused] [11])) =
    some (.target [unjustified 3 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]] [place 4]) := by
  decide +kernel

/-- A function with the key 1 of a field element, which cannot stop. -/
def inverseOrZero : FnHeader field := ⟨⟨1⟩, [F], [F], false, none⟩

/-- The inverse in the region of a choice that runs when the element is not zero, and zero in
the other region. -/
def inverseInRegion : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .choose ⟨2⟩ () 10 [11]
    (.mk [] [.op ⟨3⟩ [20] (fieldRow .inverse) [0]] [20])
    (.mk [] [.op ⟨4⟩ [21] (element 0) []] [21])] [11]

/-- The inverse read before the choice, and given by its first region. -/
def inverseBeforeChoice : Region (LocalRaw field) Unit := .mk [0] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .op ⟨3⟩ [20] (fieldRow .inverse) [0],
  .choose ⟨2⟩ () 10 [11]
    (.mk [] [] [20])
    (.mk [] [.op ⟨4⟩ [21] (element 0) []] [21])] [11]

/-- The inverse read before the choice follows with no place that differs: the first region gives
the same value of the table. The whole verdict refuses it. -/
example : FollowingTests.decided [] [F] [F] false false inverseInRegion inverseBeforeChoice =
      some true ∧
    FollowingTests.safelyFollows [] [F] [F] false false inverseInRegion inverseBeforeChoice =
      some false := by
  decide +kernel

/-- And the step refuses the target, while it follows: before the choice nothing is known of the
element. -/
example : refusal (transform [] inverseOrZero inverseInRegion inverseBeforeChoice) =
    some (.target [unjustified 3 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]] []) := by
  decide +kernel

/-- A function with the key 1 of a field element and a natural, which can stop. -/
def inverseRepeated : FnHeader field := ⟨⟨1⟩, [F, .nat], [F], true, none⟩

/-- A loop as often as the natural says, which may be no iteration, carrying a field element
from zero: its body guards that the input is not zero and gives the input's inverse. The inverse
is justified only by the guard in the body. -/
def inverseInLoop : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .op ⟨2⟩ [11] (element 0) [],
  .loop ⟨3⟩ () (.count 1) [11] [12] (.mk [20, 21] [
    .guard ⟨4⟩ () 10 .refused,
    .op ⟨5⟩ [22] (fieldRow .inverse) [0]] [22])] [12]

/-- The inverse read before the loop, which its body gives. -/
def inverseBeforeLoop : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .op ⟨2⟩ [11] (element 0) [],
  .op ⟨5⟩ [22] (fieldRow .inverse) [0],
  .loop ⟨3⟩ () (.count 1) [11] [12] (.mk [20, 21] [.guard ⟨4⟩ () 10 .refused] [22])] [12]

/-- The inverse read before the loop follows with no place that differs: the guard stays in the
body, and the body gives the same value of the table. On zero iterations and the element zero,
the source returns zero and the target stops `undefined`. The whole verdict refuses it. -/
example : FollowingTests.decided [] [F, .nat] [F] true true inverseInLoop inverseBeforeLoop =
      some true ∧
    FollowingTests.safelyFollows [] [F, .nat] [F] true true inverseInLoop inverseBeforeLoop =
      some false := by
  decide +kernel

/-- And the step refuses the target, while it follows: before the loop nothing is known of the
element. -/
example : refusal (transform [] inverseRepeated inverseInLoop inverseBeforeLoop) =
    some (.target [unjustified 5 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]] []) := by
  decide +kernel

/-! ### A target that differs, and a source not accepted -/

/-- A function with the key 1 of two truth values, which can stop. -/
def twoGuards : FnHeader field := ⟨⟨1⟩, [.bool, .bool], [], true, none⟩

/-- A target that elaborates but differs from its source: two guards exchanged, so that which one
stops first is another. It differs at its first guard, which is not the skeleton's next entry. -/
example : refusal (transform [] twoGuards
    (.mk [0, 1] [.guard ⟨1⟩ () 0 .reject, .guard ⟨2⟩ () 1 .reject] [])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .guard ⟨1⟩ () 0 .reject] [])) =
    some (.differs [place 2]) := by
  decide +kernel

/-- A source that is not accepted: the inverse with nothing known of its operand. The target is
not looked at. -/
example : refusal (transform [] ⟨⟨1⟩, [F], [F], false, none⟩
    (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10])
    (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10])) =
    some (.source [unjustified 1 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]]) := by
  decide +kernel

/-- Control: a target that computes another result, `x + x` for `x + y`, differs where it
returns. -/
example : refusal (transform [] sum sumBody (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 0]] [10])) =
    some (.differs [⟨⟨1⟩, [], none, none⟩]) := by
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
example : Defs.functionsFollow before after = true := by decide +kernel

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
  Defs.functionsFollow_sound before after (by decide +kernel) before_accepted after_accepted
    (by decide +kernel) M callerHeader .head ins valid

/-- Control: a callee replaced by one that computes another result does not follow. -/
example : Defs.functionsFollow before other = false := by decide +kernel

/-- And its meaning is another, in every model: on `(1, 2)` the callee as written returns 3, and
the one that replaces it 2. -/
example (M : Model field) :
    Defs.fnTable M other calleeHeader (.tail .head) (.cons (1 : Nat) (.cons (2 : Nat) .nil)) ≠
      Defs.fnTable M before calleeHeader (.tail .head)
        (.cons (1 : Nat) (.cons (2 : Nat) .nil)) := by
  intro same
  change (Process.done (.cons (2 : Nat) .nil) : Local (HList M.Val [.nat])) =
    .done (.cons (3 : Nat) .nil) at same
  simp at same

end Zkc.Core.TransformTests

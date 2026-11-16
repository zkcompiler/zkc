import Zkc.Core.Value.Local
import Zkc.Tests.Core.Facts

/-!
The decision that two functions mean the same, on functions written by names, elaborated and
decided by the kernel.

Each pair is two bodies of a function with the key 1 over the same callees, each elaborated
against them; the decision walks the second along the skeleton of the first. Accepted: a
repeated computation shared; two computations between guards in the other order, with one
computation that nothing uses; computations moved around guards that stay in their order; a
computation moved out of a loop; the same program with other names for its values; a call of a
function that cannot stop, shared; `x + y` against `y + x`, since addition commutes; a product
and a sum with their operands exchanged inside a loop after a guard. Refused: `x - y` against
`y - x`; `(x + y) + z` against `x + (y + z)` (associativity is not a law that the decision
knows); a row of the vocabulary with its operands exchanged; two guards in the other order; a
guard dropped; a call of a function that can stop moved across a guard; two loops against one
loop that computes the same; a different key on a guard. Then the theorem for functions, applied
to two pairs, the second of them `x + y` and `y + x`: the two processes are equal on valid
inputs.

Last, the two controls on the definitions of the value form: why following asks for leaves made
in order (`Skel.Fresh`), and why what follows an attempt runs only from an end of the attempt
that can return (`Skel.Runs.attempt`).
-/

namespace Zkc.Core.SameTests

open FactsTests (field F plus minus times natural fieldRow)

-- What the check of facts returns is compared whole.
deriving instance DecidableEq for Except

/-! ## The decision -/

/-- The decision on two bodies of a function with the key 1, the input and result types and the
callees given, each elaborated against the callees with whether it can stop: whether the second
follows the skeleton of the first; nothing when one of them does not elaborate. -/
def decided (fns : List (FnHeader field)) (ins outs : List field.Ty) (stops stops' : Bool)
    (body body' : Region (LocalRaw field) Unit) : Option Bool :=
  match elabFn fns ⟨⟨1⟩, ins, outs, stops, none⟩ body,
      elabFn fns ⟨⟨1⟩, ins, outs, stops', none⟩ body' with
  | .ok ⟨inputs, fn, _⟩, .ok ⟨inputs', fn', _⟩ =>
      some (same (localValueRules field fns) (localSkelRules field fns) inputs inputs' fn fn')
  | _, _ => none

/-- A callee with the key 9 from a natural to a natural, which can stop or cannot. -/
def callee (canStop : Bool) : FnHeader field := ⟨⟨9⟩, [.nat], [.nat], canStop, none⟩

/-- Two naturals and two truth values. -/
abbrev guarded : List field.Ty := [.nat, .nat, .bool, .bool]

/-! ## Accepted -/

/-- A repeated computation is one value. -/
example : decided [] [.nat, .nat] [.nat, .nat] false false
    (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1], .op ⟨2⟩ [11] plus [0, 1]] [10, 11])
    (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10, 10]) = some true := by
  decide +kernel

/-- Two computations between guards in the other order, with a computation that nothing uses. -/
example : decided [] guarded [.nat, .nat] true true
    (.mk [0, 1, 2, 3] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] plus [0, 1],
      .op ⟨3⟩ [11] times [0, 1],
      .guard ⟨4⟩ () 3 .reject] [10, 11])
    (.mk [0, 1, 2, 3] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨3⟩ [11] times [0, 1],
      .op ⟨2⟩ [10] plus [0, 1],
      .op ⟨5⟩ [12] times [0, 0],
      .guard ⟨4⟩ () 3 .reject] [10, 11]) = some true := by
  decide +kernel

/-- Computations before, between and after guards, and the same computations after both guards:
the guards stay in their order. -/
def aroundGuards : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .op ⟨1⟩ [10] plus [0, 1],
  .guard ⟨2⟩ () 2 .reject,
  .op ⟨3⟩ [11] times [0, 1],
  .guard ⟨4⟩ () 3 .reject] [10, 11]

/-- The same computations, after both guards. -/
def afterGuards : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .guard ⟨2⟩ () 2 .reject,
  .guard ⟨4⟩ () 3 .reject,
  .op ⟨3⟩ [11] times [0, 1],
  .op ⟨1⟩ [10] plus [0, 1]] [10, 11]

example : decided [] guarded [.nat, .nat] true true aroundGuards afterGuards = some true := by
  decide +kernel

/-- A sum of a computation that does not depend on the loop, inside the loop. -/
def insideLoop : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
    .op ⟨3⟩ [22] plus [0, 1],
    .op ⟨4⟩ [23] plus [21, 22]] [23])] [11]

/-- A computation moved out of a loop. -/
example : decided [] [.nat, .nat] [.nat] false false insideLoop
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .op ⟨3⟩ [12] plus [0, 1],
      .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [23] plus [21, 12]] [23])] [11]) = some true := by
  decide +kernel

/-- The same program with other names for its values, the inputs and those of the loop's region
among them. -/
example : decided [] [.nat, .nat] [.nat] false false insideLoop
    (.mk [7, 8] [
      .op ⟨1⟩ [40] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [40] [41] (.mk [50, 51] [
        .op ⟨3⟩ [52] plus [7, 8],
        .op ⟨4⟩ [53] plus [51, 52]] [53])] [41]) = some true := by
  decide +kernel

/-- A call of a function that cannot stop is a value: two calls on one operand are one. -/
example : decided [callee false] [.nat] [.nat] false false
    (.mk [0] [
      .op ⟨1⟩ [10] (.call ⟨9⟩) [0],
      .op ⟨2⟩ [11] (.call ⟨9⟩) [0],
      .op ⟨3⟩ [12] plus [10, 11]] [12])
    (.mk [0] [
      .op ⟨1⟩ [10] (.call ⟨9⟩) [0],
      .op ⟨3⟩ [12] plus [10, 10]] [12]) = some true := by
  decide +kernel

/-- `x + y`. -/
def sum : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10]

/-- `y + x`. -/
def commutedSum : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [1, 0]] [10]

/-- `x + y` against `y + x`: accepted, since addition commutes; the table places `y + x` with its
operands in the order of `x + y`, so the two are one value. It was refused before the decision
knew that law. -/
example : decided [] [.nat, .nat] [.nat] false false sum commutedSum = some true := by
  decide +kernel

/-- A product and a sum with their operands exchanged, inside a loop that comes after a guard,
and the product again after the loop: each is the value of the first. -/
example : decided [] [.nat, .nat, .bool] [.nat, .nat] true true
    (.mk [0, 1, 2] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] (natural 0) [],
      .loop ⟨3⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [22] times [0, 1],
        .op ⟨5⟩ [23] plus [21, 22]] [23]),
      .op ⟨6⟩ [12] times [0, 1]] [11, 12])
    (.mk [0, 1, 2] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] (natural 0) [],
      .loop ⟨3⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [22] times [1, 0],
        .op ⟨5⟩ [23] plus [22, 21]] [23]),
      .op ⟨6⟩ [12] times [1, 0]] [11, 12]) = some true := by
  decide +kernel

/-! ## Refused -/

/-- `x - y` against `y - x`: a difference does not commute. -/
example : decided [] [.nat, .nat] [.nat] false false
    (.mk [0, 1] [.op ⟨1⟩ [10] minus [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] minus [1, 0]] [10]) = some false := by
  decide +kernel

/-- `(x + y) + z` against `x + (y + z)`: the same value only by the associativity of addition,
which is not a law that the decision knows; only the order of two operands is. -/
example : decided [] [.nat, .nat, .nat] [.nat] false false
    (.mk [0, 1, 2] [.op ⟨1⟩ [10] plus [0, 1], .op ⟨2⟩ [11] plus [10, 2]] [11])
    (.mk [0, 1, 2] [.op ⟨1⟩ [10] plus [1, 2], .op ⟨2⟩ [11] plus [0, 10]] [11]) = some false := by
  decide +kernel

/-- A row of the vocabulary with its operands exchanged: the addition of field elements does not
commute for the decision, whatever a model does; that a row commutes would be a law of the
model. -/
example : decided [] [F, F] [F] false false
    (.mk [0, 1] [.op ⟨1⟩ [10] (fieldRow .add) [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] (fieldRow .add) [1, 0]] [10]) = some false := by
  decide +kernel

/-- Two guards in the other order: which one stops first is kept. -/
example : decided [] [.bool, .bool] [] true true
    (.mk [0, 1] [.guard ⟨1⟩ () 0 .reject, .guard ⟨2⟩ () 1 .reject] [])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .guard ⟨1⟩ () 0 .reject] []) = some false := by
  decide +kernel

/-- A guard dropped. -/
example : decided [] [.nat, .bool] [.nat] true false
    (.mk [0, 1] [.guard ⟨1⟩ () 1 .reject] [0])
    (.mk [0, 1] [] [0]) = some false := by
  decide +kernel

/-- A call of a function that can stop, moved across a guard: such a call is kept in order. -/
example : decided [callee true] [.nat, .bool] [.nat] true true
    (.mk [0, 1] [.op ⟨1⟩ [10] (.call ⟨9⟩) [0], .guard ⟨2⟩ () 1 .reject] [10])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .op ⟨1⟩ [10] (.call ⟨9⟩) [0]] [10]) = some false := by
  decide +kernel

/-- Two loops against one loop that computes the same: the decision keeps every loop in order,
as an entry of the skeleton, and does not decide the fusion of loops. -/
example : decided [] [.nat, .nat] [.nat, .nat] false false
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [.op ⟨3⟩ [22] plus [21, 0]] [22]),
      .loop ⟨4⟩ () (.fixed 3) [10] [12] (.mk [30, 31] [.op ⟨5⟩ [32] plus [31, 1]] [32])]
      [11, 12])
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [10, 10] [11, 12] (.mk [20, 21, 31] [
        .op ⟨3⟩ [22] plus [21, 0],
        .op ⟨5⟩ [32] plus [31, 1]] [22, 32])] [11, 12]) = some false := by
  decide +kernel

/-- A different key on a guard: where it stops is part of what it does. -/
example : decided [] [.nat, .bool] [.nat] true true
    (.mk [0, 1] [.guard ⟨1⟩ () 1 .reject] [0])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject] [0]) = some false := by
  decide +kernel

/-! ## The theorem for functions -/

/-- The body of a function with the key 1 and no callee, elaborated with the names of its
inputs; nothing when it does not elaborate. -/
def elaborated (ins outs : List field.Ty) (stops : Bool) (body : Region (LocalRaw field) Unit) :
    Option ((inputs : Names ins) × Term (localDialect field []) (Ctx.empty.extend inputs) outs) :=
  match elabFn [] ⟨⟨1⟩, ins, outs, stops, none⟩ body with
  | .ok ⟨inputs, fn, _⟩ => some ⟨inputs, fn⟩
  | .error _ => none

/-- Computations around guards, elaborated. -/
def aroundGuardsTyped := (elaborated guarded [.nat, .nat] true aroundGuards).get (by decide +kernel)

/-- The same computations after the guards, elaborated. -/
def afterGuardsTyped := (elaborated guarded [.nat, .nat] true afterGuards).get (by decide +kernel)

/-- No callee. -/
def noCallees (M : Model field) : FnTable M [] := fun _ callee _ => nomatch callee

/-- The two bodies mean the same on every valid input, in every model, for any replies
permitted: both are accepted by the check of facts, have distinct addresses, and the second
follows the skeleton of the first. -/
example (M : Model field) (ins : HList M.Val guarded) (valid : ins.All M.Valid)
    (permitted : ∀ op, NoSig.Reply op → Prop) :
    Process.SameWhen permitted
      (aroundGuardsTyped.2.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend aroundGuardsTyped.1 ins))
      (afterGuardsTyped.2.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend afterGuardsTyped.1 ins)) :=
  functions_same_sound aroundGuardsTyped.1 afterGuardsTyped.1 aroundGuardsTyped.2
    afterGuardsTyped.2 ⟨1⟩ ⟨1⟩ (bounds := []) (bounds' := [])
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) M
    (noCallees M) List.nodup_nil (fun _ callee => nomatch callee)
    (fun _ callee => nomatch callee) (fun _ callee => nomatch callee) ins valid permitted

/-- So, a function having no effects, the two processes are equal. -/
example (M : Model field) (ins : HList M.Val guarded) (valid : ins.All M.Valid) :
    aroundGuardsTyped.2.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend aroundGuardsTyped.1 ins) =
      afterGuardsTyped.2.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend afterGuardsTyped.1 ins) :=
  functions_same_equal aroundGuardsTyped.1 afterGuardsTyped.1 aroundGuardsTyped.2
    afterGuardsTyped.2 ⟨1⟩ ⟨1⟩ (bounds := []) (bounds' := [])
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) M
    (noCallees M) List.nodup_nil (fun _ callee => nomatch callee)
    (fun _ callee => nomatch callee) (fun _ callee => nomatch callee) ins valid

/-- `x + y`, elaborated. -/
def sumTyped := (elaborated [.nat, .nat] [.nat] false sum).get (by decide +kernel)

/-- `y + x`, elaborated. -/
def commutedSumTyped := (elaborated [.nat, .nat] [.nat] false commutedSum).get (by decide +kernel)

/-- `x + y` and `y + x` have equal processes on every valid input, in every model: the decision
accepts the pair, and the law `commutative` of the local operations makes that sound. -/
example (M : Model field) (ins : HList M.Val [.nat, .nat]) (valid : ins.All M.Valid) :
    sumTyped.2.denote (localSem M [] (noCallees M)) [] (Env.empty.extend sumTyped.1 ins) =
      commutedSumTyped.2.denote (localSem M [] (noCallees M)) []
        (Env.empty.extend commutedSumTyped.1 ins) :=
  functions_same_equal sumTyped.1 commutedSumTyped.1 sumTyped.2 commutedSumTyped.2 ⟨1⟩ ⟨1⟩
    (bounds := []) (bounds' := [])
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    ((Term.repeatedAddress_eq_none _).mp (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) M
    (noCallees M) List.nodup_nil (fun _ callee => nomatch callee)
    (fun _ callee => nomatch callee) (fun _ callee => nomatch callee) ins valid

/-! ## Controls on the definitions of the value form -/

/-- The operations of the dialect of the controls: one asks for a reply and returns it, one
stops with `true`, which stands for `undefined`. -/
inductive ToyOp : List Unit → List Unit → Type where
  | ask : ToyOp [] [()]
  | fail : ToyOp [] [()]

/-- A dialect of one type whose attempts anyone may own, with no condition, variant or count. -/
@[reducible] def toy : Dialect where
  Ty := Unit
  Op := ToyOp
  Who := Unit
  Condition _ _ := False
  Alternatives _ _ _ := False
  Count _ _ := False
  index _ := ()
  Attempt _ := True
  Gives _ _ := True
  collected _ _ := ()

/-- Its semantics: values are truth values; asking calls for a reply and returns it; failing
stops with `true`; the end of an attempt calls for a reply. -/
def toySem : Semantics toy where
  Val _ := Bool
  S := ⟨Unit, fun _ => Bool⟩
  H := Bool
  op := fun {_ _} _ o _ _ => match o with
    | .ask => .call () fun reply => .done (.cons reply .nil)
    | .fail => .halt true
  holds := fun {_ _} ok _ => nomatch ok
  stop := fun _ _ _ => false
  pick := fun {_ _ _} ok _ => nomatch ok
  count := fun {_ _} ok _ => nomatch ok
  index := fun _ _ => false
  begin := fun _ _ _ => .done false
  settle := fun _ _ _ => .call () fun _ => .done ()
  collect := fun _ _ _ => false

/-- Asking is kept in order; failing is a value; nothing commutes. -/
def toyRules : ValueRules toy Unit where
  written := fun {_ _} o => match o with
    | .ask => none
    | .fail => some ()
  place := fun _ => 0
  commutes := fun _ => false

/-- Following decides types and performers by equality, and finds any two operations the
same. -/
def toyChecks : SkelRules toy where
  sameTy := inferInstanceAs (DecidableEq Unit)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun _ _ => true

/-! ### Leaves made in order -/

/-- The context of the name `0`. -/
abbrev oneName : Ctx Unit := Ctx.empty.insert 0 ()

/-- Ask, and return the reply. -/
def returnsReply : Term toy oneName [()] :=
  .op ⟨1⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil))

/-- Ask, and return the value of the name `0`. -/
def returnsInput : Term toy oneName [()] :=
  .op ⟨1⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨0, rfl⟩ .nil))

/-- The skeleton of `returnsReply` made with its leaf at the identifier `5` of the name `0`:
asking, then returning the leaf. -/
def reusedLeaf : Skel toy [()] := .effect ⟨1⟩ ToyOp.ask [] 5 (.ret [5])

/-- The name `0` at the identifier `5`. -/
def atFive : Ctx Nat := Ctx.empty.insert 0 5

/-- A state above the identifier `5`. -/
def aboveFive : FactCheck.St Unit Unit := ⟨FactCheck.Table.empty toyRules.place, 6, [], []⟩

/-- Both terms follow the skeleton from the state above `5`: following binds the name of the
reply to the skeleton's leaf, which is the identifier of the name `0`. -/
example : (returnsReply.follows toyRules toyChecks reusedLeaf atFive aboveFive).isSome = true := by
  decide +kernel
example : (returnsInput.follows toyRules toyChecks reusedLeaf atFive aboveFive).isSome = true := by
  decide +kernel

/-- The skeleton's leaf is not made above the values that the run already has. -/
example : ¬ reusedLeaf.Fresh 6 := fun fresh => absurd (fresh : 6 ≤ 5 ∧ _).1 (by decide)

/-- And the two terms do not mean the same: on the reply `false`, one returns `false` and the
other `true`. So following needs `Skel.Fresh` (`Term.follows_runs`). -/
example : ¬ Process.SameWhen (fun _ _ => True)
    (returnsReply.denote toySem [] fun _ _ _ => true)
    (returnsInput.denote toySem [] fun _ _ _ => true) := by
  intro same
  cases same with
  | call _ next => cases next false trivial

/-! ### What follows an attempt -/

/-- An attempt whose body gives nothing, then failing, then nothing. -/
def failsAfterAttempt : Term toy Ctx.empty [] :=
  .attempt ⟨1⟩ () trivial (.cons 0 .nil) (.ret .nil) .nil
    (.op ⟨2⟩ ToyOp.fail .nil (.cons 1 .nil) (.ret .nil))

/-- No reply is permitted, and the end of the attempt calls for one: the run never stops, and in
particular never `undefined`. -/
theorem failsAfterAttempt_safe : (failsAfterAttempt.denote toySem [] Env.empty).Every
    (fun _ _ => False) (fun _ => True) (fun stop => ¬ stop = true) :=
  fun _ never => never.elim

/-- Failing is a value of the dialect: it stops with `true`, which stands for `undefined`. -/
theorem toyBinding : toyRules.Binding toySem (fun _ _ _ => False) (· = true) where
  computes := by
    intro _ _ o raw written key path values
    cases o with
    | ask => cases written
    | fail => exact .inr ⟨true, rfl, rfl⟩
  functional := fun _ _ _ _ ran => ran.elim
  commutative := fun _ _ _ _ _ ran => ran.elim

/-- The term runs its own skeleton (`Term.skeleton_runs`), whose attempt asks nothing of what
follows it, since its end cannot return. -/
example : Skel.Runs toySem (fun _ _ => False) (fun _ _ _ => False)
    (failsAfterAttempt.skeleton toyRules Ctx.empty
      ⟨FactCheck.Table.empty toyRules.place, 0, [], []⟩).2.table [] (fun _ => none)
    (failsAfterAttempt.skeleton toyRules Ctx.empty
      ⟨FactCheck.Table.empty toyRules.place, 0, [], []⟩).1
    (failsAfterAttempt.denote toySem [] Env.empty) :=
  (Term.skeleton_runs toySem (fun _ _ => False) (fun _ _ _ => False) toyRules toyBinding
    failsAfterAttempt Ctx.empty ⟨FactCheck.Table.empty toyRules.place, 0, [], []⟩ [] Env.empty
    (fun _ => none) trivial (fun _ _ => rfl)
    (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed) failsAfterAttempt_safe).1

/-- What follows the attempt stops `undefined`, and so does not run what follows it in the
skeleton: a run of the attempt that asked for what follows from every end, not only from one
that can return, would not hold of this term. -/
example : ¬ Skel.Runs toySem (fun _ _ => False) (fun _ _ _ => False)
    (FactCheck.Table.empty toyRules.place) [] (fun _ => none) (.ret [] : Skel toy [])
    ((Term.op ⟨2⟩ ToyOp.fail .nil (.cons 1 .nil) (.ret .nil) : Term toy Ctx.empty []).denote
      toySem [] Env.empty) := by
  intro runs
  cases runs

end Zkc.Core.SameTests

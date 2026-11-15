import Zkc.Core.Admission.Elaboration
import Zkc.Tests.Core.Shapes

/-!
The elaboration of functions by names. For each rule, a program that is accepted and one that
is refused, with the refusal: its rule, its place and what the rule found; the latest binding
of a name; and the printed form of each accepted program, elaborated back to it. The kernel
evaluates each.
-/

namespace Zkc.Core.Elaboration

abbrev plain := Shapes.plain

/-- A program of one function, with the key 1. -/
def single (ins outs : List plain.Ty) (canStop : Bool) (body : Region (LocalRaw plain) Unit) :
    NamedProgram plain :=
  ⟨[.fn ⟨1⟩ ins outs canStop none body]⟩

/-- The first refusal of a program; nothing when it is accepted. -/
def refusal (named : NamedProgram plain) : Option (Refusal plain) :=
  match elaborateFunctions named with
  | .ok _ => none
  | .error refusals => refusals.head?

/-- The refusal of the body of a function against the headers before it; nothing when it is
accepted. -/
def bodyRefusal (fns : List (FnHeader plain)) (hdr : FnHeader plain)
    (body : Region (LocalRaw plain) Unit) : Option (Refusal plain) :=
  match elabFn fns hdr body with
  | .ok _ => none
  | .error problem => some (problem.refusal hdr.key)

/-- The place of an instruction of a definition. -/
def at_ (definition instruction : Nat) : Place := ⟨⟨definition⟩, [], some ⟨instruction⟩, none⟩

/-- The place of a definition as a whole. -/
def whole (definition : Nat) : Place := ⟨⟨definition⟩, [], none, none⟩

/-- A variant of a natural or a truth value. -/
def natOrBool : plain.Ty := .variant ⟨7⟩ (.cons .nat (.cons .bool .nil))

/-- A linear record without fields. -/
def token : plain.Ty := .record ⟨5⟩ true .nil

/-! ## Names in scope and operations -/

/-- The sum of the two inputs. -/
def add : NamedProgram plain :=
  single [.nat, .nat] [.nat] false (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1]] [2])

example : refusal add = none := by decide

/-- An operand that is not in scope. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 5]] [2])) =
    some ⟨.scope, at_ 1 1, .name 5⟩ := by
  decide

/-- An exit that is not in scope. -/
example : refusal (single [.nat] [.nat] false (.mk [0] [] [7])) =
    some ⟨.scope, whole 1, .name 7⟩ := by
  decide

/-- An operand of another type. -/
example : refusal (single [.bool, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1]] [2])) =
    some ⟨.operands, at_ 1 1, .types [.nat, .nat] [.bool, .nat]⟩ := by
  decide

/-- An operation that the core owns, written with types that it does not take. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [.nat] []) [0, 1]] [2])) =
    some ⟨.owned, at_ 1 1, .operation (.owned .natAdd [.nat] [])⟩ := by
  decide

/-- The wrong number of results. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2, 3] (.owned .natAdd [] []) [0, 1]] [2])) =
    some ⟨.results, at_ 1 1, .number 1 2⟩ := by
  decide

/-- The wrong number of inputs. -/
example : refusal (single [.nat, .nat] [.nat] false (.mk [0] [] [0])) =
    some ⟨.inputs, whole 1, .number 2 1⟩ := by
  decide

/-! ## Literals -/

def literal : NamedProgram plain :=
  single [] [.bool] false (.mk [] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])

example : refusal literal = none := by decide

example : refusal (single [] [.bool] false (.mk [] [.op ⟨1⟩ [0] (.literal .bool [2]) []] [0])) =
    some ⟨.literal, at_ 1 1, .operation (.literal .bool [2])⟩ := by
  decide

/-! ## Calls and keys -/

/-- A function that gives its input, and a function that calls it. -/
def calls : NamedProgram plain :=
  ⟨[.fn ⟨1⟩ [.nat] [.nat] false none (.mk [0] [] [0]),
    .fn ⟨2⟩ [.nat] [.nat] false none (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩

example : refusal calls = none := by decide

/-- A callee that is not there. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none (.mk [0] [] [0]),
    .fn ⟨2⟩ [.nat] [.nat] false none (.mk [0] [.op ⟨1⟩ [1] (.call ⟨9⟩) [0]] [1])]⟩ =
    some ⟨.callee, at_ 2 1, .callee ⟨9⟩ 0⟩ := by
  decide

/-- A callee that is there twice: a body against headers with a repeated key, which no program
has. -/
example : bodyRefusal [⟨⟨1⟩, [.nat], [.nat], false, none⟩, ⟨⟨1⟩, [.nat], [.nat], false, none⟩]
    ⟨⟨2⟩, [.nat], [.nat], false, none⟩ (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1]) =
    some ⟨.callee, at_ 2 1, .callee ⟨1⟩ 2⟩ := by
  decide

/-- A call on operands of other types than the callee takes. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none (.mk [0] [] [0]),
    .fn ⟨2⟩ [.bool] [.nat] false none (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩ =
    some ⟨.operands, at_ 2 1, .types [.nat] [.bool]⟩ := by
  decide

/-- A repeated key. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none (.mk [0] [] [0]),
    .fn ⟨1⟩ [.nat] [.nat] false none (.mk [0] [] [0])]⟩ = some ⟨.key, whole 1, .key ⟨1⟩⟩ := by
  decide

/-- A protocol: the rules of the protocol dialect are not built. -/
example : refusal ⟨[.protocol ⟨1⟩ 1 [] [] (.mk [] [] [])]⟩ =
    some ⟨.protocol, whole 1, .key ⟨1⟩⟩ := by
  decide

/-! ## Guards and stopping -/

/-- A guard on a truth value, in a function whose header says that it can stop. -/
def guarded : NamedProgram plain :=
  single [.bool] [.bool] true (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])

example : refusal guarded = none := by decide

/-- A condition that is not a truth value. -/
example : refusal (single [.nat] [.nat] true (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])) =
    some ⟨.condition, at_ 1 1, .type .nat⟩ := by
  decide

/-- A header that says that the function cannot stop, over a body with a guard. -/
example : refusal (single [.bool] [.bool] false (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])) =
    some ⟨.stops, whole 1, .stops false true⟩ := by
  decide

/-- A header that says that the function can stop, over a body that cannot. -/
example : refusal (single [.nat] [.nat] true (.mk [0] [] [0])) =
    some ⟨.stops, whole 1, .stops true false⟩ := by
  decide

/-- A call of a function that can stop can stop. -/
example : refusal ⟨[.fn ⟨1⟩ [.bool] [.bool] true none (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0]),
    .fn ⟨2⟩ [.bool] [.bool] false none (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩ =
    some ⟨.stops, whole 2, .stops false true⟩ := by
  decide

/-! ## Choices -/

/-- A natural chosen by a truth value. -/
def chosen : NamedProgram plain :=
  single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .nat [3]) []] [5])
      (.mk [] [.op ⟨3⟩ [5] (.literal .nat [4]) []] [5])] [1])

example : refusal chosen = none := by decide

/-- Regions of a choice that give different types. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .nat [3]) []] [5])
      (.mk [] [.op ⟨3⟩ [5] (.literal .bool [1]) []] [5])] [1])) =
    some ⟨.regions, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide

/-- A choice on a natural. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1] (.mk [] [] [0]) (.mk [] [] [0])] [1])) =
    some ⟨.condition, at_ 1 1, .type .nat⟩ := by
  decide

/-! ## Case analyses -/

/-- A natural from a variant of a natural or a truth value. -/
def analysed : NamedProgram plain :=
  single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [] [9],
       .mk [9] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]]] [1])

example : refusal analysed = none := by decide

/-- A subject that is not a variant. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9]]] [1])) =
    some ⟨.variant, at_ 1 1, .type .nat⟩ := by
  decide

/-- The wrong number of arms. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9]]] [1])) =
    some ⟨.arms, at_ 1 1, .number 2 1⟩ := by
  decide

/-- Arms that give different types. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9], .mk [9] [] [9]]] [1])) =
    some ⟨.armTypes, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide

/-- An arm without a name for its payload. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10],
       .mk [9] [.op ⟨3⟩ [10] (.literal .nat [0]) []] [10]]] [1])) =
    some ⟨.inputs, at_ 1 1, .number 1 0⟩ := by
  decide

/-! ## Loops -/

/-- A sum carried over three iterations, with the iteration number of each collected. -/
def looped : NamedProgram plain :=
  single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1, 2]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.owned .natAdd [] []) [10, 11]] [12, 10])] [1])

example : refusal looped = none := by decide

/-- A loop as often as an input says. -/
def counted : NamedProgram plain :=
  single [.nat, .nat] [.nat] false (.mk [0, 1]
    [.loop ⟨1⟩ () (.count 1) [0] [2]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.owned .natAdd [] []) [10, 11]] [12])] [2])

example : refusal counted = none := by decide

/-- A body that does not give back the carried types. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.literal .bool [0]) []] [12])] [1])) =
    some ⟨.carried, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide

/-- A count that is not a natural. -/
example : refusal (single [.nat, .bool] [.nat] false (.mk [0, 1]
    [.loop ⟨1⟩ () (.count 1) [0] [2] (.mk [10, 11] [] [11])] [2])) =
    some ⟨.count, at_ 1 1, .type .bool⟩ := by
  decide

/-! ## Blocks and attempts -/

/-- A literal in a block. -/
def blocked : NamedProgram plain :=
  single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5])] [1])

example : refusal blocked = none := by decide

/-- A refusal in a block is at the block's number. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [2]) []] [5])] [1])) =
    some ⟨.literal, ⟨⟨1⟩, [(⟨1⟩, 0)], some ⟨2⟩, none⟩, .operation (.literal .bool [2])⟩ := by
  decide

/-- An attempt in a function: nobody owns one. -/
example : refusal (single [] [.nat] false (.mk [] [.attempt ⟨1⟩ () [1] (.mk [5] [] [5])] [1])) =
    some ⟨.attempt, at_ 1 1, .nothing⟩ := by
  decide

/-! ## Linear values and addresses -/

/-- A linear value, made and given. -/
def linear : NamedProgram plain :=
  single [] [token] false (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [0])

example : refusal linear = none := by decide

/-- A linear value given twice. -/
example : refusal (single [] [token, token] false
    (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [0, 0])) =
    some ⟨.linear, whole 1, .nothing⟩ := by
  decide

/-- A linear value not used. -/
example : refusal (single [] [] false
    (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [])) =
    some ⟨.linear, whole 1, .nothing⟩ := by
  decide

/-- Two instructions with one key. -/
example : refusal (single [.nat, .nat] [.nat] false (.mk [0, 1]
    [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1], .op ⟨1⟩ [3] (.owned .natAdd [] []) [2, 1]] [3])) =
    some ⟨.distinct, whole 1, .nothing⟩ := by
  decide

/-! ## The latest binding of a name -/

/-- The name of the input is bound again, to a truth value: the exit gives the later one. -/
def shadowed : NamedProgram plain :=
  single [.nat] [.bool] false (.mk [0] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])

example : refusal shadowed = none := by decide

example : refusal (single [.nat] [.nat] false
    (.mk [0] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])) =
    some ⟨.outputs, whole 1, .types [.nat] [.bool]⟩ := by
  decide

/-! ## A case analysis without an arm -/

/-- A variant without alternatives. -/
def nothing : plain.Ty := .variant ⟨3⟩ .nil

/-- A case analysis of a value of a variant without alternatives, which has no arm, giving
values of the types `mid`, none of which the rest uses. -/
def armless (mid : List plain.Ty) : Term (localDialect plain []) [nothing] [] :=
  .cases (mid := mid) ⟨1⟩ () .head ⟨⟨3⟩, .nil, rfl, rfl⟩ (fun _ _ => trivial) .nil (.ret .nil)

/-- What the case analysis at the start of a term gives. -/
def gives {Γ outs : List plain.Ty} : Term (localDialect plain []) Γ outs → List plain.Ty
  | .cases (mid := mid) .. => mid
  | _ => []

/-- Two terms that differ only in what a case analysis without an arm gives are printed alike:
the printed form of a case analysis writes the names of its results, not their types. So the
round trip holds of a term whose case analyses without an arm give nothing (`Term.armed`), and
of every term that elaboration gives, and not of every typed term. -/
example : printBody (fun o => LocalOp.print o) (fun _ => ()) (armless [.nat]) =
    printBody (fun o => LocalOp.print o) (fun _ => ()) (armless [.bool]) := rfl

example : armless [.nat] ≠ armless [.bool] := fun same => by
  have different := congrArg gives same
  simp [gives, armless] at different

example : (armless []).armed = true ∧ (armless [.nat]).armed = false := by decide

/-! ## The printed form of each accepted program elaborates to it -/

/-- The printed form of the program that a program elaborates to, elaborated. -/
def again (named : NamedProgram plain) : Except (List (Refusal plain)) (Typed plain) :=
  (elaborateFunctions named).bind fun p => elaborateFunctions (print p)

example : again add = elaborateFunctions add := by rfl
example : again literal = elaborateFunctions literal := by rfl
example : again calls = elaborateFunctions calls := by rfl
example : again guarded = elaborateFunctions guarded := by rfl
example : again chosen = elaborateFunctions chosen := by rfl
example : again analysed = elaborateFunctions analysed := by rfl
example : again looped = elaborateFunctions looped := by rfl
example : again counted = elaborateFunctions counted := by rfl
example : again blocked = elaborateFunctions blocked := by rfl
example : again linear = elaborateFunctions linear := by rfl
example : again shadowed = elaborateFunctions shadowed := by rfl

/-- The printed form names each value by its level: the input is 0 and the truth value bound
after it is 1. -/
example : (elaborateFunctions shadowed).map print =
    .ok ⟨[.fn ⟨1⟩ [.nat] [.bool] false none
      (.mk [0] [.op ⟨1⟩ [1] (.literal .bool [1]) []] [1])]⟩ := by
  rfl

end Zkc.Core.Elaboration

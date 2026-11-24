import Zkc.Core.Admission.Elaboration
import Zkc.Tests.Core.Shapes

/-!
The elaboration of functions by names. For each rule, a program that is accepted and one that
is refused, with the refusal: its rule, its place and what the rule found; where a refusal is at
each construct; the literals of each type; linear use at each construct, by the name of the value,
and which types are linear; single assignment at each place that binds a name, the results of a
choice, a case analysis and a loop among them; and the round trip of each accepted program in
both directions: the erased form of what it elaborates to elaborates to the same, and is the
program. The kernel evaluates each.
-/

namespace Zkc.Core.Elaboration

abbrev plain := Shapes.plain

/-- A program of one function, with the key 1. -/
def single (ins outs : List plain.Ty) (canStop : Bool) (body : Region (LocalRaw plain) Unit) :
    NamedProgram plain :=
  ⟨[.fn ⟨1⟩ ins outs canStop none Summary.empty body]⟩

def functionError {V : Vocabulary} (e : ProgramRefusal V) : Option (DefinitionRefusal V) :=
  some (.fn e)

/-- The first refusal of a program; nothing when it is accepted. -/
def refusal (named : NamedProgram plain) : Option (DefinitionRefusal plain) :=
  match elaborateFunctions named with
  | .ok _ => none
  | .error refusals => refusals.head?

/-- The refusal of the body of a function against the headers before it; nothing when it is
accepted. -/
def bodyRefusal (fns : List (FnHeader plain)) (hdr : FnHeader plain)
    (body : Region (LocalRaw plain) Unit) : Option (DefinitionRefusal plain) :=
  match elabFn fns hdr body with
  | .ok _ => none
  | .error refusal => some (.fn refusal)

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

example : refusal add = none := by decide +kernel

/-- An operand that is not in scope. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 5]] [2])) =
    functionError ⟨.scope, at_ 1 1, .name 5⟩ := by
  decide +kernel

/-- An exit that is not in scope. -/
example : refusal (single [.nat] [.nat] false (.mk [0] [] [7])) =
    functionError ⟨.scope, whole 1, .name 7⟩ := by
  decide +kernel

/-- An operand of another type. -/
example : refusal (single [.bool, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1]] [2])) =
    functionError ⟨.operands, at_ 1 1, .types [.nat, .nat] [.bool, .nat]⟩ := by
  decide +kernel

/-- An operation that the core owns, written with types that it does not take. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2] (.owned .natAdd [.nat] []) [0, 1]] [2])) =
    functionError ⟨.owned, at_ 1 1, .operation (.owned .natAdd [.nat] [])⟩ := by
  decide +kernel

/-- The wrong number of results. -/
example : refusal (single [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [2, 3] (.owned .natAdd [] []) [0, 1]] [2])) =
    functionError ⟨.results, at_ 1 1, .number 1 2⟩ := by
  decide +kernel

/-- The wrong number of inputs. -/
example : refusal (single [.nat, .nat] [.nat] false (.mk [0] [] [0])) =
    functionError ⟨.inputs, whole 1, .number 2 1⟩ := by
  decide +kernel

/-! ## Literals -/

def literal : NamedProgram plain :=
  single [] [.bool] false (.mk [] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])

example : refusal literal = none := by decide +kernel

example : refusal (single [] [.bool] false (.mk [] [.op ⟨1⟩ [0] (.literal .bool [2]) []] [0])) =
    functionError ⟨.literal, at_ 1 1, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-! ## Calls and keys -/

/-- A function that gives its input, and a function that calls it. -/
def calls : NamedProgram plain :=
  ⟨[.fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0]),
    .fn ⟨2⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩

example : refusal calls = none := by decide +kernel

/-- A callee that is not there. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0]),
    .fn ⟨2⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.call ⟨9⟩) [0]] [1])]⟩ =
    functionError ⟨.callee, at_ 2 1, .callee ⟨9⟩ 0⟩ := by
  decide +kernel

/-- A callee that is there twice: a body against headers with a repeated key, which no program
has. -/
example : bodyRefusal [⟨⟨1⟩, [.nat], [.nat], false, none, Summary.empty⟩, ⟨⟨1⟩, [.nat], [.nat], false, none, Summary.empty⟩]
    ⟨⟨2⟩, [.nat], [.nat], false, none, Summary.empty⟩ (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1]) =
    functionError ⟨.callee, at_ 2 1, .callee ⟨1⟩ 2⟩ := by
  decide +kernel

/-- A call on operands of other types than the callee takes. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0]),
    .fn ⟨2⟩ [.bool] [.nat] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩ =
    functionError ⟨.operands, at_ 2 1, .types [.nat] [.bool]⟩ := by
  decide +kernel

/-- A repeated key. -/
example : refusal ⟨[.fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0]),
    .fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [] [0])]⟩ = functionError ⟨.key, whole 1, .key ⟨1⟩⟩ := by
  decide +kernel

/-- The empty protocol has a typed body and a computed empty shape. -/
example : (elaborateProgram (V := plain) ⟨[.protocol ⟨1⟩ 1 [] [] (.mk [] [] [])]⟩).isOk := by
  decide +kernel

/-! ## Guards and stopping -/

/-- A guard on a truth value, in a function whose header says that it can stop. -/
def guarded : NamedProgram plain :=
  single [.bool] [.bool] true (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])

example : refusal guarded = none := by decide +kernel

/-- A condition that is not a truth value. -/
example : refusal (single [.nat] [.nat] true (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])) =
    functionError ⟨.condition, at_ 1 1, .type .nat⟩ := by
  decide +kernel

/-- A header that says that the function cannot stop, over a body with a guard. -/
example : refusal (single [.bool] [.bool] false (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0])) =
    functionError ⟨.stops, whole 1, .stops false true⟩ := by
  decide +kernel

/-- A header that says that the function can stop, over a body that cannot. -/
example : refusal (single [.nat] [.nat] true (.mk [0] [] [0])) =
    functionError ⟨.stops, whole 1, .stops true false⟩ := by
  decide +kernel

/-- A call of a function that can stop can stop. -/
example : refusal ⟨[.fn ⟨1⟩ [.bool] [.bool] true none Summary.empty (.mk [0] [.guard ⟨1⟩ () 0 .reject] [0]),
    .fn ⟨2⟩ [.bool] [.bool] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩ =
    functionError ⟨.stops, whole 2, .stops false true⟩ := by
  decide +kernel

/-! ## Choices -/

/-- A natural chosen by a truth value. -/
def chosen : NamedProgram plain :=
  single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .nat [3]) []] [5])
      (.mk [] [.op ⟨3⟩ [6] (.literal .nat [4]) []] [6])] [1])

example : refusal chosen = none := by decide +kernel

/-- Regions of a choice that give different types. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .nat [3]) []] [5])
      (.mk [] [.op ⟨3⟩ [6] (.literal .bool [1]) []] [6])] [1])) =
    functionError ⟨.regions, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide +kernel

/-- A choice on a natural. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1] (.mk [] [] [0]) (.mk [] [] [0])] [1])) =
    functionError ⟨.condition, at_ 1 1, .type .nat⟩ := by
  decide +kernel

/-! ## Case analyses -/

/-- A natural from a variant of a natural or a truth value. -/
def analysed : NamedProgram plain :=
  single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [] [9],
       .mk [11] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]]] [1])

example : refusal analysed = none := by decide +kernel

/-- A subject that is not a variant. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9]]] [1])) =
    functionError ⟨.variant, at_ 1 1, .type .nat⟩ := by
  decide +kernel

/-- The wrong number of arms. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9]]] [1])) =
    functionError ⟨.arms, at_ 1 1, .number 2 1⟩ := by
  decide +kernel

/-- Arms that give different types. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9], .mk [10] [] [10]]] [1])) =
    functionError ⟨.armTypes, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide +kernel

/-- An arm without a name for its payload. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10],
       .mk [9] [.op ⟨3⟩ [11] (.literal .nat [0]) []] [11]]] [1])) =
    functionError ⟨.inputs, at_ 1 1, .number 1 0⟩ := by
  decide +kernel

/-! ## Loops -/

/-- A sum carried over three iterations, with the iteration number of each collected. -/
def looped : NamedProgram plain :=
  single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1, 2]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.owned .natAdd [] []) [10, 11]] [12, 10])] [1])

example : refusal looped = none := by decide +kernel

/-- A loop as often as an input says. -/
def counted : NamedProgram plain :=
  single [.nat, .nat] [.nat] false (.mk [0, 1]
    [.loop ⟨1⟩ () (.count 1) [0] [2]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.owned .natAdd [] []) [10, 11]] [12])] [2])

example : refusal counted = none := by decide +kernel

/-- A body that does not give back the carried types. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.literal .bool [0]) []] [12])] [1])) =
    functionError ⟨.carried, at_ 1 1, .types [.nat] [.bool]⟩ := by
  decide +kernel

/-- A count that is not a natural. -/
example : refusal (single [.nat, .bool] [.nat] false (.mk [0, 1]
    [.loop ⟨1⟩ () (.count 1) [0] [2] (.mk [10, 11] [] [11])] [2])) =
    functionError ⟨.count, at_ 1 1, .type .bool⟩ := by
  decide +kernel

/-! ## Blocks and attempts -/

/-- A literal in a block. -/
def blocked : NamedProgram plain :=
  single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5])] [1])

example : refusal blocked = none := by decide +kernel

/-- A refusal in a block is at the block's number. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [2]) []] [5])] [1])) =
    functionError ⟨.literal, ⟨⟨1⟩, [(⟨1⟩, 0)], some ⟨2⟩, none⟩, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-- An attempt in a function: nobody owns one. -/
example : refusal (single [] [.nat] false (.mk [] [.attempt ⟨1⟩ () [1] (.mk [5] [] [5])] [1])) =
    functionError ⟨.attempt, at_ 1 1, .nothing⟩ := by
  decide +kernel

/-! ## Linear values and addresses -/

/-- A linear value, made and given. -/
def linear : NamedProgram plain :=
  single [] [token] false (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [0])

example : refusal linear = none := by decide +kernel

/-- A linear value given twice: refused at the instruction that binds it, by its name, used
twice. -/
example : refusal (single [] [token, token] false
    (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [0, 0])) =
    functionError ⟨.linear, at_ 1 1, .uses 0 2⟩ := by
  decide +kernel

/-- A linear value not used. -/
example : refusal (single [] [] false
    (.mk [] [.op ⟨1⟩ [0] (.owned .make [token] []) []] [])) =
    functionError ⟨.linear, at_ 1 1, .uses 0 0⟩ := by
  decide +kernel

/-- A linear input not used: refused at the definition, by its name. -/
example : refusal (single [token] [] false (.mk [0] [] [])) =
    functionError ⟨.linear, whole 1, .uses 0 0⟩ := by
  decide +kernel

/-- A linear value from around a choice that one region uses and the other does not: refused at
the choice, as a value from around it, by its name, with its count in the second region. -/
example : refusal (single [token, .bool] [token] false (.mk [0, 1]
    [.choose ⟨1⟩ () 1 [2]
      (.mk [] [] [0])
      (.mk [] [.op ⟨2⟩ [5] (.owned .make [token] []) []] [5])] [2])) =
    functionError ⟨.linear, at_ 1 1, .around 0 0⟩ := by
  decide +kernel

/-- A linear value from around a loop that its body uses: refused at the loop, as a value from
around it, by its name, with its count in the body. -/
example : refusal (single [token] [.seq token (some 1)] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 1) [] [1] (.mk [5] [] [0])] [1])) =
    functionError ⟨.linear, at_ 1 1, .around 0 1⟩ := by
  decide +kernel

/-- A variant whose second alternative is linear. -/
def natOrToken : plain.Ty := .variant ⟨8⟩ (.cons .nat (.cons token .nil))

/-- A linear payload that its arm does not use: refused at the case analysis, by the name of the
payload. -/
example : refusal (single [natOrToken] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [] [9],
       .mk [11] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]]] [1])) =
    functionError ⟨.linear, at_ 1 1, .uses 11 0⟩ := by
  decide +kernel

/-- Two instructions with one key: refused at the second. -/
example : refusal (single [.nat, .nat] [.nat] false (.mk [0, 1]
    [.op ⟨1⟩ [2] (.owned .natAdd [] []) [0, 1], .op ⟨1⟩ [3] (.owned .natAdd [] []) [2, 1]] [3])) =
    functionError ⟨.distinct, at_ 1 1, .nothing⟩ := by
  decide +kernel

/-- Two instructions with one key in a block: refused at the second, inside the block. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk []
      [.op ⟨2⟩ [5] (.literal .bool [0]) [], .op ⟨2⟩ [6] (.literal .bool [1]) []] [6])] [1])) =
    functionError ⟨.distinct, ⟨⟨1⟩, [(⟨1⟩, 0)], some ⟨2⟩, none⟩, .nothing⟩ := by
  decide +kernel

/-- An instruction whose key is the key of a block: refused at the instruction. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5]),
     .op ⟨1⟩ [2] (.owned .boolNot [] []) [1]] [2])) =
    functionError ⟨.distinct, at_ 1 1, .nothing⟩ := by
  decide +kernel

/-! ## Where a refusal is, at each construct -/

/-- The exit of a region of a choice that is not in scope: refused at the choice. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1] (.mk [] [] [7]) (.mk [] [] [7])] [1])) =
    functionError ⟨.scope, at_ 1 1, .name 7⟩ := by
  decide +kernel

/-- A guard's condition that is not in scope. -/
example : refusal (single [.bool] [.bool] true (.mk [0] [.guard ⟨1⟩ () 9 .reject] [0])) =
    functionError ⟨.scope, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- A choice's condition that is not in scope. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 9 [1] (.mk [] [] [0]) (.mk [] [] [0])] [1])) =
    functionError ⟨.scope, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- A case analysis's subject that is not in scope. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 9 [1] [.mk [9] [] [9], .mk [10] [] [10]]] [1])) =
    functionError ⟨.scope, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- A loop's carried value that is not in scope. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [9] [1] (.mk [10, 11] [] [11])] [1])) =
    functionError ⟨.scope, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- A loop's count that is not in scope. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.count 9) [0] [1] (.mk [10, 11] [] [11])] [1])) =
    functionError ⟨.scope, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- Of two operands not in scope, the first. -/
example : refusal (single [.nat] [.nat] false
    (.mk [0] [.op ⟨1⟩ [2] (.owned .natAdd [] []) [5, 6]] [2])) =
    functionError ⟨.scope, at_ 1 1, .name 5⟩ := by
  decide +kernel

/-- A choice that binds the wrong number of results. -/
example : refusal (single [.bool] [.bool] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1, 2] (.mk [] [] [0]) (.mk [] [] [0])] [1])) =
    functionError ⟨.results, at_ 1 1, .number 1 2⟩ := by
  decide +kernel

/-- A case analysis that binds the wrong number of results. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1, 2]
      [.mk [9] [] [9], .mk [11] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]]] [1])) =
    functionError ⟨.results, at_ 1 1, .number 1 2⟩ := by
  decide +kernel

/-- A loop that binds the wrong number of results. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1, 2, 3] (.mk [10, 11] [] [11])] [1])) =
    functionError ⟨.results, at_ 1 1, .number 1 3⟩ := by
  decide +kernel

/-- A block that binds the wrong number of results. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1, 2] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5])] [1])) =
    functionError ⟨.results, at_ 1 1, .number 1 2⟩ := by
  decide +kernel

/-- A body of a loop that names fewer inputs than the index and the carried values. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10] [] [10])] [1])) =
    functionError ⟨.inputs, at_ 1 1, .number 2 1⟩ := by
  decide +kernel

/-- A refusal after an operation: at the instruction after it. -/
example : refusal (single [.nat] [.nat] true (.mk [0]
    [.op ⟨1⟩ [1] (.literal .nat [0]) [], .guard ⟨2⟩ () 1 .reject] [0])) =
    functionError ⟨.condition, at_ 1 2, .type .nat⟩ := by
  decide +kernel

/-- A refusal after a guard. -/
example : refusal (single [.bool] [.bool] true (.mk [0]
    [.guard ⟨1⟩ () 0 .reject, .op ⟨2⟩ [5] (.literal .bool [2]) []] [5])) =
    functionError ⟨.literal, at_ 1 2, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-- A refusal in the first region of a choice. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .bool [2]) []] [5]) (.mk [] [] [0])] [1])) =
    functionError ⟨.literal, at_ 1 2, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-- A refusal in the second region of a choice. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [] [0]) (.mk [] [.op ⟨2⟩ [5] (.literal .bool [2]) []] [5])] [1])) =
    functionError ⟨.literal, at_ 1 2, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-- A refusal after a choice. -/
example : refusal (single [.bool] [.bool] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1] (.mk [] [] [0]) (.mk [] [] [0]),
     .op ⟨2⟩ [5] (.literal .bool [2]) []] [5])) =
    functionError ⟨.literal, at_ 1 2, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-- A variant of three naturals. -/
def threeNaturals : plain.Ty := .variant ⟨9⟩ (.cons .nat (.cons .nat (.cons .nat .nil)))

/-- A refusal in the second arm of a case analysis. -/
example : refusal (single [threeNaturals] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9], .mk [] [] [0], .mk [10] [] [10]]] [1])) =
    functionError ⟨.inputs, at_ 1 1, .number 1 0⟩ := by
  decide +kernel

/-- A refusal in the third arm of a case analysis. -/
example : refusal (single [threeNaturals] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1] [.mk [9] [] [9], .mk [10] [] [10], .mk [] [] [0]]] [1])) =
    functionError ⟨.inputs, at_ 1 1, .number 1 0⟩ := by
  decide +kernel

/-- A refusal after a case analysis. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [] [9], .mk [11] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]],
     .op ⟨3⟩ [5] (.literal .nat [1, 2]) []] [5])) =
    functionError ⟨.literal, at_ 1 3, .operation (.literal .nat [1, 2])⟩ := by
  decide +kernel

/-- A refusal after a loop. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10, 11] [] [11]),
     .op ⟨2⟩ [5] (.literal .nat []) []] [5])) =
    functionError ⟨.literal, at_ 1 2, .operation (.literal .nat [])⟩ := by
  decide +kernel

/-- A refusal after a block. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5]),
     .op ⟨3⟩ [6] (.literal .bool [2]) []] [6])) =
    functionError ⟨.literal, at_ 1 3, .operation (.literal .bool [2])⟩ := by
  decide +kernel

/-! ## Literals of each type -/

/-- The refusal, or nothing, of a literal of the type with the data. -/
def literalOf (τ : plain.Ty) (data : List Nat) : Option (DefinitionRefusal plain) :=
  refusal (single [] [τ] false (.mk [] [.op ⟨1⟩ [0] (.literal τ data) []] [0]))

/-- The refusal of a literal of the type with the data. -/
def literalRefused (τ : plain.Ty) (data : List Nat) : Option (DefinitionRefusal plain) :=
  functionError ⟨.literal, at_ 1 1, .operation (.literal τ data)⟩

/-- A literal applied to an operand: it takes none. -/
example : refusal (single [.nat] [.nat] false (.mk [0] [.op ⟨1⟩ [1] (.literal .nat [3]) [0]] [1])) =
    functionError ⟨.operands, at_ 1 1, .types [] [.nat]⟩ := by
  decide +kernel

/-- A natural reads one number: nothing left over, nothing missing. -/
example : literalOf .nat [1, 2] = literalRefused .nat [1, 2] ∧
    literalOf .nat [] = literalRefused .nat [] := by
  decide +kernel

/-- An `index<4>` reads a number below 4. -/
example : literalOf (.fin 4) [3] = none ∧ literalOf (.fin 4) [4] = literalRefused (.fin 4) [4] := by
  decide +kernel

/-- A sequence of a size reads that many items. -/
example : literalOf (.seq (.fin 256) (some 2)) [1, 2] = none ∧
    literalOf (.seq (.fin 256) (some 2)) [1] = literalRefused (.seq (.fin 256) (some 2)) [1] := by
  decide +kernel

/-- A sequence of any length reads its length first. -/
example : literalOf (.seq .nat none) [2, 5, 6] = none ∧
    literalOf (.seq .nat none) [3, 5, 6] = literalRefused (.seq .nat none) [3, 5, 6] := by
  decide +kernel

/-- A tuple of a natural and a truth value. -/
def natAndTruth : plain.Ty := .tuple (.cons .nat (.cons .bool .nil))
/-- A record of a natural and a truth value. -/
def natAndTruthRecord : plain.Ty := .record ⟨3⟩ false (.cons .nat (.cons .bool .nil))

/-- A tuple reads each component. -/
example : literalOf natAndTruth [5, 1] = none ∧
    literalOf natAndTruth [5, 2] = literalRefused natAndTruth [5, 2] := by
  decide +kernel

/-- A record reads each field. -/
example : literalOf natAndTruthRecord [5, 1] = none ∧
    literalOf natAndTruthRecord [5] = literalRefused natAndTruthRecord [5] := by
  decide +kernel

/-- A variant reads the position of its alternative, then the payload. -/
example : literalOf natOrBool [1, 0] = none ∧
    literalOf natOrBool [2, 0] = literalRefused natOrBool [2, 0] ∧
    literalOf natOrBool [1, 5] = literalRefused natOrBool [1, 5] := by
  decide +kernel

/-- A linear record without fields reads no data. -/
example : literalOf token [] = none := by decide +kernel

/-! ## Linear use at each construct -/

/-- A record of a natural and a linear value: linear, though not marked so. -/
def natAndToken : plain.Ty := .record ⟨6⟩ false (.cons .nat (.cons token .nil))

/-- A linear value given twice: refused at the definition, by its name, used twice. -/
def givenTwice (τ : plain.Ty) : Option (DefinitionRefusal plain) :=
  refusal (single [τ] [τ, τ] false (.mk [0] [] [0, 0]))

/-- Each type with a linear part is linear (LN1): a sequence of linear values, a tuple, a record
not marked linear and a variant with a linear part. -/
example : givenTwice (.seq token (some 1)) = functionError ⟨.linear, whole 1, .uses 0 2⟩ ∧
    givenTwice (.tuple (.cons token (.cons .nat .nil))) = functionError ⟨.linear, whole 1, .uses 0 2⟩ ∧
    givenTwice natAndToken = functionError ⟨.linear, whole 1, .uses 0 2⟩ ∧
    givenTwice natOrToken = functionError ⟨.linear, whole 1, .uses 0 2⟩ := by
  decide +kernel

/-- A choice gives a linear value that the rest does not use: refused at the choice, by the name
of its result. -/
example : refusal (single [.bool] [] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.owned .make [token] []) []] [5])
      (.mk [] [.op ⟨3⟩ [6] (.owned .make [token] []) []] [6])] [])) =
    functionError ⟨.linear, at_ 1 1, .uses 1 0⟩ := by
  decide +kernel

/-- Both regions of a choice give the linear value from around: it is used once, not twice. -/
example : refusal (single [token, .bool] [token] false (.mk [0, 1]
    [.choose ⟨1⟩ () 1 [2] (.mk [] [] [0]) (.mk [] [] [0])] [2])) = none := by
  decide +kernel

/-- A linear value from around a choice, after a natural: refused by its name, with its count in
the second region. -/
example : refusal (single [.nat, token, .bool] [token] false (.mk [0, 1, 2]
    [.choose ⟨1⟩ () 2 [3]
      (.mk [] [] [1]) (.mk [] [.op ⟨2⟩ [5] (.owned .make [token] []) []] [5])] [3])) =
    functionError ⟨.linear, at_ 1 1, .around 1 0⟩ := by
  decide +kernel

/-- The arms of a case analysis that use the linear value from around differently: refused at
the case analysis, as a value from around it (LN2), with its count in the arm that differs. -/
example : refusal (single [token, natOrBool] [token] false (.mk [0, 1]
    [.cases ⟨1⟩ () 1 [2]
      [.mk [9] [] [0], .mk [11] [.op ⟨2⟩ [10] (.owned .make [token] []) []] [10]]] [2])) =
    functionError ⟨.linear, at_ 1 1, .around 0 0⟩ := by
  decide +kernel

/-- Arms that both give the linear value from around: it is used once. -/
example : refusal (single [token, natOrBool] [token] false (.mk [0, 1]
    [.cases ⟨1⟩ () 1 [2] [.mk [9] [] [0], .mk [10] [] [0]]] [2])) = none := by
  decide +kernel

/-- A case analysis gives a linear value that the rest does not use: refused at the case
analysis, by the name of its result. -/
example : refusal (single [natOrBool] [] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [.op ⟨2⟩ [10] (.owned .make [token] []) []] [10],
       .mk [11] [.op ⟨3⟩ [12] (.owned .make [token] []) []] [12]]] [])) =
    functionError ⟨.linear, at_ 1 1, .uses 1 0⟩ := by
  decide +kernel

/-- A linear payload that its arm gives: the subject is used, and the payload too. -/
example : refusal (single [natOrToken] [token] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [.op ⟨2⟩ [10] (.owned .make [token] []) []] [10], .mk [11] [] [11]]] [1])) =
    none := by
  decide +kernel

/-- A case analysis without arms uses nothing, and is accepted. -/
example : refusal (single [.variant ⟨3⟩ .nil] [] false (.mk [0] [.cases ⟨1⟩ () 0 [] []] [])) =
    none := by
  decide +kernel

/-- A loop that carries a linear value and gives it back: its initial value is used once. -/
example : refusal (single [token] [token] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10, 11] [] [11])] [1])) = none := by
  decide +kernel

/-- A body that drops the carried linear value: refused at the loop, by the name of the body's
input. -/
example : refusal (single [token] [token] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1]
      (.mk [10, 11] [.op ⟨2⟩ [12] (.owned .make [token] []) []] [12])] [1])) =
    functionError ⟨.linear, at_ 1 1, .uses 11 0⟩ := by
  decide +kernel

/-- A loop whose carried linear result the rest does not use: refused at the loop, by the name of
its result. -/
example : refusal (single [token] [] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10, 11] [] [11])] [])) =
    functionError ⟨.linear, at_ 1 1, .uses 1 0⟩ := by
  decide +kernel

/-- The initial value of a carried linear value is a use: given again, the input is used
twice. -/
example : refusal (single [token] [token, token] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10, 11] [] [11])] [1, 0])) =
    functionError ⟨.linear, whole 1, .uses 0 2⟩ := by
  decide +kernel

/-- A block that gives the linear value from around: it is used once. -/
example : refusal (single [token] [token] false (.mk [0]
    [.block ⟨1⟩ 0 [1] (.mk [] [] [0])] [1])) = none := by
  decide +kernel

/-- A block gives a linear value that the rest does not use: refused at the block, by the name
of its result. -/
example : refusal (single [] [] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.owned .make [token] []) []] [5])] [])) =
    functionError ⟨.linear, at_ 1 1, .uses 1 0⟩ := by
  decide +kernel

/-- A linear value made inside a block and not used: the place of the refusal has the block. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk []
      [.op ⟨2⟩ [5] (.owned .make [token] []) [], .op ⟨3⟩ [6] (.literal .bool [0]) []] [6])] [1])) =
    functionError ⟨.linear, ⟨⟨1⟩, [(⟨1⟩, 0)], some ⟨2⟩, none⟩, .uses 5 0⟩ := by
  decide +kernel

/-- Two linear inputs, the second not used: refused by its name. -/
example : refusal (single [token, token] [token] false (.mk [0, 1] [] [0])) =
    functionError ⟨.linear, whole 1, .uses 1 0⟩ := by
  decide +kernel

/-- The parts of a record of a natural and a linear value, the linear one not used: refused by
its name. -/
example : refusal (single [natAndToken] [.nat] false
    (.mk [0] [.op ⟨1⟩ [1, 2] (.owned .take [natAndToken] []) [0]] [1])) =
    functionError ⟨.linear, at_ 1 1, .uses 2 0⟩ := by
  decide +kernel

/-- A vocabulary with one nominal type, which is linear, and no row, law or literal. -/
def linearNominal : Vocabulary where
  TypeKey := Unit
  RowKey := Empty
  LawKey := Empty
  row r := nomatch r
  law r := nomatch r
  literal _ _ := false
  linear _ := true
  decided r := nomatch r

/-- The refusal, or nothing, of a function over `linearNominal` that gives its one input as the
outputs named. -/
def nominalGiven (exit : List Nat) : Option (DefinitionRefusal linearNominal) :=
  match elaborateFunctions (V := linearNominal)
      ⟨[.fn ⟨1⟩ [.nominal ()] (exit.map fun _ => .nominal ()) false none Summary.empty (.mk [0] [] exit)]⟩ with
  | .ok _ => none
  | .error refusals => refusals.head?

/-- A nominal type that the vocabulary says is linear is linear: given once it is accepted, and
given twice it is refused. -/
example : nominalGiven [0] = none ∧
    nominalGiven [0, 0] = functionError ⟨.linear, whole 1, .uses 0 2⟩ := by
  decide +kernel

/-! ## Single assignment: a definition binds each name at one place -/

/-- The name of the input bound again, to a truth value: refused at the instruction that binds it
again, by the rule `assignment`, with the name. -/
def shadowed : NamedProgram plain :=
  single [.nat] [.bool] false (.mk [0] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])

example : refusal shadowed = functionError ⟨.assignment, at_ 1 1, .name 0⟩ := by decide +kernel

/-- The rule `outputs` is decided before single assignment: the same program, whose exit is
typed by the later binding, given as a natural, is refused for its outputs. -/
example : refusal (single [.nat] [.nat] false
    (.mk [0] [.op ⟨1⟩ [0] (.literal .bool [1]) []] [0])) =
    functionError ⟨.outputs, whole 1, .types [.nat] [.bool]⟩ := by
  decide +kernel

/-- A result bound twice in one body: refused at the second instruction that binds it. -/
example : refusal (single [] [.nat] false (.mk []
    [.op ⟨1⟩ [1] (.literal .nat [3]) [], .op ⟨2⟩ [1] (.literal .nat [4]) []] [1])) =
    functionError ⟨.assignment, at_ 1 2, .name 1⟩ := by
  decide +kernel

/-- Two results of one instruction with one name: refused at the instruction. -/
example : refusal (single [natAndTruth] [.bool] false
    (.mk [0] [.op ⟨1⟩ [1, 1] (.owned .take [natAndTruth] []) [0]] [1])) =
    functionError ⟨.assignment, at_ 1 1, .name 1⟩ := by
  decide +kernel

/-- Two inputs of the definition with one name: no instruction binds it, so it is refused at the
definition as a whole. -/
example : refusal (single [.nat, .nat] [.nat] false (.mk [0, 0] [] [0])) =
    functionError ⟨.assignment, whole 1, .name 0⟩ := by
  decide +kernel

/-- An input of the region of a loop with the name of the definition's input around it: refused at
the loop, which binds its region's inputs. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.loop ⟨1⟩ () (.fixed 3) [0] [1] (.mk [10, 0] [] [0])] [1])) =
    functionError ⟨.assignment, at_ 1 1, .name 0⟩ := by
  decide +kernel

/-- Two sibling regions of a choice that bind one name: refused at the instruction of the second
region that binds it. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.choose ⟨1⟩ () 0 [1]
      (.mk [] [.op ⟨2⟩ [5] (.literal .nat [3]) []] [5])
      (.mk [] [.op ⟨3⟩ [5] (.literal .nat [4]) []] [5])] [1])) =
    functionError ⟨.assignment, at_ 1 3, .name 5⟩ := by
  decide +kernel

/-- Two sibling arms of a case analysis whose payloads have one name: refused at the case
analysis, which binds its arms' payloads. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.cases ⟨1⟩ () 0 [1]
      [.mk [9] [] [9],
       .mk [9] [.op ⟨2⟩ [10] (.literal .nat [0]) []] [10]]] [1])) =
    functionError ⟨.assignment, at_ 1 1, .name 9⟩ := by
  decide +kernel

/-- Two blocks of a stepped loop whose bodies bind one name: refused inside the second block, at
its instruction, under its number. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5]),
     .block ⟨1⟩ 1 [2] (.mk [] [.op ⟨2⟩ [5] (.owned .boolNot [] []) [1]] [5])] [2])) =
    functionError ⟨.assignment, ⟨⟨1⟩, [(⟨1⟩, 1)], some ⟨2⟩, none⟩, .name 5⟩ := by
  decide +kernel

/-- A name bound by an operation, then again as the result of a choice: refused at the choice,
which binds its results. Its regions bind nothing. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.op ⟨1⟩ [1] (.literal .nat [3]) [],
     .choose ⟨2⟩ () 0 [1] (.mk [] [] [1]) (.mk [] [] [1])] [1])) =
    functionError ⟨.assignment, at_ 1 2, .name 1⟩ := by
  decide +kernel

/-- A name bound by an operation, then again as the result of a case analysis: refused at the
case analysis, which binds its results. Its arms' payloads have other names. -/
example : refusal (single [natOrBool] [.nat] false (.mk [0]
    [.op ⟨1⟩ [1] (.literal .nat [3]) [],
     .cases ⟨2⟩ () 0 [1]
      [.mk [9] [] [9],
       .mk [10] [.op ⟨3⟩ [11] (.literal .nat [0]) []] [11]]] [1])) =
    functionError ⟨.assignment, at_ 1 2, .name 1⟩ := by
  decide +kernel

/-- A name bound by an operation, then again as the result of a loop: refused at the loop, which
binds its results. The inputs of its region have other names. -/
example : refusal (single [.nat] [.nat] false (.mk [0]
    [.op ⟨1⟩ [1] (.literal .nat [3]) [],
     .loop ⟨2⟩ () (.fixed 3) [0] [1] (.mk [10, 11] [] [11])] [1])) =
    functionError ⟨.assignment, at_ 1 2, .name 1⟩ := by
  decide +kernel

/-- The same choice inside a block: the place has the block around the choice. -/
example : refusal (single [.bool] [.nat] false (.mk [0]
    [.op ⟨1⟩ [1] (.literal .nat [3]) [],
     .block ⟨3⟩ 0 [2] (.mk []
      [.choose ⟨2⟩ () 0 [1] (.mk [] [] [1]) (.mk [] [] [1])] [1])] [2])) =
    functionError ⟨.assignment, ⟨⟨1⟩, [(⟨3⟩, 0)], some ⟨2⟩, none⟩, .name 1⟩ := by
  decide +kernel

/-- Two blocks of a stepped loop that bind one name as their results: refused at the second
block, which binds it. -/
example : refusal (single [] [.bool] false (.mk []
    [.block ⟨1⟩ 0 [1] (.mk [] [.op ⟨2⟩ [5] (.literal .bool [0]) []] [5]),
     .block ⟨1⟩ 1 [1] (.mk [] [.op ⟨2⟩ [6] (.owned .boolNot [] []) [1]] [6])] [1])) =
    functionError ⟨.assignment, at_ 1 1, .name 1⟩ := by
  decide +kernel

/-- One name in two definitions: each definition binds it at one place, and the program is
accepted. -/
def sameNameTwice : NamedProgram plain :=
  ⟨[.fn ⟨1⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.owned .natAdd [] []) [0, 0]] [1]),
    .fn ⟨2⟩ [.nat] [.nat] false none Summary.empty (.mk [0] [.op ⟨1⟩ [1] (.call ⟨1⟩) [0]] [1])]⟩

example : refusal sameNameTwice = none := by decide +kernel

/-! ## A case analysis without an arm -/

/-- A variant without alternatives. -/
def nothing : plain.Ty := .variant ⟨3⟩ .nil

/-- A case analysis of a value of a variant without alternatives, which has no arm, giving
values of the types `mid`, named from `1`, none of which the rest uses. -/
def armless (mid : List plain.Ty) : Term (localDialect plain []) (Ctx.positional [nothing]) [] :=
  .cases (mid := mid) ⟨1⟩ () (var 0) ⟨⟨3⟩, .nil, rfl, rfl⟩ (fun _ _ => trivial) .nil
    (Names.counting 1 mid) (.ret .nil)

/-- What the case analysis at the start of a term gives. -/
def gives {Γ : Ctx plain.Ty} {outs : List plain.Ty} : Term (localDialect plain []) Γ outs →
    List plain.Ty
  | .cases (mid := mid) .. => mid
  | _ => []

/-- Two terms that differ only in what a case analysis without an arm gives are erased alike:
the erased form of a case analysis writes the names of its results, not their types. This is
why what elaboration decides about a body includes that its case analyses without an arm give
nothing (`FnConditions.armed`): the second term satisfies no conditions, and the round trip
holds of every typed program. -/
example : eraseBody (fun o => LocalOp.print o) (fun _ => ()) (armless [.nat]) =
    eraseBody (fun o => LocalOp.print o) (fun _ => ()) (armless [.bool]) := rfl

example : armless [.nat] ≠ armless [.bool] := fun same => by
  have different := congrArg gives same
  simp [gives, armless] at different

example : (armless []).armed = true ∧ (armless [.nat]).armed = false := by decide +kernel

/-! ## The round trip of each accepted program -/

/-- The erased form of the program that a program elaborates to, elaborated. -/
def again (named : NamedProgram plain) : Except (List (DefinitionRefusal plain)) (Typed plain) :=
  (elaborateFunctions named).bind fun p => elaborateFunctions (erase p)

/-- The erased form of the program that a program elaborates to. -/
def erased (named : NamedProgram plain) :
    Except (List (DefinitionRefusal plain)) (NamedProgram plain) :=
  (elaborateFunctions named).map erase

/-- Erased then elaborated: the erased form of what each accepted program elaborates to
elaborates to the same typed program. -/
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
example : again sameNameTwice = elaborateFunctions sameNameTwice := by rfl

/-- Elaborated then erased: each accepted program is the erased form of what it elaborates to,
with its own names. -/
example : erased add = .ok add := by rfl
example : erased literal = .ok literal := by rfl
example : erased calls = .ok calls := by rfl
example : erased guarded = .ok guarded := by rfl
example : erased chosen = .ok chosen := by rfl
example : erased analysed = .ok analysed := by rfl
example : erased looped = .ok looped := by rfl
example : erased counted = .ok counted := by rfl
example : erased blocked = .ok blocked := by rfl
example : erased linear = .ok linear := by rfl
example : erased sameNameTwice = .ok sameNameTwice := by rfl

/-! ## Located protocol calls -/

/-- A callee returns a value held by its role zero. The caller chooses who plays that role. -/
def locatedCaller (callee : Key) (roles holders : List Role) : NamedProgram plain :=
  ⟨[.protocol ⟨30⟩ 2 [Shapes.nat [0]] [Shapes.nat [0]] (.mk [1] [] [1]),
    .protocol ⟨31⟩ 2 [Shapes.nat holders] [Shapes.nat [1]]
      (.mk [1] [.op ⟨4⟩ [2] (.apply callee roles) [1]] [2])]⟩

private def firstProtocolError (p : NamedProgram plain) : Option (DefinitionRefusal plain) :=
  match elaborateProgram p with
  | .ok _ => none
  | .error failures => failures.head?

example : (elaborateProgram (locatedCaller ⟨30⟩ [1, 0] [1])).isOk := by decide +kernel
set_option maxHeartbeats 3000000 in
example : (elaborateProgram (locatedCaller ⟨30⟩ [1, 0] [1])).map erase =
    .ok (locatedCaller ⟨30⟩ [1, 0] [1]) := by rfl
example : firstProtocolError (locatedCaller ⟨30⟩ [1, 1] [1]) =
    some (.protocol ⟨.operands, at_ 31 4, .operation (.apply ⟨30⟩ [1, 1])⟩) := by decide +kernel
example : firstProtocolError (locatedCaller ⟨30⟩ [1] [1]) =
    some (.protocol ⟨.operands, at_ 31 4, .number 2 1⟩) := by decide +kernel
example : firstProtocolError (locatedCaller ⟨30⟩ [0, 1] [1]) =
    some (.protocol ⟨.operands, at_ 31 4, .types [Shapes.nat [0]] [Shapes.nat [1]]⟩) := by
  decide +kernel
example : firstProtocolError (locatedCaller ⟨99⟩ [1, 0] [1]) =
    some (.protocol ⟨.callee, at_ 31 4, .callee ⟨99⟩ 0⟩) := by decide +kernel
example : firstProtocolError ⟨[.protocol ⟨1⟩ 1 [Shapes.nat [2]] [] (.mk [0] [] [])]⟩ =
    some (.protocol ⟨.portHolders, whole 1, .given [Shapes.nat [2]]⟩) := by decide +kernel
example : firstProtocolError ⟨[.protocol ⟨1⟩ 2 [Shapes.nat [1]] []
    (.mk [0] [.op ⟨4⟩ [1] (.event (.flow .message 0 [1]) .nat) [0]] [])]⟩ =
    some (.protocol ⟨.operands, at_ 1 4, .operation (.event (.flow .message 0 [1]) .nat)⟩) := by
  decide +kernel

/-- Erasing and reading the two nested, communicating protocols recovers the whole program. -/
example : elaborateProgram (erase (⟨_, Shapes.roundsProgram, by decide⟩ : Typed plain)) =
    .ok ⟨_, Shapes.roundsProgram, by decide⟩ := elaborateProgram_erase _


end Zkc.Core.Elaboration

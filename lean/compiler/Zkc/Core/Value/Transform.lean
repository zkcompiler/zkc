module

public import Zkc.Core.Value.Follows
public import Zkc.Core.Facts.Local
public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-!
A transformation of a function, as a checked step.

What the decision is told of a function: every operation is a value, by its written form, except
a call of a function that can stop with a reason, which is kept in order (`localValueRules`);
following decides types and performers by equality and two operations by their written forms
(`localSkelRules`).

A transformation takes a stored function and gives a stored function. Nothing about how the
target was found is trusted. The step elaborates both, checks the facts of both, and decides
that the target follows the skeleton of the source (`transform`). What it returns is data: the
two accepted functions (`Transformed`), or why it refuses (`TransformRefusal`). What its success
means is in `Value/TransformSound.lean`: on valid inputs the two have the same meaning, the target
is safe by its own check of facts, it is the source of the next step, and the stored forms of
what the step returns are what it was given.

Two programs over the same headers are compared function by function (`Defs.follows`): each
function of the second follows the skeleton of the function of the first with its header. That
the functions of the second then mean what those of the first mean, their callers included, is
`Defs.follows_sound` (`Admission/Programs.lean`).
-/

namespace Zkc.Core

section
variable (V : Vocabulary)

/-- What the value form is told of the operations of a function: every operation is a value,
by its written form, except a call of a function that can stop with a reason, which is kept in
order. The table places the applications as the check of facts places them. -/
def localValueRules (fns : List (FnHeader V)) : ValueRules (localDialect V fns) (LocalRaw V) where
  written := fun o => bif LocalOp.canStop o then none else some (LocalOp.print o)
  place := (localFactRules V fns).place

/-- What following decides for a function: types and performers by equality, and two operations
by their written forms. -/
def localSkelRules (fns : List (FnHeader V)) : SkelRules (localDialect V fns) where
  sameTy := inferInstanceAs (DecidableEq V.Ty)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun o o' => decide (LocalOp.print o = LocalOp.print o')

end

variable {V : Vocabulary}

/-! ## One step -/

/-- A function accepted against the headers before it: its input names, its body with what
elaboration decided about it, and the bounds of its loops that the check of facts gives. -/
structure AcceptedFn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  inputs : Names hdr.ins
  body : Fn V fns hdr inputs
  conditions : FnConditions body
  bounds : List (Place × Nat)

/-- A stored function, accepted: elaborated, then its facts checked. Every refusal otherwise. -/
def acceptFn (fns : List (FnHeader V)) (hdr : FnHeader V) (region : Region (LocalRaw V) Unit) :
    Except (List (ProgramRefusal V)) (AcceptedFn V fns hdr) :=
  match elabFn fns hdr region with
  | .error refusal => .error [refusal]
  | .ok ⟨inputs, body, conditions⟩ =>
      match checkFacts (localFactRules V fns) hdr.key none inputs body with
      | .error refusals => .error refusals
      | .ok bounds => .ok ⟨inputs, body, conditions, bounds⟩

/-- Why a transformation of a function is not accepted: its source or its target is refused, or
the decision cannot tell that the target means what the source means. -/
inductive TransformRefusal (V : Vocabulary) where
  | source (refusals : List (ProgramRefusal V))
  | target (refusals : List (ProgramRefusal V))
  | undecided

/-- A step of transformation of one function: the source and the target, both accepted. -/
structure Transformed (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  source : AcceptedFn V fns hdr
  target : AcceptedFn V fns hdr

/-- The step from a stored function to a stored function with the same header: both are
accepted, and the target follows the skeleton of the source. -/
def transform (fns : List (FnHeader V)) (hdr : FnHeader V)
    (source target : Region (LocalRaw V) Unit) :
    Except (TransformRefusal V) (Transformed V fns hdr) :=
  match acceptFn fns hdr source with
  | .error refusals => .error (.source refusals)
  | .ok accepted =>
      match acceptFn fns hdr target with
      | .error refusals => .error (.target refusals)
      | .ok accepted' =>
          if same (localValueRules V fns) (localSkelRules V fns) accepted.inputs accepted'.inputs
              accepted.body accepted'.body then .ok ⟨accepted, accepted'⟩
          else .error .undecided

/-! ## Two programs over the same headers -/

/-- A function of the first program, against a program whose headers are said to be the first's
up to that function: when the second's last definition is a function too, whether it follows
the first's skeleton and the definitions before it follow (`rest`); a protocol there does not
follow. The headers are an argument with an equation, so that the second program can be taken
apart whatever its last definition is. -/
def Defs.followsFn (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : FnHeader V) (inputs : Names hdr.ins) (body : Fn V fns hdr inputs)
    (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨hdr :: fns, protocols⟩ → Bool
  | _, .nil, same => nomatch same
  | _, .fn (hs := hs) _ inputs' body' _ rest', rfl =>
      same (localValueRules V hs.fns) (localSkelRules V hs.fns) inputs inputs' body body' &&
        rest rest'
  | _, .protocol .., _ => false

/-- A protocol of the first program, against a program whose headers are said to be the first's
up to that protocol: when the second's last definition is a protocol too, whether the
definitions before it follow (`rest`); the protocols are not compared. A function there does not
follow. -/
def Defs.followsProtocol (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : ProtocolHeader V) (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨fns, hdr :: protocols⟩ → Bool
  | _, .nil, same => nomatch same
  | _, .fn .., _ => false
  | _, .protocol _ _ _ _ rest', rfl => rest rest'

/-- Whether the functions of the second program follow the skeletons of those of the first,
one by one: the two programs have the same headers, and each function is decided against the one
with its header. A protocol is not compared. Two programs whose functions and protocols come in
another order do not follow. The recursion is on the first program; the second is taken apart at
each definition by `Defs.followsFn` and `Defs.followsProtocol`. -/
def Defs.follows : {hs : Headers V} → Defs V hs → Defs V hs → Bool
  | _, .nil, _ => true
  | _, .fn (hs := hs) hdr inputs body _ rest, defs' =>
      Defs.followsFn hs.fns hs.protocols hdr inputs body (fun rest' => Defs.follows rest rest')
        defs' rfl
  | _, .protocol (hs := hs) hdr _ _ _ rest, defs' =>
      Defs.followsProtocol hs.fns hs.protocols hdr (fun rest' => Defs.follows rest rest') defs' rfl

end Zkc.Core

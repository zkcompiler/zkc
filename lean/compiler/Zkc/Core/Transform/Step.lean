module

public import Zkc.Core.Facts.Walk
public import Zkc.Core.Facts.Local
public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-!
A transformation of a function, as a checked step.

A transformation takes a stored function and gives a stored function. Nothing about how the
target was found is trusted. The step elaborates the source and analyses it once
(`Analysis.analyse`), with the rules of the function dialect (`localFactRules`, `localSkelRules`);
it elaborates the target and follows the analysis of the source with it (`Analysis.follow`)
(`transform`). The target is not analysed by itself: every instruction that it keeps in order
must be the next entry of the source's skeleton, its values join the source's table, and its
requirements are decided from what is known where it evaluates them. What the step returns is
data: the two accepted functions (`Transformed`), or why it refuses (`TransformRefusal`): the
source refused, the target refused by elaboration or by the analysis while it follows, or the
places where the target is not the next entry of the source's skeleton. What its success means
is in `Transform/StepSound.lean`: on valid inputs the two have the same meaning, the target is
safe, two steps compose, and the stored forms of what the step returns are what it was given.

Two programs over the same headers are compared function by function (`Defs.functionsFollow`):
each function of the second follows the analysis of the function of the first with its header
with no place that differs. That the functions of the second then mean what those of the first
mean, their callers included, when both programs are accepted, is `Defs.functionsFollow_sound`
(`Admission/Programs.lean`).
-/

namespace Zkc.Core

open Analysis

variable {V : Vocabulary}

/-! ## One step -/

/-- A function accepted against the headers before it: its input names, its body with what
elaboration decided about it, and the bounds of its loops that the analysis gives (by its own
check of facts, or while it follows the function that it replaces). -/
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
      match checkFacts (localFactRules V fns) (localSkelRules V fns) hdr.key none inputs body with
      | .error refusals => .error refusals
      | .ok bounds => .ok ⟨inputs, body, conditions, bounds⟩

/-- Why a transformation of a function is not accepted: its source is refused; its target is
refused, by elaboration or by the analysis while it follows the source; or the target is not
the next entry of the source's skeleton at the places given. -/
inductive TransformRefusal (V : Vocabulary) where
  | source (refusals : List (ProgramRefusal V))
  | target (refusals : List (ProgramRefusal V))
  | differs (places : List Place)

/-- A step of transformation of one function: the source, accepted by the check of facts, and
the target, accepted while it follows the analysis of the source. -/
structure Transformed (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  source : AcceptedFn V fns hdr
  target : AcceptedFn V fns hdr

/-- The step from a stored function to a stored function with the same header: the source is
elaborated and analysed, and the target is elaborated and follows the analysis of the source
with no refusal and no place that differs. What it returns: the source as accepted, and the
target with the bounds of its loops found while following. -/
def transform (fns : List (FnHeader V)) (hdr : FnHeader V)
    (source target : Region (LocalRaw V) Unit) :
    Except (TransformRefusal V) (Transformed V fns hdr) :=
  match elabFn fns hdr source with
  | .error refusal => .error (.source [refusal])
  | .ok ⟨inputs, body, conditions⟩ =>
      let first := analyse (localFactRules V fns) (localSkelRules V fns) hdr.key none inputs body
      match first.state.st.refusals with
      | refusal :: refusals => .error (.source (refusal :: refusals).reverse)
      | [] =>
          match elabFn fns hdr target with
          | .error refusal => .error (.target [refusal])
          | .ok ⟨inputs', body', conditions'⟩ =>
              let second := follow (localFactRules V fns) (localSkelRules V fns) hdr.key none first
                inputs' body'
              match second.state.st.refusals, second.state.differs with
              | [], [] =>
                  .ok ⟨⟨inputs, body, conditions, first.state.st.bounds.reverse⟩,
                    ⟨inputs', body', conditions', second.state.st.bounds.reverse⟩⟩
              | [], place :: places => .error (.differs (place :: places).reverse)
              | refusal :: refusals, _ => .error (.target (refusal :: refusals).reverse)

/-! ## Two programs over the same headers -/

/-- A function of the first program, against a program whose headers are said to be the first's
up to that function: when the second's last definition is a function too, whether it follows
the analysis of the first's with no place that differs and the definitions before it follow
(`rest`); a protocol there does not follow. -/
def Defs.followsFn (fns : List (FnHeader V)) (protocols : List (ProtocolHeader V))
    (hdr : FnHeader V) (inputs : Names hdr.ins) (body : Fn V fns hdr inputs)
    (rest : Defs V ⟨fns, protocols⟩ → Bool) :
    {hs : Headers V} → Defs V hs → hs = ⟨hdr :: fns, protocols⟩ → Bool
  | _, .nil, impossible => nomatch impossible
  | _, .fn (hs := hs) _ inputs' body' _ rest', rfl =>
      (follow (localFactRules V hs.fns) (localSkelRules V hs.fns) hdr.key none
          (analyse (localFactRules V hs.fns) (localSkelRules V hs.fns) hdr.key none inputs body)
          inputs' body').state.differs.isEmpty && rest rest'
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

/-- Whether the functions of the second program follow those of the first, one by one: the two
programs have the same headers, and each function follows the analysis of the one with its
header with no place that differs. A protocol is not compared. -/
def Defs.functionsFollow : {hs : Headers V} → Defs V hs → Defs V hs → Bool
  | _, .nil, _ => true
  | _, .fn (hs := hs) hdr inputs body _ rest, defs' =>
      Defs.followsFn hs.fns hs.protocols hdr inputs body
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl
  | _, .protocol (hs := hs) hdr _ _ _ rest, defs' =>
      Defs.followsProtocol hs.fns hs.protocols hdr
        (fun rest' => Defs.functionsFollow rest rest') defs' rfl

end Zkc.Core

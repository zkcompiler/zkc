module

public import Zkc.Core.Facts.Walk
public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Facts
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-!
A function elaborated against the headers before it, the judgments about it, and the two
decisions of the analysis that produce them.

There is one record of data for a function, the elaborated function (`TypedFn`): its input
names, its body and what elaboration decided about it (`typeFn`). What is said of it is a
proposition, against every table of callees with distinct keys that never stop `undefined` on
valid inputs, keep validity, and stop only `undefined` where their headers say that they cannot
stop (`Callees`): it is safe, never stopping `undefined` on valid inputs and returning valid
values (`TypedFn.Safe`); its loops respect bounds (`TypedFn.Bounded`); both, it is assured with
those bounds (`TypedFn.Assured`); two of them mean the same on every valid input
(`TypedFn.SameAs`).

Two decisions produce these judgments (`Transform/StepSound.lean`). The check of facts of a
function (`TypedFn.check`) gives the bounds of its loops or its refusals; when it accepts, the
function is assured. Whether a second function follows the analysis of a first
(`TypedFn.follows`): the second is elaborated and follows the analysis of the first
(`Analysis.follow`); it is not analysed by itself: every instruction that it keeps in order must
be the next entry of the first's skeleton, its values join the first's table, and its
requirements are decided from what is known where it evaluates them. It gives the refusals of the
analysis while the second follows and the places where the second is not the next entry of the
skeleton, or, when there is neither, the bounds of the second's loops. The refusals of the
first's own analysis are not read: when the first is safe, by whatever route, the second is
assured and means the same. Why a step from one function to a stored one is refused is
`StepRefusal`; the step itself, which takes an assured function and gives one, is
`AssuredFn.step` (`Transform/Assured.lean`).
-/

namespace Zkc.Core

open Analysis

variable {V : Vocabulary}

/-! ## A function and the judgments about it -/

/-- A function elaborated against the headers before it: its input names and its body with
what elaboration decided about it. -/
structure TypedFn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  inputs : Names hdr.ins
  body : Fn V fns hdr inputs
  conditions : FnConditions body

/-- The elaboration of a stored function. -/
def typeFn (fns : List (FnHeader V)) (hdr : FnHeader V) (region : Region (LocalRaw V) Unit) :
    Except (ProgramRefusal V) (TypedFn V fns hdr) :=
  match elabFn fns hdr region with
  | .error refusal => .error refusal
  | .ok ⟨inputs, body, conditions⟩ => .ok ⟨inputs, body, conditions⟩

section
variable {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- The meaning of a function on inputs, against callees. -/
def TypedFn.meaning (f : TypedFn V fns hdr) (M : Model V) (table : FnTable M fns)
    (ins : HList M.Val hdr.ins) : Local (HList M.Val hdr.outs) :=
  f.body.denote (localSem M fns table) [] (Env.empty.extend f.inputs ins)

/-- A function is safe: against every callees, on valid inputs, it never stops `undefined` and
returns valid values. -/
def TypedFn.Safe (f : TypedFn V fns hdr) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table →
    ∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
      (f.meaning M table ins).Every (fun _ _ => True) (fun outs => outs.All M.Valid)
        (· ≠ .undefined)

/-- The loops of a function respect bounds: against every callees, on valid inputs, every loop
that a run reaches runs at most as often as an annotation says, for every annotation whose
entries at this function are among the bounds. -/
def TypedFn.Bounded (f : TypedFn V fns hdr) (bounds : List (Place × Nat)) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table → ∀ F : List (Place × Nat),
    (∀ p b, (p, b) ∈ F → p.definition = hdr.key → p.role = none → (p, b) ∈ bounds) →
    ∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
      f.body.EveryLoop (localSem M fns table) (fun _ _ => True)
        (Annotation.Bounded ⟨F⟩ hdr.key none) [] [] (Env.empty.extend f.inputs ins)

/-- A function is assured, with the bounds of its loops. -/
structure TypedFn.Assured (f : TypedFn V fns hdr) (bounds : List (Place × Nat)) : Prop where
  safe : f.Safe
  bounded : f.Bounded bounds

/-- Two functions have the same meaning on every valid input, against every callees. -/
def TypedFn.SameAs (f g : TypedFn V fns hdr) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table →
    ∀ ins : HList M.Val hdr.ins, ins.All M.Valid → f.meaning M table ins = g.meaning M table ins

/-! ## The two decisions -/

/-- The check of facts of an elaborated function: its refusals, or the bounds of its loops. -/
def TypedFn.check (f : TypedFn V fns hdr) : Except (List (ProgramRefusal V)) (List (Place × Nat)) :=
  checkFacts (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩ f.inputs f.body

/-- Whether a second function follows the analysis of a first: the refusals of the analysis
while it follows and the places where it is not the next entry of the first's skeleton, or,
when there is neither, the bounds of the second's loops. The refusals of the first's own
analysis are not read: the first is assured by whoever gives it. -/
def TypedFn.follows (source target : TypedFn V fns hdr) :
    Except (List (ProgramRefusal V) × List Place) (List (Place × Nat)) :=
  let first := analyse (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩
    source.inputs source.body
  let second := follow (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩ first
    target.inputs target.body
  match second.state.st.refusals, second.state.differs with
  | [], [] => .ok second.state.st.bounds.reverse
  | refusals, places => .error (refusals.reverse, places.reverse)

end

/-- Why a step is not accepted: its target does not elaborate (no place: it was not walked) or
is refused by the analysis while it follows, with the places where it differs, if any; or,
with no refusal, the places where it differs. -/
inductive StepRefusal (V : Vocabulary) where
  | target (refusals : List (ProgramRefusal V)) (differs : List Place)
  | differs (places : List Place)

end Zkc.Core

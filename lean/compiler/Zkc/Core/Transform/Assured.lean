module

public import Zkc.Core.Transform.StepSound

@[expose] public section

/-!
An assured function, the two ways to make one, and the step of a transformation.

What a pipeline of transformations passes along is a function with the bounds of its loops and
the proposition that it is assured with them (`AssuredFn`). It can be made only with that
proposition, so a step cannot be taken from a function that nobody assured. There are two ways
to make one. Admission by the source language's checks (`admitFn`): the stored function
elaborates and the check of facts accepts it (`TypedFn.check_assured`). A step from an assured
function to a stored target (`AssuredFn.step`): the target elaborates and follows the analysis of
the source with no refusal and no place that differs (`TypedFn.follows_assured`, from the
source's safety, which it carries). A step never admits its source again: the source is assured
by whoever made it. Each carries its proof, so it is defined after the theorems that give it.

A step relates functions with the same meaning (`AssuredFn.step_same`); two steps compose with
no condition on the middle function (`AssuredFn.step_then`); two steps from one function give
functions with the same meaning (`AssuredFn.step_both`); and the stored form of what admission
and a step return is what they were given (`admitFn_erases`, `AssuredFn.step_erases`).
-/

namespace Zkc.Core

variable {V : Vocabulary}

/-! ## An assured function and the two ways to make one -/

/-- A function with the bounds of its loops and the fact that it is assured with them. -/
structure AssuredFn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  fn : TypedFn V fns hdr
  bounds : List (Place × Nat)
  assured : fn.Assured bounds

/-- The admission of a stored function by the source language's checks: it elaborates and the
check of facts accepts it. The first way to have an assured function. -/
def admitFn (fns : List (FnHeader V)) (hdr : FnHeader V) (region : Region (LocalRaw V) Unit) :
    Except (List (ProgramRefusal V)) (AssuredFn V fns hdr) :=
  match typeFn fns hdr region with
  | .error refusal => .error [refusal]
  | .ok f =>
      match checked : f.check with
      | .error refusals => .error refusals
      | .ok bounds => .ok ⟨f, bounds, f.check_assured checked⟩

/-- A step from an assured function to a stored target: the target elaborates and follows the
analysis of the source. The second way to have an assured function. -/
def AssuredFn.step {fns : List (FnHeader V)} {hdr : FnHeader V} (source : AssuredFn V fns hdr)
    (target : Region (LocalRaw V) Unit) : Except (StepRefusal V) (AssuredFn V fns hdr) :=
  match typeFn fns hdr target with
  | .error refusal => .error (.target [refusal] [])
  | .ok second =>
      match followed : source.fn.follows second with
      | .ok bounds =>
          .ok ⟨second, bounds, (TypedFn.follows_assured source.assured.safe followed).1⟩
      | .error ([], places) => .error (.differs places)
      | .error (refusals, places) => .error (.target refusals places)

/-! ## What admission and a step give -/

section
variable {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- What admission gives: the stored function typed, whose facts the check accepts with the
bounds given. -/
theorem admitFn_ok {region : Region (LocalRaw V) Unit} {admitted : AssuredFn V fns hdr}
    (accepted : admitFn fns hdr region = .ok admitted) :
    typeFn fns hdr region = .ok admitted.fn ∧ admitted.fn.check = .ok admitted.bounds := by
  unfold admitFn at accepted
  split at accepted
  · cases accepted
  · rename_i f typed
    split at accepted
    · cases accepted
    · rename_i bounds checked
      cases accepted
      exact ⟨typed, checked⟩

/-- What a step gives: the target typed, which follows the analysis of the source with the
bounds given. -/
theorem AssuredFn.step_ok {source next : AssuredFn V fns hdr} {target : Region (LocalRaw V) Unit}
    (accepted : source.step target = .ok next) :
    typeFn fns hdr target = .ok next.fn ∧ source.fn.follows next.fn = .ok next.bounds := by
  unfold AssuredFn.step at accepted
  split at accepted
  · cases accepted
  · rename_i second typed
    split at accepted
    · rename_i bounds followed
      cases accepted
      exact ⟨typed, followed⟩
    · cases accepted
    · cases accepted

/-- **The target of a step means the same as its source.** -/
theorem AssuredFn.step_same {source next : AssuredFn V fns hdr}
    {target : Region (LocalRaw V) Unit} (accepted : source.step target = .ok next) :
    source.fn.SameAs next.fn :=
  (TypedFn.follows_assured source.assured.safe (AssuredFn.step_ok accepted).2).2

/-- **Two steps compose**, with no condition on the middle function: the source of the first
and the target of the second mean the same. The middle function is never admitted again. -/
theorem AssuredFn.step_then {first second third : AssuredFn V fns hdr}
    {middle last : Region (LocalRaw V) Unit} (accepted : first.step middle = .ok second)
    (accepted' : second.step last = .ok third) : first.fn.SameAs third.fn :=
  (AssuredFn.step_same accepted).trans (AssuredFn.step_same accepted')

/-- **Two steps from one function give functions with the same meaning.** -/
theorem AssuredFn.step_both {source one other : AssuredFn V fns hdr}
    {left right : Region (LocalRaw V) Unit} (accepted : source.step left = .ok one)
    (accepted' : source.step right = .ok other) : one.fn.SameAs other.fn :=
  (AssuredFn.step_same accepted).symm.trans (AssuredFn.step_same accepted')

/-- The stored form of what admission returns is what it was given. -/
theorem admitFn_erases {region : Region (LocalRaw V) Unit} {admitted : AssuredFn V fns hdr}
    (accepted : admitFn fns hdr region = .ok admitted) :
    eraseFn admitted.fn.inputs admitted.fn.body = region :=
  eraseFn_elab region (typeFn_ok (admitFn_ok accepted).1)

/-- The stored form of what a step returns is the target that it was given. -/
theorem AssuredFn.step_erases {source next : AssuredFn V fns hdr}
    {target : Region (LocalRaw V) Unit} (accepted : source.step target = .ok next) :
    eraseFn next.fn.inputs next.fn.body = target :=
  eraseFn_elab target (typeFn_ok (AssuredFn.step_ok accepted).1)

end

end Zkc.Core

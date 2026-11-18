module

public import Zkc.Core.Facts.Loops
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-! Elaborated functions, their execution and their assurance and equivalence judgments. -/

namespace Zkc.Core

variable {V : Vocabulary}

/-! ## A function and the judgments about it -/

/-- A function elaborated against the headers before it: its input names and its body with
what elaboration decided about it. -/
structure TypedFn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) where
  inputs : Names hdr.ins
  body : Fn V fns hdr inputs
  conditions : FnConditions body
  notes : BodyAnalysis.Annotations (LocalRaw V) := []

/-- The elaboration of a stored function. -/
def typeFn (fns : List (FnHeader V)) (hdr : FnHeader V) (region : Region (LocalRaw V) Unit)
    (notes : BodyAnalysis.Annotations (LocalRaw V) := []) :
    Except (ProgramRefusal V) (TypedFn V fns hdr) :=
  match elabFn fns hdr region with
  | .error refusal => .error refusal
  | .ok ⟨inputs, body, conditions⟩ => .ok ⟨inputs, body, conditions, notes⟩

section
variable {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- The meaning of a function on inputs, against callees. -/
def TypedFn.meaning (f : TypedFn V fns hdr) (M : Model V) (table : FnTable M fns)
    (ins : HList M.Val hdr.ins) : Local (HList M.Val hdr.outs) :=
  f.body.denote (localSem M fns table) [] (Env.empty.extend f.inputs ins)

/-- A function is safe: against every callees, it satisfies the summary of its header
(`HeaderSummary.Holds`). On valid inputs that satisfy its requirements, it
never stops `undefined` and returns valid values that, with the inputs, satisfy its guarantees. -/
def TypedFn.Safe (f : TypedFn V fns hdr) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table →
    HeaderSummary.Holds M table hdr.summary (f.meaning M table)

/-- The loops of a function respect bounds: against every callees, on valid inputs that satisfy
the requirements of its header's summary, every loop that a run reaches runs at most as often as
an annotation says, for every annotation whose entries at this function are among the bounds. -/
def TypedFn.Bounded (f : TypedFn V fns hdr) (bounds : List (Place × Nat)) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table → ∀ F : List (Place × Nat),
    (∀ p b, (p, b) ∈ F → p.definition = hdr.key → p.role = none → (p, b) ∈ bounds) →
    ∀ ins : HList M.Val hdr.ins, ins.All M.Valid → FnHeader.Required M table hdr ins →
      f.body.EveryLoop (localSem M fns table) (fun _ _ => True)
        (Annotation.Bounded ⟨F⟩ hdr.key none) [] [] (Env.empty.extend f.inputs ins)

/-- A function is assured, with the bounds of its loops. -/
structure TypedFn.Assured (f : TypedFn V fns hdr) (bounds : List (Place × Nat)) : Prop where
  safe : f.Safe
  bounded : f.Bounded bounds

/-- Two functions have the same meaning on every valid input that satisfies the requirements of
their header's summary, against every callees. -/
def TypedFn.SameAs (f g : TypedFn V fns hdr) : Prop :=
  ∀ (M : Model V) (table : FnTable M fns), Callees M table →
    ∀ ins : HList M.Val hdr.ins, ins.All M.Valid → FnHeader.Required M table hdr ins →
      f.meaning M table ins = g.meaning M table ins

end
end Zkc.Core

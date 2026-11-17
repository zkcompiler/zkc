module

public import Zkc.Core.Meaning.Requirement

@[expose] public section

/-!
The contract of a definition, in the language of requirements, as evidence.

A summary is what a call of a definition must establish of its operands and what it may then
take of its operands and results, both in the language in which an operation states its domain
(`Requirement`, `Meaning/Requirement.lean`), so that an analysis can decide the first at a call
and learn the second (`Summary`, data beside `Requirement` in `Program/Requirement.lean`). A
definition satisfies a summary when, on valid inputs of which every requirement holds, it never
stops undefined, and what it returns is valid and, with the inputs, satisfies every guarantee
(`Summary.Holds`, `Meaning/Requirement.lean`, where the callees of a function are asked it). That
is a contract in the sense of `Contract` (`Evidence/Call.lean`): for the function dialect, whose
reading of values is in `Meaning/Validity.lean`, a summary that holds of a function's entry in a
table is the contract of that entry whose precondition is valid inputs that satisfy the
requirements, whose postcondition is valid results that satisfy the guarantees, and whose stops
are not undefined (`localSummary_contract`, `Evidence/Call.lean`), and so knowledge of every call
of it (`localSummary_satisfies`). The summary
with no requirement and no guarantee holds exactly of a definition that, on valid inputs, never
stops undefined and returns valid values (`Summary.holds_empty`): it is being assured.
-/

namespace Zkc.Core

/-- **The summary with no requirement and no guarantee** holds of a definition exactly when, on
valid inputs, it never stops undefined and returns valid values. -/
theorem Summary.holds_empty {D : Dialect} {Raw : Type} (sem : Semantics D)
    (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    (undefined : sem.H → Prop) {ins outs : List D.Ty}
    (run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)) :
    Summary.Holds sem permitted R Run Valid undefined Summary.empty run ↔
      ∀ inputs : HList sem.Val ins, (∀ v, v ∈ sem.dyns inputs → Valid v) →
        (run inputs).Every permitted (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v)
          (fun stop => ¬ undefined stop) := by
  constructor
  · intro holds inputs valid
    exact Process.every_mono _ _ (fun _ returned => returned.1) (fun _ stop => stop)
      (holds inputs valid fun _ none => nomatch none)
  · intro safe inputs valid _
    exact Process.every_mono _ _ (fun _ returned => ⟨returned, fun _ none => nomatch none⟩)
      (fun _ stop => stop) (safe inputs valid)

end Zkc.Core

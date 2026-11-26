import ZkcFormal.Written.Soundness

/-!
What a rejected statement is, for every decision of every package.

A statement is rejected when no valid witness makes the relation return true. A relation that,
at every argument list, stops or returns false therefore rejects every statement. Under the
premise "every valid witness makes the relation return false" this did not hold: a witness at
which the relation stops left the statement outside the claim, whatever the verifier did there.

The frontend refuses a relation that can stop, so no source of the tree separates the two
meanings; the difference is in what the statement says, and this is a statement about it.
-/

open Zkc.Core Zkc.Subject ZkcFormal.Written

example {V : Vocabulary} (M : Model V) {pkg : Package V} {scheme : WrittenRoot pkg}
    (d : Decision scheme) (p : Typed V) (relation : Member p.headers.fns d.relation.header)
    (xs : HList (RV M scheme.verifier) scheme.entry.header.ins)
    (results : ∀ args : HList M.Val d.relation.header.ins,
      functionResult (M := M) (t := .bool) (d.boolean ▸ fnMeaning M p relation args) = none ∨
      functionResult (M := M) (t := .bool) (d.boolean ▸ fnMeaning M p relation args) = some false) :
    Soundness.Rejected M d p relation xs :=
  Soundness.rejected_of_results M d fun args ↦ by
    rcases results args with stops | declines
    · rw [stops]; exact fun accepted ↦ nomatch accepted
    · rw [declines]; exact fun accepted ↦ Bool.false_ne_true (Option.some.inj accepted)

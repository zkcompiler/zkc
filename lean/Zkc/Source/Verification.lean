module

public import Zkc.Source.Validation
public import Zkc.Specification

@[expose] public section

/-! Turn checked source equivalence into a reusable verification certificate.

The contract and reference proof are explicit author/library inputs. A source
producer supplies neither an equality axiom nor a security-theorem selector.
The normalizer can be incomplete; a failed check creates no certificate.
-/

namespace Zkc.Source.Normalizer

variable {language : Language} {I : PIR.Signature}
  [DecidableEq language.Ty] [DecidableEq language.Op]
  {meaning : Interpretation language I} {Γ : List language.Ty} {ty : language.Ty}
  {source reference : RawProgram language.Ty language.Op}

/-- The exact admitted source inherits any contract on the complete open
process family. A consumer's experiment assumptions remain in `verify`. -/
theorem certificate (normalizer : Normalizer meaning)
    (actual : Verification.Imported (RawProgram.elaborate (language := language) Γ ty) source)
    (target : Verification.Imported (RawProgram.elaborate (language := language) Γ ty) reference)
    (contract : (Environment meaning.Value Γ → PIR.Proc I (meaning.Value ty)) → Prop)
    (conforms : contract (fun env => target.program.denote meaning env))
    (checked : normalizer.check Γ ty source reference = true) :
    Verification.Certificate actual (fun program env => program.denote meaning env) contract := by
  have same : (fun env => actual.program.denote meaning env) =
      (fun env => target.program.denote meaning env) := by
    funext env
    have equality := normalizer.check_sound Γ ty source reference checked env
    rw [source.denote_elaborate meaning actual.program actual.admitted env,
      reference.denote_elaborate meaning target.program target.admitted env] at equality
    exact equality
  exact ⟨same ▸ conforms⟩

end Zkc.Source.Normalizer

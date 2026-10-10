import Zkc.Compiler.Lowering
import Zkc.Compiler.PlanEncoding

/-! Source-relative checking of a directly lowered plan.

The caller supplies the retained source independently of the candidate. Success
contains a decoded plan and a theorem about every binding and handler. This
first rule accepts the direct lowering only; failure to match does not prove a
candidate incorrect, and success is not a protocol-security or native-code proof.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

variable {language : Language} [DecidableEq language.Ty]

structure CheckedPlan {Γ ty} (source : Program language Γ ty)
    (candidate : RawProgram language.Ty language.Op) where
  plan : Plan language Γ ty
  decoded : decodePlan Γ ty candidate = .ok plan
  correct : ∀ {interface : PIR.Signature} (meaning : Interpretation language interface)
    {S E : Type} (handler : PIR.Handler interface S E)
    (env : Environment meaning.Value Γ) (state : S),
    plan.run meaning handler env state = (source.denote meaning env).run handler state

/-- Exact finite comparison is sufficient for this registered direct-lowering rule. -/
def checkDirect [DecidableEq language.Op] {Γ ty} (source : Program language Γ ty)
    (candidate : RawProgram language.Ty language.Op) : Option (CheckedPlan source candidate) :=
  if same : (lower source).erase = candidate then
    some {
      plan := lower source
      decoded := same ▸ Plan.decode_erase (lower source)
      correct := by
        intro interface meaning S E handler env state
        exact lower_correct meaning handler source env state
    }
  else none

/-- A successfully checked plan cannot denote a different decoded candidate. -/
theorem CheckedPlan.decoded_unique {Γ ty} {source : Program language Γ ty}
    {candidate : RawProgram language.Ty language.Op} (checked : CheckedPlan source candidate)
    (other : Plan language Γ ty) (decoded : decodePlan Γ ty candidate = .ok other) :
    checked.plan = other := Except.ok.inj (checked.decoded.symm.trans decoded)

end Zkc.Compiler

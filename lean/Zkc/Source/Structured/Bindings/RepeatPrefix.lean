module

public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Split a retained region at a repeat on its continuation spine. Every
earlier guard, action and bind runs first. The prefix returns the actual live
environment, so later equations can quantify over arbitrary earlier replies. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Bindings.RepeatAt
open Zkc.Source
variable {site : RepeatSite}

/-- A cut is sequential only when the repeat is reached by following
continuations. A repeat inside a callback can execute zero or more times. -/
def onSpine {inputs outputs : List Ty} {root : Region protocolDialect inputs outputs} :
    RepeatAt site root → Bool
  | .here => true
  | .next _ _ _ _ found | .bindNext _ _ found => found.onSpine
  | .bindBody .. | .repeatBody .. => false

def beforeRepeat {inputs outputs : List Ty} {root : Region protocolDialect inputs outputs}
    (occurrence : RepeatAt site root) (linear : occurrence.onSpine = true) :
    Region protocolDialect inputs site.context :=
  match occurrence with
  | .here => .ret (Operands.identity _)
  | .next op args callbacks _ found => .letOp op args callbacks (found.beforeRepeat linear)
  | .bindNext body _ found => .bind body (found.beforeRepeat linear)
  | .bindBody .. | .repeatBody .. => nomatch linear

theorem spine_outputs {inputs outputs : List Ty} {root : Region protocolDialect inputs outputs}
    (occurrence : RepeatAt site root) (linear : occurrence.onSpine = true) : site.outputs = outputs := by
  induction occurrence with
  | here => rfl
  | next _ _ _ _ _ ih | bindNext _ _ _ ih => exact ih linear
  | bindBody | repeatBody => contradiction

/-- Exact equality of free processes, before choosing a prover or a handler.
A stopped prefix bypasses the repeat and the rest of the protocol. -/
theorem denote_prefix {I : PIR.Signature} (meaning : RegionMeaning protocolDialect I)
    {inputs outputs : List Ty} {root : Region protocolDialect inputs outputs}
    (occurrence : RepeatAt site root) (linear : occurrence.onSpine = true)
    (env : Environment meaning.Value inputs) :
    root.denote meaning env = ((occurrence.beforeRepeat linear).denote meaning env).bind fun live ↦
      ((occurrence.spine_outputs linear ▸ site.region : Region protocolDialect site.context outputs).denote meaning live.get) := by
  induction occurrence with
  | here =>
    simp only [beforeRepeat, Region.denote, PIR.Process.bind, Operands.get_eval_identity]
  | next op args callbacks tail found ih =>
    simp only [beforeRepeat, Region.denote, PIR.Process.bind_assoc]
    congr 1
    funext values
    exact ih linear (env.prepend values)
  | bindNext body tail found ih =>
    simp only [beforeRepeat, Region.denote, PIR.Process.bind_assoc]
    congr 1
    funext values
    exact ih linear (env.prepend values)
  | bindBody | repeatBody => contradiction

end Zkc.Source.Structured.Bindings.RepeatAt

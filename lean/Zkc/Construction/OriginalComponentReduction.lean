module

public import Zkc.Construction.OriginalLoop
public meta import Zkc.Construction.OriginalHeadReduction

@[expose] public meta section
/-! Normalization barriers for certified component boundaries. These simprocs
return the identical expression and contribute no semantic equality. A component
certificate checks its arguments and callbacks before structural composition. -/
namespace Zkc.Construction.Original
open Lean Meta Simp

/-- Unfold one reached typed projection without forcing nested captures.
Abstract dialect rows can hide the constructor from ordinary simp. Returning
one definition lets the projection laws simplify retained contexts first;
the kernel checks the resulting definitional equality. -/
def reduceTypedProjection (expression : Expr) : SimpM Simp.Step := do
  if let some reduced ← withTransparency .all <| unfoldDefinition? expression then
    return .visit { expr := reduced }
  return .continue

simproc_decl reduceSequence (Zkc.Source.RoleFamily.sequence _) := reduceTypedProjection
simproc_decl reducePresent (Zkc.Source.Values.present _) := reduceTypedProjection
simproc_decl reducePrepend (Zkc.Source.Environment.prepend _ _ _) := reduceTypedProjection
simproc_decl reducePush (Zkc.Source.Environment.push _ _ _) := reduceTypedProjection

/-- Expose one reached source constructor. Opaque callback regions remain
component boundaries; the bind normalizer retains the unreached continuation. -/
simproc_decl simplifyRegionHead (Zkc.Source.Region.denote _ _ _) := fun expression => do
  let arguments := expression.getAppArgs
  let body := arguments[arguments.size - 2]!
  unless [``Zkc.Source.Region.ret, ``Zkc.Source.Region.stop,
      ``Zkc.Source.Region.bind, ``Zkc.Source.Region.letOp].any body.isAppOf do
    return .done { expr := expression }
  if let some reduced ← withTransparency .all <| unfoldDefinition? expression then
    return .visit { expr := reduced }
  return .continue

simproc_decl stopAtRegion (Zkc.Source.Region.denote _ _ _) :=
  fun expression => return .done { expr := expression }

simproc_decl stopAtRepeat (Zkc.Source.Structured.denoteRepeatOn _ _ _ _ _ _ _ _ _) :=
  fun expression => return .done { expr := expression }

simproc_decl stopAtInvoke (Zkc.Source.Structured.invoke _ _ _) :=
  fun expression => return .done { expr := expression }

simproc_decl stopAtViewLoop (Domain.View.loop _ _ _ _ _ _) :=
  fun expression => return .done { expr := expression }

simproc_decl stopAtViewHelper (Domain.View.helper _ _ _ _ _) :=
  fun expression => return .done { expr := expression }

/-- Simplify a reached bind prefix and its administrative reassociation, while
leaving the unreached continuation untouched. Congruence and each rewrite carry
ordinary equality proofs checked by the kernel. -/
simproc_decl simplifyBindHead (PIR.Process.bind _ _) := fun expression => do
  let arguments := expression.getAppArgs
  let firstProcess := arguments[arguments.size - 2]!
  let next := arguments.back!
  let reduced ← simpLoop firstProcess
  let updated := mkAppN expression.getAppFn (arguments.set! (arguments.size - 2) reduced.expr)
  let change : Result ← if firstProcess == reduced.expr then pure { expr := expression }
    else do
      let proof ← withTransparency .all <|
        mkAppM ``bindHead #[firstProcess, reduced.expr, ← reduced.getProof, next]
      pure { expr := updated, proof? := some proof }
  match ← rewritePost false updated with
  | .visit result => return .visit (← change.mkEqTrans result)
  | .done result => return .done (← change.mkEqTrans result)
  | .continue (some result) => return .done (← change.mkEqTrans result)
  | .continue none => return .done change

end Zkc.Construction.Original

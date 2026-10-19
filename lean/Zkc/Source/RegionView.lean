module

public import Zkc.Source.Structure
public meta import Lean.Elab.Tactic

@[expose] public section

namespace Zkc.Source
open Lean Meta Elab Term

/-- Materialize Region/Regions constructors and their typed data fields.
Keep the dialect and proof fields shared; no operation meaning or repeat is run. -/
private meta partial def materializeRegion (source : Expr) : MetaM Expr := do
  let source ← whnf source
  let recursive := source.isAppOf ``Region.letOp || source.isAppOf ``Region.bind ||
    source.isAppOf ``Regions.cons
  unless recursive || source.isAppOf ``Region.ret || source.isAppOf ``Region.stop ||
      source.isAppOf ``Regions.nil do
    throwError "region_view%: expected a concrete typed Region or Regions constructor, got {source}"
  let mut args := source.getAppArgs
  let count := args.size
  for index in [1:count] do
    if recursive && index >= count - 2 then
      args := args.set! index (← materializeRegion args[index]!)
    else
      args := args.set! index (← reduce args[index]! false true true)
  return mkAppN source.getAppFn args

/-- Generate a typed view from an existing typed body, including checked-body
projections. Use `rfl` to connect a named generated view back to its source;
this is an elaboration convenience, not admission or a semantic theorem.
For proof-only views, use `noncomputable def`: reducing an imported checker may
expose implementation constants that its compiled runtime interface does not export. -/
elab "region_view% " source:term : term <= expectedType => do
  let original ← elabTerm source expectedType
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let generated ← materializeRegion original
  unless ← isDefEq original generated do
    throwError "region_view%: generated view differs from the typed source"
  return generated

end Zkc.Source

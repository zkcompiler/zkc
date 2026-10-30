module

public import Zkc.Construction.Uniform.SourceProcess
public meta import ZkcTools.ConstructionBindings.ArtifactBindingTactic

@[expose] public meta section
namespace Zkc.Construction.Uniform.SourceProcess
open Lean
/-- Shared proof normalization of the checked finite views. Arithmetic laws
are equations of Domain.calculate, not another calculation implementation. -/
macro "normalize_scalar_connection" " unfolding " "[" definitions:term,* "]" : tactic => do
  let defs := definitions.getElems
  `(tactic|
    (normalize_artifact_operations [groupScale, groupAdd, groupEqual, booleanAnd]
      unfolding [$defs,*, sourceView, receive, send, query, returnValues,
        PIR.Process.interpret, Zkc.Construction.Original.forgetCheckpoints,
        Zkc.Construction.Domain.templateOrigin, Zkc.Construction.Domain.queryOrigin,
        Zkc.Construction.Template.origin, Zkc.Construction.Template.qualify,
        Zkc.Construction.Template.repeats, Zkc.Construction.Domain.atCoordinates,
        Zkc.Construction.Context.message, Zkc.Construction.Context.query,
        Zkc.Construction.Context.role, Zkc.Construction.Context.suite,
        Zkc.Construction.Context.contract, Zkc.Construction.Context.request,
        Zkc.Construction.Context.replacement?, Zkc.Construction.Context.service,
        Zkc.Construction.Context.fiatShamir,
        Zkc.Construction.Payload.ofValue,
        Zkc.Source.Structured.Ty.isHandle, Bool.not_false, Bool.not_true,
        List.append_assoc, List.isEmpty_nil, List.take_nil,
        Zkc.Construction.Domain.Calculations.fieldAdd,
        Zkc.Construction.Domain.Calculations.fieldEqual]
    <;> rfl))
end Zkc.Construction.Uniform.SourceProcess

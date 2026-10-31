module

public import Zkc.Source.Structured.UnitViews
public import Zkc.Source.Structured.BodyBindings
public import Zkc.Protocols.TableMembership.SourceLaws
public import ZkcExamples.Structured.TableMembershipData
public import ZkcExamples.Structured.TableMembershipBodies

@[expose] public section

/-! Exact whole-unit admission from literal bodies of the retained table
membership subject. All callbacks and the original realization remain bound. -/
namespace ZkcExamples.Structured.TableMembershipViews
open Zkc.Source Zkc.Source.Structured TableMembershipBodies

set_option smartUnfolding false

structured_views TableMembershipData.snapshot
  helpers [containsDecision, containsStep, contains, queryDecision, queryStep,
    membership, realization, formula, checkMembership]
  protocols [run]

namespace Associations
structured_associations TableMembershipViews
  [containsDecision, containsStep, contains, queryDecision, queryStep,
    membership, realization, formula, checkMembership]
end Associations

/-- Install the reusable helper closure on this exact admitted source. -/
theorem installedBodies : Zkc.Protocols.TableMembership.Source.Bodies
    unit.definitions "koala-bear" names := by
  bind_structured_bodies

end ZkcExamples.Structured.TableMembershipViews

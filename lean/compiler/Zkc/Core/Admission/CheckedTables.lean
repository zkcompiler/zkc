module

public import Zkc.Core.Facts.Body.RoleSafety
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Meaning.Tables
public import Zkc.Core.Transform.Function

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts
variable {V : Vocabulary}

/-- Evidence collected in declaration order. A function contributes its safety against earlier
callees. A protocol contributes a successful check of its projection at
every declared participant. The other projections follow from the scope of the protocol. -/
def CheckedBodies : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn hdr inputs body ok rest notes =>
    (TypedFn.mk inputs body ok notes : TypedFn V _ hdr).Safe ∧ CheckedBodies rest
  | _, .protocol (hs := hs) hdr inputs body _ rest =>
    (∃ catalog : FunctionContracts hs.fns, ∀ r ∈ List.range hdr.roles, ∃ bounds,
      checkRole catalog r hdr (inputs := inputs) (project r body) = .ok bounds) ∧ CheckedBodies rest

/-- Compose actual function and role tables at every declaration. Safety of a role application
is supplied by the corresponding earlier projection in the table. -/
theorem checkedTables (M : Model V) : ∀ {hs : Headers V} (defs : Defs V hs),
    (hs.fns.map (·.key)).Nodup → CheckedBodies defs →
    Callees M (Defs.fnTable M defs) ∧ RCallees M (Defs.rTable M defs)
  | _, .nil, distinct, _ => by
    exact ⟨⟨distinct, (fun _ f => nomatch f), (fun _ f => nomatch f), (fun _ f => nomatch f)⟩,
      (fun _ p => nomatch p)⟩
  | _, .fn hdr inputs body ok rest _, distinct, checked => by
    obtain ⟨safe, earlier⟩ := checked
    have ⟨fns, roles⟩ := checkedTables M rest (List.nodup_cons.mp distinct).2 earlier
    refine ⟨⟨distinct, ?_, ?_, Defs.fnTable_stops_undefined M _⟩, roles⟩
    · intro callee found
      cases found with
      | head => exact HeaderSummary.holds_tables (safe M _ fns)
      | tail found => exact HeaderSummary.holds_tables (fns.satisfies _ found)
    · intro callee found args outs valid ran
      cases found with
      | tail found => exact fns.keeps _ found args outs valid ran
      | head =>
        change body.denote (localSem M _ (Defs.fnTable M rest)) [] (Env.empty.extend inputs args) = .done outs at ran
        have kept := Term.denote_valid (Defs.fnTable M rest) fns.keeps body [] (Env.empty.extend inputs args)
          (Env.extend_valid (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed) inputs args valid)
        rw [ran] at kept
        exact kept
  | _, .protocol hdr inputs body ok rest, distinct, checked => by
    obtain ⟨⟨catalog, passes⟩, earlier⟩ := checked
    have ⟨fns, roles⟩ := checkedTables M rest distinct earlier
    refine ⟨fns, ?_⟩
    intro callee found r path args valid
    cases found with
    | head =>
      by_cases declared : r ∈ List.range hdr.roles
      · obtain ⟨bounds, pass⟩ := passes r declared
        exact checkedProjection_safe catalog r hdr body ok pass M _ _ fns roles path args valid
      · exact (outsideProjection M _ _ declared roles body ok.within path _ (Env.extend_preserves
          (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed) inputs args valid)
          (fun _ _ _ => True) []).1
    | tail found => exact roles _ found r path args valid

end Zkc.Core.BodyAnalysis.RoleContracts

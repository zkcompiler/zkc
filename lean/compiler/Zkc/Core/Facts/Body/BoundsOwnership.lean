module

public import Zkc.Core.Facts.Body.Verdicts

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw)

/-- Each analysis starts with empty bounds, even when it inherits a value table. -/
private theorem analyseFrom_places (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) (wf : start.WF) :
    ∀ q ∈ (analyseFrom cfg notes summary inputs body start).state.bounds,
      q.1.definition = cfg.definition ∧ q.1.role = cfg.role := by
  obtain ⟨_, _, _, _, _, added, bounds, places⟩ :=
    analyseFrom_stateGrew cfg notes summary inputs body start wf
  intro q hq
  have mem : q ∈ added := by simpa only [bounds, List.append_nil] using hq
  obtain ⟨blocks, key, atPlace, _⟩ := places q mem
  rw [atPlace]
  exact ⟨rfl, rfl⟩

/-- Every bound returned by the checker belongs to the configured definition and role. -/
theorem checkFacts_places [DecidableEq D.Ty] (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) {bounds : List (Place × Nat)}
    (accepted : checkFacts cfg notes summary inputs body = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = cfg.definition ∧ q.1.role = cfg.role := by
  obtain ⟨_, _, rfl⟩ := (checkFacts_ok_iff cfg inputs body notes summary bounds).mp accepted
  intro q hq
  exact analyseFrom_places cfg notes summary inputs body _ (Values.empty_wf _) q
    (List.mem_reverse.mp hq)

/-- Comparison returns bounds in the candidate's definition and the configured role. -/
theorem followChecked_places (checks : SkelRules D) (candidateKey : Key)
    (notes notes' : Annotations Raw) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) {bounds : List (Place × Nat)}
    (accepted : followChecked cfg checks candidateKey notes notes' summary inputs inputs' body body' =
      .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = candidateKey ∧ q.1.role = cfg.role := by
  rw [followChecked_bounds cfg checks candidateKey inputs inputs' body body' notes notes' summary
    accepted]
  have sourceWF := (analyseFrom_grew cfg notes summary inputs body _
    (Values.empty_wf cfg.rules.place)).2
  intro q hq
  exact analyseFrom_places { cfg with definition := candidateKey } notes' summary inputs' body' _
    sourceWF q (List.mem_reverse.mp hq)

end Zkc.Core.BodyAnalysis

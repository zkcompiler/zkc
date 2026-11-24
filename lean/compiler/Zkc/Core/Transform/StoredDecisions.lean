module

public import Zkc.Core.Transform.FunctionReporting
public import Zkc.Core.Transform.FunctionBounds

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}


private theorem acceptedEvidence (f : TypedFn V hs hdr)
    (checked : checkFactEvidence f = .ok ()) (catalog : FunctionContracts hs) :
    catalog.AnnotationEvidence f [] f.notes := by
  have absent : f.notes.find? (fun e => e.2.isGiven) = none := by
    cases found : f.notes.find? (fun e => e.2.isGiven) with
    | none => rfl
    | some item => simp [checkFactEvidence, found] at checked
  have internal : f.notes.any (fun e => e.2.isGiven) = false := by
    exact List.any_eq_false.mpr (List.find?_eq_none.mp absent)
  exact catalog.evidenceOfLaws f internal (by simp)

theorem checkStored_accepted (f : TypedFn V hs hdr) {bounds}
    (ok : checkStored f = .ok bounds) :
    ∃ catalog : FunctionContracts hs, catalog.checkFunction f [] f.notes = .ok bounds ∧
      catalog.AnnotationEvidence f [] f.notes := by
  cases hc : FunctionContracts.check hs with
  | error e => simp [checkStored, hc, Except.mapError, Bind.bind, Except.bind] at ok
  | ok catalog =>
    cases hf : catalog.checkFunction f [] f.notes with
    | error e => simp [checkStored, hc, hf, Except.mapError, Bind.bind, Except.bind] at ok
    | ok bs =>
      cases he : checkFactEvidence f with
      | error e => simp [checkStored, hc, hf, he, Except.mapError, Bind.bind, Except.bind] at ok
      | ok u =>
        cases u
        simp [checkStored, hc, hf, he, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at ok
        exact ⟨catalog, ok ▸ hf, acceptedEvidence f he catalog⟩

theorem compareStored_accepted (f g : TypedFn V hs hdr) {bounds}
    (ok : compareStored f g = .ok bounds) :
    ∃ catalog : FunctionContracts hs, catalog.compareFunctions f g [] f.notes g.notes = .ok bounds ∧
      catalog.AnnotationEvidence g [] g.notes := by
  cases hc : FunctionContracts.check hs with
  | error e => simp [compareStored, hc, Except.mapError, Bind.bind, Except.bind] at ok
  | ok catalog =>
    cases hf : catalog.compareFunctions f g [] f.notes g.notes with
    | error e => simp [compareStored, hc, hf, Except.mapError, Bind.bind, Except.bind] at ok
    | ok bs =>
      cases he : checkFactEvidence g with
      | error e => simp [compareStored, hc, hf, he, Except.mapError, Bind.bind, Except.bind] at ok
      | ok u =>
        cases u
        simp [compareStored, hc, hf, he, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at ok
        exact ⟨catalog, ok ▸ hf, acceptedEvidence g he catalog⟩

theorem checkStored_assured (f : TypedFn V hs hdr) {bounds}
    (ok : checkStored f = .ok bounds) : f.Assured bounds := by
  obtain ⟨catalog, checked, evidence⟩ := checkStored_accepted f ok
  exact catalog.checkAnnotated_assured f evidence checked

theorem compareStored_assured (f g : TypedFn V hs hdr) (safe : f.Safe) {bounds}
    (ok : compareStored f g = .ok bounds) : g.Assured bounds ∧ f.SameAs g := by
  obtain ⟨catalog, checked, evidence⟩ := compareStored_accepted f g ok
  exact catalog.compareAnnotated_assured f g safe evidence checked

theorem checkStored_places (f : TypedFn V hs hdr) {bounds}
    (ok : checkStored f = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = hdr.key ∧ q.1.role = none := by
  obtain ⟨catalog, checked, _⟩ := checkStored_accepted f ok
  exact catalog.checkFunction_places f checked

theorem compareStored_places (f g : TypedFn V hs hdr) {bounds}
    (ok : compareStored f g = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = hdr.key ∧ q.1.role = none := by
  obtain ⟨catalog, checked, _⟩ := compareStored_accepted f g ok
  exact catalog.compareFunctions_places f g checked

end Zkc.Core.BodyAnalysis

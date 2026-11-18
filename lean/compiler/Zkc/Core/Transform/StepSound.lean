module

public import Zkc.Core.Transform.Step
public import Zkc.Core.Transform.StoredDecisions
public import Zkc.Core.Evidence.Claim

@[expose] public section

/-! Semantic judgments for stored function checks and checked replacements. -/

namespace Zkc.Core

/-! ## The judgments about a function -/

section
variable {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- The relation "same meaning" of functions is symmetric. -/
theorem TypedFn.SameAs.symm {f g : TypedFn V fns hdr} (same : f.SameAs g) : g.SameAs f :=
  fun M table callees ins valid required => (same M table callees ins valid required).symm

/-- The relation "same meaning" of functions is transitive. -/
theorem TypedFn.SameAs.trans {f g h : TypedFn V fns hdr} (first : f.SameAs g)
    (second : g.SameAs h) : f.SameAs h :=
  fun M table callees ins valid required =>
    (first M table callees ins valid required).trans (second M table callees ins valid required)

/-- What a stored function is typed as is its elaboration. -/
theorem typeFn_ok {region : Region (LocalRaw V) Unit} {notes : BodyAnalysis.Annotations (LocalRaw V)} {f : TypedFn V fns hdr}
    (typed : typeFn fns hdr region notes = .ok f) :
    elabFn fns hdr region = .ok ⟨f.inputs, f.body, f.conditions⟩ := by
  unfold typeFn at typed
  split at typed
  · cases typed
  · rename_i elaborated
    cases typed
    exact elaborated

theorem typeFn_notes {region : Region (LocalRaw V) Unit} {notes : BodyAnalysis.Annotations (LocalRaw V)}
    {f : TypedFn V fns hdr} (typed : typeFn fns hdr region notes = .ok f) : f.notes = notes := by
  unfold typeFn at typed
  split at typed <;> cases typed
  rfl

/-- Admission establishes safety and the recorded loop bounds. -/
theorem TypedFn.check_assured (f : TypedFn V fns hdr) {bounds : List (Place × Nat)}
    (checked : f.check = .ok bounds) : f.Assured bounds :=
  BodyAnalysis.checkStored_assured f checked

/-- The bounds returned by admission belong to the function being checked. -/
theorem TypedFn.check_places (f : TypedFn V fns hdr) {bounds : List (Place × Nat)}
    (checked : f.check = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = hdr.key ∧ q.1.role = none :=
  BodyAnalysis.checkStored_places f checked

/-- A checked replacement of a safe function preserves its meaning and is assured. -/
theorem TypedFn.follows_assured {source target : TypedFn V fns hdr}
    {bounds : List (Place × Nat)} (safe : source.Safe) (followed : source.follows target = .ok bounds) :
    target.Assured bounds ∧ source.SameAs target :=
  BodyAnalysis.compareStored_assured source target safe followed

/-- **A function is safe exactly when its body is assured** in the scope of a function, and returns
what satisfies its guarantees: for every model and callees, on the empty path and the inputs bound
to valid values that satisfy the requirements of its header's summary, it is assured with the
validity of the model and the stop `undefined` (`Assured`, `Evidence/Claim.lean`), and on each such
input every return, with the inputs, satisfies the summary's guarantees (`Claim`). The judgment
about a function is the generic one at that scope, with the guarantees. -/
theorem TypedFn.safe_iff_assured (f : TypedFn V fns hdr) :
    f.Safe ↔ ∀ (M : Model V) (table : FnTable M fns), Callees M table →
      Zkc.Core.Assured (localSem M fns table) (fun _ _ => True) (ValidDyn M) (· = .undefined)
          f.body
          (fun path env => path = [] ∧ ∃ ins : HList M.Val hdr.ins, ins.All M.Valid ∧
            FnHeader.Required M table hdr ins ∧ env = Env.empty.extend f.inputs ins) ∧
        ∀ ins : HList M.Val hdr.ins, ins.All M.Valid → FnHeader.Required M table hdr ins →
          Claim (localSem M fns table) (fun _ _ => True) f.body
            (fun path env => path = [] ∧ env = Env.empty.extend f.inputs ins)
            (fun outs => ∀ guarantee, guarantee ∈ hdr.summary.ensures →
              guarantee.Holds M
                ((localSem M fns table).dyns ins ++ (localSem M fns table).dyns outs))
            (fun _ => True) := by
  constructor
  · intro safe M table callees
    refine ⟨⟨fun path env ⟨empty, ins, valid, required, bound⟩ => ?_⟩,
      fun ins valid required path env ⟨empty, bound⟩ => ?_⟩
    · subst empty bound
      exact Process.every_mono _ _ (fun _ returned => returned.1) (fun _ stop => stop)
        (safe M table callees ins (((localSem M fns table).dyns_valid_iff ins).mpr valid)
          required)
    · subst empty bound
      exact Process.every_mono _ _ (fun _ returned => returned.2) (fun _ _ => trivial)
        (safe M table callees ins (((localSem M fns table).dyns_valid_iff ins).mpr valid)
          required)
  · intro assured M table callees ins valid required
    have valid' := ((localSem M fns table).dyns_valid_iff ins).mp valid
    exact Process.every_mono _ _ (fun _ both => both) (fun _ both => both.1)
      (Process.every_and _ _
        ((assured M table callees).1.holds [] _ ⟨rfl, ins, valid', required, rfl⟩)
        ((assured M table callees).2 ins valid' required [] _ ⟨rfl, rfl⟩))

end

end Zkc.Core

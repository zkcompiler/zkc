module

public import Zkc.Core.Transform.Step
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Evidence.Claim

@[expose] public section

/-!
What the judgments about a function rest on.

The check of facts is a producer of assurance: a function that it accepts under its header's
summary satisfies the summary (`checkFacts_holds`, from `Analysis.analyse_holds`) and is assured
with the bounds that it gives (`TypedFn.check_assured`, the bounds from `checkFacts_sound`).
Following is another, from a source that is safe by any route: when a second function follows the
analysis of a first that is safe with no refusal and no place that differs, the second is assured
with the bounds recorded while it follows, and the two mean the same on the inputs that satisfy
the requirements (`TypedFn.follows_assured`, from `localFollow_assured`, the theorem of the
analysis for functions). The second is not analysed by itself, and the refusals of the first's
own analysis are not read. "The same meaning" of functions is symmetric and transitive
(`TypedFn.SameAs.symm`, `TypedFn.SameAs.trans`), and that a function is safe is that its body is
assured, in the sense of `Evidence/Claim.lean`, in the scope of the empty path and its inputs bound
to valid values that satisfy the requirements, and on each such input returns what satisfies the
guarantees (`TypedFn.safe_iff_assured`). What a stored function is typed as is its elaboration
(`typeFn_ok`).
-/
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
theorem typeFn_ok {region : Region (LocalRaw V) Unit} {f : TypedFn V fns hdr}
    (typed : typeFn fns hdr region = .ok f) :
    elabFn fns hdr region = .ok ⟨f.inputs, f.body, f.conditions⟩ := by
  unfold typeFn at typed
  split at typed
  · cases typed
  · rename_i elaborated
    cases typed
    exact elaborated

/-- **The check of facts is a producer of assurance.** A function that the check of facts
accepts under its header's summary satisfies the summary (`checkFacts_holds`, from
`Analysis.analyse_holds`), and its loops respect the bounds that the check gives on the inputs
that satisfy the requirements (`checkFacts_sound`). -/
theorem TypedFn.check_assured (f : TypedFn V fns hdr) {bounds : List (Place × Nat)}
    (checked : f.check = .ok bounds) : f.Assured bounds :=
  ⟨fun _ _ callees =>
    checkFacts_holds callees hdr.key hdr.summary f.inputs f.body f.conditions.distinct checked,
   fun _ _ callees F recorded ins valid required =>
    (checkFacts_sound callees hdr.key hdr.summary f.inputs f.body f.conditions.distinct checked F
      recorded ins valid required).1⟩

open Analysis in
/-- What it is for a second function to follow a first: it follows the analysis of the first
with no refusal and no place that differs, and its bounds are those recorded while it
follows. -/
theorem TypedFn.follows_ok {source target : TypedFn V fns hdr} {bounds : List (Place × Nat)}
    (followed : source.follows target = .ok bounds) :
    (follow (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
        (analyse (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
          source.inputs source.body) target.inputs target.body).accepted = true ∧
      bounds = (follow (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
        (analyse (localFactRules V fns) (localRules fns).skel hdr.key none hdr.summary.lift
          source.inputs source.body) target.inputs target.body).state.st.bounds.reverse := by
  unfold TypedFn.follows at followed
  dsimp only at followed
  split at followed
  · rename_i refused same
    cases followed
    exact ⟨by simp only [Exit.accepted, refused, same, List.isEmpty_nil, Bool.and_self], rfl⟩
  · cases followed

/-- **Following is a producer of assurance and of sameness, from a source that is safe by any
route.** When a second function follows the analysis of a first that is safe, however that is
known, both under their header's summary, the second is assured with the bounds recorded while it
follows, and the two mean the same on the inputs that satisfy the requirements
(`localFollow_assured`). The refusals of the first's own analysis are not read. -/
theorem TypedFn.follows_assured {source target : TypedFn V fns hdr}
    {bounds : List (Place × Nat)} (safe : source.Safe)
    (followed : source.follows target = .ok bounds) :
    target.Assured bounds ∧ source.SameAs target := by
  obtain ⟨accepted, recordedBounds⟩ := TypedFn.follows_ok followed
  have sound := fun (M : Model V) (table : FnTable M fns) (callees : Callees M table)
      (F : List (Place × Nat))
      (recorded : ∀ p b, (p, b) ∈ F → p.definition = hdr.key → p.role = none → (p, b) ∈ bounds)
      (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid)
      (required : FnHeader.Required M table hdr ins) =>
    localFollow_assured callees hdr.key hdr.key hdr.summary source.inputs target.inputs
      source.body target.body target.conditions.distinct accepted F
      (fun p b inside here unowned => by
        have mine := recorded p b inside here unowned
        rw [recordedBounds] at mine
        exact List.mem_reverse.mp mine)
      ins valid required
      (Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
        (safe M table callees ins (((localSem M fns table).dyns_valid_iff ins).mpr valid)
          required))
  exact ⟨⟨fun M table callees ins valid required =>
      Process.every_mono _ _
        (fun outs returned => ⟨((localSem M fns table).dyns_valid_iff outs).mpr returned.1,
          returned.2⟩)
        (fun _ stop => stop)
        (sound M table callees [] (fun _ _ none => nomatch none) ins
          (((localSem M fns table).dyns_valid_iff ins).mp valid) required).2.1,
    fun M table callees F recorded ins valid required =>
      (sound M table callees F recorded ins valid required).1⟩,
    fun M table callees ins valid required =>
      (sound M table callees [] (fun _ _ none => nomatch none) ins valid required).2.2⟩

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
              guarantee.Holds Empty.elim (localReading M)
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

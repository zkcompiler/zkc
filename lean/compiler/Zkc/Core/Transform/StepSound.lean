module

public import Zkc.Core.Transform.Step
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Evidence.Claim

@[expose] public section

/-!
What the judgments about a function rest on.

The check of facts is a producer of assurance: a function that it accepts is assured with the
bounds that it gives (`TypedFn.check_assured`, from `checkFacts_sound`). Following is another,
from a source that is safe by any route: when a second function follows the analysis of a first
that is safe with no refusal and no place that differs, the second is assured with the bounds
recorded while it follows, and the two mean the same (`TypedFn.follows_assured`, from
`localFollow_assured`, the theorem of the analysis for functions). The second is not analysed by
itself, and the refusals of the first's own analysis are not read. "The same meaning" of
functions is symmetric and transitive (`TypedFn.SameAs.symm`, `TypedFn.SameAs.trans`), and that
a function is safe is that its body is assured, in the sense of `Evidence/Claim.lean`, in the
scope of the empty path and its inputs bound to valid values (`TypedFn.safe_iff_assured`). What
a stored function is typed as is its elaboration (`typeFn_ok`).
-/
namespace Zkc.Core

/-! ## The judgments about a function -/

section
variable {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}

/-- The relation "same meaning" of functions is symmetric. -/
theorem TypedFn.SameAs.symm {f g : TypedFn V fns hdr} (same : f.SameAs g) : g.SameAs f :=
  fun M table callees ins valid => (same M table callees ins valid).symm

/-- The relation "same meaning" of functions is transitive. -/
theorem TypedFn.SameAs.trans {f g h : TypedFn V fns hdr} (first : f.SameAs g)
    (second : g.SameAs h) : f.SameAs h :=
  fun M table callees ins valid =>
    (first M table callees ins valid).trans (second M table callees ins valid)

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
accepts is assured with the bounds that the check gives (`checkFacts_sound`). -/
theorem TypedFn.check_assured (f : TypedFn V fns hdr) {bounds : List (Place × Nat)}
    (checked : f.check = .ok bounds) : f.Assured bounds :=
  ⟨fun _ _ callees ins valid =>
    (checkFacts_sound callees hdr.key f.inputs f.body f.conditions.distinct checked []
      (fun _ _ none => nomatch none) ins valid).2,
   fun _ _ callees F recorded ins valid =>
    (checkFacts_sound callees hdr.key f.inputs f.body f.conditions.distinct checked F recorded
      ins valid).1⟩

open Analysis in
/-- What it is for a second function to follow a first: it follows the analysis of the first
with no refusal and no place that differs, and its bounds are those recorded while it
follows. -/
theorem TypedFn.follows_ok {source target : TypedFn V fns hdr} {bounds : List (Place × Nat)}
    (followed : source.follows target = .ok bounds) :
    (follow (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩
        (analyse (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩ source.inputs
          source.body) target.inputs target.body).accepted = true ∧
      bounds = (follow (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩
        (analyse (localFactRules V fns) (localRules fns).skel hdr.key none ⟨[], []⟩ source.inputs
          source.body) target.inputs target.body).state.st.bounds.reverse := by
  unfold TypedFn.follows at followed
  dsimp only at followed
  split at followed
  · rename_i refused same
    cases followed
    exact ⟨by simp only [Exit.accepted, refused, same, List.isEmpty_nil, Bool.and_self], rfl⟩
  · cases followed

/-- **Following is a producer of assurance and of sameness, from a source that is safe by any
route.** When a second function follows the analysis of a first that is safe, however that is
known, the second is assured with the bounds recorded while it follows, and the two mean the
same (`localFollow_assured`). The refusals of the first's own analysis are not read. -/
theorem TypedFn.follows_assured {source target : TypedFn V fns hdr}
    {bounds : List (Place × Nat)} (safe : source.Safe)
    (followed : source.follows target = .ok bounds) :
    target.Assured bounds ∧ source.SameAs target := by
  obtain ⟨accepted, recordedBounds⟩ := TypedFn.follows_ok followed
  have sound := fun (M : Model V) (table : FnTable M fns) (callees : Callees M table)
      (F : List (Place × Nat))
      (recorded : ∀ p b, (p, b) ∈ F → p.definition = hdr.key → p.role = none → (p, b) ∈ bounds)
      (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid) =>
    localFollow_assured callees hdr.key hdr.key source.inputs target.inputs source.body target.body
      target.conditions.distinct accepted F
      (fun p b inside here unowned => by
        have mine := recorded p b inside here unowned
        rw [recordedBounds] at mine
        exact List.mem_reverse.mp mine)
      ins valid
      (Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
        (safe M table callees ins valid))
  exact ⟨⟨fun M table callees ins valid =>
      (sound M table callees [] (fun _ _ none => nomatch none) ins valid).2.1,
    fun M table callees F recorded ins valid => (sound M table callees F recorded ins valid).1⟩,
    fun M table callees ins valid =>
      (sound M table callees [] (fun _ _ none => nomatch none) ins valid).2.2⟩

/-- **A function is safe exactly when its body is assured** in the scope of a function: for
every model and callees, on the empty path and the inputs bound to valid values, with the
validity of the model and the stop `undefined` (`Assured`, `Evidence/Claim.lean`). The judgment
about a function is the generic one at that scope. -/
theorem TypedFn.safe_iff_assured (f : TypedFn V fns hdr) :
    f.Safe ↔ ∀ (M : Model V) (table : FnTable M fns), Callees M table →
      Zkc.Core.Assured (localSem M fns table) (fun _ _ => True) (ValidDyn M) (· = .undefined)
        f.body
        (fun path env => path = [] ∧
          ∃ ins : HList M.Val hdr.ins, ins.All M.Valid ∧ env = Env.empty.extend f.inputs ins) := by
  constructor
  · intro safe M table callees
    refine ⟨fun path env ⟨empty, ins, valid, bound⟩ => ?_⟩
    subst empty bound
    exact Process.every_mono _ _
      (fun outs returned => ((localSem M fns table).dyns_valid_iff outs).mpr returned)
      (fun _ stop => stop) (safe M table callees ins valid)
  · intro assured M table callees ins valid
    exact Process.every_mono _ _
      (fun outs returned => ((localSem M fns table).dyns_valid_iff outs).mp returned)
      (fun _ stop => stop) ((assured M table callees).holds [] _ ⟨rfl, ins, valid, rfl⟩)

end

end Zkc.Core

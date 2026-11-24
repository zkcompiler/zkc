module

public import Zkc.Core.Facts.Body.Statements
public import Zkc.Core.Meaning.Validity

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {Raw Val : Type}

def Contract.UsesOnly (allowed : Raw → Bool) (c : Contract Raw) : Bool :=
  c.requires.all (Expr.UsesOnly allowed) && c.ensures.all (Expr.UsesOnly allowed)

section
variable {allowed : Raw → Bool} {old new : Raw → List Val → List Val → Prop}
    (preserve : ∀ op, allowed op = true → ∀ xs ys, old op xs ys → new op xs ys)

set_option linter.unusedSectionVars false in
include preserve in
mutual
  theorem Expr.Denotes.transport {xs : List Val} {e : Expr Raw} {v : Val}
      (den : Expr.Denotes old xs e v) (stable : Expr.UsesOnly allowed e = true) : Expr.Denotes new xs e v :=
    match den with
    | .arg h => .arg h
    | .apply named ran picked => .apply (Exprs.Denote.transport named (Bool.and_eq_true_iff.mp stable).2)
        (preserve _ (Bool.and_eq_true_iff.mp stable).1 _ _ ran) picked
  theorem Exprs.Denote.transport {xs : List Val} {es : Exprs Raw} {vs : List Val}
      (den : Exprs.Denote old xs es vs) (stable : Exprs.UsesOnly allowed es = true) : Exprs.Denote new xs es vs :=
    match den with
    | .nil => .nil
    | .cons one rest => .cons (Expr.Denotes.transport one (Bool.and_eq_true_iff.mp stable).1)
        (Exprs.Denote.transport rest (Bool.and_eq_true_iff.mp stable).2)
end

include preserve in
theorem Expr.Holds.transport {xs : List Val} {e : Expr Raw} {R : Reading Val}
    (holds : e.Holds old R xs) (stable : Expr.UsesOnly allowed e = true) : e.Holds new R xs :=
  let ⟨v, den, trueAt⟩ := holds
  ⟨v, den.transport preserve stable, trueAt⟩

end

/-- Stability across function tables is independent of totality on valid inputs. -/
def tableIndependent {V : Vocabulary} : LocalRaw V → Bool
  | .call _ => false
  | _ => true

section
variable {V : Vocabulary} (M : Model V) {fns fns' : List (FnHeader V)}
    (table : FnTable M fns) (table' : FnTable M fns')

/-- A non-call has the same return witnesses across arbitrary function-header lists and tables. -/
theorem localReturns_transport (op : LocalRaw V) (stable : tableIndependent op = true)
    (xs ys) (ran : LocalReturns M table op xs ys) : LocalReturns M table' op xs ys := by
  obtain ⟨ins, outs, typed, args, returned, rfl, rfl, rfl, done⟩ := ran
  have hin := (localSem_dyns table table' args).symm
  have hout := (localSem_dyns table table' returned).symm
  cases typed with
  | row key sig known => exact ⟨_, _, .row key sig known, args, returned, rfl, hin, hout, done⟩
  | owned o => exact ⟨_, _, .owned o, args, returned, rfl, hin, hout, done⟩
  | literal t data reads => exact ⟨_, _, .literal t data reads, args, returned, rfl, hin, hout, done⟩
  | call _ => contradiction

abbrev localRun (table : FnTable M fns) :=
  ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M)

theorem validRun_transport (op : LocalRaw V) (stable : tableIndependent op = true) (xs ys)
    (ran : localRun M table op xs ys) : localRun M table' op xs ys :=
  ⟨localReturns_transport M table table' op stable xs ys ran.1, ran.2⟩

/-- A fixed run satisfies a stored stable contract in either table's interpretation. -/
theorem Contract.holds_tables {ins outs : List V.Ty} (summary : Contract (LocalRaw V))
    (stable : summary.UsesOnly tableIndependent = true) (run : HList M.Val ins → Local (HList M.Val outs))
    (holds : summary.HoldsWith (localSem M fns table) (fun _ _ => True) (localReading M)
      (ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M))
      (ValidDyn M) (· = .undefined) run) :
    summary.HoldsWith (localSem M fns' table') (fun _ _ => True) (localReading M)
      (ValidRun (localSem M fns' table') (LocalReturns M table') (ValidDyn M))
      (ValidDyn M) (· = .undefined) run := by
  intro values valid required
  obtain ⟨reqs, ens⟩ := Bool.and_eq_true_iff.mp stable
  have inputs := localSem_dyns table table' values
  rw [← inputs] at valid required
  have original := holds values valid (fun e m => (required e m).transport
    (validRun_transport M table' table) (List.all_eq_true.mp reqs e m))
  refine Process.every_mono _ _ (fun results h => ?_) (fun _ h => h) original
  obtain ⟨validResults, ensures⟩ := h
  rw [← inputs, ← localSem_dyns table table' results]
  exact ⟨validResults, fun e m => (ensures e m).transport (validRun_transport M table table')
    (List.all_eq_true.mp ens e m)⟩

end
end Zkc.Core.BodyAnalysis

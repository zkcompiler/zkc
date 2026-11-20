module

public import Zkc.Formal.Written.SumcheckRows
public import Zkc.Formal.Interactive.PairReadback
public import Zkc.Vocabulary.Project
public import Zkc.Core.Admission.Theorems

@[expose] public section
namespace Zkc.Tests.Formal.SourcePairMembers
open Core Zkc.Vocabulary.Project Formal.Interactive.Sumcheck
abbrev bindings : Bindings := {}
abbrev V := bindings.vocabulary

abbrev sourceRows := Zkc.Formal.Written.SumcheckRows.sourceRows

abbrev rows := sourceRows bindings

inductive Evaluation where
  | interpolation
  | affine

def expected (form : Evaluation) (boundary evaluate : Key) (apart : boundary ≠ evaluate) : Typed V :=
  let b := rows.scalarHeader boundary [rows.pair]
  let e := rows.scalarHeader evaluate [rows.pair,rows.scalarTy]
  let earlier : Defs V ⟨[b],[]⟩ := .fn b _ (rows.boundaryBody [] boundary)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact rfl | (change ([0,1,2,3] : List Nat).Nodup; decide)) .nil
  let defs : Defs V ⟨[e,b],[]⟩ := match form with
    | .interpolation => .fn e _ (rows.evaluateBody [b] evaluate)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact rfl |
            (change ([0,1,2,3,4,5,6,7,8] : List Nat).Nodup; decide)) earlier
    | .affine => .fn e _ (rows.affineBody [b] evaluate)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | exact rfl |
            (change ([0,1,2,3,4,5,6,7] : List Nat).Nodup; decide)) earlier
  ⟨_, defs, by simp [Headers.keys, e, b, ScalarRows.scalarHeader, Ne.symm apart]⟩

/-- The witnesses are references in the admitted table. Both equations concern the Core
meaning at those references and quantify over every compatible model and every scalar input. -/
def PairValues (p : Typed V) (b e : Key) : Prop :=
  ∃ (boundary : Member p.headers.fns (rows.scalarHeader b [rows.pair]))
    (evaluate : Member p.headers.fns (rows.scalarHeader e [rows.pair,rows.scalarTy])),
    ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], rows.Arithmetic M →
    ∀ a z r : rows.F M,
      fnMeaning M p boundary (.cons (a,z,()) .nil) = .done (.cons (a+z) .nil) ∧
      fnMeaning M p evaluate (.cons (a,z,()) (.cons r .nil)) = .done (.cons (line (a,z) r) .nil)

theorem expected_values (form : Evaluation) (b e : Key) (apart : b ≠ e) :
    PairValues (expected form b e apart) b e := by
  refine ⟨.tail .head, .head, ?_⟩
  intro M field math a z r
  cases form with
  | interpolation => exact ⟨rows.boundary_value M _ b a z math, rows.evaluate_value M _ e a z r math⟩
  | affine => exact ⟨rows.boundary_value M _ b a z math, rows.affine_value M _ e a z r math⟩

/-- A successful check returns the two meaning laws for the actual program produced by admission. -/
def certify {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (form : Evaluation) (accepted : admit named assoc = .ok a) (boundary evaluate : Key) :
    Option (PLift (PairValues a.program boundary evaluate)) := do
  if apart : boundary ≠ evaluate then
    letI := identifyAdmitted accepted (expected form boundary evaluate apart)
    if same : a.program = expected form boundary evaluate apart then
      return ⟨same ▸ expected_values form boundary evaluate apart⟩
    else none
  else none

end Zkc.Tests.Formal.SourcePairMembers

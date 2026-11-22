module

public import ZkcFormal.Interactive.HonestSumcheck
public import ZkcFormal.Interactive.TotalReplies

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.SourceCompleteness
open Zkc.Core JointEntry
open HonestPairs (SumRow Arithmetic args)

variable {V : Vocabulary} (rows : ScalarRows V) (sums : (n : Nat) → SumRow rows n)
variable (vectors : (n : Nat) → TableRestriction.Rows rows.scalarTy n) (events : ReductionRound.Events rows.scalarTy)
variable (p : Zkc.Core.Typed V) (key : Key) (n : Nat)

/-- A joint return for every reply, on any well-sized public table satisfying the source sum. -/
structure Certificate where
  shape : Shape V
  root : Member p.headers.protocols (TableVerifier.header rows.scalarTy n key shape)
  everyRun : ∀ (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)],
    Arithmetic rows sums vectors events n M → ∀ path (xs : List (rows.F M)) (claim : rows.F M),
    xs.length = 2^n → claim = xs.sum →
    Returns (protocolMeaning M p root path (args rows M n xs claim)) (fun out => out.1 = .nil)

def certify (red eval : Key) (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k)) :
    Option (Certificate rows sums vectors events p key n) := do
  let ⟨shape,root,law⟩ ← HonestPairs.certify rows sums vectors events p key red eval n evaluation
  return ⟨shape,root,by
    intro M _ _ math path xs claim size valid
    obtain ⟨x,rfl⟩ := Cube.exists_flatten_of_length n xs size
    exact law M math path x claim valid⟩

variable {rows sums vectors events p key n}

/-- Core validity supplies the required length of the public table. -/
theorem Certificate.everyValid (cert : Certificate rows sums vectors events p key n)
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : Arithmetic rows sums vectors events n M) (path : List Frame)
    (xs : List (rows.F M)) (claim : rows.F M)
    (valid : M.Valid (TableHalves.table rows.scalarTy n) xs) (correct : claim = xs.sum) :
    Returns (protocolMeaning M p cert.root path (args rows M n xs claim)) (fun out => out.1 = .nil) :=
  cert.everyRun M math path xs claim (valid.2 _ rfl) correct

/-- At least one complete supported return exists, including its actual final service state. -/
theorem Certificate.reaches (cert : Certificate rows sums vectors events p key n)
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : Arithmetic rows sums vectors events n M) (path : List Frame)
    (xs : List (rows.F M)) (claim : rows.F M) (size : xs.length = 2^n) (valid : claim = xs.sum)
    {σ : Type} (K : Experiment (GSig M) σ) (s : σ)
    (total : K.TotalOn (protocolMeaning M p cert.root path (args rows M n xs claim)) s) :
    ∃ out u, K.Reaches (protocolMeaning M p cert.root path (args rows M n xs claim)) s out u ∧ out.1 = .nil :=
  K.reaches_of_every _ s (cert.everyRun M math path xs claim size valid) total

/-- Unit return probability for a stateful service with full reply mass on its supported paths. -/
theorem Certificate.probability_one (cert : Certificate rows sums vectors events p key n)
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : Arithmetic rows sums vectors events n M) (path : List Frame)
    (xs : List (rows.F M)) (claim : rows.F M) (size : xs.length = 2^n) (valid : claim = xs.sum)
    {σ : Type} (K : Experiment (GSig M) σ) (s : σ)
    (total : K.TotalOn (protocolMeaning M p cert.root path (args rows M n xs claim)) s) :
    K.probability (protocolMeaning M p cert.root path (args rows M n xs claim)) s (fun _ _ => true) = 1 :=
  K.probability_one_of_every _ s (cert.everyRun M math path xs claim size valid) total

#print axioms certify
#print axioms Certificate.everyValid
#print axioms Certificate.reaches
#print axioms Certificate.probability_one
end ZkcFormal.Interactive.Sumcheck.SourceCompleteness

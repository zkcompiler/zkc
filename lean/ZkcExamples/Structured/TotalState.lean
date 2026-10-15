module

public import ZkcExamples.Structured.TotalStateData
public import Zkc.Source.Structured.Laws

@[expose] public section

/-! Universal equations for the retained native export. The nominal scalar
domain is interpreted in an explicit commutative ring; vector admission keeps
the unsigned index limit. These theorems concern the imported logical process. -/

namespace ZkcExamples.Structured.TotalState
open Zkc.Source Zkc.Source.Structured

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
-- Rewriting dependent callback types needs the resolved operation signatures.
set_option backward.isDefEq.respectTransparency false

/-- The program is computed by admission of the actual exported constructor data. -/
def program : Program := (check TotalStateData.snapshot).toOption.get (by decide +kernel)

theorem admitted : check TotalStateData.snapshot = .ok program := by rfl

def imported : Imported TotalStateData.snapshot := ⟨program, admitted⟩

private abbrev scalar : Ty := .field "bls12-381.fr"
private abbrev vector : Ty := .vector "bls12-381.fr"

private abbrev foldSpec : FoldSpec :=
  ⟨⟨"items", [vector], "bls12-381.fr", .here, true⟩,
    [scalar, scalar], [], "step", ""⟩

private def stepReturn : Region dialect
    [scalar, scalar, scalar, .index, vector] [scalar, scalar] :=
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

/-- A typed view of the checked helper, retaining the actual checked read. -/
private def stepBody : Region dialect [scalar, scalar, .index, vector] [scalar, scalar] :=
  .letOp (.boundedAt "bls12-381.fr")
    (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))
    .nil stepReturn

private def mainBody : Region dialect [vector, scalar, scalar] [scalar, scalar] :=
  .letOp (.fold foldSpec)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    .nil (.ret (.cons .here (.cons (.there .here) .nil)))

private abbrev stepHelper : Helper :=
  ⟨"step", [scalar, scalar, .index, vector], [scalar, scalar]⟩

variable {F : Type} [CommRing F] [DecidableEq F]

private def helpers : Meanings F :=
  [⟨stepHelper, fun args => stepBody.denote (meaning F []) args.get⟩]

def inputs (xs : List F) (a b : F) :
    Values (scalarAssignment F)
      [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons xs (.cons a (.cons b .nil))

def outputs (a b : F) :
    Values (scalarAssignment F) [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons a (.cons b .nil)

def process (xs : List F) (a b : F) := program.denote F (inputs xs a b)

private theorem process_fold (xs : List F) (a b : F) :
    process xs a b = denoteFold helpers foldSpec (inputs xs a b) := by
  change mainBody.denote (meaning F helpers) (inputs xs a b).get = _
  simp only [mainBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
    Values.get, operation]
  trans (denoteFold helpers foldSpec (inputs xs a b)).bind .done
  · congr 1
    funext result
    cases result with
    | cons a rest => cases rest with
      | cons b rest => cases rest; rfl
  · exact PIR.Proc.bind_done _

/-- Mathematical ordered pair fold: every item replaces `(a, b)` with `(b, x)`. -/
def reference (xs : List F) (a b : F) : F × F :=
  xs.foldl (fun state x => (state.2, x)) (a, b)

private theorem step_read (xs : List F) (a b x : F) (i : Nat)
    (read : xs[i]? = some x) :
    invoke helpers stepHelper (.cons a (.cons b (.cons i (.cons xs .nil)))) =
      .done (outputs b x) := by
  rw [invoke_found helpers stepHelper
    (fun args => stepBody.denote (meaning F []) args.get) (by rfl)]
  let args : Values (scalarAssignment F) [scalar, scalar, .index, vector] :=
    .cons a (.cons b (.cons i (.cons xs .nil)))
  exact congrArg
    (fun action : Closed (Values (scalarAssignment F) [scalar]) =>
      action.bind fun values => stepReturn.denote (meaning F [])
        (Environment.prepend args.get values))
    (boundedAt_exact [] "bls12-381.fr" xs i x read)

omit [CommRing F] [DecidableEq F] in
private theorem range_reads (xs : List F) (fallback : F) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
      congrArg (List.cons x) ih

omit [CommRing F] [DecidableEq F] in
private theorem values_fold (xs : List F) (a b : F) :
    xs.foldl (fun state x => outputs (state.get (.there .here)) x) (outputs a b) =
      outputs (reference xs a b).1 (reference xs a b).2 := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih => exact ih b x

/-- Universal complete-process equation for the actual admitted snapshot.
Only enumerated indices are read, so dynamic checked-read safety suffices. -/
theorem process_eq_reference (xs : List F) (a b : F)
    (lengthValid : xs.length < indexLimit) :
    process xs a b = .done (outputs (reference xs a b).1 (reference xs a b).2) := by
  rw [process_fold]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons xs (.nil : Values (scalarAssignment F) []))).admit =
        .returned (List.range xs.length) := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, lengthValid]
  have folded := denoteFold_reference helpers foldSpec (.cons xs .nil) (outputs a b) .nil
    (List.range xs.length) domainAdmitted
    (fun state (i : Nat) => outputs (state.get (.there .here)) (xs[i]?.getD 0))
    (fun _ => True) trivial (by
      intro state i member _
      change Nat at i
      cases state with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      have bound := enumerated_index_bound xs i member
      have read : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
      constructor
      · rw [foldTransition_unfiltered helpers foldSpec (by rfl)]
        change invoke helpers stepHelper (.cons a (.cons b (.cons i (.cons xs .nil)))) =
          .done (outputs b (xs[i]?.getD 0))
        rw [read]
        exact step_read xs a b xs[i] i read
      · trivial)
  change denoteFold helpers foldSpec
    ((Values.cons xs Values.nil).append ((outputs a b).append Values.nil)) = _
  rw [folded]
  have enumeration := congrArg
    (fun items : List F => items.foldl
      (fun state x => outputs (state.get (.there .here)) x) (outputs a b))
    (range_reads xs 0)
  rw [List.foldl_map] at enumeration
  rw [enumeration, values_fold]

/-- Oversized domains refuse before any callback, rather than using unchecked reads. -/
theorem process_refuses (xs : List F) (a b : F)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    process xs a b = .halt .refused := by
  rw [process_fold]
  change denoteFold helpers foldSpec
    ((Values.cons xs Values.nil).append ((outputs a b).append Values.nil)) = _
  rw [denoteFold_pack]
  simp [Finite.execute, DomainSpec.denote, foldSpec, Values.get, Finite.Domain.admit,
    lengthInvalid, Finite.admitThen]

/-- The complete equation includes domain admission on every input. -/
theorem process_eq_checked_reference (xs : List F) (a b : F) :
    process xs a b =
      if xs.length < indexLimit then
        .done (outputs (reference xs a b).1 (reference xs a b).2)
      else .halt .refused := by
  split
  · exact process_eq_reference xs a b ‹_›
  · exact process_refuses xs a b ‹_›

theorem process_nil (a b : F) : process [] a b = .done (outputs a b) :=
  process_eq_reference [] a b (by change 0 < indexLimit; decide +kernel)

theorem process_singleton (x a b : F) : process [x] a b = .done (outputs b x) :=
  process_eq_reference [x] a b (by change 1 < indexLimit; decide +kernel)

theorem process_pair (x y a b : F) : process [x, y] a b = .done (outputs x y) :=
  process_eq_reference [x, y] a b (by change 2 < indexLimit; decide +kernel)

/-- Arbitrary prefixes cannot change the ordered final pair of a two-item suffix. -/
theorem process_append_pair (xs : List F) (x y a b : F)
    (lengthValid : (xs ++ [x, y]).length < indexLimit) :
    process (xs ++ [x, y]) a b = .done (outputs x y) := by
  simpa [reference, List.foldl_append] using
    process_eq_reference (xs ++ [x, y]) a b lengthValid

/-- The exported source descriptor is retained by the admitted subject. -/
theorem exact_subject : imported.program.snapshot = TotalStateData.snapshot :=
  imported.exactSubject

/-- A downstream client consumes the equation through the exact imported subject. -/
theorem imported_eq_reference (xs : List F) (a b : F)
    (lengthValid : xs.length < indexLimit) :
    imported.program.denote F (inputs xs a b) =
      .done (outputs (reference xs a b).1 (reference xs a b).2) :=
  process_eq_reference xs a b lengthValid

end ZkcExamples.Structured.TotalState

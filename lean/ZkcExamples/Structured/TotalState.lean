module

public import ZkcExamples.Structured.TotalStateData
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.Structured.UnitViews

@[expose] public section

/-! Universal equations for the retained native export. The nominal scalar
domain is interpreted in an explicit commutative ring; vector admission keeps
the unsigned index limit. These theorems concern the imported logical process. -/

namespace ZkcExamples.Structured.TotalState
open Zkc.Source Zkc.Source.Structured

abbrev scalar : Ty := .field "bls12-381.fr"
abbrev vector : Ty := .vector "bls12-381.fr"

abbrev foldSpec : FoldSpec :=
  ⟨⟨"items", [vector], "bls12-381.fr", .here, true⟩,
    [scalar, scalar], [], "step", "", .math⟩

def stepReturn : Region dialect
    [scalar, scalar, scalar, .index, vector] [scalar, scalar] :=
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

/-- A typed view of the checked helper, retaining the actual checked read. -/
def stepBody : Region dialect [scalar, scalar, .index, vector] [scalar, scalar] :=
  .letOp (.boundedAt "bls12-381.fr")
    (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))
    .nil stepReturn

def mainBody : Region dialect [vector, scalar, scalar] [scalar, scalar] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.fold foldSpec)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    .nil (.ret (.cons .here (.cons (.there .here) .nil)))

abbrev stepHelper : Helper :=
  ⟨"step", .math, [scalar, scalar, .index, vector], [scalar, scalar]⟩

def protocolSignature : ProtocolSignature where
  name := "main"
  roles := ["P"]
  inputs := [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0], [0]]

set_option smartUnfolding true in
def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fold {domain := {name := "items", inputs := [.vector "bls12-381.fr"], field := "bls12-381.fr", container := .here, indices := true}, state := [.field "bls12-381.fr", .field "bls12-381.fr"], captures := [], step := "step", predicate := "", kind := .math}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

-- The program is the literal checked unit admitted from the exact exported
-- constructor data, with its closed single-role projection.
structured_closed_views TotalStateData.snapshot
  helpers [step]
  protocols [protocol]
  root mainBody

theorem admitted : checkClosed TotalStateData.snapshot = .ok program := kernel_admission

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

variable (F G) in
private def table : Meanings F G := program.payload.meanings F G

-- Direct reduction avoids expanding the dependent admission equations.
set_option smartUnfolding false in
/-- The named checked declaration supplies its own invocation equation in the
complete table, independent of the position of unrelated declarations. -/
private theorem invoke_step (arguments : Values (assignment F G)
    [scalar, scalar, .index, vector]) :
    invoke (table F G) stepHelper arguments =
      stepBody.denote (meaning F G (table F G)) arguments.get :=
  Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload stepDefinition step_member
    stepBody (by rfl) arguments

def inputs (xs : List F) (a b : F) :
    Values (assignment F G)
      [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons xs (.cons a (.cons b .nil))

def outputs (a b : F) :
    Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .cons a (.cons b .nil)

set_option smartUnfolding false in
def process (xs : List F) (a b : F) :
    Closed (Values (assignment F G) [.field "bls12-381.fr", .field "bls12-381.fr"]) :=
  program.denote F G (inputs xs a b)

set_option smartUnfolding false in
private theorem process_fold (xs : List F) (a b : F) :
    process (G := G) xs a b = Evaluation.denoteFold (table F G) foldSpec (inputs xs a b) := by
  have bodyLaw : mainBody.denote (meaning F G (table F G)) (inputs xs a b).get =
      Evaluation.denoteFold (table F G) foldSpec (inputs xs a b) := by
    set_option smartUnfolding true in
      simp only [mainBody, Region.denote, meaning, Operands.eval, Regions.denote, inputs,
        Values.get, Evaluation.meaning, Evaluation.operation,
        SiteObservations.closed, SiteObservations.silent, PIR.Proc.bind, Environment.prepend]
    trans (Evaluation.denoteFold (table F G) foldSpec (inputs xs a b)).bind .done
    · congr 1
      funext result
      cases result with
      | cons a rest => cases rest with
        | cons b rest => cases rest; rfl
    · exact PIR.Proc.bind_done _
  exact (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload mainBody (by rfl) (inputs xs a b)).trans bodyLaw

/-- Mathematical ordered pair fold: every item replaces `(a, b)` with `(b, x)`. -/
def reference (xs : List F) (a b : F) : F × F :=
  xs.foldl (fun state x => (state.2, x)) (a, b)

private theorem step_read (xs : List F) (a b x : F) (i : Nat)
    (read : xs[i]? = some x) :
    invoke (table F G) stepHelper (.cons a (.cons b (.cons i (.cons xs .nil)))) =
      .done (outputs b x) := by
  rw [invoke_step]
  let args : Values (assignment F G) [scalar, scalar, .index, vector] :=
    .cons a (.cons b (.cons i (.cons xs .nil)))
  exact congrArg
    (fun action : Closed (Values (assignment F G) [scalar]) =>
      action.bind fun values => stepReturn.denote (meaning F G (table F G))
        (Environment.prepend args.get values))
    (Evaluation.boundedAt_exact SiteObservations.closed (table F G) "bls12-381.fr" xs i x read)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem range_reads (xs : List F) (fallback : F) :
    (List.range xs.length).map (fun i => xs[i]?.getD fallback) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using
      congrArg (List.cons x) ih

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem values_fold (xs : List F) (a b : F) :
    xs.foldl (fun state x => outputs (G := G) (state.get (.there .here)) x) (outputs a b) =
      outputs (reference xs a b).1 (reference xs a b).2 := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih => exact ih b x

/-- Universal complete-process equation for the actual admitted snapshot.
Only enumerated indices are read, so dynamic checked-read safety suffices. -/
theorem process_eq_reference (xs : List F) (a b : F)
    (lengthValid : xs.length < indexLimit) :
    process (G := G) xs a b = .done (outputs (reference xs a b).1 (reference xs a b).2) := by
  rw [process_fold]
  have domainAdmitted :
      (foldSpec.domain.denote (.cons xs (.nil : Values (assignment F G) []))).admit =
        .returned (List.range xs.length) := by
    simp [foldSpec, DomainSpec.denote, Finite.Domain.admit, Values.get, lengthValid]
  have folded := Evaluation.denoteFold_reference (table F G) foldSpec (.cons xs .nil) (outputs a b) .nil
    (List.range xs.length) domainAdmitted
    (fun state (i : Nat) => outputs (G := G) (state.get (.there .here)) (xs[i]?.getD 0))
    (fun _ => True) trivial (by
      intro state i member _
      change Nat at i
      cases state with | cons a rest => ?_
      cases rest with | cons b rest => ?_
      cases rest
      have bound := Evaluation.enumerated_index_bound xs i member
      have read : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
      constructor
      · exact (Evaluation.foldTransition_unfiltered (table F G) foldSpec (by rfl)
          (.cons xs .nil) .nil (.cons a (.cons b .nil)) i).trans
          (by
            have result := step_read (G := G) xs a b xs[i] i read
            rw [read]
            exact result)
      · trivial)
  change Evaluation.denoteFold (table F G) foldSpec
    ((Values.cons xs Values.nil).append ((outputs a b).append Values.nil)) = _
  rw [folded]
  have enumeration := congrArg
    (fun items : List F => items.foldl
      (fun state x => outputs (G := G) (state.get (.there .here)) x) (outputs a b))
    (range_reads xs 0)
  rw [List.foldl_map] at enumeration
  exact congrArg PIR.Proc.done (enumeration.trans (values_fold xs a b))

/-- Unrepresentable domain lengths exhaust before any callback. -/
theorem process_exhausted (xs : List F) (a b : F)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    process (G := G) xs a b = .halt .exhausted := by
  rw [process_fold]
  change Evaluation.denoteFold (table F G) foldSpec
    ((Values.cons xs Values.nil).append ((outputs a b).append Values.nil)) = _
  rw [Evaluation.denoteFold_pack]
  simp [Finite.execute, DomainSpec.denote, foldSpec, Values.get, Finite.Domain.admit,
    lengthInvalid, Finite.admitThen]

/-- The complete equation includes domain admission on every input. -/
theorem process_eq_checked_reference (xs : List F) (a b : F) :
    process (G := G) xs a b =
      if xs.length < indexLimit then
        .done (outputs (reference xs a b).1 (reference xs a b).2)
      else .halt .exhausted := by
  split
  · exact process_eq_reference xs a b ‹_›
  · exact process_exhausted xs a b ‹_›

theorem process_nil (a b : F) : process (G := G) [] a b = .done (outputs a b) :=
  process_eq_reference [] a b (by change 0 < indexLimit; decide +kernel)

theorem process_singleton (x a b : F) : process (G := G) [x] a b = .done (outputs b x) :=
  process_eq_reference [x] a b (by change 1 < indexLimit; decide +kernel)

theorem process_pair (x y a b : F) : process (G := G) [x, y] a b = .done (outputs x y) :=
  process_eq_reference [x, y] a b (by change 2 < indexLimit; decide +kernel)

/-- Arbitrary prefixes cannot change the ordered final pair of a two-item suffix. -/
theorem process_append_pair (xs : List F) (x y a b : F)
    (lengthValid : (xs ++ [x, y]).length < indexLimit) :
    process (G := G) (xs ++ [x, y]) a b = .done (outputs x y) := by
  simpa [reference, List.foldl_append] using
    process_eq_reference (xs ++ [x, y]) a b lengthValid

set_option smartUnfolding false in
/-- A downstream client consumes the equation through the exact imported subject. -/
theorem imported_eq_reference (xs : List F) (a b : F)
    (lengthValid : xs.length < indexLimit) :
    imported.program.denote F G (inputs xs a b) =
      .done (outputs (reference xs a b).1 (reference xs a b).2) :=
  process_eq_reference xs a b lengthValid

end ZkcExamples.Structured.TotalState

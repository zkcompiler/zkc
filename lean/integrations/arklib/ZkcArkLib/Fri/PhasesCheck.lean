module

public import ZkcArkLib.Fri.PhasesCausal
public import ZkcArkLib.Fri.SourceTerminal

/-! # Guarded mathematical Check

These operations are permission to perform a read of a word already fixed by publication.
They return Unit, so an arbitrary complete-outcome handler may abort or change state, but
cannot replace a published value. The source publication/readback profile must establish
that property for actual handles. This is a small mathematical protocol, not source syntax
evaluation. An application to a concrete source must prove this property for its installed handles.

The selected read precedes its equality guard; the guard precedes the next virtual read;
the virtual read precedes low then high base reads. Association is tested at the initial
read before the first virtual read. Numeric, local-call and structural setup failures are
additional source obligations, rather than silently successful ideal operations.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

variable {F : Type} [Field F] [DecidableEq F]

/-- The actual normalized source coefficient value has the terminal meaning used here. -/
theorem terminal_source_evaluate (roots : ℕ → F) (cs : List F) (shift : F)
    (size position : ℕ) :
    Zkc.Source.Structured.Numerical.evaluate
      (Zkc.Source.Structured.PolynomialValue.ofCoefficients 0 cs).coefficients
      (point roots shift size position) = terminal roots cs shift size position := by
  rw [SourceTerminal.evaluate_eq, terminal, evaluate_eq]

inductive CheckOperation where
  | read (round logSize position : ℕ)
  | view (round logSize position : ℕ)
  | terminal
  deriving DecidableEq, Repr

def checkOperations : PIR.Signature := ⟨CheckOperation, fun _ ↦ Unit⟩

/-- Three ordered permission boundaries for one installed binary virtual fold. -/
def foldReads {m : ℕ} (round : ℕ) (position : Fin (2 ^ m)) :
    PIR.Process checkOperations Unit :=
  .call (.view round (m + 1) position.val) fun _ =>
    .call (.read round (m + 1) (lowIndex position).val) fun _ =>
      .call (.read round (m + 1) (highIndex position).val) fun _ => .done ()

theorem foldReads_yields {m : ℕ} (round : ℕ) (position : Fin (2 ^ m)) :
    PIR.Yields (fun _ ↦ True) (foldReads round position) := fun _ _ _ ↦ trivial

def checkPath (roots : ℕ → F) : {m R : ℕ} → ℕ → Layers F m R → F →
    Fin (2 ^ m) → F → PIR.Process checkOperations Unit
  | m, _, _, .final cs, shift, position, expected =>
      .call .terminal fun _ =>
        if terminal roots cs shift m position = expected then .done () else .halt .reject
  | m + 1, _, round, .fold word beta rest, shift, position, expected =>
      .call (.read round (m + 1) position.val) fun _ =>
        if word position = expected then
          (foldReads round (lowHalf position)).bind fun _ =>
            checkPath roots (round + 1) rest (shift * shift) (lowHalf position)
              (foldedValue roots (word (lowIndex (lowHalf position)))
                (word (highIndex (lowHalf position))) shift (m + 1) (lowHalf position) beta)
        else .halt .reject

theorem checkPath_yields (roots : ℕ → F) : ∀ {m R : ℕ} (round : ℕ)
    (layers : Layers F m R) (shift : F) (position : Fin (2 ^ m)) (expected : F),
    PIR.Yields (fun _ ↦ path roots layers shift position expected = true)
      (checkPath roots round layers shift position expected)
  | m, _, round, .final cs, shift, position, expected => by
      simp only [checkPath, PIR.Yields]
      intro _
      split
      · simpa only [PIR.Yields, path, decide_eq_true_eq] using ‹_ = _›
      · trivial
  | _, _, round, .fold word beta rest, shift, position, expected => by
      intro _
      split
      · rename_i equal
        apply (foldReads_yields round (lowHalf position)).bind
        intro _ _
        exact (checkPath_yields roots (round + 1) rest _ _ _).mono
          (fun _ tail ↦ by simpa only [path, equal, decide_true, Bool.true_and] using tail)
      · trivial

/-- Optional association is a value at this query ordinal, including repeated positions. -/
def checkFirst (roots : ℕ → F) {m R : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (position : Fin (2 ^ (m + 1))) (associatedValue : Option F) :
    PIR.Process checkOperations Unit :=
  match layers with
  | .fold word beta rest =>
      .call (.read 0 (m + 1) position.val) fun _ =>
        if associatedValue.all (· = word position) then
          (foldReads 0 (lowHalf position)).bind fun _ =>
            checkPath roots 1 rest (shift * shift) (lowHalf position)
              (foldedValue roots (word (lowIndex (lowHalf position)))
                (word (highIndex (lowHalf position))) shift (m + 1) (lowHalf position) beta)
        else .halt .reject

theorem checkFirst_yields (roots : ℕ → F) {m R : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (position : Fin (2 ^ (m + 1))) (associatedValue : Option F) :
    PIR.Yields (fun _ ↦ firstPath roots layers shift position = true ∧
      ∀ value ∈ associatedValue, value = firstValue layers position)
      (checkFirst roots layers shift position associatedValue) := by
  cases layers with
  | fold word beta rest =>
      intro _
      split
      · rename_i association
        apply (foldReads_yields 0 (lowHalf position)).bind
        intro _ _
        apply (checkPath_yields roots 1 rest _ _ _).mono
        intro _ tail
        refine ⟨tail, ?_⟩
        simpa only [firstValue_eq, Option.all_eq_true, decide_eq_true_eq,
          Option.mem_def] using association
      · trivial

def checkList (roots : ℕ → F) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) (association : Fin s → Option F) :
    List (Fin s) → PIR.Process checkOperations Unit
  | [] => .done ()
  | q :: qs => (checkFirst roots layers shift (positions q) (association q)).bind fun _ =>
      checkList roots layers shift positions association qs

theorem checkList_yields (roots : ℕ → F) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) (association : Fin s → Option F) :
    ∀ qs, PIR.Yields (fun _ ↦ ∀ q ∈ qs,
      firstPath roots layers shift (positions q) = true ∧
        ∀ value ∈ association q, value = firstValue layers (positions q))
      (checkList roots layers shift positions association qs)
  | [] => by simp [checkList, PIR.Yields]
  | q :: qs => by
      apply (checkFirst_yields roots layers shift (positions q) (association q)).bind
      intro _ head
      exact (checkList_yields roots layers shift positions association qs).mono
        (fun _ tail ↦ by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro head tail)

/-- Typed setup has already established dimensions. Exact coefficients precede every read. -/
def check (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) (association : Fin s → Option F) :
    PIR.Process checkOperations (Result F (m + 1) s) :=
  if exactCoefficients t layers.coefficients then
    (checkList roots layers shift positions association (List.finRange s)).bind fun _ =>
      .done ⟨true, positions, values layers positions⟩
  else .halt .reject

theorem check_yields (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) (association : Fin s → Option F) :
    PIR.Yields (fun result ↦ accepts roots t layers shift positions = true ∧
      result.accepted = true ∧ result.positions = positions ∧
      result.valuesV = values layers positions ∧
      ∀ q value, value ∈ association q → value = result.valuesV q)
      (check roots t layers shift positions association) := by
  unfold check
  split
  · rename_i length
    apply (checkList_yields roots layers shift positions association (List.finRange s)).bind
    intro _ all
    refine ⟨?_, rfl, rfl, rfl, ?_⟩
    · simp only [accepts, length, Bool.true_and, List.all_eq_true]
      exact fun q member ↦ (all q member).1
    · intro q value member
      exact (all q (List.mem_finRange q)).2 value member
  · trivial

end ZkcSecurity.ArkLib.Fri.Phases

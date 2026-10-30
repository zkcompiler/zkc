import ZkcSecurity.Bindings.Oracle.AuthenticatedPermutation
import Mathlib.Data.Fin.Rev

/-! Reuse and refusal clients of the parametric positional permutation adapter.
The finite controls test its boundaries; they are not its mathematical proof. -/

set_option autoImplicit false
namespace TestsSecurity.OraclePermutation

open ZkcSecurity.Families.Proximity ZkcSecurity.Commitment
open ZkcSecurity.Realizations.Oracle.Permutation
open OracleComp OracleSpec

/-! First client: reversal of a fixed-reference code, with arbitrary alphabet,
size, reference and gap. Both exact validity and No use the permuted code. -/
section Reversal
variable {Value : Type} [DecidableEq Value] (size : ℕ) (reference word : Fin (size + 1) → Value)
  (threshold : ℚ≥0)

omit [DecidableEq Value] in
theorem reversal_valid :
    reindex Fin.revPerm word ∈ permutedCode Fin.revPerm {reference} ↔ word = reference := by
  simpa using mem_permutedCode_iff Fin.revPerm {reference} word

theorem reversal_far :
    Far (permutedCode Fin.revPerm {reference}) threshold (reindex Fin.revPerm word) ↔
      Far {reference} threshold word :=
  far_reindex_iff Fin.revPerm {reference} threshold word

variable {J : PIR.Signature} {Shape : Type}

omit [DecidableEq Value] in
theorem reversal_read (words : Words J Shape Value) (tables : List (Table Value))
    (handle : ℕ) (found : tables[handle]? = some (positionalTable word)) (index : Fin (size + 1)) :
    withTables words tables (read Fin.revPerm handle index) = .done (word index.rev) :=
  withTables_read words Fin.revPerm word tables handle found index

end Reversal

/-! Second client: swap two positions in a repetition code. A different code
family and permutation reuse the same distance/No and exact access laws. -/
section Repetition
variable {Value : Type} [DecidableEq Value] (size : ℕ)

def repetitionCode : Set (Fin (size + 2) → Value) := {word | ∃ value, word = fun _ => value}

omit [DecidableEq Value] in
theorem repetitionCode_permuted (permutation : Equiv.Perm (Fin (size + 2))) :
    permutedCode permutation (repetitionCode (Value := Value) size) = repetitionCode size := by
  ext word
  constructor
  · rintro ⟨_, ⟨value, rfl⟩, rfl⟩
    exact ⟨value, rfl⟩
  · rintro ⟨value, rfl⟩
    exact ⟨fun _ => value, ⟨value, rfl⟩, rfl⟩

theorem swap_repetition_far (threshold : ℚ≥0) (word : Fin (size + 2) → Value) :
    Far (permutedCode (Equiv.swap 0 1) (repetitionCode (Value := Value) size)) threshold
        (reindex (Equiv.swap 0 1) word) ↔
      Far (repetitionCode size) threshold word :=
  far_reindex_iff (Equiv.swap 0 1) (repetitionCode size) threshold word

theorem swap_same_repetition_code (threshold : ℚ≥0) (word : Fin (size + 2) → Value) :
    Far (repetitionCode size) threshold (reindex (Equiv.swap 0 1) word) ↔
      Far (repetitionCode size) threshold word := by
  simpa only [repetitionCode_permuted] using swap_repetition_far size threshold word

variable {J : PIR.Signature} {Shape : Type}

omit [DecidableEq Value] in
theorem swap_repetition_read (words : Words J Shape Value) (word : Fin (size + 2) → Value)
    (tables : List (Table Value)) (handle : ℕ)
    (found : tables[handle]? = some (positionalTable word)) (index : Fin (size + 2)) :
    withTables words tables (read (Equiv.swap 0 1) handle index) =
      .done (reindex (Equiv.swap 0 1) word index) :=
  withTables_read words (Equiv.swap 0 1) word tables handle found index

end Repetition

theorem reversal_nonidentity : (Fin.revPerm : Equiv.Perm (Fin 4)) ≠ Equiv.refl _ := by
  intro equal
  have impossible := congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation 0) equal
  contradiction

theorem swap_nonidentity : (Equiv.swap (0 : Fin 4) 1) ≠ Equiv.refl _ := by
  intro equal
  have impossible := congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation 0) equal
  simp at impossible

def zeroWord : Fin 4 → Bool := fun _ => false
def oneError : Fin 4 → Bool := fun index => decide (index = 1)

theorem noninjective_indices : ¬ Function.Injective (fun _ : Fin 4 => (0 : Fin 4)) := by
  intro injective
  have impossible := injective (a₁ := 0) (a₂ := 1) rfl
  contradiction

/-- Collapsing all positions loses the only error, destroying normalized distance. -/
theorem noninjective_loses_distance :
    relativeDistance (oneError ∘ fun _ : Fin 4 => 0) (zeroWord ∘ fun _ : Fin 4 => 0) = 0 ∧
      relativeDistance oneError zeroWord = 1 / 4 := by
  decide +kernel

/-- Exact invalidity lies in the gap; it is not a farness premise. -/
theorem invalid_but_near : oneError ∉ ({zeroWord} : Set (Fin 4 → Bool)) ∧
    ¬ Far {zeroWord} (1 / 2) oneError := by
  constructor
  · intro member
    have equal : oneError = zeroWord := member
    have impossible := congrFun equal 1
    contradiction
  · intro far
    have impossible := far zeroWord (by simp)
    have distance : relativeDistance oneError zeroWord = 1 / 4 := by decide +kernel
    rw [distance] at impossible
    exact (by decide +kernel : ¬ (1 / 2 : ℚ≥0) ≤ 1 / 4) impossible

theorem near_stays_near_after_permutation :
    reindex Fin.revPerm oneError ∉ permutedCode Fin.revPerm {zeroWord} ∧
      ¬ Far (permutedCode Fin.revPerm {zeroWord}) (1 / 2) (reindex Fin.revPerm oneError) := by
  rw [mem_permutedCode_iff, far_reindex_iff]
  exact invalid_but_near

/-- Both requests have the same Yes set, but changing the fixed gap breaks No transport. -/
theorem same_yes_different_no : Far {zeroWord} (1 / 4) oneError ∧
    ¬ Far {zeroWord} (1 / 2) oneError := by
  refine ⟨?_, invalid_but_near.2⟩
  intro codeword member
  have equal : codeword = zeroWord := member
  subst codeword
  decide +kernel

/-- Reindexing the word without reindexing its code can even break exact validity. -/
theorem wrong_code_direction :
    oneError ∈ ({oneError} : Set (Fin 4 → Bool)) ∧
      reindex Fin.revPerm oneError ∉ ({oneError} : Set (Fin 4 → Bool)) := by
  refine ⟨by simp, ?_⟩
  intro equal
  have impossible := congrFun equal 1
  contradiction

def base : PIR.Signature where
  Op := Unit
  Reply _ := Table Bool

def words : Words base Unit Bool where
  word _ := ()
  toTable _ table := table
  ofTable _ table := table

/-- An implementation may return exactly the right value after redundant access. -/
def excessiveRead (index : Fin 4) : PIR.Process (committed base Unit Bool) Bool :=
  .call (.read 0 0) fun _ => .call (.read 0 (Fin.revPerm index).val) .done

theorem excessiveRead_value (word : Fin 4 → Bool) (index : Fin 4) :
    withTables words [positionalTable word] (excessiveRead index) =
      withTables words [positionalTable word] (read Fin.revPerm 0 index) := by
  unfold excessiveRead
  rw [withTables]
  have first : lookup [positionalTable word] 0 0 = some (word 0) := by
    simpa [lookup] using positionalTable_at word (0 : Fin 4)
  rw [first]
  rfl

theorem excessiveRead_refused (index : Fin 4) : ¬ PIR.Within 1 (excessiveRead index) := by
  intro bounded
  exact bounded false

theorem oneRead_has_exact_cost (index : Fin 4) :
    PIR.Within 1 (read (J := base) (Shape := Unit) (Value := Bool) Fin.revPerm 0 index) ∧
      ¬ PIR.Within 0 (read (J := base) (Shape := Unit) (Value := Bool) Fin.revPerm 0 index) :=
  ⟨read_within_one _ _ _, read_not_within_zero _ _ _⟩

/-- Missing references reject rather than supplying a default word. -/
theorem missing_handle_rejects (index : Fin 4) :
    withTables words [] (read Fin.revPerm 0 index) = .halt .reject :=
  withTables_read_missing words Fin.revPerm [] 0 index rfl

/-! The existing lazy random oracle returns a point mass on a cached key.
It differs from a fresh uniform bit, which can return the opposite bit. -/
abbrev BitSpec := Unit →ₒ Fin 2

theorem cached_bit_is_deterministic (cache : BitSpec.QueryCache) (found : cache () = some 0) :
    (BitSpec.randomOracle ()).run cache = pure (0, cache) :=
  QueryImpl.withCaching_run_some uniformSampleImpl found

theorem cached_bit_is_not_fresh (cache : BitSpec.QueryCache) (found : cache () = some 0) :
    ((BitSpec.randomOracle ()).run' cache) ≠ ($ᵗ (Fin 2)) := by
  intro equal
  have opposite : (1 : Fin 2) ∈ support ($ᵗ (Fin 2)) := by simp
  rw [← equal, StateT.run'_eq, cached_bit_is_deterministic cache found] at opposite
  simp at opposite

#print axioms ZkcSecurity.Families.Proximity.far_reindex_iff
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.run_read
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.authenticated_read_bind
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.authenticated_query_bound
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.authenticated_no_transcript_queries
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.authenticated_cache_extends
#print axioms ZkcSecurity.Realizations.Oracle.Permutation.authenticated_transcript_frame
#print axioms invalid_but_near
#print axioms excessiveRead_refused
#print axioms cached_bit_is_not_fresh

end TestsSecurity.OraclePermutation

module

public import Zkc.Claims.Registry
public import ZkcSecurity.Transformations.Commitment.FiniteRecovery
public import VCVio.OracleComp.EvalDist

@[expose] public section

/-! A closed, versioned model-level registration for finite straight-line
recovery. The library interprets the profile; a registry entry cannot carry a
replacement relation, access handler, algorithm or proposition. The original
recovery request is an index, not copied application metadata. This module has
no ArkLib dependency and issues no compiler or native-runtime receipt. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.FiniteRecovery
open OracleComp OracleSpec Zkc.Claims
open ZkcSecurity.Commitment.FiniteRecovery

def identifier : Identifier := ⟨"extractors.finite_two_cell_sum", 0⟩
def schema : String := "zkc.extractor.finite-two-cell-sum/0"

/-- A closed library interpretation, rather than an evidence-owned program. -/
inductive Profile where
  | orderedTwoCellSum
  deriving DecidableEq

def profileEntry : Export Profile := ⟨identifier, schema, some .orderedTwoCellSum⟩
def registry : Registry Profile := ⟨[profileEntry]⟩

/-- Every probabilistic sender of a pair is allowed, including invalid pairs.
Recovery receives that same pair. -/
abbrev Sender (F : Type) := ProbComp (F × F)

variable {F : Type} [Add F] [DecidableEq F]

/-- Keep the sent cells and the actual two-read verifier's verdict together.
The only input available to the verifier is the immutable answer function. -/
def run (request : Request F) (sender : Sender F) : ProbComp ((F × F) × Bool) := do
  let cells ← sender
  pure (cells, evalWithAnswerFn (answers cells) request.verifier)

omit [Add F] [DecidableEq F] in
/-- Exact operational cost, independent of validity or sender support. -/
theorem query_bound_iff (request : Request F) (bound : Nat) :
    IsQueryBoundP request.extract (fun _ => True) bound ↔ 2 ≤ bound := by
  have : Nonempty F := ⟨request.expectedSum⟩
  simp [Request.extract, isQueryBoundP_query_bind_iff]
  omega

/-- The complete selected proposition. All semantic functions come from the
original request API. These fields are proofs, never alternative code. -/
structure Guarantee (request : Request F) (queries : Nat) : Prop where
  queriesFixed : queries = 2
  queryCost : ∀ bound, IsQueryBoundP request.extract (fun _ => True) bound ↔ 2 ≤ bound
  recovered : ∀ cells, evalWithAnswerFn (answers cells) request.extract = cells
  acceptance : ∀ sender : Sender F,
    Pr{let observed ← run request sender}[observed.2 = true] =
      Pr{let cells ← sender}[request.Holds (evalWithAnswerFn (answers cells) request.extract)]

def Profile.meaning (profile : Profile) (request : Request F) (queries : Nat) : Prop :=
  match profile with
  | .orderedTwoCellSum => Guarantee request queries

/-- Lookup, schema and resource selection precede evidence. The shared registry
owns missing keys, unknown versions and duplicate detection. -/
structure Evaluation (registrations : Registry Profile) (selected : Identifier)
    (request : Request F) (queries : Nat) where
  entry : Export Profile
  registered : registrations.lookup selected = .ok entry
  identified : entry.identifier = identifier
  schemaMatched : entry.schema = schema
  profile : Profile
  defined : entry.definition = some profile
  queriesFixed : queries = 2

def Evaluation.meaning {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (evaluation : Evaluation registrations selected request queries) : Prop :=
  evaluation.profile.meaning request queries

/-- Even a registry assembled by a caller can select only the fixed library
proposition. Evidence cannot reinterpret a registered identifier. -/
theorem Evaluation.meaning_eq {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (evaluation : Evaluation registrations selected request queries) :
    evaluation.meaning = Guarantee request queries := by
  cases evaluation.profile
  rfl

def evaluate (registrations : Registry Profile) (selected : Identifier)
    (request : Request F) (queries : Nat) :
    Except ResolutionError (Except Incomplete (Evaluation registrations selected request queries)) :=
  match registered : registrations.lookup selected with
  | .error error => .error error
  | .ok entry =>
    if identified : entry.identifier = identifier then
      if schemaMatched : entry.schema = schema then
        match defined : entry.definition with
        | none => .ok (.error ⟨[schema]⟩)
        | some profile =>
          if queriesFixed : queries = 2 then
            .ok (.ok ⟨entry, registered, identified, schemaMatched, profile, defined, queriesFixed⟩)
          else .error (.schema "finite recovery requires exactly two cell queries")
      else .error (.schema "finite recovery profile schema mismatch")
    else .error (.schema "finite recovery profile identifier mismatch")

/-- Canonical positive evaluation still crosses the shared registry lookup. -/
def canonical (request : Request F) : Evaluation registry identifier request 2 :=
  ⟨profileEntry, rfl, rfl, rfl, .orderedTwoCellSum, rfl, rfl⟩

omit [Add F] [DecidableEq F] in
theorem evaluate_canonical (request : Request F) :
    evaluate registry identifier request 2 = .ok (.ok (canonical request)) := rfl

/-- A proof method for the fixed evaluated proposition; it contributes no
semantic data. Full recovery holds for every pair before checking its sum. -/
theorem certify {registrations : Registry Profile} {selected : Identifier}
    {request : Request F} {queries : Nat}
    (evaluation : Evaluation registrations selected request queries) : evaluation.meaning := by
  rw [evaluation.meaning_eq]
  refine ⟨evaluation.queriesFixed, query_bound_iff request, extract_eq request, ?_⟩
  intro sender
  simp only [run, ← map_eq_pure_bind, prEvent_map, verifier_eq, decide_eq_true_eq, extract_eq]

end ZkcSecurity.Claims.FiniteRecovery

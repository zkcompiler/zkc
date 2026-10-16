module

public import Zkc.Source.Structured.LogicalChecking
public import ZkcExamples.Structured.SumcheckLogicalContext

@[expose] public section

/-! Exported logical-context metadata for the Sumcheck residual request, checked
against the actual retained Reduction root. The positive case checks to exactly
the atoms used by the security consumer; each negative case is refused with a
named reason. Identities carry static arities, so instances that share a native
representation remain distinct. -/
namespace ZkcExamples.Structured.SumcheckLogicalChecking
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical
open Zkc.Polynomial.Multilinear
open SumcheckContractBindings SumcheckLogicalContext

set_option maxRecDepth 20000

instance : DecidableEq vocabulary.Sorts := inferInstanceAs (DecidableEq TableSort)

def tableIdentity (dimension : Nat) : Identity :=
  ⟨"zkc::multilinear::logic::Polynomial", [.domain "bls12-381.fr", .nat dimension]⟩
def sumIdentity (dimension : Nat) : Identity :=
  ⟨"sumcheck::logic::Sum", [.domain "bls12-381.fr", .nat dimension]⟩
def residualIdentity (remaining count : Nat) : Identity :=
  ⟨"zkc::multilinear::logic::Evaluates", [.domain "bls12-381.fr", .nat remaining, .nat count]⟩

def sortCandidate (identity : Identity) : Option TableSort :=
  match identity.statics with
  | [_, .nat dimension] => some (.table dimension)
  | _ => none

def predicateCandidate (identity : Identity) : Option TablePredicate :=
  match identity.statics with
  | [_, .nat dimension] => some (.sum dimension)
  | [_, .nat remaining, .nat count] => some (.residual remaining count)
  | _ => none

/-- Candidates are accepted only when their full identity matches. -/
def resolution : Resolution vocabulary :=
  .ofCandidates vocabulary sortCandidate predicateCandidate

/-- The exported form of the residual request at the retained root. -/
def residualExport (remaining count : Nat) : RawContext where
  binders := [.library (tableIdentity (remaining + count))]
  atoms := [⟨residualIdentity remaining count,
    [.binder 0, .observed .output 2 1, .observed .output 3 1]⟩,
    ⟨sumIdentity (remaining + count), [.binder 0, .observed .input 2 1]⟩]

variable {F G : Type}

/-- The export checks to the security consumer's atoms. -/
theorem residual_export_checks :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature (residualExport 0 1) =
      .ok ⟨tableContext 1, [residualAtom 0 1, initialAtom 1]⟩ := by
  rfl

/-- The repacked root's export names the same identities with the repacked
ports, and checks to the transported atoms. -/
theorem repacked_export_checks :
    checkContext (Value := assignment F G) resolution repackedRoot.protocol.signature
      ⟨[.library (tableIdentity 1)],
        [⟨residualIdentity 0 1, [.binder 0, .observed .output 0 1, .observed .output 1 1]⟩,
         ⟨sumIdentity 1, [.binder 0, .observed .input 0 1]⟩]⟩ =
      .ok ⟨tableContext 1, [rootMap.atom (residualAtom 0 1), rootMap.atom (initialAtom 1)]⟩ := by
  rfl

/-- The retained root's export does not check against the repacked root: its
port positions now name P's residual values, not V's point. -/
theorem retained_export_refused_at_repacked :
    checkContext (Value := assignment F G) resolution repackedRoot.protocol.signature
      (residualExport 0 1) = .error (.observationMismatch .output 2 1) := by
  rfl

/-- A generic identity applied at the wrong static instance: the exported sum
over arity two is applied to a binder of arity one. -/
theorem ill_scoped_instance_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
      ⟨[.library (tableIdentity 1)], [⟨sumIdentity 2, [.binder 0, .observed .input 2 1]⟩]⟩ =
      .error (.sortMismatch 0) := by
  rfl

theorem unbound_binder_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
      ⟨[.library (tableIdentity 1)], [⟨sumIdentity 1, [.binder 1, .observed .input 2 1]⟩]⟩ =
      .error (.unboundBinder 1) := by
  rfl

/-- Observing V's point vector where the sum needs a scalar is refused, as is
observing P's input where only V holds the claim. -/
theorem wrong_observation_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
        ⟨[.library (tableIdentity 1)], [⟨sumIdentity 1, [.binder 0, .observed .output 2 1]⟩]⟩ =
        .error (.observationMismatch .output 2 1) ∧
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
        ⟨[.library (tableIdentity 1)], [⟨sumIdentity 1, [.binder 0, .observed .input 2 0]⟩]⟩ =
        .error (.observationMismatch .input 2 0) := by
  constructor <;> rfl

/-- An identity without its static arity names no instance. -/
theorem missing_static_argument_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
      ⟨[.library ⟨"zkc::multilinear::logic::Polynomial", [.domain "bls12-381.fr"]⟩], []⟩ =
      .error (.unknownSort ⟨"zkc::multilinear::logic::Polynomial", [.domain "bls12-381.fr"]⟩) := by
  rfl

/-- A candidate with the right shape but another declaration is not accepted. -/
theorem foreign_declaration_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
      ⟨[.library (tableIdentity 1)], [⟨⟨"sumcheck::logic::Other", [.domain "bls12-381.fr", .nat 1]⟩,
        [.binder 0, .observed .input 2 1]⟩]⟩ =
      .error (.unknownPredicate ⟨"sumcheck::logic::Other", [.domain "bls12-381.fr", .nat 1]⟩) := by
  rfl

theorem arity_mismatch_refused :
    checkContext (Value := assignment F G) resolution reductionRoot.protocol.signature
      ⟨[.library (tableIdentity 1)], [⟨sumIdentity 1, [.binder 0]⟩]⟩ =
      .error (.arityMismatch (sumIdentity 1)) := by
  rfl

/-- Two exported occurrences of one identity, as source aliases produce, check
to one predicate code and hence read one meaning. -/
theorem aliases_share_meaning
    (left right : Atom vocabulary (assignment F G) reductionRoot.protocol.signature (tableContext 1))
    (first second : RawAtom)
    (leftChecked : checkAtom resolution reductionRoot.protocol.signature (tableContext 1) first = .ok left)
    (rightChecked : checkAtom resolution reductionRoot.protocol.signature (tableContext 1) second = .ok right)
    (same : first.predicate = second.predicate) : left.predicate = right.predicate :=
  checkAtom_alias resolution reductionRoot.protocol.signature leftChecked rightChecked same

/-- Arity is part of identity although every table has the same native vector
representation. The same runtime vector can represent a table of arity two and
is not a table of arity three. -/
theorem arity_is_identity :
    vocabulary.sortIdentity (.table 2) ≠ vocabulary.sortIdentity (.table 3) ∧
    (ofList? 2 ([0, 1, 2, 3] : List Int)).isSome = true ∧
    (ofList? 3 ([0, 1, 2, 3] : List Int)).isSome = false := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [ofList?_isSome_iff]; rfl
  · cases present : (ofList? 3 ([0, 1, 2, 3] : List Int)).isSome with
    | false => rfl
    | true =>
      have := (ofList?_isSome_iff (n := 3) ([0, 1, 2, 3] : List Int)).mp present
      cases this

end ZkcExamples.Structured.SumcheckLogicalChecking

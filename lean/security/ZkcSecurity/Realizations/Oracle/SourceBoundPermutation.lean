module

public import ZkcSecurity.Families.Proximity.Contract
public import ZkcSecurity.Realizations.Oracle.AuthenticatedPermutation
public import Zkc.Source.Structured.RelationMeaning
public import Mathlib.Data.Fin.Rev

@[expose] public section

/-! A small installed relation client of the parametric positional library.
The request fixes the Boolean ABI, code, ordering and positive rational gap.
The registry supplies exact membership; the selected proximity contract supplies
the separate No predicate. Executable access remains the existing typed read,
not a claimed correspondence with a compiled source oracle operation. -/

set_option autoImplicit false
namespace ZkcSecurity.Realizations.Oracle.SourceBoundPermutation

open Zkc.Source Zkc.Source.Structured Zkc.Obligations
open ZkcSecurity.Families.Proximity
open ZkcSecurity.Commitment

abbrev Word := Fin 4 → Bool
abbrev wordTypes : List Ty := [.boolean, .boolean, .boolean, .boolean]

def encode (model : DomainModel) (word : Word) : Values model.Value wordTypes :=
  .cons (word 0) (.cons (word 1) (.cons (word 2) (.cons (word 3) .nil)))

def decode (model : DomainModel) (values : Values model.Value wordTypes) : Word :=
  fun index => match index.val with
    | 0 => values.get .here
    | 1 => values.get (.there .here)
    | 2 => values.get (.there (.there .here))
    | _ => values.get (.there (.there (.there .here)))

@[simp] theorem decode_encode (model : DomainModel) (word : Word) :
    decode model (encode model word) = word := by
  funext index
  fin_cases index <;> rfl

def reference : Word := fun index => decide (index = 1)

inductive Code where
  | fixedReference | repetition
  deriving DecidableEq

def Code.words : Code → Set Word
  | .fixedReference => {reference}
  | .repetition => {word | ∃ value, word = fun _ => value}

inductive PositionOrder where
  | reversal | swap
  deriving DecidableEq

def PositionOrder.permutation : PositionOrder → Equiv.Perm (Fin 4)
  | .reversal => Fin.revPerm
  | .swap => Equiv.swap 0 1

/-- Both supported gaps are actual positive distance parameters, not Boolean
relation outputs. Their numerator and denominator also occur in static ABI. -/
inductive Gap where
  | quarter | half
  deriving DecidableEq

def Gap.threshold : Gap → ℚ≥0
  | .quarter => 1 / 4
  | .half => 1 / 2

theorem Gap.positive (gap : Gap) : 0 < gap.threshold := by
  cases gap <;> decide +kernel

inductive Side where
  | source | output
  deriving DecidableEq

structure Request where
  code : Code
  ordering : PositionOrder
  gap : Gap
  deriving DecidableEq

def Request.words (request : Request) : Side → Set Word
  | .source => request.code.words
  | .output => permutedCode request.ordering.permutation request.code.words

def Request.claim (request : Request) (side : Side) : ClaimRelation Word Unit :=
  relation (request.words side) request.gap.threshold request.gap.positive

/-- Descriptive static constructors retain code and permutation direction even
when two particular membership predicates happen to coincide. -/
def Request.arguments (request : Request) (side : Side) : List OriginTerm :=
  [.boolean, .natural "4",
   .nominal .record (match request.code with
     | .fixedReference => "FixedReference" | .repetition => "Repetition") [],
   .nominal .record (match request.ordering with
     | .reversal => "Reversal" | .swap => "SwapFirstTwo") [],
   .natural "1", .natural (match request.gap with | .quarter => "4" | .half => "2"),
   .nominal .record (match side with | .source => "SourceCode" | .output => "OutputCode") []]

def identity : OpaqueFamilyIdentity := ⟨"positional.proximity/0", "boolean_word", "0"⟩

def declaration (request : Request) (side : Side) (name : String) : Relation :=
  ⟨name, .publicDef, identity.kind, identity.key, identity.revision,
    wordTypes, [.boolean], List.replicate 4 "statement", none, request.arguments side⟩

def instanceMeaning (model : DomainModel) (request : Request) (side : Side) :
    OpaqueInstance model.Value :=
  ⟨wordTypes, [.boolean], List.replicate 4 "statement",
    fun values => decode model values ∈ request.words side⟩

/-- One reusable installed family, restricted to this request before evidence.
Changing a gap, code, ordering, dimension or argument type requires a new
request; a proof record cannot silently change adapter selection. -/
def family (model : DomainModel) (request : Request) : OpaqueFamily model.Value where
  identity := identity
  instantiate arguments :=
    if arguments = request.arguments .source then some (instanceMeaning model request .source)
    else if arguments = request.arguments .output then some (instanceMeaning model request .output)
    else none

def registry (model : DomainModel) (request : Request) : OpaqueRegistry model.Value :=
  ⟨[family model request], by simp⟩

def selectedBinding (model : DomainModel) (request : Request) (side : Side) (name : String) :
    OpaqueRegistry.Binding (registry model request) (declaration request side name) where
  instantiation := instanceMeaning model request side
  selected := by
    cases side <;> simp [registry, OpaqueRegistry.lookup, family, declaration,
      Relation.opaqueIdentity, identity, Request.arguments]
  inputs := rfl
  outputs := rfl
  purposes := rfl
  opaqueKind := by
    change (!(identity.kind.toList.take 4 == ['z', 'k', 'c', '.'])) = true
    decide +kernel
  noFormula := rfl

/-- Any evidence for the fixed lookup has exactly the installed code meaning.
There is no supplied predicate, empty encoding domain, or partial readback. -/
theorem binding_exact (model : DomainModel) (request : Request) (side : Side) (name : String)
    (binding : OpaqueRegistry.Binding (registry model request) (declaration request side name))
    (word : Word) :
    binding.Holds (encode model word) ↔ (request.claim side).Holds word () := by
  exact (binding.unique_meaning (selectedBinding model request side name) (encode model word)).trans (by
    change decode model (encode model word) ∈ request.words side ↔ word ∈ request.words side
    rw [decode_encode])

theorem yes_transport (request : Request) (word : Word) :
    (request.claim .source).token.Yes word ↔
      (request.claim .output).token.Yes (reindex request.ordering.permutation word) := by
  simp only [Request.claim, relation_yes, Request.words, mem_permutedCode_iff]

theorem no_transport (request : Request) :
    (request.claim .source).SoundLink (request.claim .output)
      (reindex request.ordering.permutation) :=
  permutation_sound request.ordering.permutation request.code.words request.gap.threshold request.gap.positive

/-- The body is exactly the existing one-read Process, at the unchanged handle.
The encoded source word is logical data only and is not an executable input. -/
def body {J : PIR.Signature} {Shape : Type} (request : Request) (handle : Nat) (index : Fin 4) :
    PIR.Process (committed J Shape Bool) Bool :=
  Permutation.read request.ordering.permutation handle index

theorem body_readback {J : PIR.Signature} {Shape : Type} (words : Words J Shape Bool)
    (request : Request) (word : Word) (tables : List (Table Bool)) (handle : Nat)
    (found : tables[handle]? = some (Permutation.positionalTable word)) (index : Fin 4) :
    withTables words tables (body request handle index) =
      .done (reindex request.ordering.permutation word index) :=
  Permutation.withTables_read words request.ordering.permutation word tables handle found index

theorem body_cost {J : PIR.Signature} {Shape : Type} (request : Request) (handle : Nat)
    (index : Fin 4) :
    PIR.Within 1 (body (J := J) (Shape := Shape) request handle index) ∧
      ¬ PIR.Within 0 (body (J := J) (Shape := Shape) request handle index) :=
  ⟨Permutation.read_within_one _ _ _, Permutation.read_not_within_zero _ _ _⟩

end ZkcSecurity.Realizations.Oracle.SourceBoundPermutation

import ZkcSecurity.Bindings.Oracle.SourceBoundPermutation
import Zkc.Source.Structured.ComponentChecking
import Zkc.Source.Structured.UnitViews
import Mathlib.Algebra.Ring.Int.Defs

/-! Exact imported relation association plus the existing actual positional
access law. The admitted source helper only reorders four Boolean coordinates;
it is deliberately not represented as a compiled source oracle read. -/

set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace TestsSecurity.SourceBoundOraclePermutation
open Zkc.Source Zkc.Source.Structured Zkc.Obligations
open ZkcSecurity.Families.Proximity ZkcSecurity.Commitment
open ZkcSecurity.Realizations.Oracle
open SourceBoundPermutation

def reversal : Request := ⟨.fixedReference, .reversal, .half⟩
def swap : Request := ⟨.repetition, .swap, .quarter⟩
def narrower : Request := { reversal with gap := .quarter }
def model := ringModel Int Int

def application : Side → RelationApplication
  | .source => ⟨"SourceWord", List.ofFn (fun index : Fin 4 => ⟨.input, index.val, "V", false⟩)⟩
  | .output => ⟨"OutputWord", List.ofFn (fun index : Fin 4 => ⟨.output, index.val, "V", false⟩)⟩

private def indices : PositionOrder → List Nat
  | .reversal => [3, 2, 1, 0]
  | .swap => [1, 0, 2, 3]

def snapshot (request : Request) : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [],
    [declaration request .source "SourceWord", declaration request .output "OutputWord"], [],
    [.function ⟨"reindex_word", .math, .privateDef, wordTypes, wordTypes, none, [], none,
      .block [] (.ret (indices request.ordering))⟩,
     .function ⟨"main", .protocol, .publicDef, wordTypes, wordTypes,
      some ⟨["V"], List.replicate 4 ["V"], List.replicate 4 ["V"]⟩, [],
      some (.protocol ⟨"main", []⟩),
      .block [.instruction (.call "reindex_word") [0, 1, 2, 3] wordTypes [] ""] (.ret [0, 1, 2, 3])⟩],
    [⟨"main", [⟨.continuation, "proximity", application .source, some (application .output), none⟩]⟩],
    blsRows, {}⟩

private abbrev helper : Helper := ⟨"reindex_word", .math, wordTypes, wordTypes⟩
private def helperBody : PositionOrder → Region dialect wordTypes wordTypes
  | .reversal => .ret (.cons (.there (.there (.there .here)))
      (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))
  | .swap => .ret (.cons (.there .here)
      (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))))
private def mainSignature : ProtocolSignature :=
  ⟨"main", ["V"], wordTypes, wordTypes, List.replicate 4 [0], List.replicate 4 [0]⟩
noncomputable section SourceViews
private def mainBody : Region protocolDialect wordTypes wordTypes :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke helper) rfl)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))) .nil
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here))) .nil)))))

namespace ReversalUnit
structured_views (snapshot reversal)
  helpers [reindex_word := (helper, helperBody .reversal)] protocols [main := main]
end ReversalUnit
namespace SwapUnit
structured_views (snapshot swap)
  helpers [reindex_word := (helper, helperBody .swap)] protocols [main := main]
end SwapUnit
end SourceViews

def sourceRelation (request : Request) : RelationBinding (snapshot request) (application .source) :=
  ⟨⟨0, by change 0 < 2; decide⟩, rfl⟩
def outputRelation (request : Request) : RelationBinding (snapshot request) (application .output) :=
  ⟨⟨1, by change 1 < 2; decide⟩, rfl⟩
def sourceMeaning (request : Request) (imported : Imported (snapshot request)) :
    RelationMeaning imported (sourceRelation request) model.Value (registry model request) :=
  .opaque (selectedBinding model request .source "SourceWord")
def outputMeaning (request : Request) (imported : Imported (snapshot request)) :
    RelationMeaning imported (outputRelation request) model.Value (registry model request) :=
  .opaque (selectedBinding model request .output "OutputWord")

/-- The environment checks both retained rows, not just the row used by a proof. -/
def reversalEnvironment : RelationEnvironmentOn ReversalUnit.imported model.toCarriers :=
  .ofChecked (registry model reversal) (by decide +kernel)
def swapEnvironment : RelationEnvironmentOn SwapUnit.imported model.toCarriers :=
  .ofChecked (registry model swap) (by decide +kernel)

def reversalOwner : ContractBinding ReversalUnit.imported :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩
def swapOwner : ContractBinding SwapUnit.imported :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, rfl⟩

theorem exact_contract_applications :
    (reversalOwner.clause ⟨0, by decide⟩).subject = application .source ∧
    (reversalOwner.clause ⟨0, by decide⟩).residual = some (application .output) ∧
    (swapOwner.clause ⟨0, by decide⟩).subject = application .source ∧
    (swapOwner.clause ⟨0, by decide⟩).residual = some (application .output) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- These are applications of the actual shared component association gate.
True is the total encoding domain, not the installed membership predicate. -/
theorem source_association (request : Request) (imported : Imported (snapshot request)) :
    (sourceMeaning request imported).RealizesClaim (request.claim .source) rfl
      (fun word _ => encode model word) (fun _ _ => True) := by
  intro word witness
  exact (binding_exact model request .source "SourceWord" _ word).symm.trans
    (by simp only [true_and]; rfl)

theorem output_association (request : Request) (imported : Imported (snapshot request)) :
    (outputMeaning request imported).RealizesClaim (request.claim .output) rfl
      (fun word _ => encode model word) (fun _ _ => True) := by
  intro word witness
  exact (binding_exact model request .output "OutputWord" _ word).symm.trans
    (by simp only [true_and]; rfl)

theorem registered_source (word : Word) :
    reversalEnvironment.meanings (sourceRelation reversal).index (encode model word) ↔
      (reversal.claim .source).Holds word () :=
  (reversalEnvironment.meanings_exact (sourceRelation reversal).index
    (selectedBinding model reversal .source "SourceWord") _).trans
    (binding_exact model reversal .source "SourceWord" _ word)

theorem registered_output (word : Word) :
    swapEnvironment.meanings (outputRelation swap).index (encode model word) ↔
      (swap.claim .output).Holds word () :=
  (swapEnvironment.meanings_exact (outputRelation swap).index
    (selectedBinding model swap .output "OutputWord") _).trans
    (binding_exact model swap .output "OutputWord" _ word)

/-- The association also denotes the independent source logical translation,
at the exact admitted relation position used by the contract. -/
theorem source_logical_meaning (word : Word) :
    Logical.relationMeaningOn model reversalEnvironment (sourceRelation reversal).index
      (encode model word) ↔ (reversal.claim .source).Holds word () :=
  ((sourceMeaning reversal ReversalUnit.imported).holds_iff_logical
    reversalEnvironment rfl _).symm.trans (binding_exact model reversal .source "SourceWord" _ word)

theorem output_logical_meaning (word : Word) :
    Logical.relationMeaningOn model swapEnvironment (outputRelation swap).index
      (encode model word) ↔ (swap.claim .output).Holds word () :=
  ((outputMeaning swap SwapUnit.imported).holds_iff_logical
    swapEnvironment rfl _).symm.trans (binding_exact model swap .output "OutputWord" _ word)

/-- Arbitrary replacement evidence still has the request's installed meaning. -/
theorem evidence_cannot_change_meaning
    (evidence : RelationMeaning ReversalUnit.imported (sourceRelation reversal)
      model.Value (registry model reversal)) (word : Word) :
    evidence.HoldsOn rfl (encode model word) ↔ (reversal.claim .source).Holds word () :=
  (evidence.unique_meaning (sourceMeaning reversal ReversalUnit.imported) rfl _).trans
    (binding_exact model reversal .source "SourceWord" _ word)

/-- The source helper is admitted at the exact body and full typed ABI. -/
theorem reversal_helper (word : Word) :
    invoke (closedMeaningsOn model ReversalUnit.program.payload.definitions) helper (encode model word) =
      .done (encode model (reindex reversal.ordering.permutation word)) := by
  kernel_rfl

theorem swap_helper (word : Word) :
    invoke (closedMeaningsOn model SwapUnit.program.payload.definitions) helper (encode model word) =
      .done (encode model (reindex swap.ordering.permutation word)) := by
  kernel_rfl

theorem reversal_nonidentity : reversal.ordering.permutation ≠ Equiv.refl _ := by
  intro same
  have impossible := congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation 0) same
  contradiction
theorem swap_nonidentity : swap.ordering.permutation ≠ Equiv.refl _ := by
  intro same
  have impossible := congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation 0) same
  simp [swap, PositionOrder.permutation] at impossible

def zeroWord : Word := fun _ => false

theorem source_positive_and_negative :
    (sourceMeaning reversal ReversalUnit.imported).HoldsOn rfl (encode model reference) ∧
      ¬ (sourceMeaning reversal ReversalUnit.imported).HoldsOn rfl (encode model zeroWord) := by
  rw [evidence_cannot_change_meaning, evidence_cannot_change_meaning]
  constructor
  · exact Set.mem_singleton reference
  · intro equal
    have impossible := congrFun equal 1
    contradiction

theorem swap_positive_and_negative :
    (outputMeaning swap SwapUnit.imported).HoldsOn rfl (encode model zeroWord) ∧
      ¬ (sourceMeaning swap SwapUnit.imported).HoldsOn rfl (encode model reference) := by
  constructor
  · apply (binding_exact model swap .output "OutputWord" _ zeroWord).mpr
    exact ⟨zeroWord, ⟨false, rfl⟩, rfl⟩
  · intro holds
    obtain ⟨value, same⟩ := (binding_exact model swap .source "SourceWord" _ reference).mp holds
    have first := congrFun same 0
    have second := congrFun same 1
    change false = value at first
    change true = value at second
    exact Bool.false_ne_true (first.trans second.symm)

/-- An installed source predicate cannot be associated with another code by
choosing different proof evidence. This is the shared checker obligation. -/
theorem source_math_mismatch_refused :
    ¬ (sourceMeaning reversal ReversalUnit.imported).RealizesClaim
      (swap.claim .source) rfl (fun word _ => encode model word) (fun _ _ => True) := by
  intro law
  exact source_positive_and_negative.2 ((law zeroWord ()).mp ⟨false, rfl⟩).2

theorem unpermuted_reference_not_output : reference ∉ reversal.words .output := by
  rintro ⟨word, member, same⟩
  have equal : word = reference := member
  subst word
  have impossible := congrFun same 1
  contradiction

/-- Keeping the source code on the output side fails the installed output
meaning even though the permutation and all four Boolean ABI ports match. -/
theorem output_code_direction_refused :
    ¬ (outputMeaning reversal ReversalUnit.imported).RealizesClaim
      (reversal.claim .source) rfl (fun word _ => encode model word) (fun _ _ => True) := by
  intro law
  have holds := ((law reference ()).mp (Set.mem_singleton reference)).2
  exact unpermuted_reference_not_output
    ((binding_exact model reversal .output "OutputWord" _ reference).mp holds)

theorem empty_encoding_domain_refused :
    ¬ (sourceMeaning reversal ReversalUnit.imported).RealizesClaim
      (reversal.claim .source) rfl (fun word _ => encode model word) (fun _ _ => False) := by
  intro law
  exact ((law reference ()).mp (Set.mem_singleton reference)).1

theorem missing_readback_refused :
    ¬ ReadbackHolds (reversal.claim .source).token.Yes none := ReadbackHolds.none _

theorem same_yes_different_no :
    (∀ word, (narrower.claim .source).token.Yes word ↔ (reversal.claim .source).token.Yes word) ∧
      (narrower.claim .source).No zeroWord ∧ ¬ (reversal.claim .source).No zeroWord := by
  refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
  · intro codeword member
    have same : codeword = reference := member
    subst codeword
    decide +kernel
  · intro far
    have impossible := far reference (Set.mem_singleton reference)
    have distance : relativeDistance zeroWord reference = 1 / 4 := by decide +kernel
    rw [distance] at impossible
    exact (by decide +kernel : ¬ (1 / 2 : ℚ≥0) ≤ 1 / 4) impossible

theorem old_no_adapter_refused :
    ¬ (narrower.claim .source).SoundLink (reversal.claim .output)
      (reindex reversal.ordering.permutation) := by
  intro law
  have far := law zeroWord same_yes_different_no.2.1
  exact same_yes_different_no.2.2
    ((far_reindex_iff reversal.ordering.permutation reversal.code.words reversal.gap.threshold zeroWord).mp far)

/-- Exact static admission refuses a new threshold even with unchanged Yes. -/
theorem old_registry_refuses_new_gap :
    (registry model reversal).resolve (declaration narrower .source "SourceWord") = none ∧
      (registry model reversal).check (snapshot narrower).relations = false := by decide +kernel

theorem old_binding_cannot_be_reused :
    ¬ Nonempty (OpaqueRegistry.Binding (registry model reversal)
      (declaration narrower .source "SourceWord")) := by
  rintro ⟨binding⟩
  have selected := binding.selected
  have missing : (registry model reversal).lookup
      (declaration narrower .source "SourceWord").opaqueIdentity = none := by decide +kernel
  rw [missing] at selected
  contradiction

def base : PIR.Signature where
  Op := Unit
  Reply _ := Table Bool
def words : Words base Unit Bool where
  word _ := ()
  toTable _ table := table
  ofTable _ table := table

/-- Both admitted relation clients use this same actual access law, on every
word including Yes, No and gap inputs, with the real partial-table premise. -/
theorem actual_read (request : Request) (word : Word) (tables : List (Table Bool))
    (handle : Nat) (found : tables[handle]? = some (Permutation.positionalTable word)) (index : Fin 4) :
    withTables words tables (body request handle index) =
      .done (reindex request.ordering.permutation word index) ∧
    PIR.Within 1 (body (J := base) (Shape := Unit) request handle index) :=
  ⟨body_readback words request word tables handle found index, (body_cost request handle index).1⟩

theorem actual_frame {State Event : Type} (handler : PIR.Handler base State Event)
    (request : Request) (word : Word) (tables : List (Table Bool)) (handle : Nat)
    (found : tables[handle]? = some (Permutation.positionalTable word)) (index : Fin 4) (state : State) :
    (withTables words tables (body request handle index)).run handler state =
      ⟨.returned (reindex request.ordering.permutation word index), state, []⟩ :=
  Permutation.ideal_frame handler words request.ordering.permutation word tables handle found index state

theorem actual_missing_handle (request : Request) (index : Fin 4) :
    withTables words [] (body request 0 index) = .halt .reject :=
  Permutation.withTables_read_missing words request.ordering.permutation [] 0 index rfl

/-- Each concrete client joins its actual imported membership association,
gap-sensitive No adapter and one-read law in the same checked theorem. -/
theorem checked_reversal (word : Word) (index : Fin 4) :
    ((sourceMeaning reversal ReversalUnit.imported).HoldsOn rfl (encode model word) ↔
      (reversal.claim .source).Holds word ()) ∧
    ((outputMeaning reversal ReversalUnit.imported).HoldsOn rfl
      (encode model (reindex reversal.ordering.permutation word)) ↔
      (reversal.claim .source).Holds word ()) ∧
    (reversal.claim .source).SoundLink (reversal.claim .output)
      (reindex reversal.ordering.permutation) ∧
    withTables words [Permutation.positionalTable word] (body reversal 0 index) =
      .done (reindex reversal.ordering.permutation word index) ∧
    PIR.Within 1 (body (J := base) (Shape := Unit) reversal 0 index) := by
  refine ⟨binding_exact model reversal .source "SourceWord" _ word, ?_,
    no_transport reversal, actual_read reversal word _ 0 rfl index⟩
  exact (binding_exact model reversal .output "OutputWord" _ _).trans
    (mem_permutedCode_iff _ _ _)

theorem checked_swap (word : Word) (index : Fin 4) :
    ((sourceMeaning swap SwapUnit.imported).HoldsOn rfl (encode model word) ↔
      (swap.claim .source).Holds word ()) ∧
    ((outputMeaning swap SwapUnit.imported).HoldsOn rfl
      (encode model (reindex swap.ordering.permutation word)) ↔
      (swap.claim .source).Holds word ()) ∧
    (swap.claim .source).SoundLink (swap.claim .output) (reindex swap.ordering.permutation) ∧
    withTables words [Permutation.positionalTable word] (body swap 0 index) =
      .done (reindex swap.ordering.permutation word index) ∧
    PIR.Within 1 (body (J := base) (Shape := Unit) swap 0 index) := by
  refine ⟨binding_exact model swap .source "SourceWord" _ word, ?_,
    no_transport swap, actual_read swap word _ 0 rfl index⟩
  exact (binding_exact model swap .output "OutputWord" _ _).trans
    (mem_permutedCode_iff _ _ _)

section Authentication
open OracleComp OracleSpec ZkcSecurity.FiatShamir
variable {E P Shape Query Y A : Type} {Raw : E → Type}
  (absorb : Typed.Interface base E P Raw) (scheme : Extractable Shape Bool Query Y)

/-- The request-selected read passes the actual history, roots and messages
unchanged to an arbitrary suffix, consuming exactly one opening on success. -/
theorem actual_authentication (request : Request) (handle : Nat) (index : Fin 4)
    (next : Bool → PIR.Process (committed base Shape Bool) A)
    (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
    (messages : List (Message P Y)) (opening : Opening Bool Y) (rest : List (Opening Bool Y))
    (shape : Shape) (root : Y) (found : roots[handle]? = some (shape, root)) :
    ZkcSecurity.Commitment.run absorb scheme ((body request handle index).bind next) history roots messages
      (opening :: rest) = (do
        let accepted ← liftHash Raw Shape
          (scheme.authenticate shape root (request.ordering.permutation index).val opening)
        if accepted then ZkcSecurity.Commitment.run absorb scheme (next opening.value) history roots messages rest
        else pure (.stopped .reject)) :=
  Permutation.authenticated_read_bind absorb scheme request.ordering.permutation handle index next
    history roots messages opening rest shape root found

/-- A positional read is not a cryptographic one-query assumption. The
authenticator's independent budget and hash-only restriction are retained. -/
theorem actual_queries (request : Request) (handle : Nat) (index : Fin 4)
    (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
    (messages : List (Message P Y)) (opening : Opening Bool Y) (rest : List (Opening Bool Y))
    (shape : Shape) (root : Y) (found : roots[handle]? = some (shape, root)) (budget : Nat)
    (bounded : IsTotalQueryBound
      (scheme.authenticate shape root (request.ordering.permutation index).val opening) budget) :
    IsTotalQueryBound (ZkcSecurity.Commitment.run absorb scheme (body request handle index)
      history roots messages (opening :: rest)) budget ∧
    AllQueriesSatisfy (ZkcSecurity.Commitment.run absorb scheme (body request handle index)
      history roots messages (opening :: rest)) (fun key => ∃ query, key = .inr query) :=
  ⟨Permutation.authenticated_query_bound absorb scheme request.ordering.permutation handle index
      history roots messages opening rest shape root found budget bounded,
    Permutation.authenticated_no_transcript_queries absorb scheme request.ordering.permutation handle index
      history roots messages opening rest shape root found⟩

variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ event, SampleableType (Raw event)] [SampleableType Y]

/-- Actual supported joint-cache executions retain all previous answers and
every transcript cell, including missing cells and rejected authentication. -/
theorem actual_capture (request : Request) (handle : Nat) (index : Fin 4)
    (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
    (messages : List (Message P Y)) (opening : Opening Bool Y) (rest : List (Opening Bool Y))
    (shape : Shape) (root : Y) (found : roots[handle]? = some (shape, root))
    (cache : (joint Raw Shape Y Query).QueryCache)
    (result : PIR.Outcome Bool × (joint Raw Shape Y Query).QueryCache)
    (supported : result ∈ support ((simulateQ (joint Raw Shape Y Query).randomOracle
      (ZkcSecurity.Commitment.run absorb scheme (body request handle index) history roots messages
        (opening :: rest))).run cache)) :
    cache ≤ result.2 ∧ ∀ key, result.2 (.inl key) = cache (.inl key) :=
  ⟨Permutation.authenticated_cache_extends absorb scheme request.ordering.permutation handle index
      history roots messages (opening :: rest) cache result supported,
    Permutation.authenticated_transcript_frame absorb scheme request.ordering.permutation handle index
      history roots messages opening rest shape root found cache result supported⟩
end Authentication

private def withArguments (relation : Relation) (arguments : List OriginTerm) : Relation :=
  { relation with staticArguments := arguments }

private def controls : List (String × Bool) := [
  ("reversal-source-admission", (check (snapshot reversal)).isOk),
  ("swap-source-admission", (check (snapshot swap)).isOk),
  ("reversal-registered-relations", (registry model reversal).check (snapshot reversal).relations),
  ("swap-registered-relations", (registry model swap).check (snapshot swap).relations),
  ("wrong-gap", !(registry model reversal).check (snapshot narrower).relations),
  ("wrong-code", !((registry model reversal).resolve
    (declaration { reversal with code := .repetition } .source "SourceWord")).isSome),
  ("wrong-ordering", !((registry model reversal).resolve
    (declaration { reversal with ordering := .swap } .source "SourceWord")).isSome),
  ("wrong-direction", !((registry model reversal).resolve
    (withArguments (declaration reversal .output "OutputWord")
      ((reversal.arguments .output).take 6 ++ [.nominal .record "UnpermutedOutput" []]))).isSome),
  ("wrong-dimension", !((registry model reversal).resolve
    (withArguments (declaration reversal .source "SourceWord")
      ([.boolean, .natural "0"] ++ (reversal.arguments .source).drop 2))).isSome),
  ("wrong-gap-argument-type", !((registry model reversal).resolve
    (withArguments (declaration reversal .source "SourceWord")
      ((reversal.arguments .source).take 4 ++ [.index] ++ (reversal.arguments .source).drop 5))).isSome),
  ("wrong-abi", !((registry model reversal).resolve
    { (declaration reversal .source "SourceWord") with inputs := [.boolean] }).isSome),
  ("wrong-purpose", !((registry model reversal).resolve
    { (declaration reversal .source "SourceWord") with purposes := List.replicate 4 "parameter" }).isSome),
  ("missing-registry", !(OpaqueRegistry.empty (Value := model.Value)).check (snapshot reversal).relations)]

def run : IO Unit := do
  for (name, passed) in controls do
    unless passed do throw (IO.userError s!"source-bound permutation control failed: {name}")
  IO.println s!"source-bound permutation: {controls.length} admission controls passed; two exact imported relation clients"

#eval run
#print axioms source_association
#print axioms output_association
#print axioms registered_source
#print axioms registered_output
#print axioms exact_contract_applications
#print axioms source_logical_meaning
#print axioms output_logical_meaning
#print axioms evidence_cannot_change_meaning
#print axioms reversal_helper
#print axioms swap_helper
#print axioms source_math_mismatch_refused
#print axioms output_code_direction_refused
#print axioms empty_encoding_domain_refused
#print axioms missing_readback_refused
#print axioms old_no_adapter_refused
#print axioms old_binding_cannot_be_reused
#print axioms actual_read
#print axioms actual_frame
#print axioms checked_reversal
#print axioms checked_swap
#print axioms actual_authentication
#print axioms actual_queries
#print axioms actual_capture

end TestsSecurity.SourceBoundOraclePermutation

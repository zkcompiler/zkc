module

public import ZkcSecurity.Bindings.Source.PublicProperties
public import ZkcSecurity.Bindings.Source.LoopContracts
public import ZkcSecurity.Families.Sumcheck.Round
public import Zkc.Obligations.ClaimRelation
public meta import ZkcSecurityTools.SourceProperties.Builder

@[expose] public section

/-! A shared draw feeds two pure residual components. Their No predicates have
an actual Yes/No gap; being outside the charged union does not establish Yes.
All outputs and an arbitrary caller capture survive application assembly.
The event bounds refer to the actual routed distribution, without independence.
-/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SourcePropertyAssembly
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Source ZkcSecurity.FiatShamir OracleComp OracleSpec

def relation : ClaimRelation Nat Unit where
  Holds code _ := code = 0
  No code := code = 1
  no_excludes _ _ no yes := by omega

theorem gap : ¬ relation.token.Yes 2 ∧ ¬ relation.No 2 := by
  simp [relation, ClaimRelation.token]

variable {carriers : Carriers}
  [samples : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]

def classify (code : Nat) : PIR.Process (Occurrence.signature carriers) Nat :=
  .call (.enter ⟨"residual", code⟩) fun _ =>
    .call (.leave ⟨"residual", code⟩) fun _ => .done code

def classification (price : ENNReal) (code : Nat) (safe : ¬ relation.No code)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = code ∧ ¬ relation.No out) history (classify code) :=
  .send rfl (.send rfl (.done ⟨rfl, safe⟩))

def source (field site : String) (handle captured : Nat)
    (left right : carriers.Field field → Nat) :
    PIR.Process (Occurrence.signature carriers) (Nat × Nat × Nat) :=
  .call (.action (.query site field (.cons handle .nil))) fun reply =>
    (classify (left reply)).bind fun a =>
    (classify (right reply)).bind fun b => .done (a, b, captured)

def shared (field site : String) (handle captured : Nat)
    (left right : carriers.Field field → Nat) (leftError rightError : ENNReal)
    (leftBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
        relation.No (left (Original.fieldReply origin field request raw))] ≤ leftError)
    (rightBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
        relation.No (right (Original.fieldReply origin field request raw))] ≤ rightError)
    (history : List (PublicProperties.Event carriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape (leftError + rightError))
      (fun _ out => out.2.2 = captured ∧ ¬ relation.No out.1 ∧ ¬ relation.No out.2.1)
      history (source field site handle captured left right) := by
  -- Both predicates and both distribution bounds are fixed before the reply.
  refine .query rfl (fun reply => relation.No (left reply) ∨ relation.No (right reply)) ?_ ?_
  · intro origin request
    exact ZkcSecurity.Families.Sumcheck.shared_challenge_union_le
      ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))) _ _
      leftError rightError (leftBound origin request) (rightBound origin request)
  · intro raw reply decoded outside
    cases decoded
    have leftSafe : ¬ relation.No (left raw) := fun bad => outside (.inl bad)
    have rightSafe : ¬ relation.No (right raw) := fun bad => outside (.inr bad)
    assemble_source_no
      [classification (carriers := carriers) (leftError + rightError) (left raw) leftSafe,
       classification (carriers := carriers) (leftError + rightError) (right raw) rightSafe]
      simplifying []

def installed (field site : String) (handle captured : Nat)
    (left right : carriers.Field field → Nat) (leftError rightError : ENNReal)
    (leftBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
        relation.No (left (Original.fieldReply origin field request raw))] ≤ leftError)
    (rightBound : ∀ (origin : Origin) (request : origin.request = some (.draw field)),
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[
        relation.No (right (Original.fieldReply origin field request raw))] ≤ rightError)
    (routing : Original.Routing) (mode : routing.mode = .validator)
    (history : List (PublicProperties.Event carriers)) (state : Original.State carriers) :
    Derivation NominalDomain.interface
      (ZkcSecurity.Obligations.boundedEscape (fun _ _ => leftError + rightError))
      (fun _ result => result.1.2.2 = captured ∧
        ¬ relation.No result.1.1 ∧ ¬ relation.No result.1.2.1) state.history
      (DomainSourceReading.presentation routing (source field site handle captured left right) state) :=
  PublicProperties.install routing mode (leftError + rightError) _ _ history
    (shared field site handle captured left right leftError rightError leftBound rightBound history) state

omit samples in
theorem no_stopped_pair {A B : Type} (scope : PairScope) (Post : A → B → Prop)
    (reason : PIR.Stop) (right : PIR.Process (Occurrence.signature carriers) B) :
    ¬ Pair scope Post (.halt reason) right := by
  intro alleged
  cases alleged

#print axioms ZkcSecurity.Source.LoopContracts.repeat_pair
#print axioms shared
#print axioms installed
end TestsSecurity.SourcePropertyAssembly

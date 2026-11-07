module

public import ZkcArkLibExamples.Fri.ClearCertificate
public import ZkcArkLibExamples.Fri.ClearFoldRoute

@[expose] public section

/-! Recover field and scalar replies, and their charged keys, from primitive
log entries. Both claims use a single table for the whole adaptive program,
including the attacker's queries. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ClearAccess
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir QueryTree QueryTreeSource
open ZkcSecurity.Examples
open OracleComp OracleSpec
open TranscriptCharge (History Table)
open ObservedQueries (Key Answer)
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcExamples.Structured.FriSource (extension)

abbrev Program (A : Type) := OracleComp (ofFn ObservedFold.Answer) A
abbrev segment := ZkcSecurity.Examples.FriScalarQueries.segment

variable {A : Type} (program : Program A) (table : Table)

theorem field (prior : History) (ordinal : Nat)
    (answer : ObservedFold.Answer (prior ++ [.challenge (ClearSites.sites.round ordinal).draw]))
    (logged : ⟨_, answer⟩ ∈ tableQueryLog program (Composition.primitiveAnswers segment table)) :
    let site := ClearSites.sites.round ordinal
    let key := TranscriptCharge.fieldKey site (ClearSites.fields ordinal) prior
    ClearCertificate.Logged (Composition.fullTranslate segment program) table key ∧
      ObservedFold.fieldAnswer prior site.draw (ClearSites.fields ordinal) answer =
        ObservedFold.fieldAnswer prior site.draw (ClearSites.fields ordinal) (table key) := by
  intro site key
  let other : Composition.OtherKey model.toCarriers 32 :=
    ⟨prior ++ [.challenge site.draw], by rw [Composition.scalarCell_iff, ClearSites.fields]; decide⟩
  have routed := Composition.loggedKey segment program table ⟨other.val, answer⟩ logged
  rw [show Composition.macroKey (height := 8) segment other.val = .inr other from
    Composition.macroKey_other segment other] at routed
  refine ⟨routed, ?_⟩
  have same := ZkcSecurity.Commitment.tableQueryLog_consistent (Composition.primitiveAnswers segment table)
    program ⟨other.val, answer⟩ logged
  have reply : answer = Composition.primitiveAnswers segment table other.val := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using same
  exact congrArg _ (reply.trans (Composition.primitiveAnswers_other segment table other))

theorem request : segment.query.request = some (.sampleIndex 32) := by decide +kernel

theorem scalar (root : History) (node : Node (Fin 32) 8)
    (answer : ObservedFold.Answer (oracleKey (encode segment (root, node))))
    (logged : ⟨_, answer⟩ ∈ tableQueryLog program (Composition.primitiveAnswers segment table)) :
    let key : ScalarKey model.toCarriers 32 := ⟨encode segment (root, node), (segment.queryAt_request _).trans request⟩
    ClearCertificate.Logged (Composition.fullTranslate segment program) table (.inl (.inl root)) ∧
      typedRenaming.read key (oracleKey key.val) rfl answer = table (.inl (.inl root)) (.inl node) := by
  intro key
  have routed := Composition.loggedKey segment program table ⟨oracleKey key.val, answer⟩ logged
  rw [show Composition.macroKey (bound := 32) (height := 8) segment (oracleKey key.val) = .inl (.inl root)
    from Composition.macroKey_node segment request root node] at routed
  have same := ZkcSecurity.Commitment.tableQueryLog_consistent (Composition.primitiveAnswers segment table)
    program ⟨oracleKey key.val, answer⟩ logged
  have reply : answer = Composition.primitiveAnswers segment table (oracleKey key.val) := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using same
  have value := Composition.primitiveAnswers_scalar segment table key
  rw [show locate (height := 8) segment key = (.inl root, .inl node) from locate_encode segment request (root, node)] at value
  exact ⟨routed, reply ▸ value⟩

end ZkcSecurity.ArkLib.Fri.ClearAccess

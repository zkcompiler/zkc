module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Batch

@[expose] public section

/-! Exhaustive dependent transcript transport. The complement contains every non-scalar cell,
including empty histories, field requests of every nominal domain, other bounds, and blocks.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec
noncomputable section
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]

/-- Membership in the entire fixed-bound scalar slice, independent of source-key parsing. -/
def ScalarCell (history : Domain.History carriers) : Prop :=
  ∃ key : ScalarKey carriers bound, oracleKey key.val = history

abbrev OtherKey (carriers : Structured.Carriers) (bound : Nat) :=
  {history : Domain.History carriers // ¬ ScalarCell (bound := bound) history}

abbrev otherRange (key : OtherKey carriers bound) := Typed.ByLast Domain.Raw key.val

abbrev primitive (carriers : Structured.Carriers) (bound height : Nat) :=
  @primitiveRange (Root carriers bound) (Coordinate bound height) (Fin bound)
    (OtherKey carriers bound) otherRange

abbrev fullRange (carriers : Structured.Carriers) (bound height : Nat) :=
  @macroRange (Root carriers bound) (Coordinate bound height) (Fin bound)
    (OtherKey carriers bound) otherRange

/-- A full typed history is routed to a parsed scalar node, its disjoint unparsed scalar root,
or its exact untouched dependent cell. No request is silently answered or excluded. -/
def fullRenaming (segment : Segment) : ZkcSecurity.Oracle.Renaming
    (Typed.ByLast (@Domain.Raw carriers)) (primitive carriers bound height) where
  cell history := if member : ScalarCell (bound := bound) history then
      some (.inl (locate segment member.choose))
    else some (.inr ⟨history, member⟩)
  injective first second target a b := by
    split at a <;> split at b
    · rename_i firstMember secondMember
      have same := Sum.inl.inj (Option.some.inj (a.trans b.symm))
      have keySame := locate_injective segment same
      exact firstMember.choose_spec.symm.trans
        ((congrArg (fun key : ScalarKey carriers bound ↦ oracleKey key.val) keySame).trans
          secondMember.choose_spec)
    · have impossible := Option.some.inj (a.trans b.symm)
      cases impossible
    · have impossible := Option.some.inj (a.trans b.symm)
      cases impossible
    · exact congrArg Subtype.val (Sum.inr.inj (Option.some.inj (a.trans b.symm)))
  read history target hit := by
    split at hit
    · rename_i member
      obtain rfl := Option.some.inj hit
      exact (typedRenaming.read member.choose history
        (congrArg some member.choose_spec)).symm
    · obtain rfl := Option.some.inj hit
      exact Equiv.refl _
  single history impossible := by
    split at impossible <;> cases impossible

/-- The complete heterogeneous macro computation for an unrestricted dependent adversary. -/
def fullTranslate (segment : Segment) {α : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α) :
    OracleComp (ofFn (fullRange carriers bound height)) α :=
  translate ((fullRenaming (bound := bound) (height := height) segment).translate program)

theorem fullTranslate_bind (segment : Segment) {α β : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (next : α → OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) β) :
    fullTranslate (height := height) (bound := bound) segment (program >>= next) =
      (fullTranslate segment program >>= fun value ↦ fullTranslate segment (next value)) := by
  simp only [fullTranslate, translate, ZkcSecurity.Oracle.Renaming.translate, simulateQ_bind]

omit [NeZero bound] in
/-- Scalar membership uses the complete terminated history, so it cannot absorb a field,
block, message or another nominal request by a host-carrier coincidence. -/
theorem scalarCell_iff (history : Domain.History carriers) (origin : Origin) :
    ScalarCell (bound := bound) (history ++ [.challenge origin]) ↔
      origin.request = some (.sampleIndex bound) := by
  constructor
  · rintro ⟨key, same⟩
    change oracleKey key.val = oracleKey (history, origin) at same
    have equal := congrArg Prod.snd (oracleKey_injective same)
    exact (congrArg Origin.request equal).symm.trans key.property
  · intro request
    exact ⟨⟨(history, origin), request⟩, rfl⟩

theorem fullRenaming_other (segment : Segment) (key : OtherKey carriers bound) :
    (fullRenaming (height := height) segment).cell key.val = some (.inr key) := by
  simp only [fullRenaming, key.property, ↓reduceDIte]

theorem fullRenaming_scalar (segment : Segment) (key : ScalarKey carriers bound) :
    (fullRenaming (height := height) segment).cell (oracleKey key.val) =
      some (.inl (locate segment key)) := by
  have member : ScalarCell (oracleKey key.val) := ⟨key, rfl⟩
  simp only [fullRenaming, member, ↓reduceDIte]
  have same : member.choose = key := Subtype.ext (oracleKey_injective member.choose_spec)
  rw [same]

local instance rawSampler [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (history : Domain.History carriers) : SampleableType (Typed.ByLast Domain.Raw history) :=
  inferInstanceAs (SampleableType (Typed.ByLast Domain.Raw history))
local instance otherSampler [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (key : OtherKey carriers bound) : SampleableType (otherRange key) := rawSampler key.val
attribute [local instance] primitiveSampler macroSampler

/-- Complete adaptive dependent-oracle equality. In particular the adversary may freely
interleave arbitrary field/index-block requests, offpath nodes and suffix-first scalar keys. -/
theorem full_exact [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α) :
    (simulateQ randomOracle program).run' ∅ =ᵈ
      (simulateQ randomOracle (fullTranslate (height := height) (bound := bound)
        segment program)).run' ∅ :=
  ((fullRenaming (height := height) (bound := bound) segment).evalDistEq_translate
    program).symm.trans
    (adaptive_exact ((fullRenaming (height := height) (bound := bound) segment).translate program))

/-- Logging before transport preserves full primitive requests and dependent replies in order,
including cache hits. Logs are not reduced to root allocations or distinct cells. -/
theorem full_logged [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α) :
    let observed := (simulateQ loggingOracle program).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (fullTranslate (height := height) (bound := bound)
        segment observed)).run' ∅ := full_exact segment _

/-- Every primitive request, including non-scalar requests and repeated cells, is budgeted. -/
theorem full_budget (segment : Segment) {α : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (budget : Nat) (bounded : IsTotalQueryBound program budget) :
    IsTotalQueryBound (fullTranslate (height := height) (bound := bound) segment program) budget :=
  translate_budget _ budget
    ((fullRenaming (height := height) (bound := bound) segment).translate_queryBound
      program budget bounded)

/-- Prover and verifier run on the same lazy macro cache. Every verifier occurrence has its
own logical call, even if the prover already exposed that root. Complete failures may be β. -/
theorem full_withVerifier_exact
    [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α β : Type}
    (prover : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (verifier : α → OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) β) :
    (simulateQ randomOracle (prover >>= verifier)).run' ∅ =ᵈ
      (simulateQ randomOracle
        (fullTranslate (height := height) (bound := bound) segment prover >>=
          fun result ↦ fullTranslate segment (verifier result))).run' ∅ := by
  simpa only [fullTranslate_bind] using
    (full_exact (height := height) (bound := bound) segment (prover >>= verifier))

theorem full_withVerifier_budget (segment : Segment) {α β : Type}
    (prover : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (verifier : α → OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) β)
    (proverBudget verifierBudget : Nat) (proverBound : IsTotalQueryBound prover proverBudget)
    (verifierBound : ∀ result, IsTotalQueryBound (verifier result) verifierBudget) :
    IsTotalQueryBound (fullTranslate (height := height) (bound := bound) segment
      (prover >>= verifier)) (proverBudget + verifierBudget) :=
  full_budget segment _ _ (isTotalQueryBound_bind proverBound verifierBound)

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition

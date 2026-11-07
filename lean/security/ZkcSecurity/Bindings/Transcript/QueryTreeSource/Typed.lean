module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Adapter
public import ZkcSecurity.Transformations.Oracle.Keys

@[expose] public section

/-! Typed logical transcript transport, using the existing dependent random-oracle renaming.
The source cell is the full terminated event history used by Typed.ask. This is not a claim
about native provider bytes or about interleaving requests outside the scalar request slice.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec MeasureTheory
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.decEq α
variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]

def scalarRawEquiv (key : ScalarKey carriers bound) :
    Domain.Raw (.challenge key.val.2 : Domain.Event carriers) ≃ Fin bound := by
  have positive : 0 < bound := Nat.pos_of_ne_zero (NeZero.ne bound)
  simpa only [Domain.Raw, key.property, Request.Raw, Request.sampleIndex, List.headD_cons,
    Request.replyBound_of_positive positive] using Equiv.refl (Fin bound)

/-- An injective dependent-cell transport into the actual typed FS transcript oracle. -/
def typedRenaming : ZkcSecurity.Oracle.Renaming
    (fun _ : ScalarKey carriers bound ↦ Fin bound) (Typed.ByLast (@Domain.Raw carriers)) where
  cell key := some (oracleKey key.val)
  injective first second target a b := by
    apply Subtype.ext
    exact oracleKey_injective (Option.some.inj (a.trans b.symm))
  read key target hit := by
    obtain rfl := Option.some.inj hit
    exact (Typed.ByLast.read Domain.Raw).trans (scalarRawEquiv key)
  single _ found := by cases found

/-- The transported operation is exactly the existing source reading's Typed.ask, followed
by its finite-carrier equivalence. No new source evaluator is used. -/
theorem typed_ask (key : ScalarKey carriers bound) :
    typedRenaming.ask key = scalarRawEquiv key <$> sourceAsk key := by
  rw [ZkcSecurity.Oracle.Renaming.ask_some typedRenaming (key := key) rfl]
  rfl

/-- Actual terminated-history query cells occur in exactly the original primitive order.
Every repeat remains a separate log entry; the scalar carrier transport erases no query. -/
theorem typed_query_log {α : Type}
    (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key)
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    (tableQueryLog (typedRenaming.translate program) table).map Sigma.fst =
      ((tableQueryLog program (typedRenaming.pullback table)).map Sigma.fst).map
        (fun key ↦ oracleKey key.val) := by
  rw [ZkcSecurity.Oracle.Renaming.tableQueryLog_translate]
  exact congrFun List.filterMap_eq_map' _

/-- One actual typed oracle query per primitive query occurrence, independently of caching. -/
theorem typed_query_count {α : Type}
    (table : (key : Domain.History carriers) → Typed.ByLast Domain.Raw key)
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    (tableQueryLog (typedRenaming.translate program) table).length =
      (tableQueryLog program (typedRenaming.pullback table)).length := by
  have counts := congrArg List.length (typed_query_log table program)
  simpa only [List.length_map] using counts

/-- Equality for every adaptive complete source-key experiment at the actual dependent
transcript oracle and at the macro-tree oracle. The generic renaming theorem couples caches;
this result does not infer joint equality from matching decoded marginals. -/
theorem typed_source_exact [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    (simulateQ randomOracle (typedRenaming.translate program)).run' ∅ =ᵈ
      (simulateQ randomOracle (translate (height := height) segment program)).run' ∅ := by
  let : MeasurableSpace α := ⊤
  exact (typedRenaming.evalDistEq_translate program).trans
    (EvalDistEq.of_evalDist_eq (adaptive_source_exact segment program))

/-- Full source-key logs may be returned through the same dependent-cache coupling. -/
theorem typed_source_logged [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    let observed := (simulateQ loggingOracle program).run
    (simulateQ randomOracle (typedRenaming.translate observed)).run' ∅ =ᵈ
      (simulateQ randomOracle (translate (height := height) segment observed)).run' ∅ :=
  typed_source_exact segment _

end
end ZkcSecurity.FiatShamir.QueryTreeSource

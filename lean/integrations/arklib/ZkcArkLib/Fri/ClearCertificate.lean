module

public import ZkcArkLib.Fri.ClearSites

@[expose] public section

/-! The common random-oracle certificate instantiated with the actual clear
deployment's sites. Clients must recover chronological execution facts for
their accepting event. The resampling inequality is proved independently
for every table, including tables an adaptive prover has already queried. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ClearCertificate
open ZkcSecurity.FiatShamir QueryTreeSource
open ZkcSecurity.Domains.KoalaBear (Octic)
open OracleComp OracleSpec
open ObservedQueries (Key Answer)
open TranscriptCharge (History Table)

/-- Membership in this *same* game's deterministic table query log. -/
def Logged {A : Type} (game : OracleComp (ofFn Answer) A) (table : Table) (key : Key) : Prop :=
  ∃ query ∈ tableQueryLog game table, query.1 = key

/-- Execution view sufficient to charge an accepting, far run. The first word
and every later challenge and index belong to this table and this prefix. -/
structure Run {A : Type} (game : OracleComp (ofFn Answer) A) (table : Table)
    {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ) where
  prior : History
  layers : Layers Octic 5 3
  draws : TranscriptCharge.DrawsRead ClearSites.sites ClearSites.fields (Logged game table) table 0 prior layers
  root : Logged game table (.inl (.inl (prior ++ ObservedLayers.observations ClearSites.sites 0 layers)))
  far : Far (RetainedDomain.domain shift nonzero) 8 δ (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial
  accepts : Phases.accepts RetainedDomain.root 0 layers shift (ObservedQueries.positions
    (table (.inl (.inl (prior ++ ObservedLayers.observations ClearSites.sites 0 layers))))) = true

noncomputable def certificate [DecidableEq Key] [∀ k, SampleableType (Answer k)] [SampleableType Octic]
    {A : Type} (game : OracleComp (ofFn Answer) A) (event : A → Prop)
    {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ)
    (observeRun : ∀ table, event (evalWithAnswerFn (QueryImpl.ofFn table) game) →
      Nonempty (Run game table nonzero δ)) : KeyedCertificate Answer game event where
  charge := TranscriptCharge.charge
    (TranscriptCharge.schedule ClearSites.sites ClearSites.fields 0 5 3 0 (RetainedDomain.domain shift nonzero) (by decide)) δ
  bad := TranscriptCharge.bad
    (TranscriptCharge.schedule ClearSites.sites ClearSites.fields 0 5 3 0 (RetainedDomain.domain shift nonzero) (by decide))
    (TranscriptCharge.QueryBad ClearSites.sites nonzero δ)
  resample := TranscriptCharge.resample _ ClearSites.sites nonzero δ
  trace table hit := by
    obtain ⟨run⟩ := observeRun table hit
    obtain ⟨key, ⟨query, logged, same⟩, escaped⟩ := TranscriptCharge.accepting_witness
      ClearSites.sites ClearSites.fields nonzero δ (Logged game table) table run.prior run.layers
      run.draws run.root run.far run.accepts
    exact ⟨query, logged, same ▸ escaped⟩

end ZkcSecurity.ArkLib.Fri.ClearCertificate

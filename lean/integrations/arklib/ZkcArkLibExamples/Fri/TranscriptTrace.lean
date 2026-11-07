module

public import ZkcArkLibExamples.Fri.TranscriptCharge

@[expose] public section

/-! Deterministic reduction on a single table. The verifier's observation
obligations concern words, delivered replies and logged keys. Safety of the
folds and the bad-event witness are derived, including when the adversary
previously queried the same address. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.TranscriptCharge
open Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcExamples.Structured.FriSource (extension)
open ObservedQueries (Key Answer)
open OracleComp OracleSpec

def wordHistory (prior : History) (site : ObservedLayers.Round) {n : Nat}
    (word : Fin n → Octic) : History :=
  prior ++ [.message site.word (.vector extension (List.ofFn word))]

/-- Every delivered beta is the reply at its logged field request, with that
round's actual public word already present. No independence assumption. -/
def DrawsRead (sites : ObservedLayers.Sites)
    (fields : ∀ i, (sites.round i).draw.request = some (.draw extension))
    (seen : Key → Prop) (table : Table) :
    {n r : Nat} → Nat → History → Layers Octic n r → Prop
  | _, _, _, _, .final _ => True
  | _, _, ordinal, prior, .fold word beta rest =>
    let site := sites.round ordinal
    let prefixWord := wordHistory prior site word
    let key := fieldKey site (fields ordinal) prefixWord
    seen key ∧ ObservedFold.fieldAnswer prefixWord site.draw (fields ordinal) (table key) = beta ∧
      DrawsRead sites fields seen table (ordinal + 1)
        (prefixWord ++ [.challenge site.draw, .message site.delivery (.field extension beta)]) rest

theorem safe_or_logged (sites : ObservedLayers.Sites)
    (fields : ∀ i, (sites.round i).draw.request = some (.draw extension))
    (seen : Key → Prop) (table : Table) (t : Nat) {n r : Nat}
    (domain : _root_.Domain.SmoothCosetFftDomain n Octic) (feasible : t + r + 1 ≤ n)
    (ordinal : Nat) (prior : History) (layers : Layers Octic n r)
    (reads : DrawsRead sites fields seen table ordinal prior layers) :
    (toTrace t domain layers).Safe (1/4) ∨
      ∃ key, seen key ∧ ∃ round ∈ schedule sites fields t n r ordinal domain feasible, round.bad key table := by
  induction layers generalizing ordinal prior with
  | final => exact Or.inl trivial
  | @fold m r word beta tail ih =>
    let site := sites.round ordinal
    let prefixWord := wordHistory prior site word
    let key := fieldKey site (fields ordinal) prefixWord
    obtain ⟨logged, answer, rest⟩ := reads
    by_cases lost : _root_.Fri.FoldingAgreementFailure domain word 1 (degreeBound r (2^t)) (1/4 : ℝ) beta
    · right
      refine ⟨key, logged, ⟨m, r, t, domain, feasible, site, fields ordinal⟩, List.mem_cons_self, ?_⟩
      refine ⟨prefixWord, rfl, word, ?_, ?_⟩
      · exact ObservedFold.wordAt_message prior site.word site.draw word rfl
      · rwa [answer]
    · rcases ih (domain.subdomain 1) (by omega) (ordinal+1) _ rest with safe | ⟨k, loggedKey, round, member, hit⟩
      · exact Or.inl ⟨lost, safe⟩
      · exact Or.inr ⟨k, loggedKey, round, List.mem_cons_of_mem _ member, hit⟩

/-- For a far, mathematically accepting transcript, the actual observed
requests include a charged fold or the charged scalar root. Only the
chronological execution facts must come from the client. -/
theorem accepting_witness (sites : ObservedLayers.Sites)
    (fields : ∀ i, (sites.round i).draw.request = some (.draw extension))
    {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ) (seen : Key → Prop) (table : Table)
    (prior : History) (layers : Layers Octic 5 3)
    (draws : DrawsRead sites fields seen table 0 prior layers)
    (logged : seen (.inl (.inl (prior ++ ObservedLayers.observations sites 0 layers))))
    (far : Far (RetainedDomain.domain shift nonzero) 8 δ (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial)
    (accepted : Phases.accepts RetainedDomain.root 0 layers shift
      (ObservedQueries.positions (table (.inl (.inl (prior ++ ObservedLayers.observations sites 0 layers))))) = true) :
    ∃ key, seen key ∧ bad (schedule sites fields 0 5 3 0 (RetainedDomain.domain shift nonzero) (by decide))
      (QueryBad sites nonzero δ) key table := by
  rcases safe_or_logged sites fields seen table 0 (RetainedDomain.domain shift nonzero) (by decide) 0 prior layers draws with safe | failed
  · exact ⟨_, logged, Or.inr ⟨layers, ObservedLayers.atRoot_observations _ _ _, safe, far, accepted⟩⟩
  · obtain ⟨key, loggedKey, hit⟩ := failed
    exact ⟨key, loggedKey, Or.inl hit⟩

end ZkcSecurity.ArkLib.Fri.TranscriptCharge

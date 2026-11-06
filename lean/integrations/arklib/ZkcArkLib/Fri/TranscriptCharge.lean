module

public import ZkcArkLib.Fri.ObservedQueries

@[expose] public section

/-! Folding draws and the scalar-query tree share one dependent random oracle.
The schedule depends on the public domain and source origins. Neither the
attacker's published words nor the replies select a different charge. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.TranscriptCharge
open Zkc.Construction ZkcSecurity.FiatShamir QueryTreeSource
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcExamples.Structured.FriSource (extension)
open ObservedQueries (Key Answer)
open OracleComp OracleSpec

abbrev History := ObservedFold.History
abbrev Table := (key : Key) → Answer key

structure Fold where
  logHalf : Nat
  tailRounds : Nat
  terminalLog : Nat
  domain : _root_.Domain.SmoothCosetFftDomain (logHalf + 1) Octic
  feasible : terminalLog + (tailRounds + 1) + 1 ≤ logHalf + 1
  site : ObservedLayers.Round
  field : site.draw.request = some (.draw extension)

def fieldKey (site : ObservedLayers.Round) (field : site.draw.request = some (.draw extension))
    (prior : History) : Key :=
  .inr ⟨prior ++ [.challenge site.draw], by
    rw [Composition.scalarCell_iff, field]
    decide⟩

namespace Fold

abbrev address (round : Fold) := fieldKey round.site round.field

theorem address_injective (round : Fold) : Function.Injective round.address := by
  intro first second equal
  exact (List.append_inj' (congrArg Subtype.val (Sum.inr.inj equal)) rfl).1

def bad (round : Fold) (key : Key) (table : Table) : Prop :=
  ∃ prior, key = round.address prior ∧
    ObservedFold.atAnswer round.domain (degreeBound round.tailRounds (2 ^ round.terminalLog))
      round.site.word round.site.draw round.field prior (table (round.address prior))

noncomputable def charge (round : Fold) (key : Key) : ENNReal := by
  classical
  exact if ∃ prior, key = round.address prior then uniqueDecodingError Octic (round.logHalf + 1) 0 else 0

theorem resample [DecidableEq Key] [sampler : ∀ key, SampleableType (Answer key)]
    [SampleableType Octic] (round : Fold) : ResampleBound Answer round.bad round.charge := by
  intro key table
  by_cases selected : ∃ prior, key = round.address prior
  · obtain ⟨prior, rfl⟩ := selected
    have atKey (answers : Table) : round.bad (round.address prior) answers ↔
        ObservedFold.atAnswer round.domain (degreeBound round.tailRounds (2 ^ round.terminalLog))
          round.site.word round.site.draw round.field prior (answers (round.address prior)) := by
      constructor
      · rintro ⟨other, equal, failure⟩
        cases round.address_injective equal
        exact failure
      · exact fun hit => ⟨prior, rfl, hit⟩
    simp only [atKey, Function.update_self, charge]
    rw [ite_eq_left ⟨prior, rfl⟩]
    exact @ObservedFold.sampled _ _ _ _ round.domain round.feasible round.site.word round.site.draw
      round.field prior (sampler (round.address prior))
  · have never (answers : Table) : ¬ round.bad key answers := fun ⟨prior, same, _⟩ => selected ⟨prior, same⟩
    simp [never, charge, selected]

end Fold

/-- Generate the folding schedule solely from dimensions and the installed
round sites. Its three retained domains are successively squared. -/
def schedule (sites : ObservedLayers.Sites) (fields : ∀ i, (sites.round i).draw.request = some (.draw extension))
    (t : Nat) : (n r ordinal : Nat) → (domain : _root_.Domain.SmoothCosetFftDomain n Octic) →
      t + r + 1 ≤ n → List Fold
  | _, 0, _, _, _ => []
  | n+1, r+1, ordinal, domain, feasible =>
    ⟨n, r, t, domain, feasible, sites.round ordinal, fields ordinal⟩ ::
      schedule sites fields t n r (ordinal+1) (domain.subdomain 1) (by omega)
  | 0, _+1, _, _, impossible => False.elim (by omega)

abbrev QueryBad (sites : ObservedLayers.Sites) {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ) :=
  ObservedQueries.bad sites shift nonzero δ

noncomputable def queryCharge (δ : ℝ) : Key → ENNReal
  | .inl (.inl _) => ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ 8
  | _ => 0

def bad (folds : List Fold) (query : Key → Table → Prop) (key : Key) (table : Table) : Prop :=
  (∃ round ∈ folds, round.bad key table) ∨ query key table

noncomputable def charge (folds : List Fold) (δ : ℝ) (key : Key) : ENNReal :=
  (folds.map (fun r => r.charge key)).sum + queryCharge δ key

theorem resample [DecidableEq Key] [∀ key, SampleableType (Answer key)] [SampleableType Octic]
    (folds : List Fold) (sites : ObservedLayers.Sites) {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ) :
    ResampleBound Answer (bad folds (QueryBad sites nonzero δ)) (charge folds δ) := by
  induction folds with
  | nil =>
    intro key table
    have bound := ObservedQueries.resample sites shift nonzero δ key table
    rcases key with (history | fallback) | other <;> simpa [bad, charge, queryCharge] using bound
  | cons round rest ih =>
    intro key table
    have splitEvent (answers : Table) : bad (round :: rest) (QueryBad sites nonzero δ) key answers ↔
        round.bad key answers ∨ bad rest (QueryBad sites nonzero δ) key answers := by
      simp [bad, or_assoc]
    simp only [splitEvent, charge, List.map_cons, List.sum_cons, add_assoc]
    exact (prEvent_or_le ($ᵗ (Answer key)) _ _).trans (add_le_add (round.resample key table) (ih key table))

end ZkcSecurity.ArkLib.Fri.TranscriptCharge

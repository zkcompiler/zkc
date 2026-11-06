module

public import ZkcArkLib.Fri.RetainedDomain
public import ZkcSecurity.Bindings.Transcript.ObservedPayload

@[expose] public section

/-! Resampling one full-word folding challenge in the source transcript.
The selected key determines the word and its length before the raw field
answer is sampled. The result applies under every background answer table. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ObservedFold
open Zkc.Source.Structured Zkc.Construction ZkcSecurity.FiatShamir
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open OracleComp

abbrev History := Domain.History model.toCarriers
abbrev Answer (key : History) := Typed.ByLast Domain.Raw key

def sizedWord {F : Type} (n : Nat) (cells : List F) : Option (Fin n → F) :=
  if size : cells.length = n then some (fun i ↦ cells[i.val]'(size.symm ▸ i.isLt)) else none

theorem sizedWord_ofFn {F : Type} {n : Nat} (word : Fin n → F) :
    sizedWord n (List.ofFn word) = some word := by
  simp [sizedWord, List.length_ofFn, List.getElem_ofFn]

def wordAt (message draw : Origin) (n : Nat) (key : History) : Option (Fin n → Octic) :=
  ObservedPayload.beforeDraw message draw (.vector ZkcExamples.Structured.FriSource.extension) key >>=
    sizedWord n

theorem wordAt_message (history : History) (message draw : Origin) {n : Nat} (word : Fin n → Octic)
    {payload : Domain.Payload model.toCarriers}
    (encoded : Domain.Payload.ofValue (.vector ZkcExamples.Structured.FriSource.extension)
      (List.ofFn word) = some payload) :
    wordAt message draw n (history ++ [.message message payload] ++ [.challenge draw]) = some word := by
  rw [wordAt, ObservedPayload.beforeDraw_observed history message draw encoded]
  exact sizedWord_ofFn word

/-- Transport preserves the full raw answer, with the field fixed by the
request at the exact occurrence. -/
def fieldAnswer (preceding : History) (draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension)) :
    Answer (preceding ++ [.challenge draw]) ≃ Octic :=
  (Typed.ByLast.read Domain.Raw).trans (Equiv.cast (by simp only [Domain.Raw, request]; rfl))

def atAnswer {m : Nat} (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (d : Nat) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension))
    (preceding : History) (raw : Answer (preceding ++ [.challenge draw])) : Prop :=
  ∃ word, wordAt message draw (2 ^ (m + 1)) (preceding ++ [.challenge draw]) = some word ∧
    _root_.Fri.FoldingAgreementFailure domain word 1 d (1 / 4 : ℝ)
      (fieldAnswer preceding draw request raw)

def escapes {m : Nat} (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (d : Nat) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension))
    (preceding : History) (table : (key : History) → Answer key) : Prop :=
  atAnswer domain d message draw request preceding (table (preceding ++ [.challenge draw]))

/-- Only the selected raw answer is random. This formulation applies both
to the primitive oracle and to the field cells of the regrouped oracle. -/
theorem sampled [SampleableType Octic] {m t R : Nat}
    (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (rate : t + (R + 1) + 1 ≤ m + 1) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension))
    (preceding : History) [SampleableType (Answer (preceding ++ [.challenge draw]))] :
    Pr{let raw ← $ᵗ (Answer (preceding ++ [.challenge draw]))}[
      atAnswer domain (degreeBound R (2 ^ t)) message draw request preceding raw] ≤
        uniqueDecodingError Octic (m + 1) 0 := by
  cases fixed : wordAt message draw (2 ^ (m + 1)) (preceding ++ [.challenge draw]) with
  | none => simp [atAnswer, fixed]
  | some word =>
    simp only [atAnswer, fixed, Option.some.injEq, exists_eq_left']
    exact (le_of_eq (SampleableType.prEvent_uniformSample_equiv (fieldAnswer preceding draw request)
      (_root_.Fri.FoldingAgreementFailure domain word 1 (degreeBound R (2 ^ t)) (1 / 4 : ℝ)))).trans
      ((Phases.foldingEscapes_uniqueDecoding domain rate).1 word)

variable [DecidableEq (Domain.Event model.toCarriers)] [SampleableType Octic]
  [∀ key : History, SampleableType (Answer key)]

/-- The round's unique-decoding charge at any candidate transcript address,
including malformed and adversarially fabricated addresses. No hypothesis
selects a fixed word, bounds resampling, or assumes a security certificate. -/
theorem resample {m t R : Nat} (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (rate : t + (R + 1) + 1 ≤ m + 1) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension))
    (preceding : History) (table : (key : History) → Answer key) :
    Pr{let raw ← $ᵗ (Answer (preceding ++ [.challenge draw]))}[
      escapes domain (degreeBound R (2 ^ t)) message draw request preceding
        (Function.update table (preceding ++ [.challenge draw]) raw)] ≤
          uniqueDecodingError Octic (m + 1) 0 := by
  simpa only [escapes, Function.update_self] using sampled domain rate message draw request preceding

/-- Extend a round to all the oracle's keys. Unrelated addresses cannot
witness this round's failure. Repeated calls at its address are still charged. -/
def badKey {m : Nat} (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (d : Nat) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension))
    (key : History) (table : (key : History) → Answer key) : Prop :=
  ∃ prior : History, key = prior ++ [.challenge draw] ∧ escapes domain d message draw request prior table

theorem allKeys {m t R : Nat} (domain : _root_.Domain.SmoothCosetFftDomain (m + 1) Octic)
    (rate : t + (R + 1) + 1 ≤ m + 1) (message draw : Origin)
    (request : draw.request = some (.draw ZkcExamples.Structured.FriSource.extension)) :
    ResampleBound Answer (badKey domain (degreeBound R (2 ^ t)) message draw request)
      (fun key ↦ if key.getLast? = some (.challenge draw) then uniqueDecodingError Octic (m + 1) 0 else 0) := by
  intro key table
  by_cases suffix : ∃ prior : History, key = prior ++ [.challenge draw]
  · obtain ⟨prior, rfl⟩ := suffix
    simpa [badKey] using resample domain rate message draw request prior table
  · have never (answers : (key : History) → Answer key) :
        ¬ badKey domain (degreeBound R (2 ^ t)) message draw request key answers :=
      fun ⟨prior, same, _⟩ ↦ suffix ⟨prior, same⟩
    simp [never]

end ZkcSecurity.ArkLib.Fri.ObservedFold

module

public import Zkc.Tools.Formal.TableCertificate
public import Zkc.Formal.Written.TableAcceptance
public import VCVio.OracleComp.ProbComp.IndepProductEvents

@[expose] public section
namespace Zkc.Formal.Written.TableVerifier
open Core Frontend.Emit TableService MeasureTheory
open scoped ENNReal

/-- A frozen table fixes the set of matching rows before the independent indices are drawn. -/
theorem fixedRows {N q : Nat} [NeZero N] (good : Finset (Fin N)) :
    𝒟[AnswerTape.answerTape (Fin N) q] (Set.univ.pi fun _ => (good : Set (Fin N))) =
      ((good.card : ℝ≥0∞) / N)^q := by
  rw [AnswerTape.evalDist_answerTape_univPi]
  simp [SampleableType.evalDist_uniformSample_eq_encard_div]

/-- The source instance uses 1024 positions, tolerance 256 and 40 independent samples. -/
theorem writtenBound (draw : Frontend.Written.DeclaredDraw) (amount : draw.ceiling = (3 / 4 : Rat)^40)
    (good : Finset (Fin 1024)) (few : good.card ≤ 1024 - 256) :
    𝒟[AnswerTape.answerTape (Fin 1024) 40] (Set.univ.pi fun _ => (good : Set (Fin 1024))) ≤
      ENNReal.ofReal (draw.ceiling : ℝ) := by
  rw [amount]
  push_cast
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [fixedRows]
  apply pow_le_pow_left'
  calc (good.card : ℝ≥0∞) / 1024 ≤ (768 : ℝ≥0∞) / 1024 := by gcongr; exact_mod_cast few
       _ = 3 / 4 := by
         rw [ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)]
         norm_num

variable {source : Frontend.Written.AdmittedRoot} (cert : Certificate source)
variable (M : Model source.emission.bindings.vocabulary)
variable [handleEq : DecidableEq (M.Val cert.handle)] [rowEq : DecidableEq (M.Val (scalar source.emission.bindings))]
variable (p : M.Val (polynomial source.emission.bindings)) (dom : M.Val cert.domain)
variable (offer : Offer (M.Val cert.handle) (M.Val (scalar source.emission.bindings)))
variable (opener : Opener (M.Val cert.handle) (M.Val (scalar source.emission.bindings)))
variable (eval : Evaluation cert.calls M (Defs.fnTable M cert.entry.definitions) p dom)

def Certificate.accepts (tape : Draw) : Bool :=
  accepted M cert.handle offer opener tape
    (roleMeaning M (compiled source) cert.root 1 [] (arguments M p dom))

/-- Conditioning the existing probabilistic process runner on one tape gives the
same return event used in the probability bound. -/
theorem Certificate.observedReturn (tape : Draw) :
    (returned <$> ProbabilisticProcess.run (service M cert.handle offer opener tape)
      (roleMeaning M (compiled source) cert.root 1 [] (arguments M p dom)) .empty) =
      pure (cert.accepts M p dom offer opener tape) := by
  unfold service
  rw [run_pointMass]
  simp [Certificate.accepts, accepted]

theorem Certificate.acceptance (tape : Draw) :
    cert.accepts M p dom offer opener tape = true ↔
    opens offer tape (opener offer.handle (request tape)) offer.handle (request tape)
      (opener offer.handle (request tape)).2 = true ∧
    ∀ j, offer.data (tape j) = eval.expected (tape j) := by
  unfold Certificate.accepts
  exact (congrArg (fun pr => accepted M cert.handle offer opener tape pr = true)
    (cert.meaning M [] (arguments M p dom))).to_iff.trans
      (@accepts_iff source.emission.bindings cert.entry.earlier cert.domain cert.handle
        cert.calls M _ _ p dom rowEq eval tape handleEq offer opener)

theorem Certificate.honestAcceptance (tape : Draw) :
    cert.accepts M p dom offer (honest offer.data) tape = true ↔
      ∀ j, offer.data (tape j) = eval.expected (tape j) := by
  rw [cert.acceptance M p dom offer (honest offer.data) eval tape]
  simp [honest_rows, opens]

/-- Probability of the compiled verifier returning under independent uniform indices
with replacement, for each table fixed before this draw and each adaptive opener. -/
theorem Certificate.sound (few : (Finset.univ.filter fun i => offer.data i = eval.expected i).card ≤ 768) :
    𝒟[AnswerTape.answerTape (Fin 1024) 40] {tape | cert.accepts M p dom offer opener tape = true} ≤
      ENNReal.ofReal (cert.draw.ceiling : ℝ) := by
  let good := Finset.univ.filter fun i => offer.data i = eval.expected i
  apply le_trans (measure_mono (t := Set.univ.pi fun _ => (good : Set (Fin 1024))) ?_)
    (writtenBound cert.draw cert.amount good few)
  intro tape passed i _
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((cert.acceptance M p dom offer opener eval tape).mp passed).2 i⟩

end Zkc.Formal.Written.TableVerifier

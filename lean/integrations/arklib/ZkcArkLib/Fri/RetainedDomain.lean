module

public import ZkcArkLib.Fri.PhasesUniqueDecoding
public import ZkcSecurity.Bindings.Models.KoalaBearNumerics
public import ZkcExamples.Structured.FriSource

@[expose] public section

/-! The retained scalar instance's actual source observer and ordered domain.
The mathematical phase bound and the observation on the source are separate
until their executions are connected. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.RetainedDomain
open Zkc.Source.Structured ZkcSecurity.Domains
open KoalaBearModel (model octicRoots octicIdentity)
open _root_.ZkcSecurity.Domains.KoalaBear (Base Octic)
open OracleComp

def root (k : Nat) : Octic :=
  ZkcSecurity.Domains.KoalaBear.embed ((koalaBearRootLiterals[k]?.getD 0 : Nat) : Base)

theorem root_eq (k : Nat) (bound : k < 25) :
    root k = ZkcSecurity.Domains.KoalaBear.embed (octicRoots.roots[k]'bound) := by
  unfold root
  apply congrArg ZkcSecurity.Domains.KoalaBear.embed
  exact (congrArg (fun n : Nat ↦ (n : Base)) (by
    simp only [List.getElem?_eq_getElem
      (show k < koalaBearRootLiterals.length from bound), Option.getD_some]
    rfl)).trans
    (KoalaBearModel.root_at k bound).symm

theorem order (k : Nat) (bound : k < 25) : IsPrimitiveRoot (root k) (2 ^ k) := by
  rw [root_eq k bound]
  exact (KoalaBearModel.octicRoots_ordered.order k _ (List.getElem?_eq_getElem bound)).map_of_injective
    ZkcSecurity.Domains.KoalaBear.embed_injective

theorem square (k : Nat) (next : k + 1 < 25) : root (k + 1) ^ 2 = root k := by
  rw [root_eq (k + 1) next, root_eq k (by omega)]
  refine (map_pow ZkcSecurity.Domains.KoalaBear.embed _ 2).symm.trans ?_
  exact congrArg ZkcSecurity.Domains.KoalaBear.embed (KoalaBearModel.octicRoots_ordered.square k _ _
    (List.getElem?_eq_getElem (show k < octicRoots.roots.length from by change k < 25; omega))
    (List.getElem?_eq_getElem next))

theorem compatible : Compatible root 5 3 :=
  fun _ _ ltFive ↦ square _ (by omega)

/-- Source numerical operations select the identical embedded root. -/
theorem domainRoot (k : Nat) (bound : k ≤ 5) :
    Numerical.domainRoot model.toFieldModel octicIdentity (2 ^ k) = .ok (root k) := by
  have size : 2 ^ k < indexLimit := by
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) bound)
      (show 2 ^ 5 < indexLimit by decide)
  have log : (2 ^ k).log2 = k := Nat.log2_two_pow
  rw [root_eq k (by omega)]
  have atIndex : octicRoots.roots[(2 ^ k).log2]? =
      some (octicRoots.roots[k]'(show k < 25 by omega)) := by
    rw [log]
    exact List.getElem?_eq_getElem _
  exact Numerical.domainRoot_eq model.toFieldModel octicIdentity (2 ^ k)
    ⟨by positivity, size, by rw [log]⟩ octicRoots KoalaBearModel.octicRoots_installed _ atIndex

def domain (shift : Octic) (nonzero : shift ≠ 0) :=
  cosetDomain shift (root 5) nonzero (order 5 (by decide))

theorem geometry (shift : Octic) (nonzero : shift ≠ 0) (j : Fin 32) :
    domain shift nonzero j = point root shift 5 j :=
  cosetDomain_point root shift nonzero (order 5 (by decide)) j

/-- The causal ideal bound at the retained profile. It uses three folding
errors and eight sequential index draws with replacement. -/
theorem phase_soundness {S E : Type} [SampleableType Octic]
    (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ)
    (prover : Phases.CausalProver Octic S (Phases.SamplingEvent 5 E))
    (positions : Phases.QueryProver 5 S E)
    (reader : PIR.MonadHandler ProbComp Phases.checkOperations S (Phases.SamplingEvent 5 E))
    (state : S) :
    Pr{let result ← Phases.experiment root 0 4 2 8 shift .scalar prover positions reader state}[
      Phases.returned (fun output ↦ output.2.accepted = true ∧
        Far (domain shift nonzero) 8 δ output.1) result] ≤
      (∑ r ∈ Finset.range 3, uniqueDecodingError Octic 5 r) +
        ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ 8 :=
  Phases.soundness_uniqueDecoding root 0 8 (domain shift nonzero) shift
    (geometry shift nonzero) compatible (by decide) δ .scalar prover positions reader state

/-- Distance is measured on the first successful full publication over the
actual coset. Duplicate query positions are permitted by the scalar policy. -/
def sourceEvent {Aux E : Type} (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ)
    (execution : ZkcExamples.Structured.FriSource.Execution model Aux E) : Prop :=
  ZkcExamples.Structured.FriSource.acceptsFirst (fun cells ↦ ∃ word : Fin 32 → Octic,
    cells = List.ofFn word ∧ Far (domain shift nonzero) 8 δ word) execution

theorem sourceEvent_stopped {Aux E : Type} {shift : Octic} {nonzero : shift ≠ 0}
    {δ : ℝ} {execution : ZkcExamples.Structured.FriSource.Execution model Aux E} {why}
    (stopped : execution.outcome = .stopped why) : ¬ sourceEvent shift nonzero δ execution := by
  intro event
  simpa [ZkcExamples.Structured.FriSource.accepted, stopped] using event.1

end ZkcSecurity.ArkLib.Fri.RetainedDomain

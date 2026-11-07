module

public import ZkcArkLibExamples.Fri.ObservedLayers
public import ZkcArkLibExamples.Fri.RetainedDomain
public import ZkcSecurityExamples.FriScalarQueries

@[expose] public section

/-! A complete answer tree at the frozen query-entry history has a charge
for all eight checks. Earlier adversarial exposure is handled by exact
simulation and resampling, not by conditioning on a fresh verifier call. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.ObservedQueries
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir QueryTree QueryTreeSource
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open OracleComp OracleSpec MeasureTheory

private theorem samples_positions (n count : Nat) :
    samples (id : Fin (2 ^ n) → _) count = List.ofFn <$> Phases.productPositions n count := by
  induction count with
  | zero => simp [samples, Phases.productPositions]
  | succ c ih =>
    simp only [samples, Phases.productPositions, ih, bind_map_left, map_bind, map_pure,
      List.ofFn_cons, id_eq]

abbrev Tree := Coordinate 32 8 → Fin 32

def positions (tree : Tree) (i : Fin 8) : Fin 32 :=
  (path id 8 (fun node => tree (.inl node)))[i.val]'(by simp)

theorem path_eq_positions (tree : Tree) :
    path id 8 (fun node => tree (.inl node)) = List.ofFn (positions tree) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

theorem ordered_path :
    (do let tree ← $ᵗ Tree; pure (List.ofFn (positions tree))) =ᵈ
      List.ofFn <$> ($ᵗ (Fin 8 → Fin 32)) := by
  let : MeasurableSpace (List (Fin 32)) := ⊤
  have product : (do let tree ← $ᵗ Tree; pure (List.ofFn (positions tree))) =ᵈ
      samples (id : Fin 32 → Fin 32) 8 :=
    EvalDistEq.of_evalDist_eq (by
      simpa only [path_eq_positions, bind_pure] using
        (macro_path_product (bound := 32) (height := 8) (pure : List (Fin 32) → ProbComp (List (Fin 32)))))
  rw [show samples (id : Fin 32 → Fin 32) 8 = List.ofFn <$> Phases.productPositions 5 8 from
    samples_positions 5 8] at product
  exact product.trans ((Phases.productPositions_sameDist 5 8).map List.ofFn)

/-- A fixed safe and far trace escapes only through eight agreeing coordinates. -/
theorem fixed {shift : Octic} (nonzero : shift ≠ 0) (δ : ℝ) (layers : Layers Octic 5 3)
    (safe : (toTrace 0 (RetainedDomain.domain shift nonzero) layers).Safe (1 / 4))
    (far : Far (RetainedDomain.domain shift nonzero) 8 δ
      (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial) :
    Pr{let tree ← $ᵗ Tree}[Phases.accepts RetainedDomain.root 0 layers shift (positions tree) = true] ≤
      ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ 8 := by
  let accept := fun p : Fin 8 → Fin 32 => Phases.accepts RetainedDomain.root 0 layers shift p = true
  have distribution := ordered_path.prEvent_eq (fun xs => ∃ p, xs = List.ofFn p ∧ accept p)
  simp only [prEvent_norm, List.ofFn_inj, exists_eq_left'] at distribution
  exact (le_of_eq distribution).trans
    (query_escape_le_of_accepts (toTrace 0 (RetainedDomain.domain shift nonzero) layers)
      (1 / 4) δ safe far (Equiv.refl _) accept (fun p ok => Phases.accepts_trace
        RetainedDomain.root 0 (RetainedDomain.domain shift nonzero) shift
        (RetainedDomain.geometry shift nonzero) RetainedDomain.compatible layers p ok))

abbrev Key := Root model.toCarriers 32 ⊕ Composition.OtherKey model.toCarriers 32
abbrev Answer := Composition.fullRange model.toCarriers 32 8

def escape (sites : ObservedLayers.Sites) (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ)
    (history : ObservedFold.History) (tree : Tree) : Prop :=
  ∃ layers, ObservedLayers.atRoot sites 5 3 history = some layers ∧
    (toTrace 0 (RetainedDomain.domain shift nonzero) layers).Safe (1 / 4) ∧
    Far (RetainedDomain.domain shift nonzero) 8 δ
      (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial ∧
    Phases.accepts RetainedDomain.root 0 layers shift (positions tree) = true

def bad (sites : ObservedLayers.Sites) (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ)
    (key : Key) (table : (key : Key) → Answer key) : Prop :=
  match key with
  | .inl (.inl history) => escape sites shift nonzero δ history (table (.inl (.inl history)))
  | _ => False

/-- Every typed macro cell has a charge under arbitrary background answers.
Malformed histories, non-scalar requests and unparsed scalar roots contribute zero. -/
theorem resample [DecidableEq Key] [sampler : ∀ key, SampleableType (Answer key)]
    (sites : ObservedLayers.Sites) (shift : Octic) (nonzero : shift ≠ 0) (δ : ℝ) :
    ResampleBound Answer (bad sites shift nonzero δ)
      (fun key => match key with
        | .inl (.inl _) => ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ 8
        | _ => 0) := by
  intro key table
  rcases key with (history | fallback) | other
  case inl.inl =>
    simp only [bad, Function.update_self]
    have law := @SampleableType.prEvent_uniformSample_equiv (Answer (.inl (.inl history))) Tree
      (sampler _) inferInstance (Equiv.refl Tree) (escape sites shift nonzero δ history)
    refine (le_of_eq law).trans ?_
    by_cases possible : ∃ layers, ObservedLayers.atRoot sites 5 3 history = some layers ∧
        (toTrace 0 (RetainedDomain.domain shift nonzero) layers).Safe (1 / 4) ∧
        Far (RetainedDomain.domain shift nonzero) 8 δ
          (toTrace 0 (RetainedDomain.domain shift nonzero) layers).initial
    · obtain ⟨layers, read, safe, far⟩ := possible
      refine (prEvent_mono _ _ _ (fun tree outcome => ?_)).trans (fixed nonzero δ layers safe far)
      obtain ⟨other, found, _, _, accepted⟩ := outcome
      cases Option.some.inj (found.symm.trans read)
      exact accepted
    · refine (le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun tree hit => ?_))).trans bot_le
      obtain ⟨layers, read, safe, far, _⟩ := hit
      exact possible ⟨layers, read, safe, far⟩
  all_goals exact le_of_eq (prEvent_false _)

end ZkcSecurity.ArkLib.Fri.ObservedQueries

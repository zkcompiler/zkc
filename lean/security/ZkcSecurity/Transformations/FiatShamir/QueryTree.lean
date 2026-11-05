module

public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Finite scalar query trees

A node is a typed response prefix, including its depth. Every possible node has its own raw
answer, including nodes outside the decoded path. `Step` must include everything observable
that affects the successor key. Identifying these nodes with source keys is a separate,
injective parsing obligation; matching service names does not establish it.

The path theorem is an exact product law before any tree-dependent conditioning. It does not
assert a product law conditional on earlier adversary queries. The complete tree is an
information-theoretic oracle answer; no efficient representation or sampling claim is made.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.QueryTree
open OracleComp OracleSpec MeasureTheory

/-- Prefix nodes of depth strictly below the supplied height. -/
def Node (Step : Type) : ℕ → Type
  | 0 => Empty
  | n + 1 => Unit ⊕ (Step × Node Step n)

instance {Step : Type} [Fintype Step] : (n : ℕ) → Fintype (Node Step n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => by
      haveI : Fintype (Node Step n) := QueryTree.instFintypeNode n
      exact inferInstanceAs (Fintype (Unit ⊕ (Step × Node Step n)))

instance {Step : Type} [DecidableEq Step] : (n : ℕ) → DecidableEq (Node Step n)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | n + 1 => by
      haveI : DecidableEq (Node Step n) := QueryTree.instDecidableEqNode n
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Step × Node Step n)))

/-- A raw reply at every prefix, rather than only at the eventually realized path. -/
abbrev Tree (Raw Step : Type) (height : ℕ) := Node Step height → Raw

/-- Follow the actual decoded replies. Repeated decoded values remain separate occurrences. -/
def path {Raw Step : Type} (decode : Raw → Step) :
    (n : ℕ) → Tree Raw Step n → List Step
  | 0, _ => []
  | n + 1, tree =>
      let step := decode (tree (.inl ()))
      step :: path decode n (fun node ↦ tree (.inr (step, node)))

@[simp] theorem path_length {Raw Step : Type} (decode : Raw → Step) (n : ℕ)
    (tree : Tree Raw Step n) : (path decode n tree).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [path, ih]

/-- The actual ordered independent raw samples, decoded one at a time. -/
def samples {Raw Step : Type} [SampleableType Raw] (decode : Raw → Step) :
    ℕ → ProbComp (List Step)
  | 0 => pure []
  | n + 1 => do
      let raw ← $ᵗ Raw
      let rest ← samples decode n
      pure (decode raw :: rest)

/-- Extracting the root leaves every child subtree unchanged. -/
theorem path_update_root {Raw Step : Type} [DecidableEq Step]
    (decode : Raw → Step) (n : ℕ) (tree : Tree Raw Step (n + 1)) (raw : Raw) :
    path decode (n + 1) (Function.update tree (.inl ()) raw) =
      decode raw :: path decode n (fun node ↦ tree (.inr (decode raw, node))) := by
  classical
  simp only [path]
  congr 2

/-- Exact path-product law, preserving every subsequent probabilistic observation.
The proof exposes the independent root cell and restricts the remaining uniform table to the
selected subtree. It never replaces a cached query by an independently resampled answer. -/
theorem path_product_bind {Raw Step α : Type} [SampleableType Raw] [Fintype Step]
    [DecidableEq Step] [MeasurableSpace α]
    (decode : Raw → Step) (n : ℕ) (next : List Step → ProbComp α) :
    𝒟[do let tree ← $ᵗ (Tree Raw Step n); next (path decode n tree)] =
      𝒟[samples decode n >>= next] := by
  classical
  let : MeasurableSpace Raw := ⊤
  induction n generalizing next with
  | zero =>
      simp only [path, samples, pure_bind]
      exact OracleComp.evalDist_bind_const _ _
  | succ n ih =>
      rw [evalDist_bind_cell_extract ($ᵗ Raw) ($ᵗ (Tree Raw Step (n + 1)))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample (.inl ())
        (fun tree _ ↦ next (path decode (n + 1) tree))]
      simp only [path_update_root, samples, bind_assoc, pure_bind]
      apply evalDist_bind_congr
      intro raw
      have restriction := EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective
        ($ᵗ (Tree Raw Step n)) ($ᵗ (Tree Raw Step (n + 1)))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
        (e := fun node : Node Step n ↦ (Sum.inr (decode raw, node) : Node Step (n + 1)))
        (by intro a b same; exact (Prod.mk.inj (Sum.inr.inj same)).2))
      have restricted := (restriction.bind_left
        (fun tree ↦ next (decode raw :: path decode n tree))).evalDist_eq
      rw [bind_map_left] at restricted
      exact restricted.trans (ih (fun rest ↦ next (decode raw :: rest)))

/-- Equality of the full ordered path distribution, including duplicate indices. -/
theorem path_product {Raw Step : Type} [SampleableType Raw] [Fintype Step]
    [DecidableEq Step] (decode : Raw → Step) (n : ℕ) :
    (do let tree ← $ᵗ (Tree Raw Step n); pure (path decode n tree)) =ᵈ samples decode n := by
  let : MeasurableSpace (List Step) := ⊤
  exact EvalDistEq.of_evalDist_eq (by simpa using path_product_bind decode n pure)

/-- A separately proved uniform decoder turns the raw product into independent uniform
observable replies. The decoder hypothesis does not assert any native byte correspondence. -/
theorem samples_uniform {Raw Step : Type} [SampleableType Raw] [SampleableType Step]
    (decode : Raw → Step) (uniformDecode : decode <$> ($ᵗ Raw) =ᵈ ($ᵗ Step)) (n : ℕ) :
    samples decode n =ᵈ OracleComp.replicate n ($ᵗ Step) := by
  induction n with
  | zero => exact EvalDistEq.rfl
  | succ n ih =>
      have law := uniformDecode.bind (fun step ↦ ih.map (List.cons step))
      simpa only [samples, OracleComp.replicate_succ_bind, bind_map_left,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using law

/-- Uniformity of every complete ordered vector, after both independence and the single-node
decoder law have been established. No conditioning on previously exposed nodes is asserted. -/
theorem path_uniform {Raw Step : Type} [SampleableType Raw] [SampleableType Step]
    [Fintype Step] [DecidableEq Step] (decode : Raw → Step)
    (uniformDecode : decode <$> ($ᵗ Raw) =ᵈ ($ᵗ Step)) (n : ℕ) :
    (do let tree ← $ᵗ (Tree Raw Step n); pure (path decode n tree)) =ᵈ
      OracleComp.replicate n ($ᵗ Step) :=
  (path_product decode n).trans (samples_uniform decode uniformDecode n)

/-- Exact mass of any length-correct ordered vector; repeated indices are allowed. -/
theorem path_vector_probability {Raw Step : Type} [SampleableType Raw] [SampleableType Step]
    [Fintype Step] [DecidableEq Step] (decode : Raw → Step)
    (uniformDecode : decode <$> ($ᵗ Raw) =ᵈ ($ᵗ Step)) (n : ℕ) (values : List Step)
    (length : values.length = n) :
    Pr{let tree ← $ᵗ (Tree Raw Step n)}[path decode n tree = values] =
      ((Fintype.card Step ^ n : ℕ) : ENNReal)⁻¹ := by
  have law := (path_uniform decode uniformDecode n).prEvent_eq (· = values)
  simp only [prEvent_norm] at law
  rw [law]
  exact SampleableType.prEvent_replicate_uniformSample length

end ZkcSecurity.FiatShamir.QueryTree

module

public import Zkc.Formal.Written.ArithmeticModel
public import Zkc.Formal.Written.LawSamplers
public import Zkc.Formal.Written.UniformVector

@[expose] public section

/-!
The samplers of the laws in the arithmetic model.

Where the scalars of the model are a field that can be sampled, the law `uniform` of the scalar
type draws one of them uniformly, and the law `uniform` of the sequences of `n` scalars draws
`n` of them, independently and uniformly (`drawVector`). Every other law is drawn as in the
standard model: the arithmetic draws extend the standard ones.

`ArithmeticModel.sampled` is the table of these laws, by key and type of reply. It is the table
of the draws in both directions (`sampled_iff_draws`): a law of the table has a sampler in the
model over every field, and a law with a sampler is in the table. `ArithmeticModel.covers` is
the coverage of a program by names with this table.
-/

namespace Zkc.Formal.Written.ArithmeticModel
open Core ProbabilisticProcess OracleComp ProbComp

variable (F G : Type) [Field F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-- The uniform law in the arithmetic model: a scalar and a sequence of `n` scalars are drawn
uniformly, and the rest as in the standard model. -/
noncomputable def uniformDraw : UniformDraws (model F G)
  | .nominal (.field .bls12381Fr), .nominal (.inl (.field .bls12381Fr)) => some ($ᵗ F)
  | .seq (.nominal (.field .bls12381Fr)) (some n),
      .seq (.nominal (.inl (.field .bls12381Fr))) (some m) =>
    if m = n then some (drawVector F n) else none
  | type, τ => StandardModel.uniformDraw (data F G) type τ

/-- The samplers of the laws in the arithmetic model. -/
noncomputable def draws : LawDraws (model F G) := uniformDraws (model F G) (uniformDraw F G)

/-- Whether the arithmetic draws have a sampler for the uniform law of a type at a type of
reply. -/
def sampledType : Zkc.Vocabulary.Ty → Standard.Ty → Bool
  | .nominal (.field .bls12381Fr), .nominal (.inl (.field .bls12381Fr)) => true
  | .seq (.nominal (.field .bls12381Fr)) (some n),
      .seq (.nominal (.inl (.field .bls12381Fr))) (some m) => m == n
  | type, τ => StandardModel.sampledType type τ

/-- Whether the arithmetic draws have a sampler for a law at a type of reply. -/
def sampled : Standard.LawKey → Standard.Ty → Bool
  | .uniform type, τ => sampledType type τ

/-- **The table is the table of the draws.** Over every field, a law is in the table exactly
when the model has a sampler for it. -/
theorem sampled_iff_draws (law : Standard.LawKey) (τ : Standard.Ty) :
    sampled law τ = (draws F G law [] .nil τ).isSome := by
  obtain ⟨type⟩ := law
  change sampledType type τ = (uniformDraw F G type τ).isSome
  unfold sampledType uniformDraw
  split
  · rfl
  · rename_i n m
    by_cases same : m = n
    · subst same
      simp only [beq_self_eq_true, ite_true]
      rfl
    · simp [same]
  · exact StandardModel.sampled_iff_draws (data F G) (.uniform _) _

/-- What the uniform law of the arithmetic model draws is what the world may give: a scalar, a
sequence of its size, and what the standard model draws. -/
theorem uniformDraw_allowed (type : Zkc.Vocabulary.Ty) (τ : Standard.Ty) (sampler : ProbComp ((model F G).Val τ))
    (has : uniformDraw F G type τ = some sampler)
    (v : (model F G).Val τ) (drawn : v ∈ support sampler) :
    Allows (model F G) (.coin (.uniform type)) [] .nil τ v := by
  unfold uniformDraw at has
  split at has
  · exact ⟨trivial, ⟨[], scalarTy⟩, rfl, rfl, rfl, trivial⟩
  · rename_i n m
    split at has
    · rename_i same
      subst same
      obtain rfl := Option.some.inj has
      have length := length_of_mem_support_drawVector (F := F) m v drawn
      have valid : (model F G).Valid (.seq scalarTy (some m)) v :=
        ⟨fun _ _ => trivial, fun k size => by cases size; exact length⟩
      have base : Zkc.Vocabulary.law (.uniform (.seq (.nominal (.field .bls12381Fr)) (some m))) =
          some ⟨[], .seq (.nominal (.field .bls12381Fr)) (some m)⟩ := by
        simp [Zkc.Vocabulary.law, Zkc.Vocabulary.isLaw]
      have signed : Standard.law (.uniform (.seq (.nominal (.field .bls12381Fr)) (some m))) =
          some ⟨[], .seq scalarTy (some m)⟩ := by
        change Option.map _ (Zkc.Vocabulary.law _) = _
        simp only [base]
        rfl
      exact ⟨valid, ⟨[], .seq scalarTy (some m)⟩, signed, rfl, rfl, valid⟩
    · exact absurd has (by simp)
  · exact StandardModel.uniformDraw_allowed (data F G) _ _ sampler has v drawn

/-- What the arithmetic samplers draw is permitted. -/
theorem draws_permitted (op : ROp (model F G))
    (sampler : ProbComp ((RSig (model F G)).Reply op))
    (has : lawSamplers (model F G) (draws F G) op = some sampler)
    (v : (RSig (model F G)).Reply op) (drawn : v ∈ support sampler) :
    Permitted (model F G) op v :=
  uniformDraws_permitted _ _ (uniformDraw_allowed F G) op sampler has v drawn

/-- The arithmetic model has a service of its laws. -/
theorem served : Served (lawSamplers (model F G) (draws F G)) (Permitted (model F G)) :=
  served_of_draws _ _ (draws_permitted F G)

/-- **The arithmetic model covers a program**: it interprets every row of the vocabulary that
the program links, and has a sampler for the law of every coin that the program draws. -/
def covers (p : NamedProgram Standard) : Bool := StandardModel.coveredBy sampled p

end Zkc.Formal.Written.ArithmeticModel

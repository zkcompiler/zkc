module

public import Zkc.Source.Structured.DomainLaws
public import Zkc.Source.Structured.NumericalEvaluation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-! Optional numerical data and its separate mathematical obligations.
Catalogue capability tags neither install data nor discharge these laws.
Completeness is required explicitly for every enabled capability; the existing
conditional `DomainLaws.inverse` alone does not establish availability. -/

namespace Zkc.Source.Structured

/-- Plonky3 0.8.0 KoalaBear base-field generators, indexed by log2(size).
These are canonical prime-subfield literals, including the size-one root. -/
def koalaBearRootLiterals : List Nat :=
  [0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031,
   0x5c4a5b99, 0x29b75a80, 0x17668b8a, 0x27ad539b, 0x334d48c7,
   0x7744959c, 0x768fc6fa, 0x303964b2, 0x3e687d4d, 0x45a60e61,
   0x6e2f4d7a, 0x163bd499, 0x6c4a8a45, 0x143ef899, 0x514ddcad,
   0x484ef19b, 0x205d63c3, 0x68e7dd49, 0x6ac49f88]

/-- A supported installed ordering. Other two-adic families remain unavailable
until their independent literal specification is supplied. -/
def installedRootLiterals : String → Option (String × List Nat)
  | "koala-bear" | "koala-bear.ext4-binomial3" | "koala-bear.ext8-binomial3" =>
      some ("koala-bear", koalaBearRootLiterals)
  | _ => none

/-- The data's exact ordering, primitive orders and adjacent squaring laws.
The embedding is the model's existing operation, with its own ring-hom laws. -/
structure OrderedRootLaw (catalogue : Catalogue) (model : FieldModel) (d : String)
    (data : TwoAdicData model.Field) : Prop where
  capability : catalogue.require d .field "TwoAdicField" = .ok ()
  installed : ∃ literals, installedRootLiterals d = some (data.base, literals) ∧
    data.roots = literals.map (fun n ↦ (n : model.Field data.base))
  embedding : EmbeddingLaw (model.embed d data.base)
  order : ∀ k root, data.roots[k]? = some root → IsPrimitiveRoot root (2 ^ k)
  square : ∀ k a b, data.roots[k]? = some a → data.roots[k + 1]? = some b → b ^ 2 = a

/-- The installed polynomial presentations and coordinate order. Injectivity
rules out silently losing bits or using a proper subfield as the whole carrier.
For the cubic tower, bit 64*j+i denotes x^i*y^j. -/
structure BinaryPresentationLaw (model : FieldModel) (d : String)
    (data : BinaryData (model.Field d)) : Prop where
  characteristic : CharP (model.Field d) 2
  presentation : ∃ x y : model.Field d,
    x ^ 64 + x ^ 4 + x ^ 3 + x + 1 = 0 ∧
    ((d = "gf2-64.pentanomial-4-3-1" ∧
        data.basis = (List.range 64).map (x ^ ·)) ∨
      (d = "gf2-64.pentanomial-4-3-1.ext3-trinomial1" ∧ y ^ 3 + y + 1 = 0 ∧
        data.basis = (List.range 192).map (fun i ↦ x ^ (i % 64) * y ^ (i / 64))))
  faithful : ∀ a b, a < 2 ^ data.basis.length → b < 2 ^ data.basis.length →
    Numerical.binaryBasisValue data.basis a = Numerical.binaryBasisValue data.basis b → a = b
  base_coordinates : d = "gf2-64.pentanomial-4-3-1.ext3-trinomial1" →
    ∃ baseData, model.binary "gf2-64.pentanomial-4-3-1" = some baseData ∧
      data.basis.take 64 = baseData.basis.map (model.embed d "gf2-64.pentanomial-4-3-1")

/-- The caller chooses which optional capabilities it enables. Empty lists
make no availability assertion; numerical evaluation still refuses absent data. -/
structure NumericalCapabilities where
  inverse : List String := []
  roots : List String := []
  binary : List String := []

structure NumericalDomainLaws (catalogue : Catalogue) (model : DomainModel)
    (enabled : NumericalCapabilities) : Prop where
  algebra : DomainLaws catalogue model
  characteristic : CharacteristicLaws catalogue model.toFieldModel
  inverse_complete : ∀ d ∈ enabled.inverse,
    catalogue.require d .field "Field" = .ok () ∧ ∃ inv, model.inverse d = some inv
  roots_complete : ∀ d ∈ enabled.roots, ∃ data, model.twoAdic d = some data
  binary_complete : ∀ d ∈ enabled.binary, ∃ data, model.binary d = some data
  roots : ∀ d data, model.twoAdic d = some data →
    OrderedRootLaw catalogue model.toFieldModel d data
  binary : ∀ d data, model.binary d = some data →
    BinaryPresentationLaw model.toFieldModel d data

theorem NumericalDomainLaws.inverse_nonzero {catalogue : Catalogue} {model : DomainModel}
    {enabled : NumericalCapabilities} (laws : NumericalDomainLaws catalogue model enabled)
    (d : String) (admitted : d ∈ enabled.inverse) (x : model.Field d) (nonzero : x ≠ 0) :
    ∃ inv : model.Field d → model.Field d,
      Numerical.inverse model.toFieldModel d x = .ok (inv x) ∧ x * inv x = 1 := by
  obtain ⟨_, inv, supplied⟩ := laws.inverse_complete d admitted
  refine ⟨inv, ?_, laws.algebra.inverse d inv supplied x nonzero⟩
  simp [Numerical.inverse, Numerical.require, nonzero, supplied]

theorem ringFieldModel_no_roots (F G : Type) [CommRing F] [DecidableEq F] (d : String)
    (n : Nat) : Numerical.domainRoot (ringFieldModel F G) d n = .error .refused := by
  simp only [Numerical.domainRoot, Numerical.require, ringFieldModel]
  split <;> rfl

theorem ringFieldModel_no_inverse (F G : Type) [CommRing F] [DecidableEq F] (d : String)
    (x : F) : Numerical.inverse (ringFieldModel F G) d x = .error .refused := by
  simp only [Numerical.inverse, Numerical.require, ringFieldModel]
  split <;> rfl

theorem Numerical.domainRoot_eq (model : FieldModel) (d : String) (n : Nat)
    (size : 0 < n ∧ n < indexLimit ∧ 2 ^ n.log2 = n) (data : TwoAdicData model.Field)
    (supplied : model.twoAdic d = some data) (root : model.Field data.base)
    (coordinate : data.roots[n.log2]? = some root) :
    Numerical.domainRoot model d n = .ok (model.embed d data.base root) := by
  simp [Numerical.domainRoot, Numerical.require, size, supplied, coordinate]

theorem Numerical.binaryValue_eq (model : FieldModel) (d : String)
    (data : BinaryData (model.Field d)) (supplied : model.binary d = some data)
    (bits : Nat) (bound : bits < 2 ^ data.basis.length) :
    Numerical.binaryValue model d bits = .ok (Numerical.binaryBasisValue data.basis bits) := by
  simp [Numerical.binaryValue, Numerical.require, supplied, bound]

end Zkc.Source.Structured

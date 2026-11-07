module

public import ZkcSecurity.Transformations.FiatShamir.CoordinateRejection
public import ZkcSecurity.Mathematics.Fields.KoalaBear

@[expose] public section

/-! The bounded octic decoder on sixteen independent 64-byte answers.
Word order, the unused high bit, coordinate rejection, and coefficient
order are fixed. Reaching the byte cap is a stopped outcome. -/
set_option autoImplicit false
namespace ZkcSecurity.Domains.KoalaBear.Sampling
open ZkcSecurity.FiatShamir CoordinateRejection
open OracleComp CompPoly.Extension

abbrev Byte := Fin 256
abbrev Block := Fin 64 → Byte
abbrev Blocks := Fin 16 → Block
abbrev Miss := Fin (2^31 - q)

/-- Byte zero is the least significant digit. -/
def littleEndian (radix : Nat) : (n : Nat) → (Fin n → Fin radix) ≃ Fin (radix^n)
  | 0 => (Equiv.ofUnique (Fin 0 → Fin radix) (Fin 1)).trans (finCongr (pow_zero radix).symm)
  | n+1 =>
    (Fin.consEquiv (fun _ : Fin (n+1) => Fin radix)).symm |>.trans
      (Equiv.prodComm ..) |>.trans
      ((littleEndian radix n).prodCongr (Equiv.refl _)) |>.trans
      finProdFinEquiv |>.trans (finCongr (pow_succ radix n).symm)

theorem littleEndian_step (r n : Nat) (bytes : Fin (n+1) → Fin r) :
    (littleEndian r (n+1) bytes).val =
      (bytes 0).val + r * (littleEndian r n (Fin.tail bytes)).val := rfl

/-- Split the high bit, then split the low word at the field modulus. -/
def classify : Fin (2^32) ≃ Word (Fin 2) Base Miss :=
  (finProdFinEquiv (m := 2) (n := 2^31)).symm.trans ((Equiv.refl _).prodCongr
    ((finSumFinEquiv (m := q) (n := 2^31-q)).symm.trans
      ((ZMod.finEquiv q).toEquiv.sumCongr (Equiv.refl _))))

/-- Exactly the low 31 bits are compared. Candidates outside the base
field are skipped, even when their residue modulo the field is small. -/
theorem candidate (word : Fin (2^32)) :
    accepted (classify word) =
      if h : word.val % 2^31 < q then some ((ZMod.finEquiv q) ⟨_, h⟩) else none := by
  obtain ⟨⟨hi, lo⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2^31)).surjective word
  have low : (finProdFinEquiv (hi, lo)).val % 2^31 = lo.val :=
    congrArg (fun p : Fin 2 × Fin (2^31) => p.2.val) (finProdFinEquiv.symm_apply_apply (hi, lo))
  rw [low]
  obtain ⟨value | miss, rfl⟩ := (finSumFinEquiv (m := q) (n := 2^31-q)).surjective lo
  · simp only [dite_true, (show (finSumFinEquiv (.inl value) : Fin (q + (2^31-q))).val < q from value.isLt)]
    simp only [classify, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.sumCongr_apply, Sum.map_inl]
    rfl
  · simp only [dite_false, (show ¬ (finSumFinEquiv (.inr miss) : Fin (q + (2^31-q))).val < q by
      change ¬ q + miss.val < q
      omega)]
    simp only [classify, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.sumCongr_apply, Sum.map_inr]
    rfl

def words : Block ≃ (Fin 16 → Fin (2^32)) :=
  ((finProdFinEquiv (m := 16) (n := 4)).symm.arrowCongr (Equiv.refl Byte)).trans
    (Equiv.curry _ _ _) |>.trans ((Equiv.refl _).arrowCongr (littleEndian 256 4))

def tape : Blocks ≃ Tape (Fin 2) Base Miss 256 :=
  ((Equiv.refl _).arrowCongr words).trans (Equiv.curry _ _ _).symm |>.trans
    ((finProdFinEquiv (m := 16) (n := 16)).arrowCongr classify) |>.trans
    (Equiv.vectorEquivFin _ _).symm

def coefficients : (Fin 8 → Base) ≃ Octic := (Ext.equivFn octicParams.toExtensionParams).symm

def octic (blocks : Blocks) : Option Octic := (decode 8 (tape blocks)).map coefficients

theorem octic_refused (blocks : Blocks) :
    octic blocks = none ↔ ((tape blocks).val.filterMap accepted).length < 8 := by
  simp only [octic, Option.map_eq_none_iff, refused_iff]

theorem octic_value (blocks : Blocks) (values : Fin 8 → Base) :
    octic blocks = some (coefficients values) ↔
      List.ofFn values <+: (tape blocks).val.filterMap accepted := by
  rw [← decode_eq_iff]
  unfold octic
  cases decode 8 (tape blocks) <;> simp

/-- The first eight bytes encode the little-endian index word. The rest
of the block contributes multiplicity to each output, including zero. -/
def indexParts : Block ≃ Fin (2^64) × (Fin 56 → Byte) :=
  ((finSumFinEquiv (m := 8) (n := 56)).symm.arrowCongr (Equiv.refl Byte)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _) |>.trans ((littleEndian 256 8).prodCongr (Equiv.refl _))

def index (block : Block) : Fin 32 := modulo 32 (indexParts block).1

noncomputable section
local instance : SampleableType Blocks := SampleableType.ofFintype _
local instance : SampleableType (Tape (Fin 2) Base Miss 256) := SampleableType.ofFintype _
local instance : SampleableType (Fin 8 → Base) := SampleableType.ofFintype _
local instance : SampleableType Octic := SampleableType.ofFintype _

theorem octic_exact : Obligations.ExactWithRefusal octic :=
  transport tape coefficients _ (CoordinateRejection.exact (fun _ => (0 : Base)))

local instance : SampleableType Block := SampleableType.ofFintype _
local instance : SampleableType (Fin 56 → Byte) := SampleableType.ofFintype _

theorem index_exact : ExactLaw index := by
  intro event
  calc
    _ = Pr{let parts ← $ᵗ (Fin (2^64) × (Fin 56 → Byte))}[event (modulo 32 parts.1)] :=
      SampleableType.prEvent_uniformSample_equiv indexParts (fun p => event (modulo 32 p.1))
    _ = Pr{let word ← $ᵗ (Fin (2^64))}[event (modulo 32 word)] :=
      SampleableType.prEvent_uniformSample_fst (β := Fin 56 → Byte) (fun w : Fin (2^64) => event (modulo 32 w))
    _ = _ := (modulo_exact 32 (2^64) (by decide)).exactLaw event

end
end ZkcSecurity.Domains.KoalaBear.Sampling

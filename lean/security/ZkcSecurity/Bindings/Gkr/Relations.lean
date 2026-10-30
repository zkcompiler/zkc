module

public import ZkcSecurity.Bindings.Gkr.Encoding
public import Zkc.Source.Structured.DomainModels
public import Zkc.Source.Structured.OpaqueRegistry

@[expose] public section

/-! Library-owned GKR relation entries. Source supplies a family identity,
ordered static arguments and logical selectors. These entries fix their
mathematics before a completeness or soundness method is selected.
-/

set_option autoImplicit false

namespace ZkcSecurity.Realizations.Gkr.Relations
open Zkc.Source Zkc.Source.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear

def residualInputs (domain : String) : List Ty :=
  [.vector domain, .vector domain, .vector domain, .vector domain,
    .vector domain, .field domain]

/-- Exact decoding makes malformed cubes and overlong prefixes false. The four
extensions remain independent before their gate expression is evaluated. -/
def Residual {F : Type} [CommRing F] (add mul left right point : List F) (claim : F) : Prop :=
  ∃ remaining : Nat,
    ∃ a m l r : Table F (remaining + point.length),
      ofList? _ add = some a ∧ ofList? _ mul = some m ∧
      ofList? _ left = some l ∧ ofList? _ right = some r ∧
      claim = booleanSum (fun bits =>
        let evaluationPoint := Quadratic.point point.length (coordinates point.length point)
          (fun i => if bits i then 1 else 0)
        extension _ a evaluationPoint *
          (extension _ l evaluationPoint + extension _ r evaluationPoint) +
          extension _ m evaluationPoint * extension _ l evaluationPoint *
            extension _ r evaluationPoint)

/-- Exact decoding determines both the remaining dimension and all four
factors. The existential presentation does not let evidence choose another
mathematical reference for the same raw arguments. -/
theorem residual_exact {F : Type} [CommRing F] {remaining : Nat}
    (add mul left right point : List F) (claim : F)
    (a m l r : Table F (remaining + point.length))
    (da : ofList? _ add = some a) (dm : ofList? _ mul = some m)
    (dl : ofList? _ left = some l) (dr : ofList? _ right = some r) :
    Residual add mul left right point claim ↔
      claim = booleanSum (fun bits =>
        let evaluationPoint := Quadratic.point point.length (coordinates point.length point)
          (fun i => if bits i then 1 else 0)
        extension _ a evaluationPoint *
          (extension _ l evaluationPoint + extension _ r evaluationPoint) +
          extension _ m evaluationPoint * extension _ l evaluationPoint *
            extension _ r evaluationPoint) := by
  constructor
  · rintro ⟨count, a', m', l', r', da', dm', dl', dr', correct⟩
    have dimensions : count + point.length = remaining + point.length :=
      Nat.pow_right_injective (by decide : 2 ≤ 2)
        ((ofList?_length add a' da').symm.trans (ofList?_length add a da))
    have same : count = remaining := Nat.add_right_cancel dimensions
    subst count
    have sameA := Option.some.inj (da'.symm.trans da)
    have sameM := Option.some.inj (dm'.symm.trans dm)
    have sameL := Option.some.inj (dl'.symm.trans dl)
    have sameR := Option.some.inj (dr'.symm.trans dr)
    subst a' m' l' r'
    exact correct
  · exact fun correct => ⟨remaining, a, m, l, r, da, dm, dl, dr, correct⟩

/-- The registered residual is precisely the sum of the independently
restricted factors. This law supplies the same reference to completeness and
adversarial soundness, including non-Boolean challenges and partial prefixes. -/
theorem residual_restricted {F : Type} [CommRing F] {remaining : Nat}
    (add mul left right point : List F) (claim : F)
    (a m l r : Table F (remaining + point.length))
    (da : ofList? _ add = some a) (dm : ofList? _ mul = some m)
    (dl : ofList? _ left = some l) (dr : ofList? _ right = some r) :
    Residual add mul left right point claim ↔
      claim = booleanSum (fun bits =>
        let fixed := coordinates point.length point
        fixPrefix point.length a fixed bits *
          (fixPrefix point.length l fixed bits + fixPrefix point.length r fixed bits) +
          fixPrefix point.length m fixed bits * fixPrefix point.length l fixed bits *
            fixPrefix point.length r fixed bits) := by
  rw [residual_exact add mul left right point claim a m l r da dm dl dr]
  have onBits (n : Nat) (table : Table F n) (bits : Fin n → Bool) :
      extension n table (fun i => if bits i then 1 else 0) = table bits :=
    extension_boolean n table bits
  simp only [← extension_fixPrefix, onBits]

/-- A missing cube cannot be repaired by choosing an existential dimension. -/
theorem residual_nonempty {F : Type} [CommRing F]
    {add mul left right point : List F} {claim : F}
    (valid : Residual add mul left right point claim) : 0 < add.length := by
  obtain ⟨remaining, a, _, _, _, da, _⟩ := valid
  rw [ofList?_length add a da]
  exact Nat.pow_pos (by decide)

theorem residual_prefix_le {F : Type} [CommRing F] {dimension : Nat}
    {add mul left right point : List F} {claim : F}
    (table : Table F dimension) (decoded : ofList? dimension add = some table)
    (valid : Residual add mul left right point claim) : point.length ≤ dimension := by
  obtain ⟨remaining, a, _, _, _, da, _⟩ := valid
  have dimensions : remaining + point.length = dimension :=
    Nat.pow_right_injective (by decide : 2 ≤ 2)
      ((ofList?_length add a da).symm.trans (ofList?_length add table decoded))
  omega

def residualMeaning (model : DomainModel) (domain : String) :
    Values model.Value (residualInputs domain) → Prop
  | .cons add (.cons mul (.cons left (.cons right (.cons point (.cons claim .nil))))) =>
      Residual add mul left right point claim

def residualFamily (model : DomainModel) : OpaqueFamily model.Value where
  identity := ⟨"gkr.rounds/0", "residual", "0"⟩
  instantiate
    | [.field domain] => some {
        inputs := residualInputs domain
        purposes := ["parameter", "parameter", "parameter", "parameter", "statement", "statement"]
        holds := residualMeaning model domain }
    | _ => none

def outputInputs (domain : String) : List Ty :=
  [.vector domain, .vector domain, .vector domain, .index, .index, .index, .vector domain]

def shapeInputs (domain : String) : List Ty :=
  [.vector domain, .vector domain, .vector domain, .vector domain, .index, .index, .index]

def outputMeaning (model : DomainModel) (domain : String) :
    Values model.Value (outputInputs domain) → Prop
  | .cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons outputs .nil)))))) =>
      (CircuitEncoding.mk inputs add mul layers selector width).Outputs outputs

def shapeMeaning (model : DomainModel) (domain : String) (maximumLayers maximumWidth : Nat) :
    Values model.Value (shapeInputs domain) → Prop
  | .cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil)))))) =>
      (CircuitEncoding.mk inputs add mul layers selector width).Admitted maximumLayers maximumWidth outputs

def outputFamily (model : DomainModel) : OpaqueFamily model.Value where
  identity := ⟨"gkr.circuit/0", "outputs", "0"⟩
  instantiate
    | [.field domain] => some {
        inputs := outputInputs domain
        purposes := ["parameter", "parameter", "parameter", "parameter", "parameter", "parameter", "statement"]
        holds := outputMeaning model domain }
    | _ => none

def shapeFamily (model : DomainModel) : OpaqueFamily model.Value where
  identity := ⟨"gkr.circuit/0", "shape", "0"⟩
  instantiate
    | [.field domain, .natural maximumLayers, .natural maximumWidth] => do
        let layers ← Zkc.Source.Format.canonicalDecimal maximumLayers
        let width ← Zkc.Source.Format.canonicalDecimal maximumWidth
        return {
          inputs := shapeInputs domain
          purposes := List.replicate 7 "parameter"
          holds := shapeMeaning model domain layers width }
    | _ => none

def registry (model : DomainModel) : OpaqueRegistry model.Value where
  families := [shapeFamily model, outputFamily model, residualFamily model]
  unique := by
    change ([⟨"gkr.circuit/0", "shape", "0"⟩,
      ⟨"gkr.circuit/0", "outputs", "0"⟩,
      ⟨"gkr.rounds/0", "residual", "0"⟩] : List OpaqueFamilyIdentity).Nodup
    decide +kernel

theorem output_exact (model : DomainModel) (domain : String)
    (inputs add mul outputs : List (model.Field domain)) (layers selector width : Nat) :
    outputMeaning model domain
      (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons outputs .nil))))))) ↔
      (CircuitEncoding.mk inputs add mul layers selector width).Outputs outputs := Iff.rfl

theorem shape_exact (model : DomainModel) (domain : String)
    (maximumLayers maximumWidth : Nat) (inputs outputs add mul : List (model.Field domain))
    (layers selector width : Nat) :
    shapeMeaning model domain maximumLayers maximumWidth
      (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil))))))) ↔
      (CircuitEncoding.mk inputs add mul layers selector width).Admitted maximumLayers maximumWidth outputs := Iff.rfl

end ZkcSecurity.Realizations.Gkr.Relations

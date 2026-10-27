module

public import ZkcSecurity.Realizations.Gkr.Encoding

@[expose] public section

/-! Exact representation of the registered circuit encoding. These laws use
only the fixed input policy and independent circuit mathematics. -/

namespace ZkcSecurity.Realizations.Gkr.Source
open Zkc.Source.Structured Zkc.Polynomial.Multilinear ZkcSecurity.Families.Gkr

variable {F : Type} [CommRing F]

structure Invocation (F : Type) where
  inputs : List F
  outputs : List F
  add : List F
  mul : List F
  layers : Nat
  selector : Nat
  width : Nat
  handle : Nat

namespace Invocation

def encoding (runtime : Invocation F) : CircuitEncoding F :=
  ⟨runtime.inputs, runtime.add, runtime.mul, runtime.layers, runtime.selector, runtime.width⟩

/-- The registered input policy concerns encoding and bounds, independently of
the circuit output claim and of every adversarial reply. -/
def Admitted (runtime : Invocation F) : Prop := runtime.encoding.Admitted 4 4 runtime.outputs

def Correct (runtime : Invocation F) : Prop := runtime.encoding.Outputs runtime.outputs

def outputTable (runtime : Invocation F) : Table F runtime.width :=
  (ofList? runtime.width runtime.outputs).getD 0

end Invocation

/-- Exactly the existing source-reading theorem's representation premises. -/
structure Represents {width : Nat} (circuit : Circuit F width) (layers : Nat) (outputs : Table F width)
    (runtime : Invocation F) : Prop where
  width_eq : runtime.width = width
  layers_eq : runtime.layers = layers
  inputsDecoded : ofList? width runtime.inputs = some circuit.inputs
  outputsDecoded : ofList? width runtime.outputs = some outputs
  addShape : runtime.add.length = 2 ^ runtime.selector * 2 ^ (width + width + width)
  mulShape : runtime.mul.length = 2 ^ runtime.selector * 2 ^ (width + width + width)
  addBound : runtime.add.length < indexLimit
  mulBound : runtime.mul.length < indexLimit
  addDecoded : ∀ layer < layers, ofList? (width + width + width)
    (CircuitEncoding.block runtime.add layer (2 ^ (width + width + width))) = some (circuit.add layer)
  mulDecoded : ∀ layer < layers, ofList? (width + width + width)
    (CircuitEncoding.block runtime.mul layer (2 ^ (width + width + width))) = some (circuit.mul layer)
  selectorBound : layers ≤ 2 ^ runtime.selector
  widthBound : width ≤ 4
  layersBound : layers ≤ 4

/-- Exact list decoding, including every used wiring block, follows from the
registered shape policy. No representation premise is supplied by evidence. -/
theorem admitted_represents (runtime : Invocation F) (admitted : runtime.Admitted) :
    Represents runtime.encoding.circuit runtime.layers runtime.outputTable runtime := by
  obtain ⟨shape, outputShape, widthBound, layersBound, dimensions⟩ := admitted
  have wiringBound : 2 ^ runtime.selector * 2 ^ (runtime.width + runtime.width + runtime.width) <
      indexLimit := by
    rw [← Nat.pow_add]
    change 2 ^ (runtime.selector + (runtime.width + runtime.width + runtime.width)) < 2 ^ 64
    exact Nat.pow_lt_pow_right (by decide)
      (by simpa only [Invocation.encoding, Nat.add_assoc] using dimensions)
  refine ⟨rfl, rfl, runtime.encoding.inputs_decode shape,
    CircuitEncoding.decode_getD runtime.outputs outputShape, shape.2.1, shape.2.2.1,
    shape.2.1 ▸ wiringBound, shape.2.2.1 ▸ wiringBound, ?_, ?_, shape.2.2.2,
    widthBound, layersBound⟩
  · intro layer inside
    exact runtime.encoding.add_decode shape layer inside
  · intro layer inside
    exact runtime.encoding.mul_decode shape layer inside

theorem admitted_correct_iff (runtime : Invocation F) (admitted : runtime.Admitted) :
    runtime.Correct ↔ runtime.outputTable = runtime.encoding.circuit.wires runtime.layers 0 := by
  have represented := admitted_represents runtime admitted
  constructor
  · intro correct
    exact Option.some.inj (represented.outputsDecoded.symm.trans correct.2)
  · intro correct
    exact ⟨admitted.1, correct ▸ represented.outputsDecoded⟩

/-- Representation cannot hide a malformed raw input, even when no layer is
executed. Its machine bounds imply the registered total selector dimension. -/
theorem represents_admitted {width : Nat} (circuit : Circuit F width) (layers : Nat)
    (outputs : Table F width) (runtime : Invocation F)
    (represented : Represents circuit layers outputs runtime) : runtime.Admitted := by
  have inputsShape := ofList?_length runtime.inputs circuit.inputs represented.inputsDecoded
  have outputsShape := ofList?_length runtime.outputs outputs represented.outputsDecoded
  have stackBound := represented.addBound
  rw [represented.addShape, ← Nat.pow_add] at stackBound
  have dimensions : runtime.selector + (width + width + width) < 64 := by
    by_contra outside
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_of_not_gt outside))) stackBound
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [Invocation.encoding, represented.width_eq] using inputsShape
  · simpa only [Invocation.encoding, represented.width_eq] using represented.addShape
  · simpa only [Invocation.encoding, represented.width_eq] using represented.mulShape
  · simpa only [Invocation.encoding, represented.layers_eq] using represented.selectorBound
  · simpa only [Invocation.encoding, represented.width_eq] using outputsShape
  · simpa only [Invocation.encoding, represented.width_eq] using represented.widthBound
  · simpa only [Invocation.encoding, represented.layers_eq] using represented.layersBound
  · simpa only [Invocation.encoding, represented.width_eq, Nat.add_assoc] using dimensions

theorem admitted_iff_represents (runtime : Invocation F) :
    runtime.Admitted ↔ Represents runtime.encoding.circuit runtime.layers runtime.outputTable runtime :=
  ⟨admitted_represents runtime,
    represents_admitted runtime.encoding.circuit runtime.layers runtime.outputTable runtime⟩

end ZkcSecurity.Realizations.Gkr.Source

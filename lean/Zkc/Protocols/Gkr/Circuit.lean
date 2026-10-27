module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Polynomial.Multilinear.Concat

@[expose] public section

/-! Layered arithmetic circuits of uniform width and the GKR layer identity.

A layer of width `w` has `2 ^ w` gates indexed by MSB-first Boolean points.
Gate `z` of a layer is computed from the layer below it through wiring tables
`add` and `mul` over the MSB-first coordinates `(z, x, y)`:

`W(z) = ∑ x y, add(z, x, y) (V(x) + V(y)) + mul(z, x, y) V(x) V(y)`,

where `V` is the layer below. The wiring tables are arbitrary field-valued
tables; those of a circuit hold 0 and 1, and a gate without wiring entries has
value zero. `values` evaluates the layers of a circuit from its inputs.

For every field point `r`, the extension of a layer at `r` is the Boolean sum
over `(x, y)` of the same expression with the wiring tables restricted at `r`
(`extension_layer`). This is the claim that the layer's Sumcheck reduces.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Gkr
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type}

/-- Wiring of a layer of width `w`, over `(z, x, y)`. -/
abbrev Wiring (F : Type) (w : Nat) := Table F (w + w + w)

section Tables
variable [CommRing F] {w : Nat}

/-- `V(x) + V(y)` over the Boolean pairs `(x, y)`. -/
def sumTable (below : Table F w) : Table F (w + w) :=
  fun pair => below (front w pair) + below (back w pair)

/-- `V(x) V(y)` over the Boolean pairs `(x, y)`. -/
def productTable (below : Table F w) : Table F (w + w) :=
  fun pair => below (front w pair) * below (back w pair)

/-- The table of a gate polynomial over `(x, y)`, from wiring tables restricted
at one gate: `add (V(x) + V(y)) + mul V(x) V(y)`. -/
def gates (add mul : Table F (w + w)) (below : Table F w) : Table F (w + w) :=
  fun pair => add pair * sumTable below pair + mul pair * productTable below pair

/-- The values of a layer from the values of the layer below it. -/
def layer (add mul : Wiring F w) (below : Table F w) : Table F w :=
  fun gate => booleanSum (gates (fun pair => add (Quadratic.point w gate pair))
    (fun pair => mul (Quadratic.point w gate pair)) below)

/-- The values of a circuit's layers. `values add mul inputs remaining index` is
the layer `index` of a circuit whose layers `index`, ..., `index + remaining - 1`
have wiring `add` and `mul` at their index and whose inputs are `inputs`: with
`layers` layers, layer `i ≤ layers` is `values add mul inputs (layers - i) i`
and the outputs are `values add mul inputs layers 0`. -/
def values (add mul : Nat → Wiring F w) (inputs : Table F w) : Nat → Nat → Table F w
  | 0, _ => inputs
  | remaining + 1, index => layer (add index) (mul index) (values add mul inputs remaining (index + 1))

theorem extension_scale_right {n : Nat} (table : Table F n) (c : F) (point : Fin n → F) :
    extension n (fun bits => table bits * c) point = extension n table point * c := by
  simp only [mul_comm _ c]
  exact extension_scale c table point

/-- The extension of the sum table at a concatenated point. -/
theorem extension_sumTable (below : Table F w) (left right : Fin w → F) :
    extension (w + w) (sumTable below) (Quadratic.point w left right) =
      extension w below left + extension w below right := by
  unfold sumTable
  rw [extension_add, extension_front, extension_back]

/-- The extension of the product table at a concatenated point. -/
theorem extension_productTable (below : Table F w) (left right : Fin w → F) :
    extension (w + w) (productTable below) (Quadratic.point w left right) =
      extension w below left * extension w below right :=
  extension_separable w below below left right

/-- The extension of a layer at any point is the Boolean sum of the gate
polynomial whose wiring is restricted at that point. -/
theorem extension_layer (add mul : Wiring F w) (below : Table F w) (point : Fin w → F) :
    extension w (layer add mul below) point =
      booleanSum (gates (fixPrefix w add point) (fixPrefix w mul point) below) := by
  unfold layer
  rw [extension_booleanSum]
  congr 1
  funext pair
  simp only [gates, fixPrefix_apply]
  rw [extension_add, extension_scale_right, extension_scale_right]

theorem values_succ (add mul : Nat → Wiring F w) (inputs : Table F w) (remaining index : Nat) :
    values add mul inputs (remaining + 1) index =
      layer (add index) (mul index) (values add mul inputs remaining (index + 1)) := rfl

end Tables

end Zkc.Protocols.Gkr

-- Materialize the unfolding equation in its defining module so joint imports
-- share one stored declaration instead of generating client-local proof copies.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Protocols.Gkr.values

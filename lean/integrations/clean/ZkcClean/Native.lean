import ZkcClean.Relation
import Zkc.Relation.AIR.RingExpression
import Lean.Data.Json.FromToJson

/-! Native presentation and emission of an exported artifact.

An artifact serializes constants as Clean's canonical naturals
(`FiniteField.val`). Native finite AIR and `zkc.ring/0` read a natural literal
as its residue in a prime field. That reading is correct only for a field whose
`FiniteField.fromNat` is `Nat.cast`; Clean's class also covers binary fields,
whose naturals encode polynomial coefficients instead. Emission therefore takes
an explicit `PrimePresentation`, and refuses any field without an installed
native identity.

The theorems compose the expression translation with the shared ring
substitution law (`Zkc.Relation.AIR.Expr.toRing_eval`) and state the meaning of
each emitted relation-arena output as a ring tree. They concern Lean terms. The
JSON emission below and the native C++/Rust readers are checked by the
maintained conformance tests, not proved: no native decoder theorem is claimed.
-/

set_option autoImplicit false

namespace ZkcClean

open Zkc.Relation Zkc.Algebra Lean

variable {F : Type} [FiniteField F]

/-! ## Ring substitution of the imported expressions -/

/-- The imported expression's shared ring tree evaluates to Clean's
`Expression.eval` on the row environment. -/
theorem export_ring {width : Nat} {e : Expression F} {t : Term}
    (exported : exportExpression width e = .ok t) :
    ∃ x, t.decode F width = some x ∧
      ∀ (statement : Fin 0 → F) (read : Nat × Fin width → F) (data : ProverData F),
        x.toRing.eval (Sum.elim statement read) =
          Expression.eval (rowEnvironment (fun column => read (0, column)) data) e := by
  obtain ⟨x, hx, eval⟩ := export_expression exported
  exact ⟨x, hx, fun statement read data => by rw [AIR.Expr.toRing_eval, eval]⟩

/-- Every imported assertion of an exported component, in order, has an
every-row scope and a ring tree equal to the corresponding upstream constraint. -/
theorem component_ring {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact)
    {cs : List (AIR.Constraint F 0 artifact.width)} (decoded : artifact.decode F = some cs) :
    List.Forall₂ (fun e (c : AIR.Constraint F 0 artifact.width) => c.scope = .every ∧
        ∀ (statement : Fin 0 → F) (read : Nat × Fin artifact.width → F) (data : ProverData F),
          c.expression.toRing.eval (Sum.elim statement read) =
            Expression.eval (rowEnvironment (fun column => read (0, column)) data) e)
      component.operations.constraints cs := by
  have admitted := exportComponent_ok exported
  unfold Artifact.decode at decoded
  rw [if_pos admitted.fieldSize_eq, admitted.assertions] at decoded
  refine (decodeAssertions_encode decoded).imp ?_
  rintro e c ⟨scope, hc⟩
  exact ⟨scope, fun statement read data => by
    rw [AIR.Expr.toRing_eval, eval_decode hc statement read data]⟩

/-! ## Prime-field presentation -/

/-- A native reading of Clean's canonical naturals: the field is the prime
field named `identity`, and every natural denotes its residue. -/
structure PrimePresentation (F : Type) [FiniteField F] where
  identity : String
  modulus : Nat
  size_eq : FiniteField.size F = modulus
  prime : modulus.Prime
  residue : ∀ n, (FiniteField.fromNat n : F) = (n : F)

/-- Clean's prime fields `F p` have the residue presentation. -/
def PrimePresentation.ofPrime (identity : String) (p : Nat) [Fact p.Prime] :
    PrimePresentation (_root_.F p) :=
  { identity, modulus := p, size_eq := rfl, prime := Fact.out, residue := fun _ => rfl }

theorem PrimePresentation.size_prime (presentation : PrimePresentation F) :
    (FiniteField.size F).Prime :=
  presentation.size_eq ▸ presentation.prime

/-- A Clean field whose size is not prime, such as a binary field `GF(2^k)`
with `k ≥ 2`, has no residue presentation and cannot be emitted. -/
theorem no_presentation_of_not_prime (notPrime : ¬ (FiniteField.size F).Prime) :
    PrimePresentation F → False :=
  fun presentation => notPrime presentation.size_prime

/-! ## The emitted relation arena as a ring tree -/

/-- The ring tree of one emitted relation-arena output: a literal denotes the
prime-subfield image of its natural and input `i` is column `i` of the row. -/
def Term.ring (F : Type) [NatCast F] : Term → RingExpression.Expr F Nat
  | .constant value => .constant (value : F)
  | .column index => .input index
  | .add left right => .add (left.ring F) (right.ring F)
  | .mul left right => .mul (left.ring F) (right.ring F)

/-- The relation arena's input assignment for one row: input `i` is column `i`. -/
def columns {width : Nat} (row : Fin width → F) (index : Nat) : F :=
  if h : index < width then row ⟨index, h⟩ else 0

theorem ring_decode (presentation : PrimePresentation F) {width : Nat} :
    ∀ {t : Term} {x : AIR.Expr F 0 width}, t.decode F width = some x →
      ∀ (statement : Fin 0 → F) (read : Nat × Fin width → F),
        (t.ring F).eval (fun index => if h : index < width then read (0, ⟨index, h⟩) else 0) =
          x.toRing.eval (Sum.elim statement read)
  | .constant value, x, h, statement, read => by
      unfold Term.decode at h
      split at h
      · cases h
        simp [Term.ring, AIR.Expr.toRing, RingExpression.Expr.eval, presentation.residue]
      · cases h
  | .column index, x, h, statement, read => by
      unfold Term.decode at h
      split at h
      · rename_i hindex
        cases h
        simp [Term.ring, AIR.Expr.toRing, RingExpression.Expr.eval, hindex]
      · cases h
  | .add left right, x, h, statement, read => by
      unfold Term.decode at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [Term.ring, AIR.Expr.toRing, RingExpression.Expr.eval]
        rw [ring_decode presentation hl statement read, ring_decode presentation hr statement read]
      · cases h
  | .mul left right, x, h, statement, read => by
      unfold Term.decode at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [Term.ring, AIR.Expr.toRing, RingExpression.Expr.eval]
        rw [ring_decode presentation hl statement read, ring_decode presentation hr statement read]
      · cases h

/-- Under the residue presentation, the emitted arena tree of an exported
expression evaluates to Clean's `Expression.eval` on the row. -/
theorem native_ring (presentation : PrimePresentation F) {width : Nat} {e : Expression F}
    {t : Term} (exported : exportExpression width e = .ok t) (row : Fin width → F)
    (data : ProverData F) :
    (t.ring F).eval (columns row) = Expression.eval (rowEnvironment row data) e := by
  obtain ⟨x, hx, eval⟩ := export_ring exported
  have := ring_decode presentation hx Fin.elim0 (fun cell => row cell.2)
  rw [eval Fin.elim0 (fun cell => row cell.2) data] at this
  exact this

/-- The outputs of an exported component's relation arena, in order, are the
upstream constraints under the residue presentation. -/
theorem component_native_ring (presentation : PrimePresentation F)
    {component : Air.Flat.Component F} {artifact : Artifact}
    (exported : exportComponent component = .ok artifact) :
    List.Forall₂ (fun e (t : Term) => ∀ (row : Fin component.width → F) (data : ProverData F),
        (t.ring F).eval (columns row) = Expression.eval (rowEnvironment row data) e)
      component.operations.constraints artifact.assertions := by
  have admitted := exportComponent_ok exported
  rw [admitted.assertions, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun e he =>
    native_ring presentation (exportExpression_of_bounded (admitted.bounded e he))

/-! ## Bounded emission -/

/-- Installed native prime fields. Any other presentation is refused rather
than mapped to an identity of the same size. -/
def nativePrimeFields : List (String × Nat) := [("koala-bear", 2130706433)]

inductive EmissionRefusal where
  | unsupportedPresentation (identity : String) (modulus : Nat)
  | fieldSize (presented artifact : Nat)
  | noncanonicalConstant (value : Nat)
  | columnOutOfRange (index : Nat)
  | limit (name : String)
  deriving DecidableEq, Repr

def Term.depth : Term → Nat
  | .constant _ | .column _ => 1
  | .add left right | .mul left right => max left.depth right.depth + 1

def Term.degree : Term → Nat
  | .constant _ => 0
  | .column _ => 1
  | .add left right => max left.degree right.degree
  | .mul left right => left.degree + right.degree

def Term.size : Term → Nat
  | .constant _ | .column _ => 1
  | .add left right | .mul left right => left.size + right.size + 1

/-- Every constant is canonical and every column is in range. -/
def Term.admit (modulus width : Nat) : Term → Except EmissionRefusal Unit
  | .constant value =>
      if value < modulus then .ok () else .error (.noncanonicalConstant value)
  | .column index => if index < width then .ok () else .error (.columnOutOfRange index)
  | .add left right | .mul left right => do
      left.admit modulus width
      right.admit modulus width

/-- Native finite-AIR and ring-arena limits, checked before building output. -/
def admitArtifact (presentation : PrimePresentation F) (artifact : Artifact) :
    Except EmissionRefusal Unit := do
  unless nativePrimeFields.contains (presentation.identity, presentation.modulus) do
    throw (.unsupportedPresentation presentation.identity presentation.modulus)
  unless artifact.fieldSize = presentation.modulus do
    throw (.fieldSize presentation.modulus artifact.fieldSize)
  unless artifact.width ≤ 65536 do throw (.limit "columns")
  unless artifact.assertions.length ≤ 4096 do throw (.limit "constraints")
  unless (artifact.assertions.map Term.size).sum ≤ 65536 do throw (.limit "nodes")
  for t in artifact.assertions do
    t.admit presentation.modulus artifact.width
    unless t.depth ≤ 64 do throw (.limit "depth")
    unless t.degree ≤ 1048576 do throw (.limit "degree")

/-- Post-order finite-AIR nodes of one assertion. Edges point backward and the
returned index is the root. -/
def Term.airNodes (nodes : Array Json) : Term → Array Json × Nat
  | .constant value =>
      (nodes.push (Json.mkObj [("op", "constant"), ("value", toString value)]), nodes.size)
  | .column index =>
      (nodes.push (Json.mkObj [("op", "read"), ("offset", toJson (0 : Nat)),
        ("column", toJson index)]), nodes.size)
  | .add left right =>
      let (nodes, lhs) := left.airNodes nodes
      let (nodes, rhs) := right.airNodes nodes
      (nodes.push (Json.mkObj [("op", "add"), ("lhs", toJson lhs), ("rhs", toJson rhs)]),
        nodes.size)
  | .mul left right =>
      let (nodes, lhs) := left.airNodes nodes
      let (nodes, rhs) := right.airNodes nodes
      (nodes.push (Json.mkObj [("op", "mul"), ("lhs", toJson lhs), ("rhs", toJson rhs)]),
        nodes.size)

/-- Post-order `zkc.ring/0` nodes appended to a shared arena. -/
def Term.ringNodes (field : String) (nodes : Array Json) : Term → Array Json × Nat
  | .constant value => (nodes.push (Json.arr #["constant", field, toString value]), nodes.size)
  | .column index => (nodes.push (Json.arr #["input", toJson index]), nodes.size)
  | .add left right =>
      let (nodes, lhs) := left.ringNodes field nodes
      let (nodes, rhs) := right.ringNodes field nodes
      (nodes.push (Json.arr #["add", toJson lhs, toJson rhs]), nodes.size)
  | .mul left right =>
      let (nodes, lhs) := left.ringNodes field nodes
      let (nodes, rhs) := right.ringNodes field nodes
      (nodes.push (Json.arr #["mul", toJson lhs, toJson rhs]), nodes.size)

/-- The native finite AIR (`zkc.air.v0`): every assertion applies to every row
and reads only the current row. There are no public inputs. -/
def emitRelation (presentation : PrimePresentation F) (artifact : Artifact) :
    Except EmissionRefusal Json := do
  admitArtifact presentation artifact
  let constraints := artifact.assertions.toArray.map fun t =>
    Json.mkObj [("scope", Json.mkObj [("kind", "every")]),
      ("nodes", Json.arr (t.airNodes #[]).1)]
  return Json.mkObj [("schema", "zkc.air.v0"), ("field", presentation.identity),
    ("columns", toJson artifact.width), ("public_inputs", toJson (0 : Nat)),
    ("constraints", Json.arr constraints)]

/-- One `zkc.ring/0` arena for the whole relation: input `i` binds column `i`
of the current row and output `j` is assertion `j`. -/
def emitArena (presentation : PrimePresentation F) (artifact : Artifact) :
    Except EmissionRefusal Json := do
  admitArtifact presentation artifact
  let (nodes, outputs) := artifact.assertions.foldl (init := (#[], #[]))
    fun (nodes, outputs) t =>
      let (nodes, root) := t.ringNodes presentation.identity nodes
      (nodes, outputs.push (toJson root))
  return Json.arr #["zkc.ring/0",
    Json.arr (Array.replicate artifact.width (Json.str presentation.identity)),
    Json.arr nodes, Json.arr outputs]

end ZkcClean

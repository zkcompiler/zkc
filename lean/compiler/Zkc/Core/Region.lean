module

public import Zkc.Core.Context
public import Zkc.Core.Process

public section

/-! Typed regions over a dialect.

A region is a sequence of operations that ends by returning values or by stopping. An
operation takes operands of the surrounding context and closed nested regions; its
results are bound in order, the last one the most recent. `Region.bind` composes a
lexical subcomputation with a shared suffix. Meanings are separate contracts.
-/

set_option autoImplicit false

namespace Zkc.Source

structure Dialect where
  Ty : Type
  Op : Type
  arguments : Op → List Ty
  results : Op → List Ty
  regions : Op → List (List Ty × List Ty)

mutual
  inductive Region (dialect : Dialect) : List dialect.Ty → List dialect.Ty → Type where
    | ret {Γ out} (values : Operands Γ out) : Region dialect Γ out
    | stop {Γ out} (reason : PIR.Stop) : Region dialect Γ out
    | letOp {Γ out} (op : dialect.Op) (arguments : Operands Γ (dialect.arguments op))
        (bodies : Regions dialect (dialect.regions op))
        (next : Region dialect (bindAll Γ (dialect.results op)) out) : Region dialect Γ out
    | bind {Γ mid out} (body : Region dialect Γ mid)
        (next : Region dialect (bindAll Γ mid) out) : Region dialect Γ out

  /-- Closed regions: each is typed in the context of its own inputs, bound in order. -/
  inductive Regions (dialect : Dialect) : List (List dialect.Ty × List dialect.Ty) → Type where
    | nil : Regions dialect []
    | cons {inputs outputs rest} (body : Region dialect (bindAll [] inputs) outputs)
        (tail : Regions dialect rest) : Regions dialect ((inputs, outputs) :: rest)
end

abbrev RegionFunction {Ty : Type} (Value : Ty → Type) (interface : PIR.Signature)
    (signature : List Ty × List Ty) :=
  Values Value signature.1 → PIR.Process interface (Values Value signature.2)

/-- The operation controls how, when and whether its region arguments execute. -/
structure RegionMeaning (dialect : Dialect) (interface : PIR.Signature) where
  Value : dialect.Ty → Type
  operation : (op : dialect.Op) → Values Value (dialect.arguments op) →
    Values (RegionFunction Value interface) (dialect.regions op) →
      PIR.Process interface (Values Value (dialect.results op))

variable {dialect : Dialect} {interface : PIR.Signature}

mutual
  @[expose] def Region.denote (meaning : RegionMeaning dialect interface) {Γ out} :
      Region dialect Γ out → Environment meaning.Value Γ →
        PIR.Process interface (Values meaning.Value out)
    | .ret values, env => .done (Operands.eval env values)
    | .stop reason, _ => .halt reason
    | .letOp op arguments bodies next, env =>
      (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind
        fun values => next.denote meaning (Environment.bindAll env values)
    | .bind body next, env =>
      (body.denote meaning env).bind fun values =>
        next.denote meaning (Environment.bindAll env values)

  @[expose] def Regions.denote (meaning : RegionMeaning dialect interface) {signatures} :
      Regions dialect signatures → Values (RegionFunction meaning.Value interface) signatures
    | .nil => .nil
    | .cons body tail =>
        .cons (fun values => body.denote meaning (Environment.ofValues values)) (tail.denote meaning)
end

/-! ## Outputs that are, by an equation, others

A step that maps the types of a region maps a list `first ++ second` of outputs to the map
of the list, where an operation asks for the maps of the two lists, appended. The two are
equal and not so by computation; the region is read at the other list. -/

/-- Values of types that are, by an equation, others. -/
@[expose] def Values.retype {Ty : Type} {Value : Ty → Type} {Γ Δ : List Ty} (same : Γ = Δ)
    (values : Values Value Γ) : Values Value Δ :=
  same ▸ values

theorem Values.retype_self {Ty : Type} {Value : Ty → Type} {Γ : List Ty} (same : Γ = Γ)
    (values : Values Value Γ) : values.retype same = values := rfl

/-- The first value stays, and the others are read at the equation of the tails. -/
theorem Values.retype_cons {Ty : Type} {Value : Ty → Type} {ty : Ty} {Γ Δ : List Ty}
    (same : ty :: Γ = ty :: Δ) (tail : Γ = Δ) (value : Value ty) (rest : Values Value Γ) :
    (Values.cons value rest).retype same = .cons value (rest.retype tail) := by
  subst tail
  rfl

/-- A region whose outputs are, by an equation, others. -/
@[expose] def Region.retype {out out' : List dialect.Ty} {Γ : List dialect.Ty} (same : out = out')
    (region : Region dialect Γ out) : Region dialect Γ out' :=
  same ▸ region

/-- The region read at other outputs returns its values, read at them. -/
theorem Region.denote_retype (meaning : RegionMeaning dialect interface)
    {out out' : List dialect.Ty} {Γ : List dialect.Ty} (same : out = out')
    (region : Region dialect Γ out) (env : Environment meaning.Value Γ) :
    (region.retype same).denote meaning env =
      (region.denote meaning env).bind fun values => .done (values.retype same) := by
  subst same
  exact (PIR.Process.bind_done _).symm

end Zkc.Source

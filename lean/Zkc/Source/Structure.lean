module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import Zkc.Source.ContextOperations
public import Zkc.Semantics.Interaction

@[expose] public section

/-! Typed structural foundation for local compiler programs.

Operation callbacks are closed over their declared inputs; operations pass captures
explicitly. Results are ordered lists, including the empty list. `Region.bind`
composes a lexical subcomputation with a shared suffix. Operation binding already
shares the suffix of its callbacks. Meanings are separate contracts.
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
        (next : Region dialect (dialect.results op ++ Γ) out) : Region dialect Γ out
    | bind {Γ mid out} (body : Region dialect Γ mid)
        (next : Region dialect (mid ++ Γ) out) : Region dialect Γ out

  inductive Regions (dialect : Dialect) : List (List dialect.Ty × List dialect.Ty) → Type where
    | nil : Regions dialect []
    | cons {inputs outputs rest} (body : Region dialect inputs outputs)
        (tail : Regions dialect rest) : Regions dialect ((inputs, outputs) :: rest)
end

abbrev RegionFunction {Ty : Type} (Value : Ty → Type) (interface : PIR.Signature)
    (signature : List Ty × List Ty) :=
  Values Value signature.1 → PIR.Proc interface (Values Value signature.2)

/-- The operation controls how, when and whether its region arguments execute. -/
structure RegionMeaning (dialect : Dialect) (interface : PIR.Signature) where
  Value : dialect.Ty → Type
  operation : (op : dialect.Op) → Values Value (dialect.arguments op) →
    Values (RegionFunction Value interface) (dialect.regions op) →
      PIR.Proc interface (Values Value (dialect.results op))

variable {dialect : Dialect} {interface : PIR.Signature}

mutual
  def Region.denote (meaning : RegionMeaning dialect interface) {Γ out} :
      Region dialect Γ out → Environment meaning.Value Γ →
        PIR.Proc interface (Values meaning.Value out)
    | .ret values, env => .done (Operands.eval env values)
    | .stop reason, _ => .halt reason
    | .letOp op arguments bodies next, env =>
      (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind
        fun values => next.denote meaning (env.prepend values)
    | .bind body next, env =>
      (body.denote meaning env).bind fun values => next.denote meaning (env.prepend values)

  def Regions.denote (meaning : RegionMeaning dialect interface) {signatures} :
      Regions dialect signatures → Values (RegionFunction meaning.Value interface) signatures
    | .nil => .nil
    | .cons body tail => .cons (fun values => body.denote meaning values.get) (tail.denote meaning)
end

mutual
  /-- Count structural nodes, not execution work: an operation may repeat a callback. -/
  def Region.nodeCount {Γ out} : Region dialect Γ out → Nat
    | .ret _ | .stop _ => 1
    | .letOp _ _ bodies next => 1 + bodies.nodeCount + next.nodeCount
    | .bind body next => 1 + body.nodeCount + next.nodeCount

  def Regions.nodeCount {signatures} : Regions dialect signatures → Nat
    | .nil => 0
    | .cons body tail => body.nodeCount + tail.nodeCount
end

/-- Closed nested regions are unchanged when the caller's operands are renamed. -/
def Region.rename {Γ Δ out} (rename : Renaming Γ Δ) :
    Region dialect Γ out → Region dialect Δ out
  | .ret values => .ret (Operands.rename rename values)
  | .stop reason => .stop reason
  | .letOp op arguments bodies next =>
    .letOp op (Operands.rename rename arguments) bodies
      (next.rename (Renaming.liftPrefix (dialect.results op) rename))
  | .bind (mid := mid) body next =>
    .bind (body.rename rename) (next.rename (Renaming.liftPrefix mid rename))

theorem Region.denote_rename (meaning : RegionMeaning dialect interface)
    {Γ Δ out} (region : Region dialect Γ out) (rename : Renaming Γ Δ)
    (env : Environment meaning.Value Δ) :
    (region.rename rename).denote meaning env =
      region.denote meaning (fun value => env (rename value)) := by
  cases region with
  | ret values => exact congrArg PIR.Proc.done (Operands.eval_rename rename env values)
  | stop reason => rfl
  | letOp op arguments bodies next =>
    simp only [Region.rename, denote, Operands.eval_rename]
    congr 1
    funext values
    rw [denote_rename, Environment.prepend_rename]
  | bind body next =>
    simp only [Region.rename, denote, denote_rename meaning body]
    congr 1
    funext values
    rw [denote_rename, Environment.prepend_rename]

termination_by sizeOf region

end Zkc.Source

-- Materialize shared unfolding equations in their defining module. Otherwise
-- separate clients can generate the same public equation name with different
-- private proof helpers, leaving its stored provider ambiguous to an audit.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Source.Regions.denote

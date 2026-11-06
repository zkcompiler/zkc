module

public import Zkc.Source.DerivationLaws

@[expose] public section

/-! Residual action forms over the existing Process, for a fixed value/effect algebra.
The source Region performs pure substitution and retains each effect continuation.
The certificate is assembled from operation laws and callback derivations. There is
no independent source evaluator and no whole-region equation accepted as evidence.
The more specialized symbolic Form presentation remains an ordinary-value consumer. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.NormalForm
open Zkc.Source

structure ActionForm {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) {inputs outputs : List dialect.Ty}
    (body : Region dialect inputs outputs) (environment : Environment meaning.Value inputs) where
  process : PIR.Process I (Values meaning.Value outputs)
  derivation : Region.Derivation meaning (fun action ↦ .call action .done)
    body environment process

/-- A local normalizer must justify each operation on every already-derived callback.
This is an operation law, never an equation for an entire source body. -/
structure ActionRules {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) where
  operation : (op : dialect.Op) → Values meaning.Value (dialect.arguments op) →
    Values (RegionFunction meaning.Value I) (dialect.regions op) →
      PIR.Process I (Values meaning.Value (dialect.results op))
  law : ∀ op args callbacks, meaning.OperationLaw (fun action ↦ .call action .done)
    op args callbacks (operation op args callbacks)

/-- Residualize an action using its actual meaning. Pure returns reduce through Process.bind;
stops discard only their unreachable continuation, and requests retain their continuation. -/
def ActionRules.residual {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) : ActionRules meaning where
  operation := meaning.operation
  law op args callbacks := RegionMeaning.OperationLaw.identity op args callbacks rfl

structure CallbackForms {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) {signatures}
    (bodies : Regions dialect signatures) where
  callbacks : Values (RegionFunction meaning.Value I) signatures
  derivation : Regions.Derivation meaning (fun action ↦ .call action .done) bodies callbacks

mutual
  /-- Compose the per-action laws along the existing Region spine. Every returned tuple,
  including an empty one, enters the next source environment. No operand is materialized. -/
  def normalizeWith {dialect : Dialect} {I : PIR.Signature}
      (meaning : RegionMeaning dialect I) (rules : ActionRules meaning) :
      {inputs outputs : List dialect.Ty} → (body : Region dialect inputs outputs) →
      (environment : Environment meaning.Value inputs) → ActionForm meaning body environment
    | _, _, .ret refs, env => ⟨.done (Operands.eval env refs), .ret refs env⟩
    | _, _, .stop reason, env => ⟨.halt reason, .stop reason env⟩
    | _, _, .bind body next, env =>
      let first := normalizeWith meaning rules body env
      let suffix := fun values ↦ normalizeWith meaning rules next (env.prepend values)
      ⟨first.process.bind (fun values ↦ (suffix values).process),
        .bind first.derivation (fun values ↦ (suffix values).derivation)⟩
    | _, _, .letOp op args bodies next, env =>
      let callbacks := normalizeCallbacks meaning rules bodies
      let suffix := fun values ↦ normalizeWith meaning rules next (env.prepend values)
      ⟨(rules.operation op (Operands.eval env args) callbacks.callbacks).bind
          (fun values ↦ (suffix values).process),
        .letOp op args callbacks.derivation (rules.law op _ _)
          (fun values ↦ (suffix values).derivation)⟩

  def normalizeCallbacks {dialect : Dialect} {I : PIR.Signature}
      (meaning : RegionMeaning dialect I) (rules : ActionRules meaning) :
      {signatures : List (List dialect.Ty × List dialect.Ty)} →
      (bodies : Regions dialect signatures) → CallbackForms meaning bodies
    | _, .nil => ⟨.nil, .nil⟩
    | _, .cons body rest =>
      let first := fun values ↦ normalizeWith meaning rules body values.get
      let tail := normalizeCallbacks meaning rules rest
      ⟨.cons (fun values ↦ (first values).process) tail.callbacks,
        .cons (fun values ↦ (first values).derivation) tail.derivation⟩
end

/-- Generic residual action normalization; specialized algebras supply the local actions. -/
def normalizeActions {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) {inputs outputs : List dialect.Ty}
    (body : Region dialect inputs outputs) (environment : Environment meaning.Value inputs) :
    ActionForm meaning body environment :=
  normalizeWith meaning (.residual meaning) body environment

theorem ActionForm.sound {dialect : Dialect} {I : PIR.Signature}
    {meaning : RegionMeaning dialect I} {inputs outputs : List dialect.Ty}
    {body : Region dialect inputs outputs} {environment : Environment meaning.Value inputs}
    (form : ActionForm meaning body environment) :
    body.denote meaning environment = form.process := form.derivation.sound_identity

@[simp] theorem normalizeActions_process {dialect : Dialect} {I : PIR.Signature}
    (meaning : RegionMeaning dialect I) {inputs outputs : List dialect.Ty}
    (body : Region dialect inputs outputs) (environment : Environment meaning.Value inputs) :
    (normalizeActions meaning body environment).process = body.denote meaning environment :=
  (normalizeActions meaning body environment).sound.symm

/-- Includes the provider's post-state and the exact ordered event list on every stop. -/
theorem ActionForm.run {dialect : Dialect} {I : PIR.Signature}
    {meaning : RegionMeaning dialect I} {inputs outputs : List dialect.Ty}
    {body : Region dialect inputs outputs} {environment : Environment meaning.Value inputs}
    (form : ActionForm meaning body environment) {S E : Type}
    (handler : PIR.Handler I S E) (state : S) :
    form.process.run handler state = (body.denote meaning environment).run handler state := by
  rw [form.sound]

end Zkc.Source.Structured.NormalForm

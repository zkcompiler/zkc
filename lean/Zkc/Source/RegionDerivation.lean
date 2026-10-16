module

public import Zkc.Source.RegionInterpretation

@[expose] public section

/-! Occurrence-local proof construction over the existing typed `Region`.

The indices fix the source, environment and target process before a proof is
constructed. There is no constructor taking a whole-region semantic equation.
Only an operation occurrence may supply a semantic law, after its callbacks
have themselves been derived for every declared input. Effects are interpreted
using the existing `PIR.Proc.interpret`; no second program evaluator is defined.
-/

set_option autoImplicit false
namespace Zkc.Source

variable {dialect : Dialect} {I J : PIR.Signature}

/-- A local obligation at one operation occurrence and its actual operands.
The law must work for every source callback tuple whose exact pointwise
translation is the derived target tuple. An arbitrary predicate on callbacks
would not justify this substitution: operations can inspect process shape. -/
def RegionMeaning.OperationLaw (meaning : RegionMeaning dialect I)
    (operations : PIR.OperationInterpretation I J) (op : dialect.Op)
    (args : Values meaning.Value (dialect.arguments op))
    (callbacks : Values (RegionFunction meaning.Value J) (dialect.regions op))
    (target : PIR.Proc J (Values meaning.Value (dialect.results op))) : Prop :=
  ∀ bodies, RegionFunctions.translate operations bodies = callbacks →
    (meaning.operation op args bodies).interpret operations = target

/-- Uniform translation is one reusable source of local laws. The equation can
specialize the translated operation differently at each occurrence. -/
theorem RegionMeaning.OperationLaw.ofTranslation
    {meaning : RegionMeaning dialect I} {operations : PIR.OperationInterpretation I J}
    (translation : meaning.Translation operations) (op : dialect.Op)
    (args : Values meaning.Value (dialect.arguments op))
    (callbacks : Values (RegionFunction meaning.Value J) (dialect.regions op))
    {target : PIR.Proc J (Values meaning.Value (dialect.results op))}
    (equation : translation.operation op args callbacks = target) :
    meaning.OperationLaw operations op args callbacks target := by
  intro bodies same
  rw [← translation.commutes, same]
  exact equation

mutual
  /-- Proof syntax indexed by the exact existing source and semantic conclusion.
  Local facts may be supplied by the enclosing theorem at the indexed environment.
  Every suffix uses the actual ordered returned tuple. Immediate-return rules
  retain facts about that tuple; immediate-stop rules need no suffix proof. -/
  inductive Region.Derivation (meaning : RegionMeaning dialect I)
      (operations : PIR.OperationInterpretation I J) :
      {Γ out : List dialect.Ty} → Region dialect Γ out →
      Environment meaning.Value Γ → PIR.Proc J (Values meaning.Value out) → Prop where
    | ret {Γ out} (refs : Operands Γ out) (env : Environment meaning.Value Γ) :
        Region.Derivation meaning operations (.ret refs) (@env) (.done (Operands.eval env refs))
    | stop {Γ out} (reason : PIR.Stop) (env : Environment meaning.Value Γ) :
        Region.Derivation meaning operations (Region.stop (out := out) reason) (@env) (.halt reason)
    | bind {Γ mid out} {body : Region dialect Γ mid}
        {next : Region dialect (mid ++ Γ) out} {env : Environment meaning.Value Γ}
        {first : PIR.Proc J (Values meaning.Value mid)}
        {suffix : Values meaning.Value mid → PIR.Proc J (Values meaning.Value out)}
        (bodyLaw : Region.Derivation meaning operations body (@env) first)
        (nextLaw : ∀ values, Region.Derivation meaning operations next (env.prepend values) (suffix values)) :
        Region.Derivation meaning operations (.bind body next) (@env) (first.bind suffix)
    | bindReturn {Γ mid out} {body : Region dialect Γ mid}
        {next : Region dialect (mid ++ Γ) out} {env : Environment meaning.Value Γ}
        {values : Values meaning.Value mid} {target : PIR.Proc J (Values meaning.Value out)}
        (bodyLaw : Region.Derivation meaning operations body (@env) (.done values))
        (nextLaw : Region.Derivation meaning operations next (env.prepend values) target) :
        Region.Derivation meaning operations (.bind body next) (@env) target
    | bindStop {Γ mid out} {body : Region dialect Γ mid}
        (next : Region dialect (mid ++ Γ) out) {env : Environment meaning.Value Γ}
        {reason : PIR.Stop}
        (bodyLaw : Region.Derivation meaning operations body (@env) (.halt reason)) :
        Region.Derivation meaning operations (.bind body next) (@env) (.halt reason)
    | letOp {Γ out} (op : dialect.Op) (args : Operands Γ (dialect.arguments op))
        {bodies : Regions dialect (dialect.regions op)}
        {next : Region dialect (dialect.results op ++ Γ) out}
        {env : Environment meaning.Value Γ}
        {callbacks : Values (RegionFunction meaning.Value J) (dialect.regions op)}
        {step : PIR.Proc J (Values meaning.Value (dialect.results op))}
        {suffix : Values meaning.Value (dialect.results op) → PIR.Proc J (Values meaning.Value out)}
        (callbackLaws : Regions.Derivation meaning operations bodies callbacks)
        (operationLaw : meaning.OperationLaw operations op (Operands.eval env args) callbacks step)
        (nextLaw : ∀ values, Region.Derivation meaning operations next (env.prepend values) (suffix values)) :
        Region.Derivation meaning operations (.letOp op args bodies next) (@env) (step.bind suffix)
    | letOpReturn {Γ out} (op : dialect.Op) (args : Operands Γ (dialect.arguments op))
        {bodies : Regions dialect (dialect.regions op)}
        {next : Region dialect (dialect.results op ++ Γ) out}
        {env : Environment meaning.Value Γ}
        {callbacks : Values (RegionFunction meaning.Value J) (dialect.regions op)}
        {values : Values meaning.Value (dialect.results op)}
        {target : PIR.Proc J (Values meaning.Value out)}
        (callbackLaws : Regions.Derivation meaning operations bodies callbacks)
        (operationLaw : meaning.OperationLaw operations op (Operands.eval env args) callbacks (.done values))
        (nextLaw : Region.Derivation meaning operations next (env.prepend values) target) :
        Region.Derivation meaning operations (.letOp op args bodies next) (@env) target
    | letOpStop {Γ out} (op : dialect.Op) (args : Operands Γ (dialect.arguments op))
        {bodies : Regions dialect (dialect.regions op)}
        (next : Region dialect (dialect.results op ++ Γ) out)
        {env : Environment meaning.Value Γ}
        {callbacks : Values (RegionFunction meaning.Value J) (dialect.regions op)}
        {reason : PIR.Stop}
        (callbackLaws : Regions.Derivation meaning operations bodies callbacks)
        (operationLaw : meaning.OperationLaw operations op (Operands.eval env args) callbacks (.halt reason)) :
        Region.Derivation meaning operations (.letOp op args bodies next) (@env) (.halt reason)

  /-- Callback evidence covers all declared inputs, including values an operation
  might supply on a later invocation. Captures remain explicit source operands. -/
  inductive Regions.Derivation (meaning : RegionMeaning dialect I)
      (operations : PIR.OperationInterpretation I J) :
      {signatures : List (List dialect.Ty × List dialect.Ty)} → Regions dialect signatures →
      Values (RegionFunction meaning.Value J) signatures → Prop where
    | nil : Regions.Derivation meaning operations .nil .nil
    | cons {inputs outputs rest} {body : Region dialect inputs outputs}
        {tail : Regions dialect rest} {callback : RegionFunction meaning.Value J (inputs, outputs)}
        {callbacks : Values (RegionFunction meaning.Value J) rest}
        (bodyLaw : ∀ values, Region.Derivation meaning operations body values.get (callback values))
        (tailLaw : Regions.Derivation meaning operations tail callbacks) :
        Regions.Derivation meaning operations (.cons body tail) (.cons callback callbacks)
end

/-- The complete process equation is an output of structural proof construction. -/
theorem Region.Derivation.sound {meaning : RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} {Γ out}
    {body : Region dialect Γ out} {env : Environment meaning.Value Γ}
    {target : PIR.Proc J (Values meaning.Value out)}
    (derivation : Region.Derivation meaning operations body (@env) target) :
    (body.denote meaning env).interpret operations = target := by
  induction derivation using Region.Derivation.rec
      (motive_2 := fun {_} bodies callbacks _ =>
        RegionFunctions.translate operations (bodies.denote meaning) = callbacks) with
  | ret => rfl
  | stop => rfl
  | bind bodyLaw nextLaw bodyIH nextIH =>
      simp only [Region.denote, PIR.Proc.interpret_bind, bodyIH]
      congr 1
      funext values
      exact nextIH values
  | bindReturn bodyLaw nextLaw bodyIH nextIH =>
      simpa only [Region.denote, PIR.Proc.interpret_bind, bodyIH, PIR.Proc.bind] using nextIH
  | bindStop next bodyLaw bodyIH =>
      simp only [Region.denote, PIR.Proc.interpret_bind, bodyIH, PIR.Proc.bind]
  | letOp op args callbackLaws operationLaw nextLaw callbacksIH nextIH =>
      simp only [Region.denote, PIR.Proc.interpret_bind, operationLaw _ callbacksIH]
      congr 1
      funext values
      exact nextIH values
  | letOpReturn op args callbackLaws operationLaw nextLaw callbacksIH nextIH =>
      simpa only [Region.denote, PIR.Proc.interpret_bind,
        operationLaw _ callbacksIH, PIR.Proc.bind] using nextIH
  | letOpStop op args next callbackLaws operationLaw callbacksIH =>
      simp only [Region.denote, PIR.Proc.interpret_bind, operationLaw _ callbacksIH, PIR.Proc.bind]
  | nil => rfl
  | cons bodyLaw tailLaw bodyIH tailIH =>
      simp only [Regions.denote, RegionFunctions.translate, tailIH]
      congr 1
      funext values
      exact bodyIH values

/-- Export the pointwise callback equation for use by other local semantic laws. -/
theorem Regions.Derivation.sound {meaning : RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} {signatures}
    {bodies : Regions dialect signatures}
    {callbacks : Values (RegionFunction meaning.Value J) signatures}
    (derivation : Regions.Derivation meaning operations bodies callbacks) :
    RegionFunctions.translate operations (bodies.denote meaning) = callbacks := by
  cases derivation with
  | nil => rfl
  | cons bodyLaw tailLaw =>
      simp only [Regions.denote, RegionFunctions.translate, tailLaw.sound]
      congr 1
      funext values
      exact (bodyLaw values).sound
termination_by sizeOf bodies
decreasing_by all_goals subst_vars; all_goals simp_all; all_goals omega

/-- Same-interface normalization needs no separate evaluator or equality record. -/
theorem Region.Derivation.sound_identity {meaning : RegionMeaning dialect I} {Γ out}
    {body : Region dialect Γ out} {env : Environment meaning.Value Γ}
    {target : PIR.Proc I (Values meaning.Value out)}
    (derivation : Region.Derivation meaning (fun op => .call op .done) body (@env) target) :
    body.denote meaning env = target := by
  simpa only [PIR.Proc.interpret_identity] using derivation.sound

/-- Equality retains all returned values, stopped post-states and ordered events,
including effects introduced by the operation interpretation. -/
theorem Region.Derivation.run {meaning : RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} {Γ out}
    {body : Region dialect Γ out} {env : Environment meaning.Value Γ}
    {target : PIR.Proc J (Values meaning.Value out)}
    (derivation : Region.Derivation meaning operations body (@env) target)
    {S E : Type} (backend : PIR.Handler J S E) (state : S) :
    target.run backend state =
      (body.denote meaning env).run (fun op s => (operations op).run backend s) state := by
  rw [← derivation.sound, PIR.Proc.run_interpret]

/-- Existing per-effect state/observation simulation composes with the derived
process equation. The local handler law is separate from structural construction. -/
theorem Region.Derivation.run_related {meaning : RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} {Γ out}
    {body : Region dialect Γ out} {env : Environment meaning.Value Γ}
    {target : PIR.Proc J (Values meaning.Value out)}
    (derivation : Region.Derivation meaning operations body (@env) target)
    {S T E F O : Type} (sourceHandler : PIR.Handler I S E) (targetHandler : PIR.Handler J T F)
    (relation : S → T → Prop) (left : E → List O) (right : F → List O)
    (law : ∀ op s t, relation s t → PIR.Related relation left right (sourceHandler op s)
      ((operations op).run targetHandler t))
    (s : S) (t : T) (initial : relation s t) :
    PIR.Related relation left right ((body.denote meaning env).run sourceHandler s)
      (target.run targetHandler t) := by
  rw [← derivation.sound]
  exact PIR.Proc.run_interpret_related operations sourceHandler targetHandler
    relation left right law _ s t initial

end Zkc.Source

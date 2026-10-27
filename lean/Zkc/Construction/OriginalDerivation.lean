module

public import Zkc.Source.RegionDerivation
public import Zkc.Construction.OriginalFold

@[expose] public section

/-! Stateful region certificates for original-derived construction views.
The source region and environment are indices. Only individual operation
occurrences accept local semantic laws; there is no whole-region equation
constructor. Callback laws quantify all inputs and all construction states.
This extends the existing Region.Derivation pattern to the stateful fold.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source

variable {dialect : Dialect} {I J : PIR.Signature} {S : Type}

abbrev StatefulCallback (Value : dialect.Ty → Type) (J : PIR.Signature) (S : Type)
    (signature : List dialect.Ty × List dialect.Ty) :=
  Values Value signature.1 → S → PIR.Process J (Values Value signature.2 × S)

def translateCallbacks {Value : dialect.Ty → Type}
    (operations : PIR.StateOperationInterpretation I J S) {signatures} :
    Values (RegionFunction Value I) signatures → Values (StatefulCallback Value J S) signatures
  | .nil => .nil
  | .cons body tail =>
      .cons (fun args state => (body args).interpretState operations state)
        (translateCallbacks operations tail)

/-- As in Region.Derivation, local operations may not silently assume callback
extensionality. The law covers every body tuple with this exact translation. -/
def OperationLaw (meaning : RegionMeaning dialect I)
    (operations : PIR.StateOperationInterpretation I J S) (op : dialect.Op)
    (args : Values meaning.Value (dialect.arguments op))
    (callbacks : Values (StatefulCallback meaning.Value J S) (dialect.regions op))
    (state : S) (target : PIR.Process J (Values meaning.Value (dialect.results op) × S)) : Prop :=
  ∀ bodies, translateCallbacks operations bodies = callbacks →
    (meaning.operation op args bodies).interpretState operations state = target

mutual
  inductive RegionDerivation (meaning : RegionMeaning dialect I)
      (operations : PIR.StateOperationInterpretation I J S) :
      {Γ out : List dialect.Ty} → Region dialect Γ out → Environment meaning.Value Γ →
        S → PIR.Process J (Values meaning.Value out × S) → Prop where
    | ret {Γ out} (refs : Operands Γ out) (env : Environment meaning.Value Γ) (state : S) :
        RegionDerivation meaning operations (.ret refs) (@env) state
          (.done (Operands.eval env refs, state))
    | stop {Γ out} (reason : PIR.Stop) (env : Environment meaning.Value Γ) (state : S) :
        RegionDerivation meaning operations (Region.stop (out := out) reason) (@env) state (.halt reason)
    | bind {Γ mid out} {body : Region dialect Γ mid} {next : Region dialect (mid ++ Γ) out}
        {env : Environment meaning.Value Γ} {state : S}
        {first : PIR.Process J (Values meaning.Value mid × S)}
        {suffix : Values meaning.Value mid × S → PIR.Process J (Values meaning.Value out × S)}
        (head : RegionDerivation meaning operations body (@env) state first)
        (tail : ∀ values final,
          RegionDerivation meaning operations next (env.prepend values) final (suffix (values, final))) :
        RegionDerivation meaning operations (.bind body next) (@env) state (first.bind suffix)
    | letOp {Γ out} (op : dialect.Op) (args : Operands Γ (dialect.arguments op))
        {bodies : Regions dialect (dialect.regions op)}
        {next : Region dialect (dialect.results op ++ Γ) out}
        {env : Environment meaning.Value Γ} {state : S}
        {callbacks : Values (StatefulCallback meaning.Value J S) (dialect.regions op)}
        {first : PIR.Process J (Values meaning.Value (dialect.results op) × S)}
        {suffix : Values meaning.Value (dialect.results op) × S →
          PIR.Process J (Values meaning.Value out × S)}
        (bodiesLaw : RegionsDerivation meaning operations bodies callbacks)
        (operationLaw : OperationLaw meaning operations op (Operands.eval env args) callbacks state first)
        (tail : ∀ values final,
          RegionDerivation meaning operations next (env.prepend values) final (suffix (values, final))) :
        RegionDerivation meaning operations (.letOp op args bodies next) (@env) state (first.bind suffix)

  inductive RegionsDerivation (meaning : RegionMeaning dialect I)
      (operations : PIR.StateOperationInterpretation I J S) :
      {signatures : List (List dialect.Ty × List dialect.Ty)} → Regions dialect signatures →
        Values (StatefulCallback meaning.Value J S) signatures → Prop where
    | nil : RegionsDerivation meaning operations .nil .nil
    | cons {inputs outputs rest} {body : Region dialect inputs outputs}
        {tail : Regions dialect rest} {callback : StatefulCallback meaning.Value J S (inputs, outputs)}
        {callbacks : Values (StatefulCallback meaning.Value J S) rest}
        (head : ∀ values state, RegionDerivation meaning operations body values.get state (callback values state))
        (tailLaw : RegionsDerivation meaning operations tail callbacks) :
        RegionsDerivation meaning operations (.cons body tail) (.cons callback callbacks)
end

/-- A complete state-threaded source equation is a theorem of the certificate. -/
theorem RegionDerivation.sound {meaning : RegionMeaning dialect I}
    {operations : PIR.StateOperationInterpretation I J S} {Γ out}
    {body : Region dialect Γ out} {env : Environment meaning.Value Γ} {state : S}
    {target : PIR.Process J (Values meaning.Value out × S)}
    (derivation : RegionDerivation meaning operations body (@env) state target) :
    (body.denote meaning env).interpretState operations state = target := by
  induction derivation using RegionDerivation.rec
      (motive_2 := fun {_} bodies callbacks _ =>
        translateCallbacks operations (bodies.denote meaning) = callbacks) with
  | ret => rfl
  | stop => rfl
  | bind head tail headIH tailIH =>
      simp only [Region.denote, PIR.Process.interpretState_bind, headIH]
      congr 1
      funext pair
      exact tailIH pair.1 pair.2
  | letOp op args bodiesLaw operationLaw tail bodiesIH tailIH =>
      simp only [Region.denote, PIR.Process.interpretState_bind, operationLaw _ bodiesIH]
      congr 1
      funext pair
      exact tailIH pair.1 pair.2
  | nil => rfl
  | cons head tailLaw headIH tailIH =>
      simp only [Regions.denote, translateCallbacks, tailIH]
      congr 1
      funext values state
      exact headIH values state

/-- Both the source callback ABI and the state parameter are universally covered. -/
theorem RegionsDerivation.sound {meaning : RegionMeaning dialect I}
    {operations : PIR.StateOperationInterpretation I J S} {signatures}
    {bodies : Regions dialect signatures}
    {callbacks : Values (StatefulCallback meaning.Value J S) signatures}
    (derivation : RegionsDerivation meaning operations bodies callbacks) :
    translateCallbacks operations (bodies.denote meaning) = callbacks := by
  cases derivation with
  | nil => rfl
  | cons head tailLaw =>
      simp only [Regions.denote, translateCallbacks, tailLaw.sound]
      congr 1
      funext values state
      exact (head values state).sound
termination_by sizeOf bodies
decreasing_by all_goals subst_vars; all_goals simp_all

end Zkc.Construction.Original

module

public import Zkc.Source.RegionDerivation

@[expose] public section

namespace Zkc.Source

variable {dialect : Dialect} {I : PIR.Signature}

/-- Identity translation preserves every callback pointwise, including stops. -/
theorem RegionFunctions.translate_identity {Value : dialect.Ty → Type} {signatures}
    (callbacks : Values (RegionFunction Value I) signatures) :
    translate (fun op => .call op .done) callbacks = callbacks := by
  induction callbacks with
  | nil => rfl
  | cons callback callbacks ih =>
    simp only [translate, PIR.Process.interpret_identity, ih]

/-- Lift a local equation to an operation law without inspecting or inlining
callee bodies. Supplying this rule is an explicit choice of the local solver. -/
theorem RegionMeaning.OperationLaw.identity {meaning : RegionMeaning dialect I}
    (op : dialect.Op) (args : Values meaning.Value (dialect.arguments op))
    (callbacks : Values (RegionFunction meaning.Value I) (dialect.regions op))
    {target : PIR.Process I (Values meaning.Value (dialect.results op))}
    (equation : meaning.operation op args callbacks = target) :
    meaning.OperationLaw (fun op => .call op .done) op args callbacks target := by
  intro bodies same
  rw [RegionFunctions.translate_identity] at same
  subst callbacks
  simpa only [PIR.Process.interpret_identity] using equation

/-- Reconstructing an ordered tuple from its typed projections preserves it. -/
theorem Values.reify_get {Ty : Type} {Value : Ty → Type} {types : List Ty}
    (values : Values Value types) : Environment.toValues values.get = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa only [Environment.toValues, Operands.identity, Operands.eval,
      Operands.eval_rename, Values.get] using congrArg (Values.cons value) ih

/-- Normalize the environment after an arbitrary returned tuple without
assuming the tuple is honest, nonempty, or equal to a participant's local copy. -/
theorem Region.Derivation.prepend_reified {meaning : RegionMeaning dialect I}
    {J : PIR.Signature} {operations : PIR.OperationInterpretation I J} {Γ added out}
    {body : Region dialect (added ++ Γ) out} (env : Environment meaning.Value Γ)
    (values : Values meaning.Value added) {target : PIR.Process J (Values meaning.Value out)}
    (law : Region.Derivation meaning operations body
      (env.prepend (Environment.toValues values.get)) target) :
    Region.Derivation meaning operations body (env.prepend values) target := by
  simpa only [Values.reify_get] using law

end Zkc.Source

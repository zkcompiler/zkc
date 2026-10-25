module

public import Zkc.Source.Structure
public import Zkc.Source.Interpretation
public import Zkc.Source.Finite
public import Zkc.Source.RegionInterpretation

@[expose] public section

/-! Bridge the single-result reference profile to the canonical typed regions.

Control descriptors pass every captured value as an explicit operand. Their
closed region arguments receive only declared inputs. The bridge preserves the
entire open process, including every reply-dependent continuation and stop.
It does not assert correspondence with a native compiler or a security result.
-/

set_option autoImplicit false

namespace Zkc.Source

/-- Scalar operations and explicit interfaces for reference structured control. -/
inductive ScalarOp (language : Language) where
  | ordinary (op : language.Op)
  | branch (captures : List language.Ty) (result : language.Ty)
  | repeat (count : Nat) (captures : List language.Ty) (accumulator : language.Ty)

/-- Every operation returns one value; control bodies are closed over their inputs. -/
abbrev scalarDialect (language : Language) : Dialect where
  Ty := language.Ty
  Op := ScalarOp language
  arguments
    | .ordinary op => language.arguments op
    | .branch captures _ => language.condition :: captures
    | .repeat _ captures accumulator => accumulator :: captures
  results
    | .ordinary op => [language.result op]
    | .branch _ result => [result]
    | .repeat _ _ accumulator => [accumulator]
  regions
    | .ordinary _ => []
    | .branch captures result => [(captures, [result]), (captures, [result])]
    | .repeat _ captures accumulator => [(accumulator :: captures, [accumulator])]

variable {language : Language} {interface : PIR.Signature}

/-- Interpret closed callbacks using only their explicit captures and accumulator. -/
abbrev Interpretation.regionMeaning (meaning : Interpretation language interface) :
    RegionMeaning (scalarDialect language) interface where
  Value := meaning.Value
  operation
    | .ordinary op, args, .nil =>
        (meaning.operation op args).bind fun value => .done (Values.singleton value)
    | .branch _ _, .cons condition captures, .cons yes (.cons no .nil) =>
        if meaning.condition condition then yes captures else no captures
    | .repeat count _ _, .cons initial captures, .cons body .nil =>
        (PIR.repeatN count
          (fun value => (body (.cons value captures)).bind fun values => .done (values.get .here))
          initial).bind fun value => .done (Values.singleton value)

/-- First-order operations and structured control commute with effect translation.
This instance discharges the generic higher-order obligation for the scalar profile. -/
def Interpretation.regionTranslation (meaning : Interpretation language interface)
    {target : PIR.Signature} (operations : PIR.OperationInterpretation interface target) :
    meaning.regionMeaning.Translation operations where
  operation := (meaning.translate operations).regionMeaning.operation
  commutes := by
    intro op args bodies
    cases op with
    | ordinary op =>
      cases bodies
      simp only [Interpretation.regionMeaning, Interpretation.translate, PIR.Process.interpret_bind]
      rfl
    | branch captures result =>
      cases args with
      | cons condition captures =>
        cases bodies with
        | cons yes rest => cases rest with
          | cons no rest =>
            cases rest
            cases selected : meaning.condition condition <;>
              simp [Interpretation.regionMeaning, RegionFunctions.translate, selected]
    | «repeat» count captures accumulator =>
      cases args with
      | cons initial captures =>
        cases bodies with
        | cons body rest =>
          cases rest
          simp only [Interpretation.regionMeaning, RegionFunctions.translate,
            PIR.Process.interpret_bind, interpret_repeat]
          rfl

/-- The reference syntax lowers into the sole canonical region carrier. -/
def Program.toRegion {Γ ty} : Program language Γ ty → Region (scalarDialect language) Γ [ty]
  | .ret value => .ret (Values.singleton value)
  | .stop reason => .stop reason
  | .letOp op arguments next => .letOp (.ordinary op) arguments .nil next.toRegion
  | .branch (Γ := Γ) (ty := ty) condition yes no =>
      .letOp (.branch Γ ty) (.cons condition (Operands.identity Γ))
        (.cons yes.toRegion (.cons no.toRegion .nil)) (.ret (Values.singleton .here))
  | .iterate (Γ := Γ) (acc := acc) count initial body next =>
      .letOp (.repeat count Γ acc) (.cons initial (Operands.identity Γ))
        (.cons body.toRegion .nil) next.toRegion

/-- For every reference program, interpretation and environment, the complete
canonical process is the reference process with its result wrapped as a singleton.
No assumption on handlers, replies, termination outcomes or captures is needed. -/
theorem Program.denote_toRegion (meaning : Interpretation language interface) {Γ ty}
    (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    program.toRegion.denote meaning.regionMeaning env =
      (program.denote meaning env).bind (fun value => .done (Values.singleton value)) := by
  induction program with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih =>
      change ((meaning.operation op (Operands.eval env arguments)).bind
        (fun value => .done (Values.singleton value))).bind
        (fun values => next.toRegion.denote meaning.regionMeaning (env.prepend values)) =
          ((meaning.operation op (Operands.eval env arguments)).bind
            (fun value => next.denote meaning (env.push value))).bind _
      simp only [PIR.Process.bind_assoc, PIR.Process.bind, Environment.prepend_singleton]
      congr 1
      funext value
      exact ih _
  | branch condition yes no yesIH noIH =>
      change (if meaning.condition (env condition) then
          yes.toRegion.denote meaning.regionMeaning (Operands.eval env (Operands.identity _)).get
        else no.toRegion.denote meaning.regionMeaning
          (Operands.eval env (Operands.identity _)).get).bind
        (fun values => .done (Values.singleton (env.prepend values .here))) =
          (if meaning.condition (env condition) then yes.denote meaning env
            else no.denote meaning env).bind _
      simp only [Operands.get_eval_identity]
      split
      · rw [yesIH, PIR.Process.bind_assoc]
        rfl
      · rw [noIH, PIR.Process.bind_assoc]
        rfl
  | iterate count initial body next bodyIH nextIH =>
      change ((PIR.repeatN count
        (fun value => (body.toRegion.denote meaning.regionMeaning
          (Values.cons value (Operands.eval env (Operands.identity _))).get).bind
            (fun values => .done (values.get .here))) (env initial)).bind
        (fun value => .done (Values.singleton value))).bind
        (fun values => next.toRegion.denote meaning.regionMeaning (env.prepend values)) =
          ((PIR.repeatN count (fun value => body.denote meaning (env.push value))
            (env initial)).bind (fun value => next.denote meaning (env.push value))).bind _
      simp only [Values.get_cons, Operands.get_eval_identity]
      have bodySame :
          (fun value => (body.toRegion.denote meaning.regionMeaning (env.push value)).bind
            (fun values => .done (values.get .here))) =
          (fun value => body.denote meaning (env.push value)) := by
        funext value
        rw [bodyIH, PIR.Process.bind_assoc]
        simp only [PIR.Process.bind, Values.get_singleton, PIR.Process.bind_done]
      rw [bodySame, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
      congr 1
      funext value
      exact nextIH _

/-- Effect translation of a lowered reference term uses the canonical law. -/
theorem Program.translate_toRegion (meaning : Interpretation language interface)
    {target : PIR.Signature} (operations : PIR.OperationInterpretation interface target)
    {Γ ty} (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    program.toRegion.denote (meaning.translate operations).regionMeaning env =
      (program.toRegion.denote meaning.regionMeaning env).interpret operations :=
  Region.denote_translate meaning.regionMeaning operations
    (meaning.regionTranslation operations) program.toRegion env

/-- The reference iterator is the same ordered finite fold followed by its suffix.
The adapter, rather than the general finite semantics, owns this profile law. -/
theorem Program.denote_iterate_fold (meaning : Interpretation language interface) {Γ ty acc}
    (count : Nat) (initial : Var Γ acc) (body : Program language (acc :: Γ) acc)
    (next : Program language (acc :: Γ) ty) (env : Environment meaning.Value Γ) :
    (Program.iterate count initial body next).denote meaning env =
      (Finite.fold (fun state (_ : Unit) => body.denote meaning (env.push state))
        (List.replicate count ()) (env initial)).bind
        (fun state => next.denote meaning (env.push state)) := by
  rw [Finite.fold_replicate]
  rfl

end Zkc.Source

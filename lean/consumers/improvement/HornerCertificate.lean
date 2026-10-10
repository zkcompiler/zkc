import Zkc.Protocols.Sumcheck.Optimization

/-! Finite certificate dispatch into existing proved transformation rules.

This reference consumer accepts a small word-list codec, a retained typed source,
and an independently supplied raw candidate. It does not modify artifact-v1
admission, identify native operations, or authenticate a transported source.
-/

set_option autoImplicit false

namespace Improvement.HornerCertificate

open PIR Zkc.Source Zkc.Compiler

inductive RuleId where
  | direct
  | horner
  deriving DecidableEq

/-- Exact version/tag payload; unknown versions, tags, omissions and trailing
words are refused. This is a prototype word format, not the production schema. -/
def decode : List Nat → Option RuleId
  | [1, 0] => some .direct
  | [1, 1] => some .horner
  | _ => none

def encode : RuleId → List Nat
  | .direct => [1, 0]
  | .horner => [1, 1]

theorem codec_roundtrip (rule : RuleId) : decode (encode rule) = some rule := by
  cases rule <;> rfl

theorem codec_exact (wire : List Nat) (rule : RuleId) (ok : decode wire = some rule) :
    wire = encode rule := by
  unfold decode at ok
  split at ok
  · cases Option.some.inj ok
    rfl
  · cases Option.some.inj ok
    rfl
  · contradiction

section Consumer
variable {F : Type} [Semiring F] {I : Signature} {S E : Type}

def directRule (invoke : F → Proc I F) (handler : Handler I S E)
    (context : List Arithmetic.Ty) (result : Arithmetic.Ty) :
    TransformationRule (Refinement.exact (Arithmetic.Horner.model invoke handler) context result) where
  Certificate := Unit
  apply source _ := some (lower source)
  sound source _ plan accepted := by
    cases Option.some.inj accepted
    exact Refinement.direct _ source

/-- Consumers install the rule implementations and semantics. The wire cannot
supply a proof, handler, relation, or extra registry entry. -/
def consume (invoke : F → Proc I F) (handler : Handler I S E)
    {context : List Arithmetic.Ty} {result : Arithmetic.Ty}
    (source : Program Arithmetic.language context result) (wire : List Nat)
    (candidate : RawProgram Arithmetic.Ty Arithmetic.Op) :
    Option (CheckedTransformation
      (Refinement.exact (Arithmetic.Horner.model invoke handler) context result) source candidate) :=
  match decode wire with
  | none => none
  | some .direct => checkTransformation (directRule invoke handler context result) source () candidate
  | some .horner => checkTransformation
      (Arithmetic.Horner.rule invoke handler context result) source () candidate

theorem accepted_refines (invoke : F → Proc I F) (handler : Handler I S E)
    {context : List Arithmetic.Ty} {result : Arithmetic.Ty}
    (source : Program Arithmetic.language context result) (wire : List Nat)
    (candidate : RawProgram Arithmetic.Ty Arithmetic.Op)
    (checked : CheckedTransformation
      (Refinement.exact (Arithmetic.Horner.model invoke handler) context result) source candidate)
    (_accepted : consume invoke handler source wire candidate = some checked) :
    (Refinement.exact (Arithmetic.Horner.model invoke handler) context result).Holds source checked.plan :=
  checked.correct

end Consumer

open Zkc.Protocols.Sumcheck

/-- The existing protocol's independently authored Horner candidate is selected
by finite data at this consumer boundary. -/
def checked {F : Type} [Semiring F] :=
  (consume (fun x : F => .done x) Optimization.noHandler
    Optimization.evaluationSource [1, 1] Optimization.candidate).get (by rfl)

theorem consumes_actual_plan {F : Type} [Semiring F] :
    (checked (F := F)).plan = (Optimization.checked (F := F)).plan := rfl

/-- The actual consumed candidate runs with the caller's coefficients and
challenge, preserving the full child execution. -/
theorem actual_execution {F : Type} [Semiring F]
    (message : Zkc.Protocols.AlgebraicRounds.Message F) (r : F) :
    (checked (F := F)).plan.run Optimization.localMeaning Optimization.noHandler
      (Optimization.inputs message r).get () = ⟨.returned (message.evaluate r), (), []⟩ := by
  rw [consumes_actual_plan]
  exact Optimization.evaluation_execution message r

def modifiedCandidate : RawProgram Arithmetic.Ty Arithmetic.Op :=
  .letOp .multiply [2, 3] (.letOp .add [2, 0]
    (.letOp .multiply [0, 4] (.letOp .add [3, 0] (.ret 0))))

theorem rejects_unknown_version : decode [2, 1] = none := rfl
theorem rejects_unknown_rule : decode [1, 7] = none := rfl
theorem rejects_trailing_data : decode [1, 1, 0] = none := rfl
theorem rejects_missing_data : decode [1] = none := rfl

theorem rejects_changed_candidate :
    (consume (fun x : Nat => .done x) Optimization.noHandler
      Optimization.evaluationSource [1, 1] modifiedCandidate).isSome = false := by rfl

theorem rejects_changed_source :
    (consume (fun x : Nat => .done x) Optimization.noHandler
      (.ret .here : Program Arithmetic.language Optimization.arguments .scalar)
      [1, 1] Optimization.candidate).isSome = false := by rfl

theorem rejects_wrong_rule :
    (consume (fun x : Nat => .done x) Optimization.noHandler
      Optimization.evaluationSource [1, 0] Optimization.candidate).isSome = false := by rfl

theorem rejects_direct_plan_as_horner :
    (consume (fun x : Nat => .done x) Optimization.noHandler
      Optimization.evaluationSource [1, 1] (lower Optimization.evaluationSource).erase).isSome = false := by rfl

theorem accepts_direct_plan :
    (consume (fun x : Nat => .done x) Optimization.noHandler
      Optimization.evaluationSource [1, 0] (lower Optimization.evaluationSource).erase).isSome = true := by rfl

end Improvement.HornerCertificate

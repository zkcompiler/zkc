module

public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! Locate the next protocol action through the original source marks,
retaining the complete continuation at every reply. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol
variable {model : DomainModel} {A B : Type}

def withMarks : List (String × String) → PIR.Process (Interface model) A → PIR.Process (Interface model) A
  | [], process => process
  | (source, observed) :: rest, process => .call (.mark source observed) fun _ ↦ withMarks rest process

theorem withMarks_bind (marks : List (String × String)) (process : PIR.Process (Interface model) A)
    (suffix : A → PIR.Process (Interface model) B) :
    (withMarks marks process).bind suffix = withMarks marks (process.bind suffix) := by
  induction marks with
  | nil => rfl
  | cons mark marks ih =>
    rcases mark with ⟨source, observed⟩
    exact congrArg (PIR.Process.call (I := Interface model) (.mark source observed)) (funext fun _ ↦ ih)

/-- An exact factorization of the free process. An interpreter may stop at
any preceding mark, and every later effect stays in the original tail. -/
def AfterMarks (wanted : (Interface model).Op → Prop) (process : PIR.Process (Interface model) A) : Prop :=
  ∃ marks op next, wanted op ∧ process = withMarks marks (.call op next)

variable {wanted : (Interface model).Op → Prop}

theorem AfterMarks.found {op : (Interface model).Op} (selected : wanted op) {next} :
    AfterMarks wanted (.call op next : PIR.Process (Interface model) A) :=
  ⟨[], op, next, selected, rfl⟩

theorem AfterMarks.mark {source observed : String}
    {next : (Interface model).Reply (.mark source observed) → PIR.Process (Interface model) A}
    (tail : AfterMarks wanted (next ())) : AfterMarks wanted (.call (.mark source observed) next) := by
  obtain ⟨marks, op, k, selected, shape⟩ := tail
  refine ⟨(source, observed) :: marks, op, k, selected, ?_⟩
  apply congrArg (PIR.Process.call (I := Interface model) (.mark source observed))
  funext reply
  cases reply
  exact shape

theorem AfterMarks.bind {process : PIR.Process (Interface model) A}
    (before : AfterMarks wanted process) (suffix : A → PIR.Process (Interface model) B) :
    AfterMarks wanted (process.bind suffix) := by
  obtain ⟨marks, op, next, selected, rfl⟩ := before
  refine ⟨marks, op, fun reply ↦ (next reply).bind suffix, selected, ?_⟩
  exact withMarks_bind marks _ _

end Zkc.Source.Structured.OracleProtocol

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

/-- Preserve the particular reply continuation as well as the reached
operation. The suffix is the original process at every possible reply. -/
def AtMarkedCall (op : (Interface model).Op)
    (after : ((Interface model).Reply op → PIR.Process (Interface model) A) → Prop)
    (process : PIR.Process (Interface model) A) : Prop :=
  ∃ marks next, process = withMarks marks (.call op next) ∧ after next

variable {op : (Interface model).Op}
  {after : ((Interface model).Reply op → PIR.Process (Interface model) A) → Prop}

theorem AtMarkedCall.found {next} (tail : after next) : AtMarkedCall op after (.call op next) :=
  ⟨[], next, rfl, tail⟩

private theorem prependMark {source observed : String}
    {next : (Interface model).Reply (.mark source observed) → PIR.Process (Interface model) A}
    {marks : List (String × String)} {rest : PIR.Process (Interface model) A}
    (tail : next () = withMarks marks rest) :
    .call (.mark source observed) next = withMarks ((source, observed) :: marks) rest := by
  apply congrArg (PIR.Process.call (I := Interface model) (.mark source observed))
  funext reply
  cases reply
  exact tail

theorem AtMarkedCall.mark {source observed : String}
    {next : (Interface model).Reply (.mark source observed) → PIR.Process (Interface model) A}
    (tail : AtMarkedCall op after (next ())) : AtMarkedCall op after (.call (.mark source observed) next) := by
  obtain ⟨marks, k, shape, selected⟩ := tail
  exact ⟨(source, observed) :: marks, k, prependMark shape, selected⟩

/-- An explicit source stop may still be preceded by cursor-validating marks. -/
def StopsAfterMarks (why : PIR.Stop) (process : PIR.Process (Interface model) A) : Prop :=
  ∃ marks, process = withMarks marks (.halt why)

theorem StopsAfterMarks.now (why : PIR.Stop) : StopsAfterMarks (model := model) (A := A) why (.halt why) :=
  ⟨[], rfl⟩

theorem StopsAfterMarks.mark {why : PIR.Stop} {source observed : String}
    {next : (Interface model).Reply (.mark source observed) → PIR.Process (Interface model) A}
    (tail : StopsAfterMarks why (next ())) : StopsAfterMarks why (.call (.mark source observed) next) := by
  obtain ⟨marks, shape⟩ := tail
  exact ⟨(source, observed) :: marks, prependMark shape⟩

end Zkc.Source.Structured.OracleProtocol

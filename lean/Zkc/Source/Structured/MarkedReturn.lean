module

public import Zkc.Source.Structured.MarkedPrefix

@[expose] public section

/-! Specify facts about a value returned after the actual source marks without
constructing the whole returned SSA environment in the companion. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol
variable {model : DomainModel} {A : Type} {property : A → Prop}

def AtMarkedReturn (property : A → Prop) (process : PIR.Process (Interface model) A) : Prop :=
  ∃ value, AfterMarks (.done value) process ∧ property value

theorem AtMarkedReturn.done {value : A} (valid : property value) :
    AtMarkedReturn (model := model) property (.done value) :=
  ⟨value, AfterMarks.here _, valid⟩

theorem AtMarkedReturn.mark {source observed : String}
    {next : (Interface model).Reply (.mark source observed) → PIR.Process (Interface model) A}
    (tail : AtMarkedReturn property (next ())) :
    AtMarkedReturn property (.call (.mark source observed) next) := by
  obtain ⟨value, marks, valid⟩ := tail
  exact ⟨value, marks.mark, valid⟩

end Zkc.Source.Structured.OracleProtocol

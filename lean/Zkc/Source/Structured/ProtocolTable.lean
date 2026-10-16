module

public import Zkc.Source.Structured.ProtocolContext
public import Zkc.Source.Component
public import Zkc.Source.Structure

@[expose] public section

namespace Zkc.Source.Structured

abbrev ProtocolFunction (Value : Ty → Type) (I : PIR.Signature)
    (signature : ProtocolSignature) :=
  ProtocolContext → Nat →
    RegionFunction (Component Value) I (signature.inputs, signature.outputs)

structure ProtocolDefinition (Value : Ty → Type) (I : PIR.Signature) where
  signature : ProtocolSignature
  invoke : ProtocolFunction Value I signature

abbrev ProtocolTable (Value : Ty → Type) (I : PIR.Signature) :=
  List (ProtocolDefinition Value I)

/-- The first name match must have the entire exact signature, including scopes. -/
def invokeProtocol {Value : Ty → Type} {I : PIR.Signature}
    (table : ProtocolTable Value I) (signature : ProtocolSignature) :
    ProtocolFunction Value I signature :=
  match table.find? (fun entry => entry.signature.name == signature.name) with
  | none => fun _ _ _ => .halt .refused
  | some entry =>
    if same : entry.signature = signature then same ▸ entry.invoke
    else fun _ _ _ => .halt .refused

@[simp] theorem invokeProtocol_nil {Value : Ty → Type} {I : PIR.Signature}
    (signature : ProtocolSignature) :
    invokeProtocol ([] : ProtocolTable Value I) signature = fun _ _ _ => .halt .refused := rfl

theorem invokeProtocol_cons_same {Value : Ty → Type} {I : PIR.Signature}
    (table : ProtocolTable Value I) (entry : ProtocolDefinition Value I) :
    invokeProtocol (entry :: table) entry.signature = entry.invoke := by
  simp [invokeProtocol]

theorem invokeProtocol_cons_other {Value : Ty → Type} {I : PIR.Signature}
    (table : ProtocolTable Value I) (entry : ProtocolDefinition Value I)
    (signature : ProtocolSignature) (different : entry.signature.name ≠ signature.name) :
    invokeProtocol (entry :: table) signature = invokeProtocol table signature := by
  simp [invokeProtocol, different]

theorem invokeProtocol_cons_mismatch {Value : Ty → Type} {I : PIR.Signature}
    (table : ProtocolTable Value I) (entry : ProtocolDefinition Value I)
    (signature : ProtocolSignature) (sameName : entry.signature.name = signature.name)
    (different : entry.signature ≠ signature) :
    invokeProtocol (entry :: table) signature = fun _ _ _ => .halt .refused := by
  simp [invokeProtocol, sameName, different]

/-- Correspondence includes every context, optional tuple and failed lookup. -/
def ProtocolTable.Interprets {Value : Ty → Type} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    (left : ProtocolTable Value I) (right : ProtocolTable Value J) : Prop :=
  ∀ signature context self args,
    (invokeProtocol left signature context self args).interpret operations =
      invokeProtocol right signature context self args

theorem ProtocolTable.Interprets.empty {Value : Ty → Type} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J) :
    Interprets (Value := Value) operations [] [] := by
  intro signature context self args
  rfl

theorem ProtocolTable.Interprets.cons {Value : Ty → Type} {I J : PIR.Signature}
    {operations : PIR.OperationInterpretation I J}
    {left : ProtocolTable Value I} {right : ProtocolTable Value J}
    (tables : Interprets operations left right) (signature : ProtocolSignature)
    (leftBody : ProtocolFunction Value I signature) (rightBody : ProtocolFunction Value J signature)
    (bodies : ∀ context self args, (leftBody context self args).interpret operations =
      rightBody context self args) :
    Interprets operations (⟨signature, leftBody⟩ :: left) (⟨signature, rightBody⟩ :: right) := by
  intro query context self args
  by_cases names : signature.name = query.name
  · by_cases same : signature = query
    · subst query
      simpa [invokeProtocol] using bodies context self args
    · rw [invokeProtocol_cons_mismatch _ _ _ names same,
        invokeProtocol_cons_mismatch _ _ _ names same]
      rfl
  · rw [invokeProtocol_cons_other _ _ _ names, invokeProtocol_cons_other _ _ _ names]
    exact tables query context self args

end Zkc.Source.Structured

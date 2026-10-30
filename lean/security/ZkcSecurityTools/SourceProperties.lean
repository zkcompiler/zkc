module

public meta import Lean.Elab.Tactic
public import Zkc.Source.Structured.NormalForm.Observation
public import ZkcSecurity.Bindings.Source.PropertyAssembly

public meta section

/-! Proof production for presentation of checked normal forms. The caller
unfolds only its selected reference definitions. This tactic reassociates the
existing process binds and checks each head by definitional equality. It never
uses protocol names, hashes or an assumed whole-source equation. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceProperties
open Lean Elab Tactic

elab "source_presentation" : tactic => do
  evalTactic (← `(tactic|
    (try simp only [PIR.Process.bind_assoc, ZkcSecurity.Source.PropertyAssembly.done_bind,
       Zkc.Source.Structured.NormalForm.entryAt_eq_get]
     repeat first
       | rfl
       | (apply congrArg (PIR.Process.bind _); funext)
       | (change ((_ : PIR.Process _ _).bind _).bind _ = _
          rw [PIR.Process.bind_assoc]
          apply congrArg (PIR.Process.bind _)
          funext)
     try (change ((_ : PIR.Process _ _).bind _).bind _ = _
          rw [PIR.Process.bind_assoc]))))

end ZkcSecurity.Tools.SourceProperties

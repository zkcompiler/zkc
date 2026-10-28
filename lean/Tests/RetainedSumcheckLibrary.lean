import Zkc.Construction.ConnectionApplicationCertificate
import Mathlib.Tactic.FinCases
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
import ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer
import ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator

/-! Actual admitted source libraries for both participant roles. The shared
reduce body retains its six-component private state and symbolic repeat. The
TwoSums root refers to one checked reduce template at two application sites.
These are source library checks; root target composition remains a separate
connection obligation. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.RetainedSumcheckLibrary
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary

namespace Small
abbrev program := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program

def reduce (role : Fin 2) : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ role
    (rolePattern role program.payload.protocols[0].inputs program.payload.protocols[0].inputScopes)).toOption.get
    (by fin_cases role <;> decide +kernel)

def root (role : Fin 2) : SourceTemplate program.payload [(reduce role).key] :=
  (SourceTemplate.build program.payload [(reduce role).key] ⟨1, by decide +kernel⟩ role
    (rolePattern role program.payload.protocols[1].inputs program.payload.protocols[1].inputScopes)).toOption.get
    (by fin_cases role <;> decide +kernel)

def library (role : Fin 2) : Library program.payload [(root role).key, (reduce role).key] :=
  .extend (.extend .empty (reduce role)) (root role)

example : (root 0).form.calleeCalls.length = 1 := by decide +kernel
example : (root 1).form.calleeCalls.length = 1 := by decide +kernel
example : (SourceTemplate.build program.payload
    [{(reduce 1).key with signature := {(reduce 1).source.signature with name := "changed"}}]
    ⟨1, by decide +kernel⟩ 1
    (rolePattern 1 program.payload.protocols[1].inputs program.payload.protocols[1].inputScopes)).isOk = false :=
  by decide +kernel
example : (SourceTemplate.build program.payload [{(reduce 1).key with role := 0}]
    ⟨1, by decide +kernel⟩ 1
    (rolePattern 1 program.payload.protocols[1].inputs program.payload.protocols[1].inputScopes)).isOk = false :=
  by decide +kernel
example (role : Fin 2) (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model program.payload) ((library role).processes model) inputs :=
  (library role).holds model inputs
end Small

namespace Two
abbrev program := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program

def reduce (role : Fin 2) : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide +kernel⟩ role
    (rolePattern role program.payload.protocols[0].inputs program.payload.protocols[0].inputScopes)).toOption.get
    (by fin_cases role <;> decide +kernel)

def root (role : Fin 2) : SourceTemplate program.payload [(reduce role).key] :=
  (SourceTemplate.build program.payload [(reduce role).key] ⟨1, by decide +kernel⟩ role
    (rolePattern role program.payload.protocols[1].inputs program.payload.protocols[1].inputScopes)).toOption.get
    (by fin_cases role <;> decide +kernel)

def library (role : Fin 2) : Library program.payload [(root role).key, (reduce role).key] :=
  .extend (.extend .empty (reduce role)) (root role)

example : (root 0).form.calleeCalls.length = 2 := by decide +kernel
example : (root 1).form.calleeCalls.length = 2 := by decide +kernel
example : (root 1).form.calleeCalls.map (fun call => call.1.val) = [0,0] := by decide +kernel
example : ((library 1).entry 1).template.source = program.payload.protocols[0] := rfl
example (role : Fin 2) (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model program.payload) ((library role).processes model) inputs :=
  (library role).holds model inputs
end Two

#print axioms Small.library
#print axioms Two.library
#print axioms Library.processes_entry
end Tests.RetainedSumcheckLibrary

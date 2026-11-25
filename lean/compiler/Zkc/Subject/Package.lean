module

public import Zkc.Core.Admission.Theorems

@[expose] public section
set_option autoImplicit false

namespace Zkc.Subject
open Core

/-- A stored program and its association, with the installation checked one definition at a
time and the success of admission of the whole package. -/
structure Package (V : Vocabulary) where
  stored : NamedProgram V
  association : Association
  installed : Typed V
  elaborated : ElaboratedFrom Typed.empty stored.definitions installed
  accepts : (admit stored association).isOk = true

namespace Package
variable {V : Vocabulary} (pkg : Package V)

/-- The installation is the program returned by the reader's admission. -/
theorem readback {a : Admitted V} (admitted : admit pkg.stored pkg.association = .ok a) :
    a.program = pkg.installed :=
  admitted_eq_of_elaborated admitted pkg.elaborated

/-- At least one admission returns a program with this association. -/
theorem admitted_exists : ∃ a, admit pkg.stored pkg.association = .ok a := by
  have ok := pkg.accepts
  cases eq : admit pkg.stored pkg.association with
  | ok a => exact ⟨a, rfl⟩
  | error e =>
    rw [eq] at ok
    contradiction

/-- Carry any property of the installation to a program returned by admission. -/
theorem transfer {a : Admitted V} (admitted : admit pkg.stored pkg.association = .ok a)
    (P : Typed V → Prop) (holds : P pkg.installed) : P a.program :=
  pkg.readback admitted ▸ holds

/-- Carry a property of a protocol, retaining the key by which a reader finds it. -/
theorem atProtocol {a : Admitted V} (admitted : admit pkg.stored pkg.association = .ok a)
    {header : ProtocolHeader V} (key : Key) (member : Member pkg.installed.headers.protocols header)
    (found : pkg.installed.findProtocol key = some ⟨header, member⟩)
    (P : (p : Typed V) → Member p.headers.protocols header → Prop) (holds : P pkg.installed member) :
    ∃ root : Member a.program.headers.protocols header,
      a.program.findProtocol key = some ⟨header, root⟩ ∧ P a.program root :=
  pkg.transfer admitted (fun p => ∃ root : Member p.headers.protocols header,
    p.findProtocol key = some ⟨header, root⟩ ∧ P p root) ⟨member, found, holds⟩

/-- Carry a property of a protocol and a function, retaining both lookups. -/
theorem atProtocolAndFunction {a : Admitted V} (admitted : admit pkg.stored pkg.association = .ok a)
    {header : ProtocolHeader V} (key : Key) (member : Member pkg.installed.headers.protocols header)
    (found : pkg.installed.findProtocol key = some ⟨header, member⟩)
    {fn : FnHeader V} (fnKey : Key) (relation : Member pkg.installed.headers.fns fn)
    (foundFn : pkg.installed.find fnKey = some (.fn relation))
    (P : (p : Typed V) → Member p.headers.protocols header → Member p.headers.fns fn → Prop)
    (holds : P pkg.installed member relation) :
    ∃ root : Member a.program.headers.protocols header,
      a.program.findProtocol key = some ⟨header, root⟩ ∧
      ∃ rel : Member a.program.headers.fns fn, a.program.find fnKey = some (.fn rel) ∧ P a.program root rel :=
  pkg.atProtocol admitted key member found (fun p root =>
    ∃ rel : Member p.headers.fns fn, p.find fnKey = some (.fn rel) ∧ P p root rel)
    ⟨relation, foundFn, holds⟩

end Package
end Zkc.Subject

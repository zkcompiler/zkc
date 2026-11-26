import Zkc.Subject.Package
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project
import ZkcFormal.Written.Soundness
import ZkcFormal.Written.StandardInterpretation

/-!
What a rejected statement is, on a relation that stops.

A statement is rejected when no valid witness makes the relation return true. The frontend
refuses a relation that can stop, so no source shows what that says where a relation stops; this
package is written by hand in the core and admitted. Its relation takes a Boolean statement and
a Boolean witness, stops when the witness is `false`, and returns the statement otherwise.

- The statement `true` is not rejected: the witness `true` makes the relation return true.
- The statement `false` is rejected, although the relation stops at the witness `false`: the
  other valid witness makes it return false, and none makes it return true. Under the premise
  "every valid witness makes the relation return false" this statement was outside every claim,
  whatever the verifier did with it.
-/

open Zkc.Core ZkcFormal.Written

namespace ZkcFormalTests.RejectedStatement

abbrev V : Zkc.Core.Vocabulary := (Zkc.Vocabulary.Project.Bindings.mk [] (by decide +kernel)).vocabulary

/-- The verifier rejects unless its first input is set. -/
def stored1 : Definition V :=
  .protocol ⟨1⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.bool, [0, 1]⟩] []
  (.mk [0, 1] [.guard ⟨0⟩ [1] 0 .reject] [])

/-- The relation: it stops unless the witness (value 1) is set, and returns the statement
(value 0). -/
def stored0 : Definition V :=
  .fn ⟨0⟩ [.bool, .bool] [.bool] true none ⟨[], []⟩
  (.mk [0, 1] [.guard ⟨0⟩ () 1 .reject] [0])
  []

def stored : NamedProgram V := ⟨[stored1, stored0]⟩
def association : Association := ⟨[], [], [], [], []⟩

noncomputable section
def programBase : Typed V := Typed.empty
kernel_ok elaborated1 with header1 names1 body1 : Elaborated V programBase.headers :=
  elaborateDefinition programBase.headers stored1
def program1 : Typed V := programBase.add elaborated1
kernel_ok elaborated0 with header0 names0 body0 : Elaborated V program1.headers :=
  elaborateDefinition program1.headers stored0
def installed : Typed V := program1.add elaborated0
theorem elaborated : ElaboratedFrom Typed.empty stored.definitions installed :=
  .cons elaborated1.eq (.cons elaborated0.eq (.nil _))
abbrev subjectPackage : Zkc.Subject.Package V :=
  ⟨stored, association, installed, elaborated, by decide +kernel⟩
end

open ZkcFormal.Written.StandardInterpretation (model)

noncomputable abbrev rootMember : Member installed.headers.protocols header1 := Member.head
noncomputable def relationMember : Member installed.headers.fns header0 := Member.head

theorem found'root : installed.findProtocol ⟨1⟩ = some ⟨header1, rootMember⟩ := by kernel_rfl
theorem found'relation : installed.find stored0.key = some (.fn relationMember) := by kernel_rfl

noncomputable def root : Zkc.Subject.WrittenRoot subjectPackage :=
  ⟨⟨header1, rootMember, found'root⟩, ⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩,
   by decide +kernel⟩

/-- The clause: the relation at the root's first input, with one witness parameter. -/
noncomputable def decision : Zkc.Subject.Decision root :=
  ⟨0, ⟨header0, relationMember, found'relation⟩, ⟨1, by decide +kernel⟩, rfl,
   (.cons ⟨⟨_, Member.head⟩, by decide +kernel, by decide +kernel⟩ .nil), none⟩

/-- The verifier's inputs with the statement `x`. -/
noncomputable abbrev inputs (x : Bool) : HList (RV model root.verifier) root.entry.header.ins :=
  .cons x (.cons true .nil)

/-- The relation's result at a statement and a witness. -/
noncomputable abbrev result (x w : Bool) : Option Bool :=
  functionResult (M := model) (t := .bool)
    (fnMeaning model installed relationMember (.cons x (.cons w .nil)))

theorem results : result true false = none ∧ result true true = some true ∧
    result false false = none ∧ result false true = some false :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- A statement that a valid witness accepts is not rejected. -/
theorem accepted_not_rejected :
    ¬ Soundness.Rejected model decision installed relationMember (inputs true) :=
  fun rejected ↦ rejected true trivial results.2.1

/-- A statement that no valid witness accepts is rejected, also where the relation stops for
a valid witness. -/
theorem stopping_rejected :
    Soundness.Rejected model decision installed relationMember (inputs false) := by
  intro w _
  change result false w ≠ some true
  cases w <;> simp [results.2.2.1, results.2.2.2]

/-- The same through the pointwise form of the library. -/
example : Soundness.Rejected model decision installed relationMember (inputs false) :=
  (Soundness.rejected_iff model decision installed relationMember (inputs false)).mpr
    fun (.cons w .nil) _ ↦ by
      change result false w ≠ some true
      cases w <;> simp [results.2.2.1, results.2.2.2]

end ZkcFormalTests.RejectedStatement

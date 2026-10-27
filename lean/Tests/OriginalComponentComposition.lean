module

import Zkc.Construction.ArtifactBindingTactic
import Zkc.Construction.OriginalComponentReduction

/-! An independent component client checks automatic bind composition. The
complete result relation changes across the prefix and its continuation. -/
set_option autoImplicit false
set_option linter.unusedTactic false
noncomputable section
namespace Tests.OriginalComponentComposition
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {carriers : Carriers}

def packetPrefix (value : Nat) :
    Original.Simulation (fun original actual : Nat => actual = original + 1)
      (fun _ frame => frame = ([] : Domain.Environment carriers))
      (.call (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done value)
      (.call (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done (value + 1)) :=
  .call _ fun _ => .done rfl

example (value : Nat) :
    Original.Simulation (fun original actual : Nat => actual = original + 1 + 2)
      (fun _ frame => frame = ([] : Domain.Environment carriers))
      ((PIR.Process.call (I := Domain.effects carriers) (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done value).bind
        fun result => .done result)
      ((PIR.Process.call (I := Domain.effects carriers) (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done (value + 1)).bind
        fun result => .done (result + 2)) := by
  derive_artifact_binding [packetPrefix]
    normalizing (simp (config := { failIfUnchanged := false }) only [↓Original.simplifyBindHead, PIR.Process.bind_done])
    solving (solve | simp_all)

abbrev PacketCertificate (value : Nat) :=
    Original.Simulation (fun original actual : Nat => ∃ saved, original = saved ∧ actual = saved + 1)
      (fun _ frame => frame = ([] : Domain.Environment carriers))
      (.call (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done value)
      (.call (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done (value + 1))

def packetExists (value : Nat) : PacketCertificate (carriers := carriers) value :=
  .call _ fun _ => .done ⟨value, rfl, rfl⟩

example (value : Nat) :
    Original.Simulation (fun original actual : Nat => actual = original + 3)
      (fun _ frame => frame = ([] : Domain.Environment carriers))
      ((PIR.Process.call (I := Domain.effects carriers) (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done value).bind
        fun result => .done result)
      ((PIR.Process.call (I := Domain.effects carriers) (.send "packet" "packet" "receiver" (.boolean true)) fun _ => .done (value + 1)).bind
        fun result => .done (result + 2)) := by
  derive_artifact_binding [packetExists]
    normalizing (
      apply Classical.choice
      try casesm* ∃ _, _
      try casesm* _ ∧ _
      try subst_vars
      constructor
      simp (config := { failIfUnchanged := false }) only [↓Original.simplifyBindHead, PIR.Process.bind_done])
    solving (solve | simp_all)

/-- A reached guard splits before component proof search. Both refusal and
successful return remain exact under the same condition. -/
example (condition : Prop) [Decidable condition] :
    Original.Simulation Eq (fun _ frame => frame = ([] : Domain.Environment carriers))
      (if condition then .done (7 : Nat) else .halt .refused)
      (if condition then .done (7 : Nat) else .halt .refused) := by
  derive_artifact_binding normalizing (skip) solving (solve | rfl)

/-- A guard inside an interpreted prefix retains rejection when composed with
the next component; its operation interpretation is arbitrary. -/
example {interface : PIR.Signature}
    (operations : PIR.OperationInterpretation interface (Domain.effects carriers))
    (condition : Prop) [Decidable condition] :
    Original.Simulation Eq (fun _ frame => frame = ([] : Domain.Environment carriers))
      (((if condition then .done (7 : Nat) else .halt .reject : PIR.Process interface Nat).interpret
        operations).bind fun value => .done (value + 1))
      (if condition then .done (8 : Nat) else .halt .reject) := by
  derive_artifact_binding normalizing (
    simp (config := { failIfUnchanged := false }) only
      [Original.interpretIf, PIR.Process.interpret, PIR.Process.bind_ite,
       PIR.Process.bind]) solving (solve | rfl)

/-- A dialect can expose its result row through an abstract declaration.
Projection normalization still checks the complete optional slot. -/
private def declaredRow : List Unit := [()]
private def declaredValues : Values (fun _ : Unit => Nat) declaredRow := .cons 7 .nil
example (environment : Environment (Component (fun _ : Unit => Nat)) []) :
    environment.prepend declaredValues.present (.here : Var [()] ()) = some 7 := by
  simp only [↓Original.reducePrepend, ↓Original.reducePush]

example : RoleFamily.sequence declaredValues.present = some declaredValues := by
  simp only [↓Original.reduceSequence]
  rfl

/-- A second dialect-independent client traverses the real region constructors,
retaining the caller context until the first result is returned. -/
example {dialect : Dialect} {interface : PIR.Signature}
    (meaning : RegionMeaning dialect interface) (ty : dialect.Ty) (value : meaning.Value ty) :
    (Region.bind (.ret (.cons .here .nil)) (.ret (.cons .here .nil)) :
      Region dialect [ty] [ty]).denote meaning (Values.cons value Values.nil).get =
      .done (.cons value .nil) := by
  simp only [↓Original.simplifyRegionHead, ↓Original.simplifyBindHead,
    ↓Original.reducePrepend, ↓Original.reducePush, Operands.eval, Values.get, PIR.Process.bind]


section
attribute [local irreducible] Original.fold
example (routing : Original.Routing) (state : Original.State carriers) (value : Bool)
    (next : (Values (Component carriers.Value) [.boolean] × Original.State carriers) →
      PIR.Process (Domain.effects carriers) Nat) :
    (Original.fold routing (.done ((.cons value .nil : Values carriers.Value [.boolean]).present)) state).bind next =
      next (.cons (some value) .nil, state) := by
  simp only [↓Original.simplifyBindHead, Original.fold_done, PIR.Process.bind]
  rfl
end

end Tests.OriginalComponentComposition

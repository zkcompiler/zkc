module

public import Tests.Generated.StructuredBindingsGenericInputs
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites

@[expose] public section

/-! Generated present-input view of the admitted source. Regenerate. -/
namespace Tests.Generated.StructuredBindingsGenericPresent
open Zkc.Source Zkc.Source.Structured NormalForm Bindings
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section

abbrev program := Tests.Generated.StructuredBindingsGenericInputs.program
def signature : Signature := ⟨[], false, true, [], []⟩
def inputPattern : InputPattern program.payload.entry.inputs := (.cons .present (.cons .present .nil))

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

noncomputable def rootForm : (Form [] [] [(.value .index), (.value .index)] [.index]) :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" (.ret (.cons (.there .here) .nil)) (.present (.var .here)) (.cons (.present (.var (.there .here))) .nil) .nil (.done (.cons (.read .here .here) .nil)))

noncomputable def rootProcess  (b0 : Nat) (b1 : Nat) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} 0).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) ((some (b0))) (.cons ((some (b1))) .nil) .nil ((Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} 0).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.ret (.cons (.there .here) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem root_calls : rootForm.CallsMatch := by
  kernel_rfl

theorem root_presentation  (b0 : Nat) (b1 : Nat) :
    ((rootForm).denote (ringModel F G) ((helpers (F := F) (G := G) program.payload).toOn) (emptyResults (ringModel F G)) (({} : ProtocolContext)) (Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} 0) (((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) [])) (.cons (b0) (.cons (b1) .nil))) =
      (rootProcess (b0) (b1)) := by
  kernel_rfl

theorem root_sites :
    Zkc.Source.Structured.NormalForm.sites rootForm [] =
      [(⟨[], "repeat", "round"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem normalized : normalize signature program.payload.entry.body 0 program.payload.entry.roles.length inputPattern = .ok rootForm := by kernel_rfl

def inputs (b0 : Nat) (b1 : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  (.cons (some b0) (.cons (some b1) .nil))

noncomputable def view (b0 : Nat) (b1 : Nat) :=
  (rootProcess (F := F) (G := G) b0 b1).bind fun out => PIR.Process.done (maskValues 0 program.payload.entry.outputScopes out)

theorem source_equation (b0 : Nat) (b1 : Nat) :
    program.participant F G 0 (inputs (F := F) (G := G) b0 b1) = view (F := F) (G := G) b0 b1 := by
  have equation := invocation (F := F) (G := G) program.payload program.payload.entry
    (List.get_mem _ _) signature 0 program.payload.entry.roles.length inputPattern
    rootForm normalized root_calls (emptyResults (ringModel F G))
    ((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) []) {} (RosterDistinct.root _ _)
    (inputs (F := F) (G := G) b0 b1) ((.cons b0 (.cons b1 .nil))) (by kernel_rfl) (emptyLaws _ _) (fun entry => entry.elim0)
  exact (program.payload.protocolTable_forgetSites (F := F) (G := G) program.payload.entry.signature {} 0 (inputs (F := F) (G := G) b0 b1)).trans
    (equation.trans (congrArg (fun p => p.bind fun out => PIR.Process.done (maskValues 0 program.payload.entry.outputScopes out))
      (root_presentation (F := F) (G := G) b0 b1)))

end
end Tests.Generated.StructuredBindingsGenericPresent

module

public import ZkcExamples.NativePrograms.Variants.SchnorrReorderedInputs
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites

@[expose] public section

/-! Generated present-input view of the admitted source. Regenerate. -/
namespace ZkcExamples.NativePrograms.Variants.SchnorrReorderedView
open Zkc.Source Zkc.Source.Structured NormalForm Bindings
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section

abbrev program := ZkcExamples.NativePrograms.Variants.SchnorrReorderedInputs.program
def signature : Signature := ⟨[], false, true, [], []⟩
def inputPattern : InputPattern program.payload.entry.inputs := (.cons .present (.cons .present (.cons .absent (.cons .absent (.cons .present .nil)))))

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

noncomputable def rootForm : (Form [] [] [(.value (.group "bls12-381.g1")), (.value (.group "bls12-381.g1")), (.value (.service "random.bls12-381.fr/0"))] [.boolean]) :=
  (.receive (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 0 (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var (.there (.there (.there .here)))) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.receive (.field "bls12-381.fr") "label_726573706f6e7365_0" 0 (.done (.cons (.present (.calc (.groupEqual "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.var .here) .nil)) .here) (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there .here)) .nil)) .here) (.cons (.var (.there (.there .here))) .nil)) .here) .nil)) .here)) .nil))))))

noncomputable def rootProcess  (b0 : G) (b1 : G) (b2 : Nat) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .call (.receive (.group "bls12-381.g1") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_636f6d6d69746d656e74_0") ((({} : ProtocolContext)).roles 0)) fun (b3 : G) =>
  .call (.query (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons (b2) .nil)) fun (b4 : F) =>
  .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_64656c6976657279_0") ((({} : ProtocolContext)).roles 0) (b4)) fun _ =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_726573706f6e7365_0") ((({} : ProtocolContext)).roles 0)) fun (b5 : F) =>
  .done ((.cons ((some (((Op.evalTotal (ringModel F G) (.groupEqual "bls12-381.g1") rfl (.cons (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b5) (b0))) (.cons (((((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b4) (b1))) + (b3))) .nil))).get .here)))) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem root_calls : rootForm.CallsMatch := by
  kernel_rfl

theorem root_presentation  (b0 : G) (b1 : G) (b2 : Nat) :
    ((rootForm).denote (ringModel F G) ((helpers (F := F) (G := G) program.payload).toOn) (emptyResults (ringModel F G)) (({} : ProtocolContext)) (Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} 1) (((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) [])) (.cons (b0) (.cons (b1) (.cons (b2) .nil)))) =
      (rootProcess (b0) (b1) (b2)) := by
  kernel_rfl

theorem root_sites :
    Zkc.Source.Structured.NormalForm.sites rootForm [] =
      [(⟨[], "receive", "label_636f6d6d69746d656e74_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "query", "label_6368616c6c656e6765"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0], "send", "label_64656c6976657279_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0], "receive", "label_726573706f6e7365_0"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem normalized : normalize signature program.payload.entry.body 1 program.payload.entry.roles.length inputPattern = .ok rootForm := by kernel_rfl

def inputs (b0 : G) (b1 : G) (b2 : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  (.cons (some b0) (.cons (some b1) (.cons none (.cons none (.cons (some b2) .nil)))))

noncomputable def view (b0 : G) (b1 : G) (b2 : Nat) :=
  (rootProcess (F := F) (G := G) b0 b1 b2).bind fun out => PIR.Process.done (maskValues 1 program.payload.entry.outputScopes out)

theorem source_equation (b0 : G) (b1 : G) (b2 : Nat) :
    program.participant F G 1 (inputs (F := F) (G := G) b0 b1 b2) = view (F := F) (G := G) b0 b1 b2 := by
  have equation := invocation (F := F) (G := G) program.payload program.payload.entry
    (List.get_mem _ _) signature 1 program.payload.entry.roles.length inputPattern
    rootForm normalized root_calls (emptyResults (ringModel F G))
    ((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) []) {} (RosterDistinct.root _ _)
    (inputs (F := F) (G := G) b0 b1 b2) ((.cons b0 (.cons b1 (.cons b2 .nil)))) (by kernel_rfl) (emptyLaws _ _) (fun entry => entry.elim0)
  exact (program.payload.protocolTable_forgetSites (F := F) (G := G) program.payload.entry.signature {} 1 (inputs (F := F) (G := G) b0 b1 b2)).trans
    (equation.trans (congrArg (fun p => p.bind fun out => PIR.Process.done (maskValues 1 program.payload.entry.outputScopes out))
      (root_presentation (F := F) (G := G) b0 b1 b2)))

end
end ZkcExamples.NativePrograms.Variants.SchnorrReorderedView

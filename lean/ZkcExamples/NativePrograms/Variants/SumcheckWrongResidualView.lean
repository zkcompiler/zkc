module

public import ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualInputs
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites

@[expose] public section

/-! Generated present-input view of the admitted source. Regenerate. -/
namespace ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView
open Zkc.Source Zkc.Source.Structured NormalForm Bindings
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section

abbrev program := ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualInputs.program
def signature : Signature := ⟨[], false, true, [], []⟩
def inputPattern : InputPattern program.payload.entry.inputs := (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present (.cons .present .nil)))))))))))

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

noncomputable def rootForm : (Form [] [] [(.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.field "bls12-381.fr")), (.value (.service "random.bls12-381.fr/0"))] [.boolean]) :=
  (.receive (.field "bls12-381.fr") "label_666972737430_0" 0 (.receive (.field "bls12-381.fr") "label_666972737431_0" 0 (.receive (.field "bls12-381.fr") "label_666972737432_0" 0 (.guard (.field "bls12-381.fr") (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) (.cons (.var .here) .nil)) .here) (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.query "label_6472617730" "bls12-381.fr" (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657230_0" 0 (.var .here) (.receive (.field "bls12-381.fr") "label_7365636f6e6430_0" 0 (.receive (.field "bls12-381.fr") "label_7365636f6e6431_0" 0 (.receive (.field "bls12-381.fr") "label_7365636f6e6432_0" 0 (.guard (.field "bls12-381.fr") (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) (.cons (.var .here) .nil)) .here) (.var (.there (.there (.there (.there (.there (.there .here))))))) (.query "label_6472617731" "bls12-381.fr" (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657231_0" 0 (.var .here) (.done (.cons (.present (.calc (.fieldEqual "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var .here) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var .here) .nil)) .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var .here) .nil)) .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there (.there (.there (.there .here))))) .nil)) .here) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var .here) .nil)) .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here)) .nil))))))))))))))

noncomputable def rootProcess  (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) (b7 : F) (b8 : F) (b9 : F) (b10 : Nat) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_666972737430_0") ((({} : ProtocolContext)).roles 0)) fun (b11 : F) =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_666972737431_0") ((({} : ProtocolContext)).roles 0)) fun (b12 : F) =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_666972737432_0") ((({} : ProtocolContext)).roles 0)) fun (b13 : F) =>
  @ite _ ((((((((b11) + (b11))) + (b12))) + (b13))) = (b9)) (Equality.decide (ringModel F G) (.field "bls12-381.fr") (((((((b11) + (b11))) + (b12))) + (b13))) (b9))
    (
      .call (.query (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_6472617730") "bls12-381.fr" (.cons (b10) .nil)) fun (b14 : F) =>
      .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_64656c6976657230_0") ((({} : ProtocolContext)).roles 0) (b14)) fun _ =>
      .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_7365636f6e6430_0") ((({} : ProtocolContext)).roles 0)) fun (b15 : F) =>
      .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_7365636f6e6431_0") ((({} : ProtocolContext)).roles 0)) fun (b16 : F) =>
      .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_7365636f6e6432_0") ((({} : ProtocolContext)).roles 0)) fun (b17 : F) =>
      @ite _ ((((((((b15) + (b15))) + (b16))) + (b17))) = (b11)) (Equality.decide (ringModel F G) (.field "bls12-381.fr") (((((((b15) + (b15))) + (b16))) + (b17))) (b11))
        (
          .call (.query (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_6472617731") "bls12-381.fr" (.cons (b10) .nil)) fun (b18 : F) =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (({} : ProtocolContext)).applicationPrefix "label_64656c6976657231_0") ((({} : ProtocolContext)).roles 0) (b18)) fun _ =>
          .done ((.cons ((some (((Op.evalTotal (ringModel F G) (.fieldEqual "bls12-381.fr") rfl (.cons (((((b15) + (((b18) * (b16))))) + (((((b18) * (b18))) * (b17))))) (.cons (((((((((b0) + (((b18) * (b1))))) + (((((b18) * (b18))) * (b2))))) + (((b14) * (((((b3) + (((b18) * (b4))))) + (((((b18) * (b18))) * (b5))))))))) + (((((b14) * (b14))) * (((((b6) + (((b18) * (b7))))) + (((((b18) * (b18))) * (b8))))))))) .nil))).get .here)))) .nil) : (Values (Component (assignment F G)) [.boolean])))
        (.halt .reject))
    (.halt .reject)

theorem root_calls : rootForm.CallsMatch := by
  kernel_rfl

theorem root_presentation  (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) (b7 : F) (b8 : F) (b9 : F) (b10 : Nat) :
    ((rootForm).denote (ringModel F G) ((helpers (F := F) (G := G) program.payload).toOn) (emptyResults (ringModel F G)) (({} : ProtocolContext)) (Runs.uniform (helpers program.payload) (program.payload.plainProtocolTable F G) {} 1) (((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) [])) (.cons (b0) (.cons (b1) (.cons (b2) (.cons (b3) (.cons (b4) (.cons (b5) (.cons (b6) (.cons (b7) (.cons (b8) (.cons (b9) (.cons (b10) .nil)))))))))))) =
      (rootProcess (b0) (b1) (b2) (b3) (b4) (b5) (b6) (b7) (b8) (b9) (b10)) := by
  kernel_rfl

theorem root_sites :
    Zkc.Source.Structured.NormalForm.sites rootForm [] =
      [(⟨[], "receive", "label_666972737430_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "receive", "label_666972737431_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0], "receive", "label_666972737432_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0], "query", "label_6472617730"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0], "send", "label_64656c6976657230_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0, 0], "receive", "label_7365636f6e6430_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0, 0, 0], "receive", "label_7365636f6e6431_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0, 0, 0, 0], "receive", "label_7365636f6e6432_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], "query", "label_6472617731"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], "send", "label_64656c6976657231_0"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem normalized : normalize signature program.payload.entry.body 1 program.payload.entry.roles.length inputPattern = .ok rootForm := by kernel_rfl

def inputs (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) (b7 : F) (b8 : F) (b9 : F) (b10 : Nat) : Values (Component (assignment F G)) program.payload.entry.inputs :=
  (.cons (some b0) (.cons (some b1) (.cons (some b2) (.cons (some b3) (.cons (some b4) (.cons (some b5) (.cons (some b6) (.cons (some b7) (.cons (some b8) (.cons (some b9) (.cons (some b10) .nil)))))))))))

noncomputable def view (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) (b7 : F) (b8 : F) (b9 : F) (b10 : Nat) :=
  (rootProcess (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10).bind fun out => PIR.Process.done (maskValues 1 program.payload.entry.outputScopes out)

theorem source_equation (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) (b7 : F) (b8 : F) (b9 : F) (b10 : Nat) :
    program.participant F G 1 (inputs (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) = view (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 := by
  have equation := invocation (F := F) (G := G) program.payload program.payload.entry
    (List.get_mem _ _) signature 1 program.payload.entry.roles.length inputPattern
    rootForm normalized root_calls (emptyResults (ringModel F G))
    ((fun entry => entry.elim0) : CalleeProcesses (ringModel F G) []) {} (RosterDistinct.root _ _)
    (inputs (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) ((.cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons b4 (.cons b5 (.cons b6 (.cons b7 (.cons b8 (.cons b9 (.cons b10 .nil)))))))))))) (by kernel_rfl) (emptyLaws _ _) (fun entry => entry.elim0)
  exact (program.payload.protocolTable_forgetSites (F := F) (G := G) program.payload.entry.signature {} 1 (inputs (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10)).trans
    (equation.trans (congrArg (fun p => p.bind fun out => PIR.Process.done (maskValues 1 program.payload.entry.outputScopes out))
      (root_presentation (F := F) (G := G) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10)))

end
end ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView

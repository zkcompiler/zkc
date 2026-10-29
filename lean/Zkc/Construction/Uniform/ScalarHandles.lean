module

public import Zkc.Construction.Uniform.SourceProcess
public import Zkc.Source.Interpretation

@[expose] public section

/-! The retained scalar handler does not observe service capability labels.
Nominal execution still uses its canonical ABI labels. This proved presentation
law permits arbitrary legacy handles without changing the actual connection. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.ScalarHandles
open Zkc.Source
variable {F G A : Type}

def replace (handle : Nat) : PIR.OperationInterpretation (Actions F G) (Actions F G)
  | .query site field _ => .call (.query site field (.cons handle .nil)) .done
  | operation => .call operation .done

theorem sourceView (context : Context) (handle : Nat) (process : PIR.Process (Actions F G) A)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    SourceProcess.sourceView context (process.interpret (replace handle)) history =
      SourceProcess.sourceView context process history := by
  induction process generalizing history with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
    cases operation <;> simp only [PIR.Process.interpret, replace, PIR.Process.bind,
      SourceProcess.sourceView]
    all_goals congr 1; funext result; exact ih _ result.2

theorem transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (context : Context) (handle : Nat) (challenge : History F G → m F)
    (process : PIR.Process (Actions F G) A) (initial : History F G) (proof : Proof F G) :
    Zkc.Construction.transform context challenge (process.interpret (replace handle)) initial proof =
      Zkc.Construction.transform context challenge process initial proof := by
  have left := SourceProcess.sourceView_transform_map context challenge
    (process.interpret (replace handle)) id initial proof
  have right := SourceProcess.sourceView_transform_map context challenge process id initial proof
  rw [sourceView] at left
  simpa only [id_eq, PIR.Process.bind_done] using left.symm.trans right

end Zkc.Construction.Uniform.ScalarHandles

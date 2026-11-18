module

public import Zkc.Core.Evidence.FunctionReadback

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.SingletonTable
open Core
variable {V : Vocabulary} (t : V.Ty) (free : Ty.isLinear V t = false)

abbrev header (k : Key) : FnHeader V := ⟨k,[.seq t (some 1),.seq t (some 0)],[t],false,none,⟨[],[]⟩⟩

def body (k : Key) (earlier : List (FnHeader V)) :
    Fn V earlier (header t k) (.cons 0 (.cons 1 .nil)) :=
  .op ⟨0⟩ (.literal .nat [0] rfl) .nil (.cons 2 .nil) <|
  .op ⟨1⟩ (.owned (.seqAt t (some 1) free)) (.cons ⟨0,rfl⟩ (.cons ⟨2,rfl⟩ .nil)) (.cons 3 .nil) <|
  .ret (.cons ⟨3,rfl⟩ .nil)

/-- Evaluation of a one-entry Boolean cube at its unique point. -/
def Law (k : Key) (run : FunctionMeaning (header t k)) : Prop :=
  ∀ (M : Model V) (v : M.Val t), run M (.cons [v] (.cons [] .nil)) = .done (.cons v .nil)

def readback (k : Key) : FunctionReadback _ (Law t k) where
  inputs := .cons 0 (.cons 1 .nil)
  body := body t free k
  armed _ := rfl
  holds _ _ _ _ := rfl

end Zkc.Formal.Interactive.Sumcheck.SingletonTable

import Zkc.Source.Program
import Zkc.Semantics.Interpretation

/-! Sequencing independently authored typed source regions.

The second region receives the first region's result followed by the original
context. Substitution at returning leaves and weakening under binders keep
both regions as inspectable source syntax. Loop bodies are unchanged; the
second region runs after the loop and its continuation return successfully.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type}

/-- Keep existing variables beneath a new context entry. -/
def Renaming.weaken {Γ : List Ty} {ty : Ty} : Renaming Γ (ty :: Γ) :=
  fun value => .there value

/-- Replace the newest variable with an existing variable of the same type. -/
def Renaming.substHead {Γ : List Ty} {ty : Ty} (value : Var Γ ty) :
    Renaming (ty :: Γ) Γ
  | _, .here => value
  | _, .there previous => previous

variable {language : Language} {interface : PIR.Signature}

/-- Sequence typed regions without introducing a host-language continuation.
The returned value may alias an original input. The second region's original
captures are weakened beneath local operation results and loop accumulators. -/
def Program.seq {Γ : List language.Ty} {a b : language.Ty}
    (program : Program language Γ a) (next : Program language (a :: Γ) b) :
    Program language Γ b :=
  match program with
  | .ret value => next.rename (Renaming.substHead value)
  | .stop reason => .stop reason
  | .letOp op arguments tail =>
    .letOp op arguments (tail.seq (next.rename (Renaming.lift Renaming.weaken)))
  | .branch condition yes no => .branch condition (yes.seq next) (no.seq next)
  | .iterate count initial body tail =>
    .iterate count initial body (tail.seq (next.rename (Renaming.lift Renaming.weaken)))

/-- Source sequencing denotes semantic binding for every interpretation and
input environment, including interpretations that expand or stop operations. -/
theorem Program.denote_seq (meaning : Interpretation language interface)
    {Γ : List language.Ty} {a b : language.Ty} (program : Program language Γ a)
    (next : Program language (a :: Γ) b) (env : Environment meaning.Value Γ) :
    (program.seq next).denote meaning env =
      (program.denote meaning env).bind
        (fun value => next.denote meaning (env.push value)) := by
  induction program with
  | ret value =>
    simp only [seq, denote, PIR.Proc.bind, denote_rename]
    congr 1
    funext ty reference
    cases reference <;> rfl
  | stop reason => rfl
  | letOp op arguments tail ih =>
    simp only [seq, denote, PIR.Proc.bind_assoc]
    congr 1
    funext value
    rw [ih]
    congr 1
    funext result
    rw [denote_rename]
    congr 1
    funext ty reference
    cases reference <;> rfl
  | branch condition yes no yesIH noIH =>
    simp only [seq, denote]
    split <;> simp_all
  | iterate count initial body tail _ tailIH =>
    simp only [seq, denote, PIR.Proc.bind_assoc]
    congr 1
    funext value
    rw [tailIH]
    congr 1
    funext result
    rw [denote_rename]
    congr 1
    funext ty reference
    cases reference <;> rfl

/-- Execution preserves the first region's effects even if the second stops. -/
theorem Program.run_seq {S E : Type} (meaning : Interpretation language interface)
    (handler : PIR.Handler interface S E) {Γ : List language.Ty} {a b : language.Ty}
    (program : Program language Γ a) (next : Program language (a :: Γ) b)
    (env : Environment meaning.Value Γ) (state : S) :
    ((program.seq next).denote meaning env).run handler state =
      ((program.denote meaning env).run handler state).follow
        (fun value => (next.denote meaning (env.push value)).run handler) := by
  rw [denote_seq, PIR.run_bind]

end Zkc.Source

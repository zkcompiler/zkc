module

public import Zkc.Core.Program.Stepped
public import Zkc.Core.Meaning.Fold

@[expose] public section

/-! The semantics of instruction prefixes. -/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D)

/-! ## The meaning of a prefix -/

/-- The meaning of a prefix, in continuation-passing form: its steps, then `k` in the environment
that they end in. -/
def Prefix.denote {A : Type} : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → List Frame → Env sem.Val Γ →
    (Env sem.Val Δ → Process sem.S sem.H A) → Process sem.S sem.H A
  | _, _, .nil, _, env, k => k env
  | _, _, .step key i results rest, path, env, k =>
      (i.denote sem key path env).bind fun values =>
        rest.denote path (env.extend results values) k

/-- **A prefix followed by a term means the prefix, then the term.** -/
theorem Prefix.denote_fill {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (t : Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ) :
    (p.fill t).denote sem path env = p.denote sem path env fun env' => t.denote sem path env' := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.fill, Term.denote_step, Prefix.denote]
      congr 1
      funext values
      exact ih _ _

/-- Two prefixes, one after the other, mean the first, then the second. -/
theorem Prefix.denote_append {A : Type} {Γ Δ Θ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (q : Prefix D Δ Θ) (path : List Frame) (env : Env sem.Val Γ)
    (k : Env sem.Val Θ → Process sem.S sem.H A) :
    (p.append q).denote sem path env k =
      p.denote sem path env fun env' => q.denote sem path env' k := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.append, Prefix.denote]
      congr 1
      funext values
      exact ih _ _

/-- The process of a prefix on its own: the environment that it ends in. -/
def Prefix.run {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame) (env : Env sem.Val Γ) :
    Process sem.S sem.H (Env sem.Val Δ) :=
  p.denote sem path env .done

/-- The meaning of a prefix with any continuation is its process, then the continuation. -/
theorem Prefix.denote_eq_run {A : Type} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame)
    (env : Env sem.Val Γ) (k : Env sem.Val Δ → Process sem.S sem.H A) :
    p.denote sem path env k = (p.run sem path env).bind k := by
  induction p with
  | nil => rfl
  | step key i results rest ih =>
      simp only [Prefix.run, Prefix.denote] at ih ⊢
      rw [Process.bind_assoc]
      congr 1
      funext values
      exact ih _ _

/-- **A prefix followed by a term is the prefix's process, then the term** on the environment
that the prefix ends in. -/
theorem Prefix.denote_fill_run {outs : List D.Ty} {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ)
    (t : Term D Δ outs) (path : List Frame) (env : Env sem.Val Γ) :
    (p.fill t).denote sem path env = (p.run sem path env).bind fun env' => t.denote sem path env' :=
  (p.denote_fill sem t path env).trans (p.denote_eq_run sem path env _)

end

end Zkc.Core

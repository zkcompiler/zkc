module

public import Zkc.Source.Expansion
public import Zkc.Source.RawSemantics

@[expose] public section

/-! Translation validation by certified normalization of actual source bodies.

Normalization is a sufficient criterion, not a complete equivalence decision.
Both inputs are elaborated and every operation remains interpreted by the same
explicit meaning. A producer may propose any candidate; success refers to the
two raw bodies passed to this checker, not to a producer-supplied digest.
-/

namespace Zkc.Source

variable {language : Language} {I : PIR.Signature}

structure Normalizer (meaning : Interpretation language I) where
  apply : {Γ : List language.Ty} → {ty : language.Ty} →
    Program language Γ ty → Program language Γ ty
  sound : ∀ {Γ ty} (program : Program language Γ ty) (env : Environment meaning.Value Γ),
    (apply program).denote meaning env = program.denote meaning env

namespace Normalizer

variable {meaning : Interpretation language I}

def identity : Normalizer meaning := ⟨id, fun _ _ => rfl⟩

def expansion (replacement : OperationExpansion language) (sound : replacement.Sound meaning) :
    Normalizer meaning := ⟨Program.expand replacement, Program.denote_expand replacement meaning sound⟩

def compose (first second : Normalizer meaning) : Normalizer meaning where
  apply program := second.apply (first.apply program)
  sound program env := (second.sound (first.apply program) env).trans (first.sound program env)

variable [DecidableEq language.Ty] [DecidableEq language.Op]

def check (normalizer : Normalizer meaning) (Γ : List language.Ty) (ty : language.Ty)
    (source candidate : RawProgram language.Ty language.Op) : Bool :=
  match source.elaborate Γ ty, candidate.elaborate Γ ty with
  | .ok first, .ok second => decide ((normalizer.apply first).erase = (normalizer.apply second).erase)
  | _, _ => false

/-- Kernel theorem for the executable checker. This establishes equality of
open processes for all values, before fixing an honest or adversarial handler. -/
theorem check_sound (normalizer : Normalizer meaning) (Γ : List language.Ty) (ty : language.Ty)
    (source candidate : RawProgram language.Ty language.Op)
    (checked : normalizer.check Γ ty source candidate = true)
    (env : Environment meaning.Value Γ) :
    source.denote meaning ty env = candidate.denote meaning ty env := by
  cases firstEq : source.elaborate Γ ty with
  | error e => simp [check, firstEq] at checked
  | ok first =>
    cases secondEq : candidate.elaborate Γ ty with
    | error e => simp [check, firstEq, secondEq] at checked
    | ok second =>
      have erased : (normalizer.apply first).erase = (normalizer.apply second).erase := by
        simpa only [check, firstEq, secondEq, decide_eq_true_eq] using checked
      have formed := congrArg (RawProgram.elaborate (language := language) Γ ty) erased
      rw [Program.elaborate_erase, Program.elaborate_erase] at formed
      have same := Except.ok.inj formed
      rw [source.denote_elaborate meaning first firstEq env,
        candidate.denote_elaborate meaning second secondEq env,
        ← normalizer.sound first env, ← normalizer.sound second env, same]

end Normalizer
end Zkc.Source

module

public import Zkc.Source.Composition

@[expose] public section

/-! Context-preserving expansion of selected operation bodies.

Each replacement receives exactly the declared operands. One pass expands
original occurrences once; it does not recursively unfold a possibly cyclic
helper dictionary. A caller may compose finitely many proved passes.
-/

namespace Zkc.Source

variable {language : Language} {I : PIR.Signature}

abbrev OperationExpansion (language : Language) :=
  (op : language.Op) → Option (Program language (language.arguments op) (language.result op))

def Program.expand (replacement : OperationExpansion language) {Γ ty} :
    Program language Γ ty → Program language Γ ty
  | .ret value => .ret value
  | .stop reason => .stop reason
  | .letOp op arguments next =>
    match replacement op with
    | none => .letOp op arguments (next.expand replacement)
    | some body => (body.rename arguments.get).seq (next.expand replacement)
  | .branch condition yes no =>
    .branch condition (yes.expand replacement) (no.expand replacement)
  | .iterate count initial body next =>
    .iterate count initial (body.expand replacement) (next.expand replacement)

def OperationExpansion.Sound (replacement : OperationExpansion language)
    (meaning : Interpretation language I) : Prop :=
  ∀ op body, replacement op = some body →
    ∀ arguments, body.denote meaning arguments.get = meaning.operation op arguments

/-- A local body equation lifts through captures, guards, loops, effects and
stops. There is no whole-program correspondence premise. -/
theorem Program.denote_expand (replacement : OperationExpansion language)
    (meaning : Interpretation language I) (sound : replacement.Sound meaning)
    {Γ ty} (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    (program.expand replacement).denote meaning env = program.denote meaning env := by
  induction program with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih =>
    cases selected : replacement op with
    | none =>
      simp only [expand, selected, denote]
      congr 1
      funext value
      exact ih (env.push value)
    | some body =>
      simp only [expand, selected, denote_seq, denote_rename, denote]
      have actual : body.denote meaning (fun v => env (arguments.get v)) =
          meaning.operation op (Operands.eval env arguments) := by
        calc
          _ = body.denote meaning (Operands.eval env arguments).get := by
            congr 1
            funext ty value
            exact (Operands.get_eval env arguments value).symm
          _ = _ := sound op body selected (Operands.eval env arguments)
      rw [actual]
      congr 1
      funext value
      exact ih (env.push value)
  | branch condition yes no yesIH noIH => simp only [expand, denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
      simp only [expand, denote, bodyIH, nextIH]

end Zkc.Source

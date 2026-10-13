module

public import Zkc.Source.Decoding

@[expose] public section

/-! Direct execution of the raw finite source grammar.

This evaluator never calls elaboration or typed program denotation. It shares
only operand lookup and primitive meanings with the typed semantics. Malformed
operands refuse when reached; successful static admission additionally checks
dormant branches and zero-iteration bodies. The correspondence theorem applies
to admitted raw syntax, not to JSON parsing or the native exporter.
-/

namespace Zkc.Source

variable {language : Language} [DecidableEq language.Ty] {I : PIR.Signature}

def RawProgram.denote (meaning : Interpretation language I) :
    (raw : RawProgram language.Ty language.Op) → {Γ : List language.Ty} →
      (ty : language.Ty) → Environment meaning.Value Γ → PIR.Proc I (meaning.Value ty)
  | .ret index, Γ, ty, env =>
    match decodeVariable Γ ty index with
    | .ok value => .done (env value)
    | .error _ => .halt .refused
  | .stop reason, _, _, _ => .halt reason
  | .letOp op indices next, Γ, ty, env =>
    match decodeOperands Γ (language.arguments op) indices with
    | .ok arguments => (meaning.operation op (Operands.eval env arguments)).bind fun value =>
        next.denote meaning ty (env.push value)
    | .error _ => .halt .refused
  | .branch index yes no, Γ, ty, env =>
    match decodeVariable Γ language.condition index with
    | .ok condition =>
      if meaning.condition (env condition) then yes.denote meaning ty env
      else no.denote meaning ty env
    | .error _ => .halt .refused
  | .iterate count acc index body next, Γ, ty, env =>
    match decodeVariable Γ acc index with
    | .ok initial =>
      (PIR.repeatN count (fun value => body.denote meaning acc (env.push value))
        (env initial)).bind fun value => next.denote meaning ty (env.push value)
    | .error _ => .halt .refused

/-- All replies and control paths, not just honest or tested executions, agree.
The result is equality of open processes, before any handler is selected. -/
theorem RawProgram.denote_elaborate (meaning : Interpretation language I)
    (raw : RawProgram language.Ty language.Op) {Γ ty}
    (program : Program language Γ ty) (admitted : raw.elaborate Γ ty = .ok program)
    (env : Environment meaning.Value Γ) :
    raw.denote meaning ty env = program.denote meaning env := by
  induction raw generalizing Γ ty with
  | ret index =>
    cases lookup : decodeVariable Γ ty index with
    | error e => simp [RawProgram.elaborate, lookup] at admitted; cases admitted
    | ok value =>
      simp [RawProgram.elaborate, lookup] at admitted
      cases admitted
      simp [RawProgram.denote, lookup, Program.denote]
  | stop reason =>
    cases admitted
    rfl
  | letOp op indices next ih =>
    cases lookup : decodeOperands Γ (language.arguments op) indices with
    | error e => simp [RawProgram.elaborate, lookup] at admitted; cases admitted
    | ok arguments =>
      cases formed : next.elaborate (language.result op :: Γ) ty with
      | error e => simp [RawProgram.elaborate, lookup, formed] at admitted; cases admitted
      | ok tail =>
        simp [RawProgram.elaborate, lookup, formed] at admitted
        cases admitted
        simp only [RawProgram.denote, lookup, Program.denote]
        congr 1
        funext value
        exact ih tail formed (env.push value)
  | branch index yes no yesIH noIH =>
    cases lookup : decodeVariable Γ language.condition index with
    | error e => simp [RawProgram.elaborate, lookup] at admitted; cases admitted
    | ok condition =>
      cases formedYes : yes.elaborate Γ ty with
      | error e => simp [RawProgram.elaborate, lookup, formedYes] at admitted; cases admitted
      | ok yesProgram =>
        cases formedNo : no.elaborate Γ ty with
        | error e => simp [RawProgram.elaborate, lookup, formedYes, formedNo] at admitted; cases admitted
        | ok noProgram =>
          simp [RawProgram.elaborate, lookup, formedYes, formedNo] at admitted
          cases admitted
          simp only [RawProgram.denote, lookup, Program.denote]
          split
          · exact yesIH yesProgram formedYes env
          · exact noIH noProgram formedNo env
  | iterate count acc index body next bodyIH nextIH =>
    cases lookup : decodeVariable Γ acc index with
    | error e => simp [RawProgram.elaborate, lookup] at admitted; cases admitted
    | ok initial =>
      cases formedBody : body.elaborate (acc :: Γ) acc with
      | error e => simp [RawProgram.elaborate, lookup, formedBody] at admitted; cases admitted
      | ok bodyProgram =>
        cases formedNext : next.elaborate (acc :: Γ) ty with
        | error e => simp [RawProgram.elaborate, lookup, formedBody, formedNext] at admitted; cases admitted
        | ok nextProgram =>
          simp [RawProgram.elaborate, lookup, formedBody, formedNext] at admitted
          cases admitted
          simp only [RawProgram.denote, lookup, Program.denote]
          have bodySame :
              (fun value => body.denote meaning acc (env.push value)) =
                (fun value => bodyProgram.denote meaning (env.push value)) := by
            funext value
            exact bodyIH bodyProgram formedBody (env.push value)
          rw [bodySame]
          congr 1
          funext value
          exact nextIH nextProgram formedNext (env.push value)

@[simp] theorem Program.denote_erase (meaning : Interpretation language I) {Γ ty}
    (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    program.erase.denote meaning ty env = program.denote meaning env :=
  program.erase.denote_elaborate meaning program (Program.elaborate_erase program) env

end Zkc.Source

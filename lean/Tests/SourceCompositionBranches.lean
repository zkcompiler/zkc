module

public import Zkc.Source.Structured.NormalizedRoot
public meta import ZkcTools.StructuredSource.Composition

/-! Composition must check complete branch results and every application. -/
section
variable {I : PIR.Signature} {A B C : Type}
  (first : PIR.Process I A) (next : A → PIR.Process I B)
  (finish : B → PIR.Process I C)

example (choice : Option Bool) :
    (match choice with
      | none => (first.bind next).bind finish
      | some enabled => if enabled then (first.bind next).bind finish
          else first.bind (fun value => (next value).bind finish)) =
    (match choice with
      | none => first.bind (fun value => (next value).bind finish)
      | some enabled => if enabled then first.bind (fun value => (next value).bind finish)
          else (first.bind next).bind finish) := by
  source_composition_equation atoms []

example (choice : Option Bool) :
    ((match choice with
      | none => first.bind next
      | some _ => first.bind next).bind finish) =
    (match choice with
      | none => first.bind (fun value => (next value).bind finish)
      | some _ => first.bind (fun value => (next value).bind finish)) := by
  source_composition_equation atoms []

example (value : A) : (PIR.Process.done value : PIR.Process I A) = .done value := by
  -- A failed proposal cannot authorize different complete returned values.
  fail_if_success
    have : (PIR.Process.done (true, value) : PIR.Process I (Bool × A)) = .done (false, value) := by
      source_composition_equation atoms []
  rfl
end

section
open Zkc.Source Zkc.Source.Structured
variable {I : PIR.Signature} {Value : Ty → Type} {ty : Ty}
example (process : PIR.Process I (Values Value [ty])) :
    (process.bind fun out => .done (.cons (out.get .here) .nil)) = process := by
  source_composition_equation atoms []
end

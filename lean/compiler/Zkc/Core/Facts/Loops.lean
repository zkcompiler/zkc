module

public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
The count of every loop that a run reaches, and the bounds of loops by their places.

`Term.EveryLoop` is a property of the count of every loop that a run of a term reaches, by the
same recursion as `Term.denote`: at every loop that a run reaches, on every path with permitted
replies, its count satisfies a predicate of the blocks around it and its key. An annotation is the
bound of every loop as often as a count, by its place (`Annotation`), what the check of facts
gives beside its verdict, and a loop is bounded by it when it runs at most as often as the bound
at its place (`Annotation.Bounded`). Nothing here is about a dialect or the vocabulary: what it is
for a program to respect an annotation is in `Facts/Facts.lean`.
-/

namespace Zkc.Core

/-! ## At every loop that a run reaches -/

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
  (B : List (Key × Nat) → Key → Nat → Prop)

mutual
  /-- At every loop that a run reaches, on every path with permitted replies, its count
  satisfies `B` at the blocks around it and its key. The blocks are those of the program as
  written: a block adds itself, a loop's body does not. -/
  def Term.EveryLoop : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Frame →
      List (Key × Nat) → Env sem.Val Γ → Prop
    | _, _, .ret _, _, _, _ => True
    | _, _, .op key o args results rest, path, blocks, env =>
        (sem.op key o path (env.all args)).Every permitted
          (fun values => Term.EveryLoop rest path blocks (env.extend results values))
          (fun _ => True)
    | _, _, .guard _ _ c ok _ rest, path, blocks, env =>
        sem.holds ok (env.get c) = true → Term.EveryLoop rest path blocks env
    | _, _, .choose _ _ c ok _ onTrue onFalse results rest, path, blocks, env =>
        (bif sem.holds ok (env.get c) then Term.EveryLoop onTrue path blocks env
          else Term.EveryLoop onFalse path blocks env) ∧
          (bif sem.holds ok (env.get c) then onTrue.denote sem path env
            else onFalse.denote sem path env).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (env.extend results mids))
            (fun _ => True)
    | _, _, .cases _ _ x ok _ arms results rest, path, blocks, env =>
        Arms.EveryLoop arms path blocks env (sem.pick ok (env.get x)) ∧
          (arms.denote sem path env (sem.pick ok (env.get x))).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (env.extend results mids))
            (fun _ => True)
    | _, _, .loop (each := each) key w times _ init inputs body results rest, path, blocks, env =>
        B blocks key (sem.times times env) ∧
          (∀ i, i < sem.times times env →
            (Process.iterate i
                (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
                0 (env.all init, HList.empties each)).Every permitted
              (fun state => Term.EveryLoop body (path ++ [.iteration key i]) blocks
                (env.extend inputs (.cons (sem.index w i) state.1))) (fun _ => True)) ∧
          (Process.iterate (sem.times times env)
              (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
              0 (env.all init, HList.empties each)).Every permitted
            (fun state => Term.EveryLoop rest path blocks
              (env.extend results (state.1.append (sem.collected times.size state.2))))
            (fun _ => True)
    | _, _, .block key number body results rest, path, blocks, env =>
        Term.EveryLoop body (path ++ [.iteration key number]) (blocks ++ [(key, number)]) env ∧
          (body.denote sem (path ++ [.iteration key number]) env).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (env.extend results mids))
            (fun _ => True)
    | _, _, .attempt key w _ inputs body results rest, path, blocks, env =>
        (sem.begin w key path).Every permitted
          (fun n => Term.EveryLoop body path blocks (env.extend inputs (.cons n .nil)) ∧
            (body.denote sem path (env.extend inputs (.cons n .nil))).Every permitted
              (fun mids => (sem.settle w key path).Every permitted
                (fun _ => Term.EveryLoop rest path blocks (env.extend results mids))
                (fun _ => True))
              (fun _ => True))
          (fun _ => True)
  /-- At every loop that a run of the arm of the alternative reaches, its payload bound to the
  name of the arm's input. -/
  def Arms.EveryLoop : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
      List Frame → List (Key × Nat) → Env sem.Val Γ → Pick sem.Val payloads → Prop
    | _, _, _, .cons inputs arm _, path, blocks, env, .here v =>
        Term.EveryLoop arm path blocks (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, blocks, env, .there p => Arms.EveryLoop rest path blocks env p
end

end

/-! ## What the check of facts gives beside its verdict -/

/-- The bound of every loop as often as a count, by its place: what the check of facts knows of
an admitted program that a consumer reads. What it knows at an instruction is not data: it is
the invariant of its proof. -/
structure Annotation where
  bounds : List (Place × Nat)
deriving DecidableEq

/-- The bound that an annotation gives a loop at a place. -/
def Annotation.boundAt (annotation : Annotation) (place : Place) : Option Nat :=
  (annotation.bounds.find? fun entry => decide (entry.1 = place)).map (·.2)

/-- The loop at the place runs at most as often as the bound that the annotation gives
there. -/
def Annotation.Bounded (annotation : Annotation) (definition : Key) (role : Option Role)
    (blocks : List (Key × Nat)) (key : Key) (count : Nat) : Prop :=
  ∀ bound, annotation.boundAt ⟨definition, blocks, some key, role⟩ = some bound → count ≤ bound

end Zkc.Core

module

public import Zkc.Core.Facts.Loops
public import Zkc.Core.Meaning.Stepped

@[expose] public section

/-!
The count of every loop that a run reaches, on the term in steps.

`Stepped.Term.EveryLoop` says of a term in steps what `Term.EveryLoop` (`Facts/Loops.lean`) says of
a term: at every loop that a run reaches, on every path with permitted replies, its count satisfies
`B` at the blocks around it and its key. The loops of a step are those of its instruction
(`Stepped.Instr.EveryLoop`: of a choice, those of the region that its condition chooses; of a case
analysis, those of the arm of its subject's alternative; of a loop, its own count and those of its
body at every iteration below the count; of a block, those of its body under its frame, the block
added to the blocks; of an attempt, those of its body at every number that its beginning gives),
and those of the rest at every result that the instruction can return
(`Stepped.Term.everyLoop_step`). The translations keep it (`Term.everyLoop_toStepped`,
`Stepped.Term.everyLoop_toTerm`), of arms too (`Arms.everyLoop_toStepped`,
`Stepped.Arms.everyLoop_toArms`), and an instruction translated back in front of a term reaches
the loops of the instruction and those of the term at every result that the instruction can
return (`Stepped.Instr.everyLoop_toTerm`), proved from the equations of the meaning
(`Meaning/Stepped.lean`).
-/

namespace Zkc.Core

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
  (B : List (Key × Nat) → Key → Nat → Prop)

mutual
  /-- At every loop that a run of a term in steps reaches, on every path with permitted replies,
  its count satisfies `B` at the blocks around it and its key. The blocks are those of the
  program as written: a block adds itself, a loop's body does not. -/
  def Stepped.Term.EveryLoop : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Stepped.Term D Γ outs →
      List Frame → List (Key × Nat) → Env sem.Val Γ → Prop
    | _, _, .ret _, _, _, _ => True
    | _, _, .step key i results rest, path, blocks, env =>
        Stepped.Instr.EveryLoop key i path blocks env ∧
          (i.denote sem key path env).Every permitted
            (fun values => Stepped.Term.EveryLoop rest path blocks (env.extend results values))
            (fun _ => True)
  /-- At every loop that a run of what an instruction at a key runs reaches. -/
  def Stepped.Instr.EveryLoop (key : Key) : {Γ : Ctx D.Ty} → {mid : List D.Ty} →
      Stepped.Instr D Γ mid → List Frame → List (Key × Nat) → Env sem.Val Γ → Prop
    | _, _, .op _ _, _, _, _ => True
    | _, _, .guard _ _ _ _, _, _, _ => True
    | _, _, .choose _ c ok _ onTrue onFalse, path, blocks, env =>
        bif sem.holds ok (env.get c) then Stepped.Term.EveryLoop onTrue path blocks env
        else Stepped.Term.EveryLoop onFalse path blocks env
    | _, _, .cases _ x ok _ arms, path, blocks, env =>
        Stepped.Arms.EveryLoop arms path blocks env (sem.pick ok (env.get x))
    | _, _, .loop (each := each) w times _ init inputs body, path, blocks, env =>
        B blocks key (sem.times times env) ∧
          ∀ i, i < sem.times times env →
            (Process.iterate i
                (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
                0 (env.all init, HList.empties each)).Every permitted
              (fun state => Stepped.Term.EveryLoop body (path ++ [.iteration key i]) blocks
                (env.extend inputs (.cons (sem.index w i) state.1))) (fun _ => True)
    | _, _, .block number body, path, blocks, env =>
        Stepped.Term.EveryLoop body (path ++ [.iteration key number]) (blocks ++ [(key, number)])
          env
    | _, _, .attempt w _ inputs body, path, blocks, env =>
        (sem.begin w key path).Every permitted
          (fun n => Stepped.Term.EveryLoop body path blocks (env.extend inputs (.cons n .nil)))
          (fun _ => True)
  /-- At every loop that a run of the arm of the alternative reaches, its payload bound to the
  name of the arm's input. -/
  def Stepped.Arms.EveryLoop : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Stepped.Arms D Γ mid payloads → List Frame → List (Key × Nat) → Env sem.Val Γ →
      Pick sem.Val payloads → Prop
    | _, _, _, .cons inputs arm _, path, blocks, env, .here v =>
        Stepped.Term.EveryLoop arm path blocks (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, blocks, env, .there p =>
        Stepped.Arms.EveryLoop rest path blocks env p
end

/-- An exit reaches no loop. -/
theorem Stepped.Term.everyLoop_ret {Γ : Ctx D.Ty} {outs : List D.Ty} (exit : HList (Var Γ) outs)
    (path : List Frame) (blocks : List (Key × Nat)) (env : Env sem.Val Γ) :
    (Stepped.Term.ret exit).EveryLoop sem permitted B path blocks env ↔ True :=
  Iff.rfl

/-- **The loops of a step** are those of its instruction, and those of the rest at every result
that the instruction can return. -/
theorem Stepped.Term.everyLoop_step {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) (results : Names mid)
    (rest : Stepped.Term D (Γ.extend results) outs) (path : List Frame)
    (blocks : List (Key × Nat)) (env : Env sem.Val Γ) :
    (Stepped.Term.step key i results rest).EveryLoop sem permitted B path blocks env ↔
      Stepped.Instr.EveryLoop sem permitted B key i path blocks env ∧
        (i.denote sem key path env).Every permitted
          (fun values => rest.EveryLoop sem permitted B path blocks (env.extend results values))
          (fun _ => True) :=
  Iff.rfl

mutual
  /-- **A term in steps reaches the loops that the term reaches**, with the same counts. -/
  theorem Term.everyLoop_toStepped : ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
      (path : List Frame) (blocks : List (Key × Nat)) (env : Env sem.Val Γ),
      t.toStepped.EveryLoop sem permitted B path blocks env ↔
        t.EveryLoop sem permitted B path blocks env
    | _, _, .ret _, _, _, _ => Iff.rfl
    | _, _, .op _ _ _ _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_op, Term.EveryLoop, Term.everyLoop_toStepped rest, true_and]
    | _, _, .guard _ _ c ok _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_guard, Term.EveryLoop, true_and]
        cases sem.holds ok (env.get c) with
        | false => exact ⟨(fun _ never => nomatch never), fun _ => trivial⟩
        | true =>
            exact ⟨fun later _ => (Term.everyLoop_toStepped rest path blocks env).mp later,
              fun later => (Term.everyLoop_toStepped rest path blocks env).mpr (later rfl)⟩
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_choose, Term.EveryLoop, Term.denote_toStepped,
          Term.everyLoop_toStepped onTrue, Term.everyLoop_toStepped onFalse,
          Term.everyLoop_toStepped rest]
    | _, _, .cases _ _ _ _ _ arms _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_cases, Term.EveryLoop, Arms.denote_toStepped,
          Arms.everyLoop_toStepped arms, Term.everyLoop_toStepped rest]
    | _, _, .loop _ _ _ _ _ _ body _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_loop, Term.EveryLoop, Term.denote_toStepped, Process.every_bind,
          Process.Every, Term.everyLoop_toStepped body, Term.everyLoop_toStepped rest, and_assoc]
    | _, _, .block _ _ body _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_block, Term.EveryLoop, Term.denote_toStepped,
          Term.everyLoop_toStepped body, Term.everyLoop_toStepped rest]
    | _, _, .attempt _ _ _ _ body _ rest, path, blocks, env => by
        simp only [Term.toStepped, Stepped.Term.everyLoop_step, Stepped.Instr.EveryLoop,
          Stepped.Instr.denote_attempt, Term.EveryLoop, Term.denote_toStepped, Process.every_bind,
          Process.Every, Term.everyLoop_toStepped body, Term.everyLoop_toStepped rest]
        exact ⟨fun ⟨first, second⟩ => Process.every_mono _ _ (fun _ both => both)
            (fun _ _ => trivial) (Process.every_and _ _ first second),
          fun both => ⟨Process.every_mono _ _ (fun _ each => each.1) (fun _ stop => stop) both,
            Process.every_mono _ _ (fun _ each => each.2) (fun _ stop => stop) both⟩⟩
  /-- Arms in steps reach the loops that the arms reach. -/
  theorem Arms.everyLoop_toStepped : ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
      (arms : Arms D Γ mid payloads) (path : List Frame) (blocks : List (Key × Nat))
      (env : Env sem.Val Γ) (pick : Pick sem.Val payloads),
      arms.toStepped.EveryLoop sem permitted B path blocks env pick ↔
        arms.EveryLoop sem permitted B path blocks env pick
    | _, _, _, .nil, _, _, _, pick => nomatch pick
    | _, _, _, .cons _ arm _, path, blocks, env, .here _ => by
        simp only [Arms.toStepped, Stepped.Arms.EveryLoop, Arms.EveryLoop,
          Term.everyLoop_toStepped arm]
    | _, _, _, .cons _ _ rest, path, blocks, env, .there _ => by
        simp only [Arms.toStepped, Stepped.Arms.EveryLoop, Arms.EveryLoop,
          Arms.everyLoop_toStepped rest]
end

/-- **A term in steps, as a term, reaches the loops that it reaches.** -/
theorem Stepped.Term.everyLoop_toTerm {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Stepped.Term D Γ outs) (path : List Frame) (blocks : List (Key × Nat))
    (env : Env sem.Val Γ) :
    t.toTerm.EveryLoop sem permitted B path blocks env ↔
      t.EveryLoop sem permitted B path blocks env := by
  conv => rhs; rw [← Stepped.Term.toTerm_toStepped t]
  exact (Term.everyLoop_toStepped sem permitted B t.toTerm path blocks env).symm

/-- Arms in steps, as arms, reach the loops that they reach. -/
theorem Stepped.Arms.everyLoop_toArms {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    (arms : Stepped.Arms D Γ mid payloads) (path : List Frame) (blocks : List (Key × Nat))
    (env : Env sem.Val Γ) (pick : Pick sem.Val payloads) :
    arms.toArms.EveryLoop sem permitted B path blocks env pick ↔
      arms.EveryLoop sem permitted B path blocks env pick := by
  conv => rhs; rw [← Stepped.Arms.toArms_toStepped arms]
  exact (Arms.everyLoop_toStepped sem permitted B arms.toArms path blocks env pick).symm

/-- **An instruction translated back in front of a term reaches the loops of the instruction**,
and those of the term at every result that the instruction can return. -/
theorem Stepped.Instr.everyLoop_toTerm {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Stepped.Instr D Γ mid) (results : Names mid)
    (rest : Zkc.Core.Term D (Γ.extend results) outs) (path : List Frame)
    (blocks : List (Key × Nat)) (env : Env sem.Val Γ) :
    (Stepped.Instr.toTerm key i results rest).EveryLoop sem permitted B path blocks env ↔
      Stepped.Instr.EveryLoop sem permitted B key i path blocks env ∧
        (i.denote sem key path env).Every permitted
          (fun values => rest.EveryLoop sem permitted B path blocks (env.extend results values))
          (fun _ => True) := by
  rw [← Term.everyLoop_toStepped sem permitted B (Stepped.Instr.toTerm key i results rest) path
    blocks env, Stepped.Instr.toTerm_toStepped, Stepped.Term.everyLoop_step]
  simp only [Term.everyLoop_toStepped]

end

end Zkc.Core

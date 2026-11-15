module

public import Zkc.Core.Meaning.Program

@[expose] public section

/-!
What an annotation says, as definitions.

`Term.EveryLoop` is a property of the count of every loop that a run of a term reaches, by the
same recursion as `Term.denote`. `Respects` says that no loop runs more often than the bound
that the annotation of an admitted program gives it, in every function
(`Defs.FunctionsRespect`) and every role program (`Defs.ProtocolsRespect`).
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
  def Term.EveryLoop : {Γ outs : List D.Ty} → Term D Γ outs → List Frame → List (Key × Nat) →
      Env sem.Val Γ → Prop
    | _, _, .ret _, _, _, _ => True
    | _, _, .op key o args rest, path, blocks, env =>
        (sem.op key o path (env.all args)).Every permitted
          (fun results => Term.EveryLoop rest path blocks (Env.extend results env))
          (fun _ => True)
    | _, _, .guard _ _ c ok _ rest, path, blocks, env =>
        sem.holds ok (env _ c) = true → Term.EveryLoop rest path blocks env
    | _, _, .choose _ _ c ok _ onTrue onFalse rest, path, blocks, env =>
        (bif sem.holds ok (env _ c) then Term.EveryLoop onTrue path blocks env
          else Term.EveryLoop onFalse path blocks env) ∧
          (bif sem.holds ok (env _ c) then onTrue.denote sem path env
            else onFalse.denote sem path env).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .cases _ _ x ok _ arms rest, path, blocks, env =>
        Arms.EveryLoop arms path blocks env (sem.pick ok (env _ x)) ∧
          (arms.denote sem path env (sem.pick ok (env _ x))).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .loop (each := each) key w times _ init body rest, path, blocks, env =>
        B blocks key (sem.times times env) ∧
          (∀ i, i < sem.times times env →
            (Process.iterate i (sem.loopStep w (fun path' env' => body.denote sem path' env')
                key path env) 0 (env.all init, HList.empties each)).Every permitted
              (fun state => Term.EveryLoop body (path ++ [.iteration key i]) blocks
                (Env.cons (sem.index w i) (Env.extend state.1 env))) (fun _ => True)) ∧
          (Process.iterate (sem.times times env)
              (sem.loopStep w (fun path' env' => body.denote sem path' env') key path env) 0
              (env.all init, HList.empties each)).Every permitted
            (fun state => Term.EveryLoop rest path blocks
              (Env.extend (state.1.append (sem.collected times.size state.2)) env))
            (fun _ => True)
    | _, _, .block key number body rest, path, blocks, env =>
        Term.EveryLoop body (path ++ [.iteration key number]) (blocks ++ [(key, number)]) env ∧
          (body.denote sem (path ++ [.iteration key number]) env).Every permitted
            (fun mids => Term.EveryLoop rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .attempt key w _ body rest, path, blocks, env =>
        (sem.begin w key path).Every permitted
          (fun n => Term.EveryLoop body path blocks (Env.cons n env) ∧
            (body.denote sem path (Env.cons n env)).Every permitted
              (fun mids => (sem.settle w key path).Every permitted
                (fun _ => Term.EveryLoop rest path blocks (Env.extend mids env)) (fun _ => True))
              (fun _ => True))
          (fun _ => True)
  /-- At every loop that a run of the arm of the alternative reaches. -/
  def Arms.EveryLoop : {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List Frame →
      List (Key × Nat) → Env sem.Val Γ → Pick sem.Val payloads → Prop
    | _, _, _, .cons arm _, path, blocks, env, .here v =>
        Term.EveryLoop arm path blocks (Env.cons v env)
    | _, _, _, .cons _ rest, path, blocks, env, .there p => Arms.EveryLoop rest path blocks env p
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

section
variable {V : Vocabulary} (M : Model V) (annotation : Annotation)

/-- Every function on valid inputs: no loop runs more often than its bound. -/
def Defs.FunctionsRespect : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn (hs := hs) hdr body _ rest =>
      (∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
        body.EveryLoop (localSem M hs.fns (Defs.fnTable M rest)) (fun _ _ => True)
          (annotation.Bounded hdr.key none) [] [] (Env.ofList ins)) ∧
        Defs.FunctionsRespect rest
  | _, .protocol _ _ _ rest => Defs.FunctionsRespect rest

/-- Every role program of every protocol on valid inputs and permitted replies: no loop runs more
often than its bound. -/
def Defs.ProtocolsRespect : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn _ _ _ rest => Defs.ProtocolsRespect rest
  | _, .protocol (hs := hs) hdr body _ rest =>
      (∀ (r : Role) (path : List Frame) (ins : HList (RV M r) hdr.ins), ins.All (RV.Valid M r) →
        (project r body).EveryLoop
          (roleSem M r (Defs.fnTable (hs := hs) M rest) (Defs.rTable M rest))
          (Permitted M)
          (annotation.Bounded hdr.key (some r)) path [] (Env.ofList ins)) ∧
        Defs.ProtocolsRespect rest

/-- Every function on valid inputs and every role program of every protocol on valid inputs
and permitted replies: no loop runs more often than its bound. -/
def Defs.Respects {hs : Headers V} (defs : Defs V hs) : Prop :=
  Defs.FunctionsRespect M annotation defs ∧ Defs.ProtocolsRespect M annotation defs

/-- Definitions without protocols respect an annotation in their protocols. -/
theorem Defs.protocolsRespect_of_none : ∀ {hs : Headers V} (defs : Defs V hs),
    hs.protocols = [] → Defs.ProtocolsRespect M annotation defs
  | _, .nil, _ => trivial
  | _, .fn _ _ _ rest, empty => Defs.protocolsRespect_of_none rest empty
  | _, .protocol _ _ _ _, empty => absurd empty (List.cons_ne_nil _ _)

end

/-- A program respects an annotation, under a model. -/
def Respects {V : Vocabulary} (M : Model V) (annotation : Annotation) (p : Typed V) : Prop :=
  Defs.Respects M annotation p.defs

/-- A program without protocols respects an annotation when its functions do. -/
theorem Respects.of_functions {V : Vocabulary} {M : Model V} {annotation : Annotation}
    (p : Typed V) (noProtocols : p.headers.protocols = [])
    (functions : Defs.FunctionsRespect M annotation p.defs) : Respects M annotation p :=
  ⟨functions, Defs.protocolsRespect_of_none M annotation p.defs noProtocols⟩

end Zkc.Core

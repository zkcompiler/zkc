module

public import Zkc.Core.Meaning.Program

@[expose] public section

/-!
What an annotation says, as definitions.

`Term.Everywhere` is a property of every instruction that a run of a term reaches, by the same
recursion as `Term.denote`. `Fact.Holds` reads the values in scope by level. `Respects` says
that what the annotation of an admitted program knows holds, and that no loop runs more often
than its bound, in every function and every role program.
-/

namespace Zkc.Core

/-! ## At every instruction that a run reaches -/

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
  (P : ∀ {Γ : List D.Ty}, List (Key × Nat) → Key → Env sem.Val Γ → Prop)
  (B : List (Key × Nat) → Key → Nat → Prop)

mutual
  /-- At every instruction that a run reaches, on every path with permitted replies, `P` holds
  of the blocks around it, its key and the environment there, and the count of every loop
  satisfies `B` at its blocks and its key. The blocks are those of the program as written: a
  block adds itself, a loop's body does not. -/
  def Term.Everywhere : {Γ outs : List D.Ty} → Term D Γ outs → List Frame → List (Key × Nat) →
      Env sem.Val Γ → Prop
    | _, _, .ret _, _, _, _ => True
    | _, _, .op key o args rest, path, blocks, env =>
        P blocks key env ∧
          (sem.op key o path (env.all args)).Every permitted
            (fun results => Term.Everywhere rest path blocks (Env.extend results env))
            (fun _ => True)
    | _, _, .guard key _ c ok _ rest, path, blocks, env =>
        P blocks key env ∧ (sem.holds ok (env _ c) = true → Term.Everywhere rest path blocks env)
    | _, _, .choose key _ c ok _ onTrue onFalse rest, path, blocks, env =>
        P blocks key env ∧
          (bif sem.holds ok (env _ c) then Term.Everywhere onTrue path blocks env
            else Term.Everywhere onFalse path blocks env) ∧
          (bif sem.holds ok (env _ c) then onTrue.denote sem path env
            else onFalse.denote sem path env).Every permitted
            (fun mids => Term.Everywhere rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .cases key _ x ok _ arms rest, path, blocks, env =>
        P blocks key env ∧ Arms.Everywhere arms path blocks env (sem.pick ok (env _ x)) ∧
          (arms.denote sem path env (sem.pick ok (env _ x))).Every permitted
            (fun mids => Term.Everywhere rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .loop (each := each) key w times _ init body rest, path, blocks, env =>
        P blocks key env ∧ B blocks key (sem.times times env) ∧
          (∀ i, i < sem.times times env →
            (Process.iterate i (sem.loopStep w (fun path' env' => body.denote sem path' env')
                key path env) 0 (env.all init, HList.empties each)).Every permitted
              (fun state => Term.Everywhere body (path ++ [.iteration key i]) blocks
                (Env.cons (sem.index w i) (Env.extend state.1 env))) (fun _ => True)) ∧
          (Process.iterate (sem.times times env)
              (sem.loopStep w (fun path' env' => body.denote sem path' env') key path env) 0
              (env.all init, HList.empties each)).Every permitted
            (fun state => Term.Everywhere rest path blocks
              (Env.extend (state.1.append (sem.collected times.size state.2)) env))
            (fun _ => True)
    | _, _, .block key number body rest, path, blocks, env =>
        Term.Everywhere body (path ++ [.iteration key number]) (blocks ++ [(key, number)]) env ∧
          (body.denote sem (path ++ [.iteration key number]) env).Every permitted
            (fun mids => Term.Everywhere rest path blocks (Env.extend mids env)) (fun _ => True)
    | _, _, .attempt key w _ body rest, path, blocks, env =>
        P blocks key env ∧
          (sem.begin w key path).Every permitted
            (fun n => Term.Everywhere body path blocks (Env.cons n env) ∧
              (body.denote sem path (Env.cons n env)).Every permitted
                (fun mids => (sem.settle w key path).Every permitted
                  (fun _ => Term.Everywhere rest path blocks (Env.extend mids env)) (fun _ => True))
                (fun _ => True))
            (fun _ => True)
  /-- At every instruction that a run of the arm of the alternative reaches. -/
  def Arms.Everywhere : {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List Frame →
      List (Key × Nat) → Env sem.Val Γ → Pick sem.Val payloads → Prop
    | _, _, _, .cons arm _, path, blocks, env, .here v =>
        Term.Everywhere arm path blocks (Env.cons v env)
    | _, _, _, .cons _ rest, path, blocks, env, .there p => Arms.Everywhere rest path blocks env p
end

end

/-! ## Facts -/

/-- What the check of facts knows of the values in scope, by their levels. These are some
of its forms. -/
inductive Fact where
  | le (a b : Nat)
  | lt (a b : Nat)
  | eq (a b : Nat)
  | truth (a : Nat) (value : Bool)

/-- What is known at each written place, and the bound of every loop. -/
structure Annotation where
  known : Place → List Fact
  bounds : Place → Option Nat

/-- How a dialect's values read as naturals and as truth values: nothing when a value is not
one, or when the role does not hold it. -/
structure Reading {D : Dialect} (sem : Semantics D) where
  nat : ∀ {a : D.Ty}, sem.Val a → Option Nat
  bool : ∀ {a : D.Ty}, sem.Val a → Option Bool

section
variable {V : Vocabulary} (M : Model V)

/-- A value as a natural: of `nat` or of a bounded type. -/
def Ty.readNat : (τ : V.Ty) → M.Val τ → Option Nat
  | .nat, v => some v
  | .fin _, v => some v
  | _, _ => none

/-- A value as a truth value. -/
def Ty.readBool : (τ : V.Ty) → M.Val τ → Option Bool
  | .bool, v => some v
  | _, _ => none

/-- How a function reads its values. -/
def localReading (fns : List (FnHeader V)) (table : FnTable M fns) : Reading (localSem M fns table) where
  nat := fun {a} v => Ty.readNat M a v
  bool := fun {a} v => Ty.readBool M a v

/-- How a role reads what it holds; a value that it does not hold reads as nothing. -/
def roleReading {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) : Reading (roleSem M r fnTable rTable) where
  nat := fun {a} v => if h : r ∈ a.holders then Ty.readNat M a.ty (reveal M h v) else none
  bool := fun {a} v => if h : r ∈ a.holders then Ty.readBool M a.ty (reveal M h v) else none

end

/-- The readings of the values in scope, the innermost first. -/
def Env.readings {α X : Type} {F : α → Type} (read : ∀ a, F a → Option X) :
    {Γ : List α} → Env F Γ → List (Option X)
  | [], _ => []
  | a :: _, env => read a (env a .head) :: Env.readings read (fun b x => env b (.tail x))

/-- The reading of the value at a level: a level is a position from the outermost
binding. -/
def Env.atLevel {α X : Type} {F : α → Type} (read : ∀ a, F a → Option X) {Γ : List α}
    (env : Env F Γ) (level : Nat) : Option X :=
  ((Env.readings read env).reverse[level]?).join

/-- A fact holds of the values in scope: the values that it names read as what it says. A
fact about a value that does not read (one that the role does not hold) does not hold. -/
def Fact.Holds {D : Dialect} {sem : Semantics D} (reading : Reading sem) {Γ : List D.Ty}
    (env : Env sem.Val Γ) : Fact → Prop
  | .le a b => ∃ x y, Env.atLevel (fun _ v => reading.nat v) env a = some x ∧
      Env.atLevel (fun _ v => reading.nat v) env b = some y ∧ x ≤ y
  | .lt a b => ∃ x y, Env.atLevel (fun _ v => reading.nat v) env a = some x ∧
      Env.atLevel (fun _ v => reading.nat v) env b = some y ∧ x < y
  | .eq a b => ∃ x y, Env.atLevel (fun _ v => reading.nat v) env a = some x ∧
      Env.atLevel (fun _ v => reading.nat v) env b = some y ∧ x = y
  | .truth a value => Env.atLevel (fun _ v => reading.bool v) env a = some value

/-! ## What an annotation says -/

/-- The facts that the annotation knows at the place of an instruction (a definition, the
blocks around it, its key, a role or not) hold of the environment there. -/
def Annotation.FactsHold (annotation : Annotation) {D : Dialect} {sem : Semantics D}
    (reading : Reading sem) (definition : Key) (role : Option Role) {Γ : List D.Ty}
    (blocks : List (Key × Nat)) (key : Key) (env : Env sem.Val Γ) : Prop :=
  ∀ fact, fact ∈ annotation.known ⟨definition, blocks, some key, role⟩ → fact.Holds reading env

/-- The loop at the place runs at most as often as the bound that the annotation gives
there. -/
def Annotation.Bounded (annotation : Annotation) (definition : Key) (role : Option Role)
    (blocks : List (Key × Nat)) (key : Key) (count : Nat) : Prop :=
  ∀ bound, annotation.bounds ⟨definition, blocks, some key, role⟩ = some bound → count ≤ bound

section
variable {V : Vocabulary} (M : Model V) (annotation : Annotation)

/-- Every function on valid inputs and every role program of every protocol on valid inputs
and permitted replies: what the annotation knows holds at every instruction reached, and no
loop runs more often than its bound. -/
def Defs.Respects : {hs : Headers V} → Defs V hs → Prop
  | _, .nil => True
  | _, .fn (hs := hs) hdr body _ rest =>
      (∀ ins : HList M.Val hdr.ins, ins.All M.Valid →
        body.Everywhere (localSem M hs.fns (Defs.fnTable M rest)) (fun _ _ => True)
          (fun blocks key env => annotation.FactsHold
            (localReading M hs.fns (Defs.fnTable M rest)) hdr.key none blocks key env)
          (annotation.Bounded hdr.key none) [] [] (Env.ofList ins)) ∧
        Defs.Respects rest
  | _, .protocol (hs := hs) hdr body _ rest =>
      (∀ (r : Role) (path : List Frame) (ins : HList (RV M r) hdr.ins), ins.All (RV.Valid M r) →
        (project r body).Everywhere
          (roleSem M r (Defs.fnTable (hs := hs) M rest) (Defs.rTable M rest))
          (Permitted M)
          (fun blocks key env => annotation.FactsHold
            (roleReading M r (Defs.fnTable (hs := hs) M rest) (Defs.rTable M rest))
            hdr.key (some r) blocks key env)
          (annotation.Bounded hdr.key (some r)) path [] (Env.ofList ins)) ∧
        Defs.Respects rest

end

/-- A program respects an annotation, under a model. -/
def Respects {V : Vocabulary} (M : Model V) (annotation : Annotation) (p : Typed V) : Prop :=
  Defs.Respects M annotation p.defs

end Zkc.Core

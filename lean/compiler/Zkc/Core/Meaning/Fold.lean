module

public import Zkc.Core.Meaning.Events

@[expose] public section

/-!
The meaning of a term, once for every dialect.

A dialect's semantics says what its values are, what an operation does, how a guard, a
choice and a loop read their subject, and what marks an attempt. The process of a term is one
fold over the term with that; the three meanings (a function, a protocol, a role program) are
this fold at three semantics. Nothing that reads the structure of a term is written per
dialect.

Many definitions are case analyses of a term that mirror `Term.denote` constructor by
constructor: the process with the record of its run (`Term.observe`), the count of every loop
that a run reaches (`Term.EveryLoop`), the uses of linear values (`Term.linearUses`), the walks
of `Program/Term.lean` (addresses, block keys, whether every case analysis is armed, whether a
term can stop, its calls, its bindings) and of `Program/Dialects.lean` (who acts, enclosure, the
shape), the place of a name bound twice (`Term.reboundAt`), projection, elaboration and erasure,
the walk of the check of facts, and the proofs about each. A new constructor of `Term` is added
to all of them.

A value is read and bound by name: a variable is read from the environment (`Env.get`,
`Env.all`), and a binding binds its names to its values (`Env.extend`), a later name anew.
-/

namespace Zkc.Core

/-! ## Lists of values -/

namespace HList

/-- The one value of a list of one. -/
def single {α : Type} {F : α → Type} {a : α} : HList F [a] → F a
  | .cons v .nil => v

/-- No value collected yet, of each type. -/
def empties {α : Type} {V : α → Type} : (items : List α) → HList (fun a => List (V a)) items
  | [] => .nil
  | _ :: rest => .cons [] (empties rest)

/-- One more value of each type, after those collected. -/
def push {α : Type} {V : α → Type} :
    {items : List α} → HList (fun a => List (V a)) items → HList V items →
      HList (fun a => List (V a)) items
  | [], .nil, .nil => .nil
  | _ :: _, .cons vs rest, .cons v more => .cons (vs ++ [v]) (rest.push more)

end HList


/-! ## The semantics of a dialect -/

/-- A value of one of the types, with its place among them. -/
inductive Pick {α : Type} (V : α → Type) : List α → Type where
  | here {a : α} {rest : List α} : V a → Pick V (a :: rest)
  | there {a : α} {rest : List α} : Pick V rest → Pick V (a :: rest)

structure Semantics (D : Dialect) where
  Val : D.Ty → Type
  S : Sig
  /-- What a stop carries. -/
  H : Type
  /-- An operation at its key, under the path of applications and iterations that reached
  it. -/
  op : ∀ {ins res : List D.Ty}, Key → D.Op ins res → List Frame → HList Val ins →
    Process S H (HList Val res)
  /-- Whether a condition holds. -/
  holds : ∀ {w : D.Who} {t : D.Ty}, D.Condition w t → Val t → Bool
  /-- The stop of a guard whose condition is false, at the guard's occurrence. -/
  stop : D.Who → Reason → Occurrence → H
  /-- The alternative of a variant, with its payload. -/
  pick : ∀ {w : D.Who} {t : D.Ty} {payloads : List D.Ty}, D.Alternatives w t payloads → Val t →
    Pick Val payloads
  count : ∀ {w : D.Who} {t : D.Ty}, D.Count w t → Val t → Nat
  /-- The iteration number as a value. -/
  index : (w : D.Who) → Nat → Val (D.index w)
  /-- The beginning of an attempt that `w` own, at its key under the path: the number of the
  attempt. It is `0` in the protocol as written. -/
  begin : (w : D.Who) → Key → List Frame → Process S H (Val (D.index w))
  /-- The end of the body of an attempt. -/
  settle : D.Who → Key → List Frame → Process S H Unit
  /-- The values that the iterations gave, as one value; of the size given, for a loop of a
  written number of iterations. -/
  collect : (size : Option Nat) → (a : D.Ty) → List (Val a) → Val (D.collected size a)

/-- The collected values of each type, as the loop gives them. -/
def Semantics.collected {D : Dialect} (sem : Semantics D) (size : Option Nat) :
    {each : List D.Ty} → HList (fun a => List (sem.Val a)) each →
      HList sem.Val (each.map (D.collected size))
  | [], .nil => .nil
  | a :: _, .cons vs rest => .cons (sem.collect size a vs) (sem.collected size rest)

/-- How often a loop runs, in an environment. -/
def Semantics.times {D : Dialect} (sem : Semantics D) {w : D.Who} {Γ : Ctx D.Ty} :
    Times D w Γ → Env sem.Val Γ → Nat
  | .fixed n, _ => n
  | .value count ok, env => sem.count ok (env.get count)

/-- The carried values and what was collected so far. -/
abbrev Semantics.LoopState {D : Dialect} (sem : Semantics D) (carried each : List D.Ty) : Type :=
  HList sem.Val carried × HList (fun a => List (sem.Val a)) each

/-- One iteration of a loop: the body, from the iteration number and the carried values bound to
the names of its inputs, under the frame of the iteration; it gives the carried values and adds
one value of each collected type. `run` is the process of the body. -/
def Semantics.loopStep {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {carried each : List D.Ty}
    (w : D.Who) (inputs : Names (D.index w :: carried))
    (run : List Frame → Env sem.Val (Γ.extend inputs) →
      Process sem.S sem.H (HList sem.Val (carried ++ each)))
    (key : Key) (path : List Frame) (env : Env sem.Val Γ) (i : Nat)
    (state : sem.LoopState carried each) : Process sem.S sem.H (sem.LoopState carried each) :=
  (run (path ++ [.iteration key i]) (env.extend inputs (.cons (sem.index w i) state.1))).bind
    fun out => .done ((HList.split carried out).1, state.2.push (HList.split carried out).2)

mutual
  /-- The process of a term. -/
  def Term.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → List Frame → Env sem.Val Γ →
        Process sem.S sem.H (HList sem.Val outs)
    | _, _, .ret exit, _, env => .done (env.all exit)
    | _, _, .op key o operands results rest, path, env =>
        (sem.op key o path (env.all operands)).bind fun values =>
          rest.denote sem path (env.extend results values)
    | _, _, .guard key w c ok why rest, path, env =>
        bif sem.holds ok (env.get c) then rest.denote sem path env
        else .halt (sem.stop w why ⟨path, key⟩)
    | _, _, .choose _ _ c ok _ onTrue onFalse results rest, path, env =>
        (bif sem.holds ok (env.get c) then onTrue.denote sem path env
          else onFalse.denote sem path env).bind fun mids =>
          rest.denote sem path (env.extend results mids)
    | _, _, .cases _ _ x ok _ arms results rest, path, env =>
        (arms.denote sem path env (sem.pick ok (env.get x))).bind fun mids =>
          rest.denote sem path (env.extend results mids)
    | _, _, .loop (each := each) key w times _ initial inputs body results rest, path, env =>
        (Process.iterate (sem.times times env)
          (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
          0 (env.all initial, HList.empties each)).bind fun state =>
          rest.denote sem path
            (env.extend results (state.1.append (sem.collected times.size state.2)))
    | _, _, .block key number body results rest, path, env =>
        (body.denote sem (path ++ [.iteration key number]) env).bind fun mids =>
          rest.denote sem path (env.extend results mids)
    | _, _, .attempt key w _ inputs body results rest, path, env =>
        (sem.begin w key path).bind fun n =>
          (body.denote sem path (env.extend inputs (.cons n .nil))).bind fun mids =>
            (sem.settle w key path).bind fun _ =>
              rest.denote sem path (env.extend results mids)
  /-- The process of the region of the alternative that a variant is, its payload bound to the
  name of the region's input. -/
  def Arms.denote {D : Dialect} (sem : Semantics D) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → List Frame →
        Env sem.Val Γ → Pick sem.Val payloads → Process sem.S sem.H (HList sem.Val mid)
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        arm.denote sem path (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, env, .there p => rest.denote sem path env p
end

end Zkc.Core

module

public import Zkc.Core.World.Layer
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Process.Handler

@[expose] public section

/-!
The meaning of the description of a handler, and of a stack of them.

A layer answers an effect when the site of the effect's occurrence, the role's part and the
types of what the effect takes and gives are those of one of its clauses: the clause's code,
under the role semantics, runs on what the effect takes and the state, bound by position
(`Env.positional`), and gives the reply and the next state; its own effects go below. Every other effect goes below unchanged. The state
of the next attempt is the local meaning of the layer's `again` code; a stop of it is the stop
of the run. A stack is its layers, the nearest to the program first.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## An effect, as a clause sees it -/

/-- The occurrence of an effect. -/
def ROp.occurrence : ROp M → Occurrence
  | .give _ _ at_ _ _ => at_
  | .get _ _ at_ _ => at_
  | .own _ _ at_ _ _ _ => at_
  | .hear _ _ at_ _ => at_
  | .begin at_ => at_
  | .settle at_ => at_

/-- The role's part of the event of an effect; the marks of an attempt are no part of an
event, and no clause answers them. -/
def ROp.part : ROp M → Option (Part V)
  | .give kind getters _ _ _ => some (.give kind getters)
  | .get kind giver _ _ => some (.get kind giver)
  | .own kind hearers _ _ _ _ => some (.own kind hearers)
  | .hear kind owner _ _ => some (.hear kind owner)
  | .begin _ => none
  | .settle _ => none

/-- The types of what an effect takes. -/
def ROp.takes : ROp M → List V.Ty
  | .give _ _ _ τ _ => [τ]
  | .get .. => []
  | .own _ _ _ ins _ _ => ins
  | .hear .. => []
  | .begin _ => []
  | .settle _ => []

/-- The types of what an effect gives back. -/
def ROp.gives : ROp M → List V.Ty
  | .give .. => []
  | .get _ _ _ τ => [τ]
  | .own _ _ _ _ _ τ => [τ]
  | .hear _ _ _ τ => [τ]
  | .begin _ => [.nat]
  | .settle _ => []

/-- What an effect takes. -/
def ROp.payload : (op : ROp M) → HList M.Val (ROp.takes M op)
  | .give _ _ _ _ x => .cons x .nil
  | .get .. => .nil
  | .own _ _ _ _ payload _ => payload
  | .hear .. => .nil
  | .begin _ => .nil
  | .settle _ => .nil

/-- The reply to an effect, from what it gives back. -/
def ROp.reply : (op : ROp M) → HList M.Val (ROp.gives M op) → (RSig M).Reply op
  | .give .., _ => ()
  | .get .., .cons v .nil => v
  | .own .., .cons v .nil => v
  | .hear .., .cons v .nil => v
  | .begin _, .cons v .nil => v
  | .settle _, _ => ()

/-- Values of a role alone, as the role holds them. -/
def aloneIn (r : Role) : {types : List V.Ty} → HList M.Val types → HList (RV M r) (alone r types)
  | [], .nil => .nil
  | τ :: _, .cons v rest => .cons (hide M r ⟨τ, [r]⟩ v) (aloneIn r rest)

/-- The values of a role alone, out of what the role holds of them. -/
def aloneOut (r : Role) : {types : List V.Ty} → HList (RV M r) (alone r types) → HList M.Val types
  | [], .nil => .nil
  | τ :: _, .cons v rest =>
      .cons (reveal M (a := ⟨τ, [r]⟩) (List.mem_singleton_self r) v) (aloneOut r rest)

/-! ## A layer -/

section
variable {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
  {r : Role} {state : V.Ty}

/-- The answer of the first clause that matches an effect; an effect that no clause matches
goes below unchanged. A clause's code that stops leaves the layer's state as it was before the
clause. -/
def Clause.answer : List (Clause V hs r state) → (op : ROp M) → M.Val state →
    Process (RSig M) (Stop × M.Val state) ((RSig M).Reply op × M.Val state)
  | [], op, s => .call op fun reply => .done (reply, s)
  | c :: cs, op, s =>
      if h : c.site.site = (ROp.occurrence M op).site ∧ some c.site.part = ROp.part M op ∧
          c.site.takes = ROp.takes M op ∧ c.site.gives = ROp.gives M op then
        ((c.code.denote (roleSem M r fnTable rTable) (ROp.occurrence M op).path
          (Env.positional (aloneIn M r (HList.append
            (cast (congrArg (HList M.Val) h.2.2.1.symm) (ROp.payload M op))
            (.cons s .nil))))).mapHalt fun why => (why, s)).map fun out =>
          let values := HList.split c.site.gives (aloneOut M r out)
          (ROp.reply M op (cast (congrArg (HList M.Val) h.2.2.2) values.1), values.2.single)
      else Clause.answer cs op s

/-- The handler that the description of a layer means. -/
def Layer.handler {ins : List (LTy V)} (l : Layer V hs r ins) :
    Handler (RSig M) (RSig M) Stop (M.Val l.state) where
  clause op s := Clause.answer M fnTable rTable l.clauses op s
  again i entry stop :=
    match l.again.denote (localSem M hs.fns fnTable) []
        (Env.positional (.cons (i : Nat) (.cons entry (.cons stop .nil)))) with
    | .done (.cons next .nil) => .ok next
    | .halt why => .error why
    | .call op _ => nomatch op

end

/-! ## A stack of layers -/

section
variable {hs : Headers V} {r : Role} {ins : List (LTy V)}

/-- The types of the states of the layers, the nearest to the program first. -/
def Stack.States : List (Layer V hs r ins) → List V.Ty
  | [] => []
  | l :: rest => l.state :: Stack.States rest

/-- What the layers take from outside the run, the nearest to the program first. -/
def Stack.Takes : List (Layer V hs r ins) → List V.Ty
  | [] => []
  | l :: rest => l.takes ++ Stack.Takes rest

/-- What the layers give at the end, the nearest to the program first. -/
def Stack.Gives : List (Layer V hs r ins) → List V.Ty
  | [] => []
  | l :: rest => l.gives ++ Stack.Gives rest

variable (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)

/-- The layers as one handler. -/
def Stack.handler : (layers : List (Layer V hs r ins)) →
    Handler (RSig M) (RSig M) Stop (HList M.Val (Stack.States layers))
  | [] =>
      { clause := fun op s => .call op fun reply => .done (reply, s)
        again := fun _ _ _ => .ok .nil }
  | l :: rest =>
      let both := (Layer.handler M fnTable rTable l).over (Stack.handler rest)
      { clause := fun op state =>
          match state with
          | .cons mine below =>
              ((both.clause op (mine, below)).mapHalt fun stop =>
                  (stop.1, .cons stop.2.1 stop.2.2)).map fun out =>
                (out.1, .cons out.2.1 out.2.2)
        again := fun i entry stop =>
          match entry, stop with
          | .cons e es, .cons t ts =>
              (both.again i (e, es) (t, ts)).map fun next => .cons next.1 next.2 }

/-- The values of the inputs that a role holds, in order. -/
def heldValues (r : Role) : {ins : List (LTy V)} → HList (RV M r) ins → HList M.Val (held r ins)
  | [], .nil => .nil
  | a :: _, .cons v rest =>
      if h : r ∈ a.holders then
        cast (by simp [held, h]) (HList.cons (reveal M h v) (heldValues r rest))
      else cast (by simp [held, h]) (heldValues r rest)

/-- The first states: each layer's `start` on its part of what the layers take and on the
inputs that the role holds, the nearest to the program first. The starts have no effects. -/
def Stack.start : (layers : List (Layer V hs r ins)) → HList (RV M r) ins →
    HList M.Val (Stack.Takes layers) → Program M (HList M.Val (Stack.States layers))
  | [], _, _ => .done .nil
  | l :: rest, inputs, taken =>
      let parts := HList.split l.takes taken
      (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
        (Env.positional (HList.append parts.1 (heldValues M r inputs))))).bind fun first =>
        (Stack.start rest inputs parts.2).map fun others => .cons first.single others

/-- What the layers give: each layer's `finish` on its last state. -/
def Stack.finish : (layers : List (Layer V hs r ins)) → HList M.Val (Stack.States layers) →
    Program M (HList M.Val (Stack.Gives layers))
  | [], _ => .done .nil
  | l :: rest, .cons s states =>
      (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
        fun mine => (Stack.finish rest states).map fun others => HList.append mine others

end

/-- The process with `frame` in front of the path of the occurrence of every private coin
that the role owns: a coin that nobody hears. Every other effect keeps its occurrence: one
between roles, and a request to a service, which must answer equal inputs alike. -/
def Process.markOwn (frame : Frame) {H A : Type} : Process (RSig M) H A → Process (RSig M) H A
  | .done a => .done a
  | .halt payload => .halt payload
  | .call (.own (.coin law) [] at_ ins payload τ) k =>
      .call (.own (.coin law) [] ⟨frame :: at_.path, at_.key⟩ ins payload τ) fun v =>
        markOwn frame (k v)
  | .call op k => .call op fun reply => markOwn frame (k reply)

/-- The retry of a deployment, from the bound and the site of its attempt: the attempt is
the region between the beginning and the end that its owner marks at that site; it is retried
when it stops with `abort`, and its attempts ran out with `exhausted` at the occurrence of the
attempt. In attempt `i`, every private coin of the body is asked under the frame of the
attempt, so that it is asked afresh. -/
def retryOf : Option (Nat × Site) → Retry (RSig M) (RSig M) Stop
  | none =>
      { bound := 1, begins := fun _ => none, ends := fun _ => none, retriable := Stop.isAbort,
        mark := fun _ p => p }
  | some (bound, site) =>
      { bound := bound
        begins := fun
          | .begin at_ =>
              if at_.site = site then some (.declared .exhausted at_, fun i => i) else none
          | _ => none
        ends := fun
          | .settle at_ => if at_.site = site then some () else none
          | _ => none
        retriable := Stop.isAbort
        mark := fun i p => Process.markOwn M (.attempt site.key i) p }

end

end Zkc.Core

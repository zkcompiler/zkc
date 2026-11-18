module

public import Zkc.Core.Facts.Domains.Rules

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 5: the skeleton.

The skeleton of a term is what the term keeps in order, written on identifiers (`Skel`): an exit,
or one entry at a key followed by the rest. An entry (`Kept`) is an operation kept in order, a
guard, or a form of control; it carries no rest, and a region inside it is a skeleton for its
own types. A shared operation has no entry. Where an entry makes leaves, it holds the number of
the first (`results`, `inputs`, `input`), the others following in order. A choice and a block
make no leaf: what a choice returns is a value of the table (a selection or the common
identifier), and what a block returns is what its body returns.

**How the relation "a process runs a skeleton" is organised** (`Skel.Runs`). A process runs a
skeleton from a path and leaves, reading every identifier through the table (`Reads`, with
`R.bool` as the truth of a value, by which a selection is read), *followed by rests*
(`Rests`): the rests of the choices and blocks whose regions the skeleton is in, innermost
first, each with the path that it runs under. The process is the whole of what remains, the
region and then the rests.

- An exit reads its identifiers as the values that the region returns, and the process is then
  what the rests run from the same leaves (`Rests.Runs`): with no rest, it returns those values;
  otherwise it runs the first rest followed by the others. So what follows a choice or a block
  runs from the leaves at the exit of the region that ran, where its results (selections, or
  leaves made inside the region) read the values that the region returned: the continuation
  form of the validator's model.
- An operation kept in order, a case analysis, a loop and an attempt are as in today's relation:
  what follows them runs for every result that they can return on permitted replies, with that
  result as the values of their result leaves, from the leaves before them. Their regions (the
  arms, the body at each iteration, the body at each number) run alone, followed by no rest.
- A guard reads its condition: it stops when the condition is false, and the rest runs when it
  is true.

What is to be proved of it: a run is kept when the table grows (`SkelRunsGrowStatement`), and two
processes that run one skeleton from the same leaves are the same on permitted replies
(`SkelRunsSameStatement`). The second needs only that written operations give one list of
results and that the values of the table are well formed: leaves and values being two spaces,
no condition is asked of the leaves (today's `Skel.Apart` and `Leaves` go).

Comparison (`Skel.differ`): the places where two skeletons differ, given what a dialect decides
of its types, performers and operations (`SkelRules`), empty exactly when the two are equal
(`SkelDifferStatement`), for decisions that are sound and reflexive (`SkelRules.Exact`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## How often a loop runs -/

/-- How often a loop of a skeleton runs: a written number of times, or as often as the value of
an identifier says. -/
inductive Count (D : Dialect) (w : D.Who) where
  | fixed (n : Nat)
  | value {t : D.Ty} (count : Ident) (ok : D.Count w t)

/-- The number of iterations, when it is written. -/
def Count.size {D : Dialect} {w : D.Who} : Count D w → Option Nat
  | .fixed n => some n
  | .value .. => none

/-! ## The skeleton -/

mutual
  /-- What a term keeps in order, on identifiers: an exit on the identifiers that it returns, or
  an entry at the key of its instruction followed by the rest. -/
  inductive Skel (D : Dialect) : List D.Ty → Type where
    | ret {outs} (exit : List Ident) : Skel D outs
    | step {outs} (key : Key) (kept : Kept D) (rest : Skel D outs) : Skel D outs
  /-- One entry of a skeleton, without what follows it. Not indexed by types: a region inside it
  is a skeleton for its own types. -/
  inductive Kept (D : Dialect) : Type where
    /-- An operation kept in order on its operands; `results` is the first of its result
    leaves. -/
    | effect {ins res : List D.Ty} (o : D.Op ins res) (operands : List Ident) (results : Nat)
    /-- A guard on a condition. -/
    | guard {t : D.Ty} (w : D.Who) (condition : Ident) (ok : D.Condition w t) (why : Reason)
    /-- A choice: no leaf, its results are values of the table. -/
    | choose {mid : List D.Ty} {t : D.Ty} (w : D.Who) (condition : Ident) (ok : D.Condition w t)
        (onTrue onFalse : Skel D mid)
    /-- A case analysis on a subject; `results` is the first of its result leaves. -/
    | cases {mid : List D.Ty} {t : D.Ty} {payloads : List D.Ty} (w : D.Who) (subject : Ident)
        (ok : D.Alternatives w t payloads) (arms : SkelArms D mid payloads) (results : Nat)
    /-- A loop: how often it runs, the initial carried values, `inputs` the leaf of the index
    (the carried values' leaves follow), its body, `results` the first of its result leaves. -/
    | loop {carried each : List D.Ty} (w : D.Who) (times : Count D w) (initial : List Ident)
        (inputs : Nat) (body : Skel D (carried ++ each)) (results : Nat)
    /-- A block: no leaf, its results are what its body returns. -/
    | block {mid : List D.Ty} (number : Nat) (body : Skel D mid)
    /-- An attempt: `input` the leaf of its number, its body, `results` the first of its result
    leaves. -/
    | attempt {mid : List D.Ty} (w : D.Who) (input : Nat) (body : Skel D mid) (results : Nat)
  /-- The arms of a case analysis of a skeleton, each with the leaf of its payload. -/
  inductive SkelArms (D : Dialect) : List D.Ty → List D.Ty → Type where
    | nil {mid} : SkelArms D mid []
    | cons {mid payload payloads} (input : Nat) (arm : Skel D mid)
        (rest : SkelArms D mid payloads) : SkelArms D mid (payload :: payloads)
end

/-- The skeleton of a step: its entry followed by the rest, or the rest alone where the
instruction has no entry (a shared operation). -/
def Skel.stepOf {D : Dialect} {outs : List D.Ty} (key : Key) : Option (Kept D) → Skel D outs →
    Skel D outs
  | some kept, rest => .step key kept rest
  | none, rest => rest

/-! ## Reading leaves -/

/-- The leaves with the values given at `lo, lo + 1, …`, and those of `ρ` elsewhere. -/
def Leaves.setFrom {Val : Type} (ρ : Leaves Val) (lo : Nat) (vs : List Val) : Leaves Val :=
  fun n => if lo ≤ n ∧ n < lo + vs.length then vs[n - lo]? else ρ n

/-- Every condition reads, by the reading of truth values, as the truth value that the semantics
takes it for. A selection is read by `R.bool` (`Reads`), so that a process runs the skeleton of a
choice needs this of the condition that it chose on. `Rules.Lawful.condition` gives it for valid
values only; the value side of the analysis (a term runs its skeleton, validation) asks it of
every value. -/
def ConditionsRead {D : Dialect} (sem : Semantics D) (R : Reading sem.Dyn) : Prop :=
  ∀ {w : D.Who} {t : D.Ty} (ok : D.Condition w t) (v : sem.Val t),
    R.bool ⟨t, v⟩ = some (sem.holds ok v)

/-! ## The processes that run a skeleton -/

/-- What follows the exit of a region whose results are of `mid`, up to the end of the outermost
skeleton, which returns `outs`: nothing, or the rest of the enclosing choice or block, with the
path that it runs under, followed by what follows that. The rest reads the region's results
through identifiers, so it is not indexed by `mid`. -/
inductive Rests (D : Dialect) : List D.Ty → List D.Ty → Type where
  | nil {outs} : Rests D outs outs
  | cons {mid mid' outs} (path : List Frame) (rest : Skel D mid') (after : Rests D mid' outs) :
      Rests D mid outs

section
variable {D : Dialect} {Raw : Type} (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (R : Reading sem.Dyn) (table : Table Raw)

/-- The number of iterations that a count says, on the leaves. -/
def Count.Is {w : D.Who} (ρ : Leaves sem.Dyn) : Count D w → Nat → Prop
  | .fixed n, count => count = n
  | .value (t := t) id ok, count =>
      ∃ v : sem.Val t, Reads Run R.bool table ρ id ⟨t, v⟩ ∧ count = sem.count ok v

mutual
  /-- The process does what the skeleton says, followed by the rests, from a path and leaves: each
  identifier is read through the table. The process is the whole of what remains. -/
  inductive Skel.Runs : List Frame → Leaves sem.Dyn → {mid outs : List D.Ty} → Skel D mid →
      Rests D mid outs → Process sem.S sem.H (HList sem.Val outs) → Prop where
    /-- An exit reads the values that the region returns; the rests run from the same leaves. -/
    | ret {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs : List D.Ty} {exit : List Ident}
        {after : Rests D mid outs} {p : Process sem.S sem.H (HList sem.Val outs)}
        (values : HList sem.Val mid) (read : ReadsAll Run R.bool table ρ exit (sem.dyns values))
        (resume : Rests.Runs ρ after values p) :
        Skel.Runs path ρ (.ret exit) after p
    /-- An operation kept in order: what follows runs for every result that it can return, on
    its result leaves. -/
    | effect {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs ins res : List D.Ty} {key : Key}
        {o : D.Op ins res} {operands : List Ident} {results : Nat} {rest : Skel D mid}
        {after : Rests D mid outs}
        {k : HList sem.Val res → Process sem.S sem.H (HList sem.Val outs)}
        (values : HList sem.Val ins) (read : ReadsAll Run R.bool table ρ operands (sem.dyns values))
        (next : ∀ returned, (sem.op key o path values).CanReturn permitted returned →
          Skel.Runs path (Leaves.setFrom ρ results (sem.dyns returned)) rest after (k returned)) :
        Skel.Runs path ρ (.step key (.effect o operands results) rest) after
          ((sem.op key o path values).bind k)
    /-- A guard whose condition holds: the rest runs. -/
    | guardHolds {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs : List D.Ty} {t : D.Ty}
        {key : Key} {w : D.Who} {condition : Ident} {ok : D.Condition w t} {why : Reason}
        {rest : Skel D mid} {after : Rests D mid outs} {p : Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run R.bool table ρ condition ⟨t, v⟩)
        (holds : sem.holds ok v = true) (next : Skel.Runs path ρ rest after p) :
        Skel.Runs path ρ (.step key (.guard w condition ok why) rest) after p
    /-- A guard whose condition does not hold: it stops at its occurrence. -/
    | guardStops {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs : List D.Ty} {t : D.Ty}
        {key : Key} {w : D.Who} {condition : Ident} {ok : D.Condition w t} {why : Reason}
        {rest : Skel D mid} {after : Rests D mid outs}
        (v : sem.Val t) (read : Reads Run R.bool table ρ condition ⟨t, v⟩)
        (fails : sem.holds ok v = false) :
        Skel.Runs path ρ (.step key (.guard w condition ok why) rest) after
          (.halt (sem.stop w why ⟨path, key⟩))
    /-- A choice whose condition holds: its first region runs, followed by the choice's rest. -/
    | chooseTrue {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs region : List D.Ty} {t : D.Ty}
        {key : Key} {w : D.Who} {condition : Ident} {ok : D.Condition w t}
        {onTrue onFalse : Skel D region} {rest : Skel D mid} {after : Rests D mid outs}
        {p : Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run R.bool table ρ condition ⟨t, v⟩)
        (holds : sem.holds ok v = true) (first : Skel.Runs path ρ onTrue (.cons path rest after) p) :
        Skel.Runs path ρ (.step key (.choose w condition ok onTrue onFalse) rest) after p
    /-- A choice whose condition does not hold: its second region runs, followed by the choice's
    rest. -/
    | chooseFalse {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs region : List D.Ty} {t : D.Ty}
        {key : Key} {w : D.Who} {condition : Ident} {ok : D.Condition w t}
        {onTrue onFalse : Skel D region} {rest : Skel D mid} {after : Rests D mid outs}
        {p : Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run R.bool table ρ condition ⟨t, v⟩)
        (fails : sem.holds ok v = false)
        (second : Skel.Runs path ρ onFalse (.cons path rest after) p) :
        Skel.Runs path ρ (.step key (.choose w condition ok onTrue onFalse) rest) after p
    /-- A case analysis: its arms run at the alternative of its subject, alone; what follows runs
    for every result that they can return, on its result leaves. -/
    | cases {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs region : List D.Ty} {t : D.Ty}
        {payloads : List D.Ty} {key : Key} {w : D.Who} {subject : Ident}
        {ok : D.Alternatives w t payloads} {arms : SkelArms D region payloads} {results : Nat}
        {rest : Skel D mid} {after : Rests D mid outs}
        {first : Process sem.S sem.H (HList sem.Val region)}
        {k : HList sem.Val region → Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run R.bool table ρ subject ⟨t, v⟩)
        (arm : SkelArms.Runs path ρ arms (sem.pick ok v) first)
        (next : ∀ returned, first.CanReturn permitted returned →
          Skel.Runs path (Leaves.setFrom ρ results (sem.dyns returned)) rest after (k returned)) :
        Skel.Runs path ρ (.step key (.cases w subject ok arms results) rest) after (first.bind k)
    /-- A loop: its body runs alone at every iteration below its count that is reached, from the
    leaves before it with the index and the carried values on its input leaves; what follows runs
    for every final state that the iterations can reach, on its result leaves. -/
    | loop {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs carried each : List D.Ty} {key : Key}
        {w : D.Who} {times : Count D w} {initial : List Ident} {inputs : Nat}
        {body : Skel D (carried ++ each)} {results : Nat} {rest : Skel D mid}
        {after : Rests D mid outs}
        {k : sem.LoopState carried each → Process sem.S sem.H (HList sem.Val outs)}
        (count : Nat) (counted : times.Is sem Run R table ρ count)
        (start : HList sem.Val carried)
        (read : ReadsAll Run R.bool table ρ initial (sem.dyns start))
        (bodyOf : Nat → HList sem.Val carried →
          Process sem.S sem.H (HList sem.Val (carried ++ each)))
        (iteration : ∀ i state, i < count →
          (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn permitted
            state →
          Skel.Runs (path ++ [.iteration key i])
            (Leaves.setFrom ρ inputs (⟨D.index w, sem.index w i⟩ :: sem.dyns state.1)) body .nil
            (bodyOf i state.1))
        (next : ∀ final,
          (Process.iterate count (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
            permitted final →
          Skel.Runs path
            (Leaves.setFrom ρ results
              (sem.dyns (final.1.append (sem.collected times.size final.2)))) rest after (k final)) :
        Skel.Runs path ρ (.step key (.loop w times initial inputs body results) rest) after
          ((Process.iterate count (sem.stepOf bodyOf) 0 (start, HList.empties each)).bind k)
    /-- A block: its body runs under its frame, followed by the block's rest under the path
    outside it. -/
    | block {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs region : List D.Ty} {key : Key}
        {number : Nat} {body : Skel D region} {rest : Skel D mid} {after : Rests D mid outs}
        {p : Process sem.S sem.H (HList sem.Val outs)}
        (inner : Skel.Runs (path ++ [.iteration key number]) ρ body (.cons path rest after) p) :
        Skel.Runs path ρ (.step key (.block number body) rest) after p
    /-- An attempt: its body runs alone on every number that its beginning can give, on its input
    leaf; what follows runs from every end of the attempt that can return, on its result
    leaves. -/
    | attempt {path : List Frame} {ρ : Leaves sem.Dyn} {mid outs region : List D.Ty} {key : Key}
        {w : D.Who} {input : Nat} {body : Skel D region} {results : Nat} {rest : Skel D mid}
        {after : Rests D mid outs}
        (bodyOf : sem.Val (D.index w) → Process sem.S sem.H (HList sem.Val region))
        {k : HList sem.Val region → Process sem.S sem.H (HList sem.Val outs)}
        (inner : ∀ number, (sem.begin w key path).CanReturn permitted number →
          Skel.Runs path (Leaves.setFrom ρ input [⟨D.index w, number⟩]) body .nil (bodyOf number))
        (next : ∀ number returned, (sem.begin w key path).CanReturn permitted number →
          (bodyOf number).CanReturn permitted returned →
          (sem.settle w key path).CanReturn permitted () →
          Skel.Runs path (Leaves.setFrom ρ results (sem.dyns returned)) rest after (k returned)) :
        Skel.Runs path ρ (.step key (.attempt w input body results) rest) after
          ((sem.begin w key path).bind fun number =>
            (bodyOf number).bind fun returned => (sem.settle w key path).bind fun _ => k returned)
  /-- What the rests run from the exit of a region that returned the values given: with no rest,
  the process returns them; otherwise it runs the first rest under its path, followed by the
  others, from the same leaves. -/
  inductive Rests.Runs : Leaves sem.Dyn → {mid outs : List D.Ty} → Rests D mid outs →
      HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs) → Prop where
    | done {ρ : Leaves sem.Dyn} {outs : List D.Ty} (values : HList sem.Val outs) :
        Rests.Runs ρ .nil values (.done values)
    | resume {ρ : Leaves sem.Dyn} {mid mid' outs : List D.Ty} {path : List Frame}
        {rest : Skel D mid'} {after : Rests D mid' outs} {values : HList sem.Val mid}
        {p : Process sem.S sem.H (HList sem.Val outs)} (next : Skel.Runs path ρ rest after p) :
        Rests.Runs ρ (.cons path rest after) values p
  /-- The process does what the arm of the alternative says, alone, its payload on the arm's
  input leaf. -/
  inductive SkelArms.Runs : List Frame → Leaves sem.Dyn → {mid payloads : List D.Ty} →
      SkelArms D mid payloads → Pick sem.Val payloads →
      Process sem.S sem.H (HList sem.Val mid) → Prop where
    | here {path : List Frame} {ρ : Leaves sem.Dyn} {mid : List D.Ty} {payload : D.Ty}
        {payloads : List D.Ty} {input : Nat} {arm : Skel D mid} {rest : SkelArms D mid payloads}
        {v : sem.Val payload} {p : Process sem.S sem.H (HList sem.Val mid)}
        (inner : Skel.Runs path (Leaves.setFrom ρ input [⟨payload, v⟩]) arm .nil p) :
        SkelArms.Runs path ρ (.cons input arm rest) (.here v) p
    | there {path : List Frame} {ρ : Leaves sem.Dyn} {mid : List D.Ty} {payload : D.Ty}
        {payloads : List D.Ty} {input : Nat} {arm : Skel D mid} {rest : SkelArms D mid payloads}
        {pick : Pick sem.Val payloads} {p : Process sem.S sem.H (HList sem.Val mid)}
        (inner : SkelArms.Runs path ρ rest pick p) :
        SkelArms.Runs path ρ (.cons (payload := payload) input arm rest) (.there pick) p
end

end

/-! ## Comparison -/

section
variable {D : Dialect}

/-- Whether two counts of one performer are the same: the same written number, or counts of the
same type, by the dialect's decision, on the same identifier. -/
def Count.same (checks : SkelRules D) {w : D.Who} : Count D w → Count D w → Bool
  | .fixed n, .fixed n' => decide (n = n')
  | .value (t := t) id _, .value (t := t') id' _ =>
      match checks.sameTy t t' with
      | isTrue _ => decide (id = id')
      | isFalse _ => false
  | .fixed _, .value .. => false
  | .value .., .fixed _ => false

/-- The location of a difference inside a body, before the caller supplies its definition and role. -/
structure BodyLocation where
  blocks : List (Key × Nat)
  instruction : Option Key
  deriving DecidableEq, Repr

def BodyLocation.under (key : Key) (number : Nat) (at_ : BodyLocation) : BodyLocation :=
  { at_ with blocks := (key,number) :: at_.blocks }

def BodyLocation.toPlace (definition : Key) (role : Option Role) (at_ : BodyLocation) : Place :=
  ⟨definition, at_.blocks, at_.instruction, role⟩

mutual
  /-- The places where two skeletons differ, in order: the key of each step at which their entries
  differ (what follows such a step is not compared), and the place `at_` of the region that the
  two are (the key of its instruction; `none` for a definition's body) where both exit on
  different identifiers. Where one exits and the other has a step, the step's key. -/
  def Skel.differ (checks : SkelRules D) (at_ : Option Key) :
      {outs outs' : List D.Ty} → Skel D outs → Skel D outs' → List BodyLocation
    | _, _, .ret exit, .ret exit' => if exit = exit' then [] else [⟨[],at_⟩]
    | _, _, .step key kept rest, .step key' kept' rest' =>
        if key = key' then
          match Kept.differ checks key kept kept' with
          | some found => found ++ Skel.differ checks at_ rest rest'
          | none => [⟨[],some key⟩]
        else [⟨[],some key'⟩]
    | _, _, .ret _, .step key' _ _ => [⟨[],some key'⟩]
    | _, _, .step key _ _, .ret _ => [⟨[],some key⟩]
  /-- Two entries at one key: nothing when they are not the same kind of entry on the same
  types, performers, identifiers and leaves; otherwise the places where their regions differ,
  each region's place being the key. -/
  def Kept.differ (checks : SkelRules D) (key : Key) : Kept D → Kept D → Option (List BodyLocation)
    | .effect (ins := ins) o operands results,
        .effect (ins := ins') (res := res') o' operands' results' =>
        match checks.sameTys ins ins' with
        | isTrue same =>
            if checks.sameOp o (cast (congrArg (fun types => D.Op types res') same.symm) o') = true ∧
                operands = operands' ∧ results = results' then some []
            else none
        | isFalse _ => none
    | .guard (t := t) w condition _ why, .guard (t := t') w' condition' _ why' =>
        match checks.sameWho w w', checks.sameTy t t' with
        | isTrue _, isTrue _ => if condition = condition' ∧ why = why' then some [] else none
        | _, _ => none
    | .choose (mid := mid) (t := t) w condition _ onTrue onFalse,
        .choose (mid := mid') (t := t') w' condition' _ onTrue' onFalse' =>
        match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid' with
        | isTrue _, isTrue _, isTrue _ =>
            if condition = condition' then
              some (Skel.differ checks (some key) onTrue onTrue' ++
                Skel.differ checks (some key) onFalse onFalse')
            else none
        | _, _, _ => none
    | .cases (mid := mid) (t := t) (payloads := payloads) w subject _ arms results,
        .cases (mid := mid') (t := t') (payloads := payloads') w' subject' _ arms' results' =>
        match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid',
          checks.sameTys payloads payloads' with
        | isTrue _, isTrue _, isTrue _, isTrue _ =>
            if subject = subject' ∧ results = results' then SkelArms.differ checks key arms arms'
            else none
        | _, _, _, _ => none
    | .loop (carried := carried) (each := each) w times initial inputs body results,
        .loop (carried := carried') (each := each') w' times' initial' inputs' body' results' =>
        match checks.sameWho w w', checks.sameTys carried carried', checks.sameTys each each' with
        | isTrue sameWho, isTrue _, isTrue _ =>
            if Count.same checks times (cast (congrArg (Count D) sameWho.symm) times') = true ∧
                initial = initial' ∧ inputs = inputs' ∧ results = results' then
              some (Skel.differ checks (some key) body body')
            else none
        | _, _, _ => none
    | .block (mid := mid) number body, .block (mid := mid') number' body' =>
        match checks.sameTys mid mid' with
        | isTrue _ =>
            if number = number' then
              some ((Skel.differ checks (some key) body body').map (BodyLocation.under key number))
            else none
        | isFalse _ => none
    | .attempt (mid := mid) w input body results, .attempt (mid := mid') w' input' body' results' =>
        match checks.sameWho w w', checks.sameTys mid mid' with
        | isTrue _, isTrue _ =>
            if input = input' ∧ results = results' then
              some (Skel.differ checks (some key) body body')
            else none
        | _, _ => none
    | _, _ => none
  /-- The arms of two case analyses at one key: nothing when they have different numbers of arms
  or different payload leaves; otherwise the places where the arms differ. -/
  def SkelArms.differ (checks : SkelRules D) (key : Key) :
      {mid mid' payloads payloads' : List D.Ty} → SkelArms D mid payloads →
        SkelArms D mid' payloads' → Option (List BodyLocation)
    | _, _, _, _, .nil, .nil => some []
    | _, _, _, _, .cons input arm rest, .cons input' arm' rest' =>
        if input = input' then
          (SkelArms.differ checks key rest rest').map (Skel.differ checks (some key) arm arm' ++ ·)
        else none
    | _, _, _, _, .nil, .cons .. => none
    | _, _, _, _, .cons .., .nil => none
end

/-- What comparison asks of a dialect's decisions: operations found the same are the same
(`SkelRules.Lawful`), and an operation is found the same as itself. Types and performers are
decided by equality, which is both. -/
def SkelRules.Exact (checks : SkelRules D) : Prop :=
  checks.Lawful ∧ ∀ {ins res : List D.Ty} (o : D.Op ins res), checks.sameOp o o = true

end

/-! ## What is to be proved of them -/

section
variable {D : Dialect} {Raw : Type}

/-- A process that runs a skeleton over a table runs it over every table with its entries. -/
def SkelRunsGrowStatement : Prop :=
  ∀ (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (R : Reading sem.Dyn) (table table' : Table Raw),
    table.Le table' →
    ∀ (path : List Frame) (ρ : Leaves sem.Dyn) {mid outs : List D.Ty} (skel : Skel D mid)
      (after : Rests D mid outs) (p : Process sem.S sem.H (HList sem.Val outs)),
      Skel.Runs sem permitted Run R table path ρ skel after p →
      Skel.Runs sem permitted Run R table' path ρ skel after p

/-- Two processes that run one skeleton, followed by the same rests, over one table whose values
are well formed, from the same path and the same leaves, are the same on permitted replies: for
written operations that give one list of results. Nothing is asked of the leaves. -/
def SkelRunsSameStatement : Prop :=
  ∀ (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (R : Reading sem.Dyn),
    (∀ raw operands results results', Run raw operands results → Run raw operands results' →
      results = results') →
    ∀ (v : Values Raw), v.WF →
    ∀ (path : List Frame) (ρ : Leaves sem.Dyn) {mid outs : List D.Ty} (skel : Skel D mid)
      (after : Rests D mid outs) (p q : Process sem.S sem.H (HList sem.Val outs)),
      Skel.Runs sem permitted Run R v.table path ρ skel after p →
      Skel.Runs sem permitted Run R v.table path ρ skel after q →
      Process.SameWhen permitted p q

/-- **Comparison is exact**: for decisions that are sound and reflexive, two skeletons of the same
types differ nowhere exactly when they are equal. -/
def SkelDifferStatement : Prop :=
  ∀ (checks : SkelRules D), SkelRules.Exact checks →
    ∀ (at_ : Option Key) {outs : List D.Ty} (s s' : Skel D outs),
      Skel.differ checks at_ s s' = [] ↔ s = s'

end

end Zkc.Core.BodyAnalysis

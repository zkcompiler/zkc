module

public import Zkc.Core.Facts.Body.Walk
public import Zkc.Core.Facts.SteppedLoops
public import Zkc.Core.Evidence.Stepped

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 7: what is to be proved of the walk.

Everything is said for any dialect, in a setting (`Setting`): the configuration of the analysis
and the definition's annotations, a semantics with its permitted replies, how values read, the
relation of written operations, which values are valid, which stops are `undefined`, the
interpretation of the domain's states (its lawfulness, `Domain.Lawful`, which is data: what a
state means), and the bounds that the statements about loops are about. The relation that the
table is about is that of written operations on valid values (`ValidRun`), as today.

**The invariant of the walk** (`Inv`), at a point of a run: no leaf at or above the counter has a
value; the identifiers of the names in scope read the names' values, and every name with an
identifier is in scope; the values of the table are well formed (these four are `Scope`, which
the value side uses with the plain relation); every leaf that has a value has a valid one; and the
domain's state means the table and the leaves.

**What an instruction returns** is stated once (`Returned`): leaves that extend the present ones,
of which the invariant holds for the scope of before the instruction, the state and the domain's
state after it, in which the identifiers that it returns read the values that it returned. Only the
statement for `step` binds them to the instruction's names.

**Per kind of instruction, three properties** about `walkInstr` (`InstrGrows`, `InstrRuns`,
`InstrSound`), each from the same property of its regions, and per property one statement for
`step` from those of its instruction and of the rest: the state grows (the table, its
well-formedness, the next value, and the leaf counter by `Instr.leafCount`); what the
instruction runs, followed by any continuation, runs its entry of the skeleton followed by any
rest, when it does not stop `undefined` (the continuation form of `Seam/Skeleton.lean`); and
soundness: from the invariant, with the annotations of the instruction defined and its facts
holding, when the walk adds no refusal, what the instruction runs, on every permitted path,
returns what `Returned` says and never stops `undefined`, the requirements of every operation that
it reaches hold there, and, where the addresses are distinct and the bounds that the setting is
about are recorded, every loop that it reaches respects them. The growth property also says that a
walk adds only refusals and bounds at its addresses (today's `Adds`), by which "no refusal" and
the recorded bounds split at a step.

**Soundness for a prefix** (`PrefixSoundStatement`), and a term as a prefix and an exit.

**The public verdicts** give safety for an admitted body and safety and equivalence for an
accepted replacement of an independently safe source.

Hypotheses that the brief's list does not name but the fixed laws force, each a definition here:
the assertions that the walk decides are defined at the types of their positions
(`Expr.Defined`, `RequiresDefined`, `Term.AnnotationsDefined`, and the summary's
guarantees), which is what elaboration's typing gives and what `Domain.Lawful.transfer` and
`.truth` need, since they speak of entries whose values read; a count reads as the index at its
number where the rules give the index's operations (`CountIsIndex`), for the invariant learned on
the count after a loop; and, on the value side, every condition reads as the truth value that the
semantics takes it for (`ConditionsRead`), since a selection is read by `R.bool`.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## What the statements are about -/

/-- What the statements are about: the configuration of the analysis and the definition's
annotations, a semantics with its permitted replies, how values read, the relation of written
operations, which values are valid, which stops are `undefined`, what the domain's states mean
(with the laws of its operations), and the bounds of loops by their places that the statements
about loops are about. -/
structure Setting (D : Dialect) (Raw : Type) where
  cfg : Config D Raw
  notes : Annotations Raw
  sem : Semantics D
  permitted : ∀ op, sem.S.Reply op → Prop
  R : Reading sem.Dyn
  Run : Raw → List sem.Dyn → List sem.Dyn → Prop
  Valid : sem.Dyn → Prop
  undefined : sem.H → Prop
  domain : cfg.domain.Lawful (ValidRun sem Run Valid) R (TypedValue sem Valid)
  F : List (Place × Nat)

namespace Setting
variable {D : Dialect} {Raw : Type} (σ : Setting D Raw)

/-- The relation that the table is about: written operations on valid values. -/
abbrev Runs : Raw → List σ.sem.Dyn → List σ.sem.Dyn → Prop := ValidRun σ.sem σ.Run σ.Valid

/-- Values, each with its type, are valid. -/
def AllValid {items : List D.Ty} (vs : HList σ.sem.Val items) : Prop :=
  ∀ v, v ∈ σ.sem.dyns vs → σ.Valid v

/-- A loop at the blocks and key given runs at most as often as the bound that the setting gives at
its place, the first of `F` there: the core's `Annotation.Bounded` of the bounds `F`, restated so
that it unfolds in one step. -/
def Bounded (blocks : List (Key × Nat)) (key : Key) (count : Nat) : Prop :=
  ∀ bound, (σ.F.find? fun entry =>
      decide (entry.1 = ⟨σ.cfg.definition, blocks, some key, σ.cfg.role⟩)).map (·.2) = some bound →
    count ≤ bound

/-- On every permitted path, the process never stops `undefined`. -/
def NotUndefined {A : Type} (p : Process σ.sem.S σ.sem.H A) : Prop :=
  p.Every σ.permitted (fun _ => True) (fun stop => ¬ σ.undefined stop)

end Setting

section
variable {D : Dialect} {Raw : Type}

/-! ## Values of names, types of names -/

/-- The value of a name in an environment, with its type: nothing for a name not in scope. -/
def valueOfName (sem : Semantics D) {Γ : Ctx D.Ty} (env : Env sem.Val Γ) (name : Name) :
    Option sem.Dyn :=
  match found : Γ.find? name with
  | some τ => some ⟨τ, env name τ found⟩
  | none => none

/-- The values of names, when each is in scope. -/
def valuesOfNames (sem : Semantics D) {Γ : Ctx D.Ty} (env : Env sem.Val Γ) (names : List Name) :
    Option (List sem.Dyn) :=
  names.mapM (valueOfName sem env)

/-- The values of the inputs as the first leaves. -/
def inputLeaves (sem : Semantics D) {types : List D.Ty} (values : HList sem.Val types) :
    Leaves sem.Dyn :=
  Leaves.setFrom (fun _ => none) 0 (sem.dyns values)

/-! ## The invariant of the walk -/

/-- What the value side has at a point of a run, for a relation of written operations: no leaf at
or above the counter has a value; every name in scope has an identifier that reads the name's
value; every name with an identifier is in scope; the values of the table are well formed. -/
structure Scope (sem : Semantics D) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
    (R : Reading sem.Dyn) {Γ : Ctx D.Ty} (ρ : Leaves sem.Dyn) (ids : Ctx Ident)
    (env : Env sem.Val Γ) (s : State Raw) : Prop where
  fresh : ∀ n, s.leaves ≤ n → ρ n = none
  agree : ∀ τ (x : Var Γ τ), ∃ id, ids.find? x.name = some id ∧
    Reads Run R.bool s.values.table ρ id ⟨τ, env.get x⟩
  bound : ∀ name id, ids.find? name = some id → ∃ τ, Γ.find? name = some τ
  wf : s.values.WF

/-- **The invariant of the walk**, at a point of a run: the scope, with the relation of written
operations on valid values; every leaf that has a value has a valid one; and the domain's state
means the table and the leaves. -/
structure Inv (σ : Setting D Raw) {Γ : Ctx D.Ty} (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident)
    (env : Env σ.sem.Val Γ) (k : σ.cfg.domain.State) (s : State Raw) : Prop
    extends Scope σ.sem σ.Runs σ.R ρ ids env s where
  valid : ∀ n v, ρ n = some v → σ.Valid v
  means : σ.domain.Means k s.values.table ρ

/-- **What an instruction or a region returns**, stated once: leaves that extend `ρ`, of which the
invariant holds for the scope of before it (`ids`, `env`), the domain's state and the state after
it, in which the identifiers that it returns read the values returned. -/
def Returned (σ : Setting D Raw) {Γ : Ctx D.Ty} {mid : List D.Ty} (ρ : Leaves σ.sem.Dyn)
    (ids : Ctx Ident) (env : Env σ.sem.Val Γ) (k : σ.cfg.domain.State) (s : State Raw)
    (returned : List Ident) (values : HList σ.sem.Val mid) : Prop :=
  ∃ ρ', ρ.Le ρ' ∧ Inv σ ρ' ids env k s ∧
    ReadsAll σ.Runs σ.R.bool s.values.table ρ' returned (σ.sem.dyns values)

/-- **What `Returned` says is the invariant of the results bound to the names**: for every names
of the results, the invariant holds, under the same leaves, of the scope extended by the names
bound to the identifiers returned and to the values returned. The one place where names are
bound, used by the statement for `step`. -/
def ReturnedBindStatement (σ : Setting D Raw) : Prop :=
  ∀ {Γ : Ctx D.Ty} {mid : List D.Ty} (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident)
    (env : Env σ.sem.Val Γ) (k : σ.cfg.domain.State) (s : State Raw) (returned : List Ident)
    (values : HList σ.sem.Val mid),
    Returned σ ρ ids env k s returned values →
    ∃ ρ', ρ.Le ρ' ∧ ∀ results : Names mid,
      Inv σ ρ' (bindIds ids results returned) (env.extend results values) k s

/-! ## At every step that a run reaches -/

/-- A property of the step at a key: of its instruction, path and environment at its entry. -/
abbrev StepProp (sem : Semantics D) : Type :=
  (cursor : StaticCursor) → (key : Key) → {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → List Frame →
    Env sem.Val Γ → Prop

section
variable (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop) (P : StepProp sem)

mutual
  /-- At every step that a run of a term reaches, on every path with permitted replies, `P` holds
  of its key, instruction, path and environment: by the recursion of `Term.EveryLoop`. -/
  def Term.EveryStep (cursor : StaticCursor) : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
      List Frame → Env sem.Val Γ → Prop
    | _, _, .ret _, _, _ => True
    | _, _, .step key i results rest, path, env =>
        P cursor key i path env ∧ Instr.EveryStep cursor key i path env ∧
          (i.denote sem key path env).Every permitted
            (fun values => Term.EveryStep cursor.next rest path (env.extend results values))
            (fun _ => True)
  /-- At every step that a run of what an instruction runs reaches, inside its regions. -/
  def Instr.EveryStep (cursor : StaticCursor) (key : Key) : {Γ : Ctx D.Ty} → {mid : List D.Ty} →
      Instr D Γ mid → List Frame → Env sem.Val Γ → Prop
    | _, _, .op _ _, _, _ => True
    | _, _, .guard _ _ _ _, _, _ => True
    | _, _, .choose _ c ok _ onTrue onFalse, path, env =>
        bif sem.holds ok (env.get c) then Term.EveryStep (cursor.region key) onTrue path env
        else Term.EveryStep (cursor.otherwise key) onFalse path env
    | _, _, .cases _ x ok _ arms, path, env =>
        Arms.EveryStep (cursor.region key) arms path env (sem.pick ok (env.get x))
    | _, _, .loop (each := each) w times _ init inputs body, path, env =>
        ∀ i, i < sem.times times env →
          (Process.iterate i
              (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
              0 (env.all init, HList.empties each)).Every permitted
            (fun state => Term.EveryStep (cursor.region key) body (path ++ [.iteration key i])
              (env.extend inputs (.cons (sem.index w i) state.1))) (fun _ => True)
    | _, _, .block number body, path, env =>
        Term.EveryStep (cursor.block key number) body (path ++ [.iteration key number]) env
    | _, _, .attempt w _ inputs body, path, env =>
        (sem.begin w key path).Every permitted
          (fun n => Term.EveryStep (cursor.region key) body path (env.extend inputs (.cons n .nil)))
          (fun _ => True)
  /-- At every step that a run of the arm of the alternative reaches. -/
  def Arms.EveryStep (cursor : StaticCursor) : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Arms D Γ mid payloads → List Frame → Env sem.Val Γ → Pick sem.Val payloads → Prop
    | _, _, _, .cons inputs arm _, path, env, .here v =>
        Term.EveryStep cursor.arm arm path (env.extend inputs (.cons v .nil))
    | _, _, _, .cons _ _ rest, path, env, .there p => Arms.EveryStep cursor.next rest path env p
end

/-- At every step of a prefix that a run reaches, and inside the regions of its instructions. -/
def Prefix.EveryStep (cursor : StaticCursor) : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → List Frame → Env sem.Val Γ → Prop
  | _, _, .nil, _, _ => True
  | _, _, .step key i results rest, path, env =>
      P cursor key i path env ∧ Instr.EveryStep sem permitted P cursor key i path env ∧
        (i.denote sem key path env).Every permitted
          (fun values => Prefix.EveryStep cursor.next rest path (env.extend results values)) (fun _ => True)

end

/-! ## Given facts, and the requirements reached -/

/-- Every fact given at the key holds at the entry of its instruction: of the values of the names
that it lists, when each is in scope. -/
def FactsAt (σ : Setting D Raw) : StepProp σ.sem :=
  fun cursor key {_} {_} i _ env => ∀ uses assertion, Annotation.fact uses assertion ∈ σ.notes.at_ (Instr.site cursor key i) →
    ∀ vs, valuesOfNames σ.sem env uses = some vs → assertion.Holds σ.Runs σ.R vs

/-- The requirements of an operation hold of the values of its operands; nothing of another
instruction. -/
def requiredAt (σ : Setting D Raw) : {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid →
    Env σ.sem.Val Γ → Prop
  | _, _, .op o operands, env => σ.cfg.rules.Required σ.sem σ.R σ.Run σ.Valid o (env.all operands)
  | _, _, .guard .., _ => True
  | _, _, .choose .., _ => True
  | _, _, .cases .., _ => True
  | _, _, .loop .., _ => True
  | _, _, .block .., _ => True
  | _, _, .attempt .., _ => True

/-- The requirements of an operation at its step, as a property of steps. -/
def RequiredAt (σ : Setting D Raw) : StepProp σ.sem :=
  fun _ _ {_} {_} i _ env => requiredAt σ i env

/-- **Every given fact holds where a run reaches it**: at every annotation `fact` that a run of the
term reaches, the assertion holds of the values of the names that it lists. The hypothesis under
which a walk that learned facts is sound. -/
def Term.EveryFact (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs) (path : List Frame) (env : Env σ.sem.Val Γ) : Prop :=
  Term.EveryStep σ.sem σ.permitted (FactsAt σ) cursor t path env

/-- Every given fact holds where a run of what an instruction runs reaches it, inside its regions
(the facts at the instruction's own key are `FactsAt`). -/
def Instr.EveryFact (σ : Setting D Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (i : Instr D Γ mid) (path : List Frame) (env : Env σ.sem.Val Γ) : Prop :=
  Instr.EveryStep σ.sem σ.permitted (FactsAt σ) cursor key i path env

/-- Every given fact holds where a run of the arm of the alternative reaches it. -/
def Arms.EveryFact (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    (arms : Arms D Γ mid payloads) (path : List Frame) (env : Env σ.sem.Val Γ)
    (pick : Pick σ.sem.Val payloads) : Prop :=
  Arms.EveryStep σ.sem σ.permitted (FactsAt σ) cursor arms path env pick

/-- Every given fact of a prefix holds where a run reaches it. -/
def Prefix.EveryFact (σ : Setting D Raw) (cursor : StaticCursor) {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame)
    (env : Env σ.sem.Val Γ) : Prop :=
  Prefix.EveryStep σ.sem σ.permitted (FactsAt σ) cursor p path env

/-- **The requirements of every operation that a run reaches hold there.** -/
def Term.EveryRequired (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs) (path : List Frame) (env : Env σ.sem.Val Γ) : Prop :=
  Term.EveryStep σ.sem σ.permitted (RequiredAt σ) cursor t path env

/-- The requirements of every operation that a run of what an instruction runs reaches, inside its
regions, hold there (an operation's own are `RequiredAt`). -/
def Instr.EveryRequired (σ : Setting D Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (i : Instr D Γ mid) (path : List Frame) (env : Env σ.sem.Val Γ) : Prop :=
  Instr.EveryStep σ.sem σ.permitted (RequiredAt σ) cursor key i path env

/-- The requirements of every operation that a run of the arm of the alternative reaches hold
there. -/
def Arms.EveryRequired (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    (arms : Arms D Γ mid payloads) (path : List Frame) (env : Env σ.sem.Val Γ)
    (pick : Pick σ.sem.Val payloads) : Prop :=
  Arms.EveryStep σ.sem σ.permitted (RequiredAt σ) cursor arms path env pick

/-! ## Decided assertions are defined -/

/-- An assertion names a value of all valid values of the given types: what elaboration's typing of
an assertion gives, with the laws `defined` and `keeps` of the operations that it applies. -/
def Expr.Defined (σ : Setting D Raw) (types : List D.Ty) (assertion : Expr Raw) : Prop :=
  ∀ args : HList σ.sem.Val types, (∀ v, v ∈ σ.sem.dyns args → σ.Valid v) →
    ∃ v, Expr.Denotes σ.Runs (σ.sem.dyns args) assertion v

/-- Every requirement of an operation is defined at the types of its operands. -/
def RequiresDefined (σ : Setting D Raw) : Prop :=
  ∀ {ins res : List D.Ty} (o : D.Op ins res),
    ∀ requirement, requirement ∈ (σ.cfg.rules.contract (σ.cfg.rules.written o)).requires →
      Expr.Defined σ ins requirement

/-- Each stated step resolves to a lemma and names of exactly its declared argument types;
its premises are defined at those types. A missing lemma, missing name or mistyped argument
cannot satisfy this elaboration obligation, even if the lemma has no premises. -/
def StepsDefinedAt (σ : Setting D Raw) (Γ : Ctx D.Ty) (site : AnnotationSite) : Prop :=
  ∀ lemma names, Annotation.step lemma names ∈ σ.notes.at_ site →
    ∃ l, σ.cfg.lemmas[lemma]? = some l ∧ typesOf Γ names = some l.parameters ∧
      ∀ premise, premise ∈ l.premises → Expr.Defined σ l.parameters premise

/-- The assertions of every invariant at the key of a loop are defined at the types of the names
it lists, the index and the carried values. -/
def InvariantsDefinedAt (σ : Setting D Raw) (Γ : Ctx D.Ty) (site : AnnotationSite) (w : D.Who)
    (carried : List D.Ty) : Prop :=
  ∀ uses assertions, Annotation.invariant uses assertions ∈ σ.notes.at_ site →
    ∀ τs, typesOf Γ uses = some τs → ∀ assertion, assertion ∈ assertions →
      Expr.Defined σ (τs ++ D.index w :: carried) assertion

mutual
  /-- The decided assertions of every annotation of a term are defined: the premises of its stated
  steps and the assertions of its invariants. -/
  def Term.AnnotationsDefined (σ : Setting D Raw) (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Prop
    | _, _, .ret _ => True
    | Γ, _, .step key i _ rest =>
        StepsDefinedAt σ Γ (Instr.site cursor key i) ∧ Instr.AnnotationsDefined σ cursor key i ∧
          Term.AnnotationsDefined σ cursor.next rest
  /-- The decided assertions of the annotations of an instruction at a key: the invariants of a
  loop, and those inside its regions. -/
  def Instr.AnnotationsDefined (σ : Setting D Raw) (cursor : StaticCursor) (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → Prop
    | _, _, .op _ _ => True
    | _, _, .guard _ _ _ _ => True
    | _, _, .choose _ _ _ _ onTrue onFalse =>
        Term.AnnotationsDefined σ (cursor.region key) onTrue ∧ Term.AnnotationsDefined σ (cursor.otherwise key) onFalse
    | _, _, .cases _ _ _ _ arms => Arms.AnnotationsDefined σ (cursor.region key) arms
    | Γ, _, .loop (carried := carried) w _ _ _ _ body =>
        InvariantsDefinedAt σ Γ (.instruction cursor key) w carried ∧ Term.AnnotationsDefined σ (cursor.region key) body
    | _, _, .block n body => Term.AnnotationsDefined σ (cursor.block key n) body
    | _, _, .attempt _ _ _ body => Term.AnnotationsDefined σ (cursor.region key) body
  /-- The decided assertions of the annotations of every arm are defined. -/
  def Arms.AnnotationsDefined (σ : Setting D Raw) (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → Prop
    | _, _, _, .nil => True
    | _, _, _, .cons _ arm rest =>
        Term.AnnotationsDefined σ cursor.arm arm ∧ Arms.AnnotationsDefined σ cursor.next rest
end

/-- The decided assertions of the annotations of a prefix are defined. -/
def Prefix.AnnotationsDefined (σ : Setting D Raw) (cursor : StaticCursor) : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Prop
  | _, _, .nil => True
  | Γ, _, .step key i _ rest =>
      StepsDefinedAt σ Γ (Instr.site cursor key i) ∧ Instr.AnnotationsDefined σ cursor key i ∧
        Prefix.AnnotationsDefined σ cursor.next rest

/-- The rules are lawful, each registered lemma holds in its declared context, and operation
requirements are defined. The setting also carries its domain laws. -/
structure Setting.Lawful (σ : Setting D Raw) : Prop where
  rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined
  lemmas : ∀ l, l ∈ σ.cfg.lemmas → l.Valid σ.Runs σ.R (TypedValue σ.sem σ.Valid)
  requires : RequiresDefined σ

/-! ## Addresses and bounds -/

/-- No bound recorded yet is at one of the addresses. -/
def BoundsApart (σ : Setting D Raw) (s : State Raw) (addresses : List (List (Key × Nat) × Key)) :
    Prop :=
  ∀ q, q ∈ s.bounds → ∀ bl key, q.1 = ⟨σ.cfg.definition, bl, some key, σ.cfg.role⟩ →
    (bl, key) ∉ addresses

/-- Every bound of the setting at one of the addresses is one that the state records. -/
def Recorded (σ : Setting D Raw) (addresses : List (List (Key × Nat) × Key)) (s : State Raw) :
    Prop :=
  ∀ p b bl key, (p, b) ∈ σ.F → p = ⟨σ.cfg.definition, bl, some key, σ.cfg.role⟩ →
    (bl, key) ∈ addresses → (p, b) ∈ s.bounds

end

/-! ## The three properties -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- What a walk adds to the state: refusals, before those that were there, and bounds, before those
that were there, each at one of the addresses given (today's `Adds`). -/
def Adds (cfg : Config D Raw) (addresses : List (List (Key × Nat) × Key))
    (before after : State Raw) : Prop :=
  (∃ new, after.refusals = new ++ before.refusals) ∧
    ∃ new, after.bounds = new ++ before.bounds ∧
      ∀ q, q ∈ new → ∃ bl key, q.1 = cfg.place bl key ∧ (bl, key) ∈ addresses

/-- The state grew: the table has the entries of before, its values are well formed, the next value
is not lower, the leaf counter went up by `count`, and only refusals and bounds at the addresses
were added. -/
def Grew (cfg : Config D Raw) (addresses : List (List (Key × Nat) × Key)) (before after : State Raw)
    (count : Nat) : Prop :=
  before.values.table.Le after.values.table ∧ after.values.WF ∧
    before.values.next ≤ after.values.next ∧ after.leaves = before.leaves + count ∧
    Adds cfg addresses before after

/-- **The walk of a term grows the state**, by the term's structural count of leaves, adding bounds
only at its addresses. -/
def TermGrows (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor)
    {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  ∀ ids s k, s.values.WF →
    Grew cfg (Term.addresses cursor.blocks t) s (walk cfg notes cursor t ids s k).state
      (Term.leafCount cfg.rules t)

/-- **The walk of an instruction grows the state**, by its structural count of leaves, adding bounds
only at its addresses. -/
def InstrGrows (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor)
    (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty} (i : Instr D Γ mid) : Prop :=
  ∀ ids s k, s.values.WF →
    Grew cfg (Instr.addresses cursor.blocks key i) s
      (walkInstr cfg notes cursor key i ids s k).state (Instr.leafCount cfg.rules i)

/-- **The walk of arms grows the state**, by their structural count of leaves, adding bounds only at
their addresses. -/
def ArmsGrows (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor)
    {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) : Prop :=
  ∀ ids s k, s.values.WF →
    Grew cfg (Arms.addresses cursor.blocks arms) s (walkArms cfg notes cursor arms ids s k).state
      (Arms.leafCount cfg.rules arms)

/-- **A term runs its skeleton**, in continuation form: from a point of a run that agrees with the
walk (`Scope`, with the plain relation), over every table with the walk's entries, the term's
process followed by a continuation runs the walk's skeleton followed by rests, when it does not
stop `undefined` and the rests run the continuation from every exit of the term: leaves that
extend these, with no value at or above the walk's final counter, in which what the term returns
reads the values returned. -/
def TermRuns (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (t : Term D Γ mid) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State) (table : Table Raw) {outs : List D.Ty}
    (after : Rests D mid outs)
    (cont : HList σ.sem.Val mid → Process σ.sem.S σ.sem.H (HList σ.sem.Val outs)),
    let e := walk σ.cfg σ.notes cursor t ids s k
    Scope σ.sem σ.Run σ.R ρ ids env s → e.state.values.table.Le table →
    σ.NotUndefined ((t.denote σ.sem path env).bind cont) →
    (∀ ρ' values, ρ.Le ρ' → (∀ n, e.state.leaves ≤ n → ρ' n = none) →
      ReadsAll σ.Run σ.R.bool e.state.values.table ρ' e.returned (σ.sem.dyns values) →
      σ.NotUndefined (cont values) →
      Rests.Runs σ.sem σ.permitted σ.Run σ.R table ρ' after values (cont values)) →
    Skel.Runs σ.sem σ.permitted σ.Run σ.R table path ρ e.skel after
      ((t.denote σ.sem path env).bind cont)

/-- **What an instruction runs runs its entry of the skeleton**, followed by any rest: what it runs,
followed by a continuation, runs its entry followed by the rest, when it does not stop
`undefined` and the rest runs the continuation from every exit of the instruction. -/
def InstrRuns (σ : Setting D Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty}
    {mid : List D.Ty} (i : Instr D Γ mid) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State) (table : Table Raw) {mid₀ outs : List D.Ty}
    (rest : Skel D mid₀) (after : Rests D mid₀ outs)
    (cont : HList σ.sem.Val mid → Process σ.sem.S σ.sem.H (HList σ.sem.Val outs)),
    let e := walkInstr σ.cfg σ.notes cursor key i ids s k
    Scope σ.sem σ.Run σ.R ρ ids env s → e.state.values.table.Le table →
    σ.NotUndefined ((i.denote σ.sem key path env).bind cont) →
    (∀ ρ' values, ρ.Le ρ' → (∀ n, e.state.leaves ≤ n → ρ' n = none) →
      ReadsAll σ.Run σ.R.bool e.state.values.table ρ' e.returned (σ.sem.dyns values) →
      σ.NotUndefined (cont values) →
      Skel.Runs σ.sem σ.permitted σ.Run σ.R table path ρ' rest after (cont values)) →
    Skel.Runs σ.sem σ.permitted σ.Run σ.R table path ρ (Skel.stepOf key e.entry rest) after
      ((i.denote σ.sem key path env).bind cont)

/-- **Arms run their skeletons**, alone, at every alternative, when they do not stop
`undefined`. -/
def ArmsRuns (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty}
    {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State) (table : Table Raw) (pick : Pick σ.sem.Val payloads),
    let e := walkArms σ.cfg σ.notes cursor arms ids s k
    Scope σ.sem σ.Run σ.R ρ ids env s → e.state.values.table.Le table →
    σ.NotUndefined (arms.denote σ.sem path env pick) →
    SkelArms.Runs σ.sem σ.permitted σ.Run σ.R table path ρ e.skel pick
      (arms.denote σ.sem path env pick)

/-- **The walk of a term is sound**: from the invariant, with the term's decided assertions defined
and its facts holding, when the walk adds no refusal, the term's process, on every permitted path,
returns what `Returned` says of the walk's exit and never stops `undefined`, and the requirements
of every operation that it reaches hold there; and, where its addresses are distinct and apart from the bounds recorded before and the setting's bounds at them
are recorded, every loop that a run reaches respects them. -/
def TermSound (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State),
    let e := walk σ.cfg σ.notes cursor t ids s k
    Inv σ ρ ids env k s → Term.AnnotationsDefined σ cursor t →
    Term.EveryFact σ cursor t path env → e.state.refusals = s.refusals →
    (t.denote σ.sem path env).Every σ.permitted (Returned σ ρ ids env e.known e.state e.returned)
        (fun stop => ¬ σ.undefined stop) ∧
      Term.EveryRequired σ cursor t path env ∧
      ((Term.addresses cursor.blocks t).Nodup → BoundsApart σ s (Term.addresses cursor.blocks t) →
        Recorded σ (Term.addresses cursor.blocks t) e.state →
        Term.EveryLoop σ.sem σ.permitted σ.Bounded t path cursor.blocks env)

/-- **The walk of an instruction is sound**: from the invariant, with its annotations' decided
assertions defined and the facts at its key and inside its regions holding, when the walk adds no
refusal, what it runs, on every permitted path, returns what `Returned` says of its exit and never
stops `undefined`, and the requirements of every operation that it reaches hold there (its own, if
it is one); and every loop that it reaches respects the setting's bounds, as for a term. -/
def InstrSound (σ : Setting D Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty}
    {mid : List D.Ty} (i : Instr D Γ mid) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State),
    let e := walkInstr σ.cfg σ.notes cursor key i ids s k
    Inv σ ρ ids env k s → StepsDefinedAt σ Γ (Instr.site cursor key i) → Instr.AnnotationsDefined σ cursor key i →
    FactsAt σ cursor key i path env → Instr.EveryFact σ cursor key i path env →
    e.state.refusals = s.refusals →
    (i.denote σ.sem key path env).Every σ.permitted
        (Returned σ ρ ids env e.known e.state e.returned) (fun stop => ¬ σ.undefined stop) ∧
      RequiredAt σ cursor key i path env ∧ Instr.EveryRequired σ cursor key i path env ∧
      ((Instr.addresses cursor.blocks key i).Nodup →
        BoundsApart σ s (Instr.addresses cursor.blocks key i) →
        Recorded σ (Instr.addresses cursor.blocks key i) e.state →
        Instr.EveryLoop σ.sem σ.permitted σ.Bounded key i path cursor.blocks env)

/-- **The walk of arms is sound**: at a valid alternative, the arm of the alternative returns, on
every permitted path, what `Returned` says of one of the exits that the walk gives the domain's
`after`, an exit that asks nobody, and never stops `undefined`; the requirements of the operations
that it reaches hold; and its loops respect the setting's bounds. -/
def ArmsSound (σ : Setting D Raw) (cursor : StaticCursor) {Γ : Ctx D.Ty}
    {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads) : Prop :=
  ∀ (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
    (s : State Raw) (k : σ.cfg.domain.State) (pick : Pick σ.sem.Val payloads),
    let e := walkArms σ.cfg σ.notes cursor arms ids s k
    PickValid σ.sem σ.Valid pick → Inv σ ρ ids env k s → Arms.AnnotationsDefined σ cursor arms →
    Arms.EveryFact σ cursor arms path env pick → e.state.refusals = s.refusals →
    (arms.denote σ.sem path env pick).Every σ.permitted
        (fun values => ∃ known returned, (Asks.nobody, known, returned) ∈ e.exits ∧
          Returned σ ρ ids env known e.state returned values)
        (fun stop => ¬ σ.undefined stop) ∧
      Arms.EveryRequired σ cursor arms path env pick ∧
      ((Arms.addresses cursor.blocks arms).Nodup →
        BoundsApart σ s (Arms.addresses cursor.blocks arms) →
        Recorded σ (Arms.addresses cursor.blocks arms) e.state →
        Arms.EveryLoop σ.sem σ.permitted σ.Bounded arms path cursor.blocks env pick)

/-! ## Growth, per kind -/

section
variable (cfg : Config D Raw) (notes : Annotations Raw)

/-- An exit grows nothing. -/
def RetGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty} (exit : HList (Var Γ) outs),
    TermGrows cfg notes cursor (.ret exit)

/-- **A step grows the state** as its instruction does, then the rest. -/
def StepGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Instr D Γ mid) (results : Names mid) (rest : Term D (Γ.extend results) outs),
    InstrGrows cfg notes cursor key i → TermGrows cfg notes cursor.next rest →
    TermGrows cfg notes cursor (.step key i results rest)

/-- An operation grows the state. -/
def OpGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {ins res : List D.Ty}
    (o : D.Op ins res) (operands : HList (Var Γ) ins),
    InstrGrows cfg notes cursor key (.op o operands)

/-- A guard grows the state. -/
def GuardGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {t : D.Ty} (w : D.Who) (c : Var Γ t)
    (ok : D.Condition w t) (why : Reason),
    InstrGrows cfg notes cursor key (.guard w c ok why)

/-- A choice grows the state when its regions do. -/
def ChooseGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty}
    (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (onTrue onFalse : Term D Γ mid),
    TermGrows cfg notes (cursor.region key) onTrue → TermGrows cfg notes (cursor.otherwise key) onFalse →
    InstrGrows cfg notes cursor key (.choose w c ok gives onTrue onFalse)

/-- A case analysis grows the state when its arms do. -/
def CasesGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid payloads : List D.Ty} {t : D.Ty}
    (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads),
    ArmsGrows cfg notes (cursor.region key) arms →
    InstrGrows cfg notes cursor key (.cases w x ok gives arms)

/-- A loop grows the state when its body does. -/
def LoopGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {carried each : List D.Ty} (w : D.Who)
    (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each)),
    TermGrows cfg notes (cursor.region key) body →
    InstrGrows cfg notes cursor key (.loop w times gives initial inputs body)

/-- A block grows the state when its body does, inside it. -/
def BlockGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty} (number : Nat)
    (body : Term D Γ mid),
    TermGrows cfg notes (cursor.block key number) body →
    InstrGrows cfg notes cursor key (.block number body)

/-- An attempt grows the state when its body does. -/
def AttemptGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty} (w : D.Who)
    (owns : D.Attempt w) (inputs : Names [D.index w]) (body : Term D (Γ.extend inputs) mid),
    TermGrows cfg notes (cursor.region key) body →
    InstrGrows cfg notes cursor key (.attempt w owns inputs body)

/-- No arms grow nothing. -/
def ArmsNilGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty},
    ArmsGrows cfg notes cursor (.nil : Arms D Γ mid [])

/-- Arms grow the state when the first arm and the others do. -/
def ArmsConsGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads),
    TermGrows cfg notes cursor.arm arm → ArmsGrows cfg notes cursor.next rest →
    ArmsGrows cfg notes cursor (.cons inputs arm rest)

/-- **The walk grows the state**, for every term: from the statements above by one mutual
induction. -/
def WalkGrowsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs),
    TermGrows cfg notes cursor t

end

/-! ## Running the skeleton, per kind -/

section
variable (σ : Setting D Raw)

/-- What the value side asks of a setting: the rules are lawful (it uses `computes`, `functional`
and `commutative`), and every condition reads as its truth value. -/
def Setting.ValueLaws : Prop :=
  σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined ∧ ConditionsRead σ.sem σ.R

/-- An exit runs its skeleton. -/
def RetRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (exit : HList (Var Γ) outs), TermRuns σ cursor (.ret exit)

/-- **A step runs its skeleton** when its instruction runs its entry and the rest runs its
skeleton. -/
def StepRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Instr D Γ mid) (results : Names mid) (rest : Term D (Γ.extend results) outs),
    InstrGrows σ.cfg σ.notes cursor key i → TermGrows σ.cfg σ.notes cursor.next rest →
    InstrRuns σ cursor key i → TermRuns σ cursor.next rest →
    TermRuns σ cursor (.step key i results rest)

/-- An operation runs its entry. -/
def OpRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {ins res : List D.Ty}
    (o : D.Op ins res) (operands : HList (Var Γ) ins), InstrRuns σ cursor key (.op o operands)

/-- A guard runs its entry. -/
def GuardRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {t : D.Ty} (w : D.Who)
    (c : Var Γ t) (ok : D.Condition w t) (why : Reason),
    InstrRuns σ cursor key (.guard w c ok why)

/-- A choice runs its entry when its regions run their skeletons. -/
def ChooseRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    {t : D.Ty} (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid),
    TermGrows σ.cfg σ.notes (cursor.region key) onTrue → TermGrows σ.cfg σ.notes (cursor.otherwise key) onFalse →
    TermRuns σ (cursor.region key) onTrue → TermRuns σ (cursor.otherwise key) onFalse →
    InstrRuns σ cursor key (.choose w c ok gives onTrue onFalse)

/-- A case analysis runs its entry when its arms run their skeletons. -/
def CasesRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty}
    {mid payloads : List D.Ty} {t : D.Ty} (w : D.Who) (x : Var Γ t)
    (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (arms : Arms D Γ mid payloads),
    ArmsGrows σ.cfg σ.notes (cursor.region key) arms → ArmsRuns σ (cursor.region key) arms →
    InstrRuns σ cursor key (.cases w x ok gives arms)

/-- A loop runs its entry when its body runs its skeleton. -/
def LoopRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {carried each : List D.Ty}
    (w : D.Who) (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each)),
    TermGrows σ.cfg σ.notes (cursor.region key) body → TermRuns σ (cursor.region key) body →
    InstrRuns σ cursor key (.loop w times gives initial inputs body)

/-- A block runs its entry when its body runs its skeleton under the block's frame. -/
def BlockRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (number : Nat) (body : Term D Γ mid),
    TermRuns σ (cursor.block key number) body →
    InstrRuns σ cursor key (.block number body)

/-- An attempt runs its entry when its body runs its skeleton. -/
def AttemptRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
    (body : Term D (Γ.extend inputs) mid),
    TermGrows σ.cfg σ.notes (cursor.region key) body → TermRuns σ (cursor.region key) body →
    InstrRuns σ cursor key (.attempt w owns inputs body)

/-- No arms run, there being no alternative. -/
def ArmsNilRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty},
    ArmsRuns σ cursor (.nil : Arms D Γ mid [])

/-- Arms run their skeletons when the first arm and the others do. -/
def ArmsConsRunsStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads),
    TermGrows σ.cfg σ.notes cursor.arm arm → ArmsGrows σ.cfg σ.notes cursor.next rest →
    TermRuns σ cursor.arm arm → ArmsRuns σ cursor.next rest →
    ArmsRuns σ cursor (.cons inputs arm rest)

/-- **Every term runs its skeleton**: from the statements above by one mutual induction. -/
def WalkRunsStatement : Prop :=
  σ.ValueLaws → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs), TermRuns σ cursor t

end

/-! ## Soundness, per kind -/

section
variable (σ : Setting D Raw)

/-- An exit is sound. -/
def RetSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (exit : HList (Var Γ) outs), TermSound σ cursor (.ret exit)

/-- **A step is sound** when its instruction and the rest are: the rest from what `Returned` says
of the instruction, with its results bound to the step's names. -/
def StepSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid outs : List D.Ty} (key : Key)
    (i : Instr D Γ mid) (results : Names mid) (rest : Term D (Γ.extend results) outs),
    InstrGrows σ.cfg σ.notes cursor key i → TermGrows σ.cfg σ.notes cursor.next rest →
    InstrSound σ cursor key i → TermSound σ cursor.next rest →
    TermSound σ cursor (.step key i results rest)

/-- An operation is sound: where none of its requirements is refused they hold, and what it
returns, shared or kept in order, is what `Returned` says. -/
def OpSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {ins res : List D.Ty}
    (o : D.Op ins res) (operands : HList (Var Γ) ins), InstrSound σ cursor key (.op o operands)

/-- A guard is sound. -/
def GuardSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {t : D.Ty} (w : D.Who)
    (c : Var Γ t) (ok : D.Condition w t) (why : Reason),
    InstrSound σ cursor key (.guard w c ok why)

/-- A choice is sound when its regions are. -/
def ChooseSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty}
    (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (gives : ∀ a, a ∈ mid → D.Gives w a)
    (onTrue onFalse : Term D Γ mid),
    TermGrows σ.cfg σ.notes (cursor.region key) onTrue → TermGrows σ.cfg σ.notes (cursor.otherwise key) onFalse →
    TermSound σ (cursor.region key) onTrue → TermSound σ (cursor.otherwise key) onFalse →
    InstrSound σ cursor key (.choose w c ok gives onTrue onFalse)

/-- A case analysis is sound when its arms are. -/
def CasesSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    {t : D.Ty} (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads),
    ArmsGrows σ.cfg σ.notes (cursor.region key) arms → ArmsSound σ (cursor.region key) arms →
    InstrSound σ cursor key (.cases w x ok gives arms)

/-- A loop is sound when its body is: its invariant holds of the initial values and is kept, it
holds at every iteration's entry and after the loop, and the bound recorded is an upper bound of
its count. -/
def LoopSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {carried each : List D.Ty}
    (w : D.Who) (times : Times D w Γ) (gives : ∀ a, a ∈ carried ++ each → D.Gives w a)
    (initial : HList (Var Γ) carried) (inputs : Names (D.index w :: carried))
    (body : Term D (Γ.extend inputs) (carried ++ each)),
    TermGrows σ.cfg σ.notes (cursor.region key) body → TermSound σ (cursor.region key) body →
    InstrSound σ cursor key (.loop w times gives initial inputs body)

/-- A block is sound when its body is, under the block's frame. -/
def BlockSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (number : Nat) (body : Term D Γ mid),
    TermGrows σ.cfg σ.notes (cursor.block key number) body →
    TermSound σ (cursor.block key number) body →
    InstrSound σ cursor key (.block number body)

/-- An attempt is sound when its body is. -/
def AttemptSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
    (body : Term D (Γ.extend inputs) mid),
    TermGrows σ.cfg σ.notes (cursor.region key) body → TermSound σ (cursor.region key) body →
    InstrSound σ cursor key (.attempt w owns inputs body)

/-- No arms are sound, there being no alternative. -/
def ArmsNilSoundStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty},
    ArmsSound σ cursor (.nil : Arms D Γ mid [])

/-- Arms are sound when the first arm and the others are. -/
def ArmsConsSoundStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {mid : List D.Ty} {payload : D.Ty}
    {payloads : List D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads),
    TermGrows σ.cfg σ.notes cursor.arm arm → ArmsGrows σ.cfg σ.notes cursor.next rest →
    TermSound σ cursor.arm arm → ArmsSound σ cursor.next rest →
    ArmsSound σ cursor (.cons inputs arm rest)

/-- **The walk is sound**, for every term: from the statements above by one mutual induction. -/
def WalkSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs), TermSound σ cursor t

end

/-! ## A prefix -/

section
variable (σ : Setting D Raw)

/-- **Soundness for a prefix**: from the invariant at its start, with its decided assertions
defined and its facts holding, when its walk adds no refusal, the prefix's process ends, on every
permitted path, in an environment of which, under leaves that extend those at its start, the
invariant holds for the identifiers, the state and the domain's state after the walk of the
prefix; and it never stops `undefined`. So what the walk knows after a prefix holds of every
environment that reaches the place after it. -/
def PrefixSoundStatement : Prop :=
  σ.Lawful → ∀ (cursor : StaticCursor) {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (path : List Frame)
    (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ) (s : State Raw)
    (k : σ.cfg.domain.State),
    let e := walkPrefix σ.cfg σ.notes cursor p ids s k
    Inv σ ρ ids env k s → Prefix.AnnotationsDefined σ cursor p → Prefix.EveryFact σ cursor p path env →
    e.state.refusals = s.refusals →
    (p.run σ.sem path env).Every σ.permitted
      (fun env' => ∃ ρ', ρ.Le ρ' ∧ Inv σ ρ' e.ids env' e.known e.state)
      (fun stop => ¬ σ.undefined stop)

/-- The walk of a prefix filled with a term is the walk of the prefix, then the walk of the term
from where the prefix's ends, the prefix's entries of the skeleton before the term's. -/
def WalkFillStatement : Prop :=
  ∀ (cursor : StaticCursor) {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (p : Prefix D Γ Δ)
    (t : Term D Δ outs) (ids : Ctx Ident) (s : State Raw) (k : σ.cfg.domain.State),
    let e := walkPrefix σ.cfg σ.notes cursor p ids s k
    let after := walk σ.cfg σ.notes (Prefix.afterCursor p cursor) t e.ids e.state e.known
    walk σ.cfg σ.notes cursor (p.fill t) ids s k =
      { after with skel := Skel.ofEntries e.entries after.skel }

end

/-- A term as a prefix and an exit: all its steps, and the names that it returns. -/
def Term.toPrefix {D : Dialect} : {Γ : Ctx D.Ty} → {outs : List D.Ty} →
    Term D Γ outs → (Δ : Ctx D.Ty) × Prefix D Γ Δ × HList (Var Δ) outs
  | Γ, _, .ret exit => ⟨Γ, .nil, exit⟩
  | _, _, .step key i results rest =>
      let after := Term.toPrefix rest
      ⟨after.1, .step key i results after.2.1, after.2.2⟩

/-- A term is its prefix filled with its exit. -/
def ToPrefixFillStatement {D : Dialect} : Prop :=
  ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs),
    (Term.toPrefix t).2.1.fill (.ret (Term.toPrefix t).2.2) = t

/-- **A term is sound as a prefix and an exit**: the first part of `TermSound` for every term from
soundness for a prefix (with `ToPrefixFillStatement` and `WalkFillStatement`). -/
def TermFromPrefixStatement (σ : Setting D Raw) : Prop :=
  PrefixSoundStatement σ → σ.Lawful →
    ∀ (cursor : StaticCursor) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
      (path : List Frame) (ρ : Leaves σ.sem.Dyn) (ids : Ctx Ident) (env : Env σ.sem.Val Γ)
      (s : State Raw) (k : σ.cfg.domain.State),
      let e := walk σ.cfg σ.notes cursor t ids s k
      Inv σ ρ ids env k s → Term.AnnotationsDefined σ cursor t →
      Term.EveryFact σ cursor t path env → e.state.refusals = s.refusals →
      (t.denote σ.sem path env).Every σ.permitted (Returned σ ρ ids env e.known e.state e.returned)
        (fun stop => ¬ σ.undefined stop)

/-! ## The main statements -/

/-- A definition satisfies a summary: on valid inputs of which every requirement holds, on
permitted replies, it never stops `undefined`, and what it returns is valid and, with the inputs,
satisfies every guarantee. `Summary.Holds` with assertions. -/
def Contract.HoldsWith (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
    (R : Reading sem.Dyn) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
    (Valid : sem.Dyn → Prop) (undefined : sem.H → Prop) (summary : Contract Raw) {ins outs : List D.Ty}
    (run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)) : Prop :=
  ∀ inputs : HList sem.Val ins, (∀ v, v ∈ sem.dyns inputs → Valid v) →
    (∀ expr ∈ summary.requires, expr.Holds Run R (sem.dyns inputs)) →
    (run inputs).Every permitted
      (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧ ∀ expr ∈ summary.ensures,
        expr.Holds Run R (sem.dyns inputs ++ sem.dyns returned))
      (fun stop => ¬ undefined stop)

/-- Interpret a contract with the analysis setting's operation and validity relations. -/
def Contract.Holds (σ : Setting D Raw) (summary : Contract Raw) {ins outs : List D.Ty}
    (run : HList σ.sem.Val ins → Process σ.sem.S σ.sem.H (HList σ.sem.Val outs)) : Prop :=
  summary.HoldsWith σ.sem σ.permitted σ.R σ.Runs σ.Valid σ.undefined run

/-- The setting of the second definition of a comparison: its key and its annotations. -/
def Setting.second (σ : Setting D Raw) (definition' : Key) (notes' : Annotations Raw) :
    Setting D Raw :=
  { σ with cfg := { σ.cfg with definition := definition' }, notes := notes' }

section
variable (σ : Setting D Raw)

/-- The value side of the analysis: the process of a body that never stops `undefined` runs the
skeleton of its analysis, from any table whose values are well formed, over the analysis's final
table, from the values of its inputs as the first leaves. (`analyse_runs`.) -/
def AnalyseRunsStatement : Prop :=
  σ.ValueLaws →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw),
      let e := analyseFrom σ.cfg σ.notes summary inputs body start
      start.WF →
      ∀ (path : List Frame) (values : HList σ.sem.Val types),
        σ.NotUndefined (body.denote σ.sem path (Env.empty.extend inputs values)) →
        Skel.Runs σ.sem σ.permitted σ.Run σ.R e.state.values.table path (inputLeaves σ.sem values)
          e.skel .nil (body.denote σ.sem path (Env.empty.extend inputs values))

/-- **A body that the analysis accepts is safe and satisfies its summary's guarantees, and respects
its bounds**: from any table whose values are well formed, for a body whose decided assertions and
whose summary's guarantees are defined, with distinct addresses, that the analysis refuses
nowhere, and bounds of the setting that the analysis recorded: on valid inputs of which every
requirement of the summary holds and where every given fact holds, every loop that a run reaches
respects the bounds, and the body never stops `undefined` and returns valid values of which, with
the inputs, every guarantee holds. (`analyse_safe`; with the start of a second walk,
`follow_safe`.) -/
def AnalyseSafeStatement : Prop :=
  σ.Lawful →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw),
      let e := analyseFrom σ.cfg σ.notes summary inputs body start
      start.WF → Term.AnnotationsDefined σ .root body →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
      (Term.addresses [] body).Nodup → e.state.refusals = [] →
      (∀ p b, (p, b) ∈ σ.F → p.definition = σ.cfg.definition → p.role = σ.cfg.role →
        (p, b) ∈ e.state.bounds) →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ .root body path (Env.empty.extend inputs values) →
        Term.EveryLoop σ.sem σ.permitted σ.Bounded body path []
            (Env.empty.extend inputs values) ∧
          (body.denote σ.sem path (Env.empty.extend inputs values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop)

/-- **A body that the analysis accepts is assured**, in the evidence layer's sense, on the starts
that give valid inputs of which the summary's requirements hold and where every given fact
holds. -/
def AnalyseAssuredStatement : Prop :=
  σ.Lawful →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs),
      Term.AnnotationsDefined σ .root body →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
      (analyse σ.cfg σ.notes summary inputs body).state.refusals = [] →
      Assured σ.sem σ.permitted σ.Valid σ.undefined body
        (fun path env => ∃ values : HList σ.sem.Val types, σ.AllValid values ∧
          (∀ requirement, requirement ∈ summary.requires →
            requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) ∧
          Term.EveryFact σ .root body path (Env.empty.extend inputs values) ∧
          env = Env.empty.extend inputs values)

/-- **A body that the analysis accepts satisfies its summary**, as a function of its inputs, where
every given fact holds. (`analyse_holds`.) -/
def AnalyseHoldsStatement : Prop :=
  σ.Lawful →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs),
      Term.AnnotationsDefined σ .root body →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
      (analyse σ.cfg σ.notes summary inputs body).state.refusals = [] →
      (∀ values : HList σ.sem.Val types,
        Term.EveryFact σ .root body [] (Env.empty.extend inputs values)) →
      Contract.Holds σ summary (fun values => body.denote σ.sem [] (Env.empty.extend inputs values))

/-- **The requirements of every operation that a run reaches hold there**, for a body that the
analysis accepts, on valid inputs of which the summary's requirements hold and where every given
fact holds. -/
def AnalyseRequiredStatement : Prop :=
  σ.Lawful →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs),
      Term.AnnotationsDefined σ .root body →
      (analyse σ.cfg σ.notes summary inputs body).state.refusals = [] →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ .root body path (Env.empty.extend inputs values) →
        Term.EveryRequired σ .root body path (Env.empty.extend inputs values)

/-- **The analysis of a definition is sound**: a body that it accepts respects its bounds, never
stops `undefined`, returns valid values of which, with the inputs, every guarantee of its summary
holds, and runs the skeleton of the analysis over its table. (`analyse_sound`.) -/
def AnalyseSoundStatement : Prop :=
  σ.Lawful → ConditionsRead σ.sem σ.R →
    ∀ {types outs : List D.Ty} (summary : Contract Raw) (inputs : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs),
      let e := analyse σ.cfg σ.notes summary inputs body
      Term.AnnotationsDefined σ .root body →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
      (Term.addresses [] body).Nodup → e.state.refusals = [] →
      (∀ p b, (p, b) ∈ σ.F → p.definition = σ.cfg.definition → p.role = σ.cfg.role →
        (p, b) ∈ e.state.bounds) →
      ∀ (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ .root body [] (Env.empty.extend inputs values) →
        Term.EveryLoop σ.sem σ.permitted σ.Bounded body [] []
            (Env.empty.extend inputs values) ∧
          (body.denote σ.sem [] (Env.empty.extend inputs values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop) ∧
          Skel.Runs σ.sem σ.permitted σ.Run σ.R e.state.values.table [] (inputLeaves σ.sem values)
            e.skel .nil (body.denote σ.sem [] (Env.empty.extend inputs values))

/-- **Validation by comparison**: when the skeletons of two bodies differ nowhere and neither body
stops `undefined`, the two have the same process on permitted replies, on every input. Both
safeties are inputs. -/
def CompareSameStatement : Prop :=
  σ.ValueLaws →
    ∀ (checks : SkelRules D) (definition' : Key) (notes' : Annotations Raw)
      {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs)
      (body' : Term D (Ctx.empty.extend inputs') outs),
      checks.Lawful →
      compareTerms σ.cfg checks definition' σ.notes notes' summary inputs inputs' body body' = [] →
      ∀ (path : List Frame) (values : HList σ.sem.Val types),
        σ.NotUndefined (body.denote σ.sem path (Env.empty.extend inputs values)) →
        σ.NotUndefined (body'.denote σ.sem path (Env.empty.extend inputs' values)) →
        Process.SameWhen σ.permitted (body.denote σ.sem path (Env.empty.extend inputs values))
          (body'.denote σ.sem path (Env.empty.extend inputs' values))

/-- **A body that follows another is safe**: its walk, from the first's final table, refuses
nothing, so it is safe and satisfies the summary's guarantees, and respects the bounds that its
walk recorded. Nothing is asked of the first. (`follow_safe`.) -/
def FollowSafeStatement : Prop :=
  σ.Lawful →
    ∀ (checks : SkelRules D) (definition' : Key) (notes' : Annotations Raw)
      {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs)
      (body' : Term D (Ctx.empty.extend inputs') outs),
      let σ' := σ.second definition' notes'
      let second := (analyseBoth σ.cfg definition' σ.notes notes' summary inputs inputs' body body').2
      follows σ.cfg checks definition' σ.notes notes' summary inputs inputs' body body' = true →
      Term.AnnotationsDefined σ' .root body' →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ' (types ++ outs) guarantee) →
      (Term.addresses [] body').Nodup →
      (∀ p b, (p, b) ∈ σ.F → p.definition = definition' → p.role = σ.cfg.role →
        (p, b) ∈ second.state.bounds) →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ' .root body' path (Env.empty.extend inputs' values) →
        Term.EveryLoop σ.sem σ.permitted σ'.Bounded body' path []
            (Env.empty.extend inputs' values) ∧
          (body'.denote σ.sem path (Env.empty.extend inputs' values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop)

/-- **A body that follows a safe body is safe and means the same**, however the first is known to
be safe: the second respects its bounds, never stops `undefined` and satisfies the summary's
guarantees, and the two processes are the same on permitted replies. Its corollary for an
accepted first body is `FollowsSoundStatement`. (`follow_assured`.) -/
def FollowsAssuredStatement : Prop :=
  σ.Lawful → ConditionsRead σ.sem σ.R →
    ∀ (checks : SkelRules D) (definition' : Key) (notes' : Annotations Raw)
      {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs)
      (body' : Term D (Ctx.empty.extend inputs') outs),
      let σ' := σ.second definition' notes'
      let second := (analyseBoth σ.cfg definition' σ.notes notes' summary inputs inputs' body body').2
      checks.Lawful →
      follows σ.cfg checks definition' σ.notes notes' summary inputs inputs' body body' = true →
      Term.AnnotationsDefined σ' .root body' →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ' (types ++ outs) guarantee) →
      (Term.addresses [] body').Nodup →
      (∀ p b, (p, b) ∈ σ.F → p.definition = definition' → p.role = σ.cfg.role →
        (p, b) ∈ second.state.bounds) →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ' .root body' path (Env.empty.extend inputs' values) →
        σ.NotUndefined (body.denote σ.sem path (Env.empty.extend inputs values)) →
        Term.EveryLoop σ.sem σ.permitted σ'.Bounded body' path []
            (Env.empty.extend inputs' values) ∧
          (body'.denote σ.sem path (Env.empty.extend inputs' values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop) ∧
          Process.SameWhen σ.permitted (body.denote σ.sem path (Env.empty.extend inputs values))
            (body'.denote σ.sem path (Env.empty.extend inputs' values))

/-- **A body that follows an accepted body is safe and means the same**: `FollowsAssuredStatement`
with the first safe because the analysis accepts it (`AnalyseSafeStatement`). Today's statement
about `follows`, as the corollary of validation by comparison. (`follow_sound`.) -/
def FollowsSoundStatement : Prop :=
  σ.Lawful → ConditionsRead σ.sem σ.R →
    ∀ (checks : SkelRules D) (definition' : Key) (notes' : Annotations Raw)
      {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs)
      (body' : Term D (Ctx.empty.extend inputs') outs),
      let σ' := σ.second definition' notes'
      let both := analyseBoth σ.cfg definition' σ.notes notes' summary inputs inputs' body body'
      checks.Lawful →
      Term.AnnotationsDefined σ .root body → Term.AnnotationsDefined σ' .root body' →
      (∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
      (Term.addresses [] body).Nodup → (Term.addresses [] body').Nodup →
      both.1.state.refusals = [] →
      follows σ.cfg checks definition' σ.notes notes' summary inputs inputs' body body' = true →
      (∀ p b, (p, b) ∈ σ.F → p.definition = definition' → p.role = σ.cfg.role →
        (p, b) ∈ both.2.state.bounds) →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ .root body path (Env.empty.extend inputs values) →
        Term.EveryFact σ' .root body' path (Env.empty.extend inputs' values) →
        Term.EveryLoop σ.sem σ.permitted σ'.Bounded body' path []
            (Env.empty.extend inputs' values) ∧
          (body'.denote σ.sem path (Env.empty.extend inputs' values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop) ∧
          Process.SameWhen σ.permitted (body.denote σ.sem path (Env.empty.extend inputs values))
            (body'.denote σ.sem path (Env.empty.extend inputs' values))

end

end

end Zkc.Core.BodyAnalysis

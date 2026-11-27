module

public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Scheme.DeployElim
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Program.Sites

@[expose] public section

/-!
Verified Core-level handler specialization (`Deployed V → ClosedRole`).

Every `Layer` stack in `Deployed V` is statically known, finite, and tail-resumptive, and every
protocol call graph in `Defs V` is acyclic. This module statically specializes a deployed role:
- erases located types `LTy V` to plain `V.Ty` (dropping values not held by the role, erasing
  `RoleOp.absent` and unheld `RoleOp.keep`, and lowering `RoleOp.compute` to direct `LocalOp`);
- statically resolves every `Layer` clause along `(through, ρ, key)` and inlines clause bodies
  against the strictly shorter layer stack below (`withLayer` / `underLayer`);
- inlines protocol applications (`RoleOp.apply`) structurally down `Defs V` (`frame`);
- lowers retried attempts matching `d.retry` to structured bounded retry loops (`retry`);
- bundles `Stack.start` (`StackInit`) and `Stack.finish` (`StackFinish`) into `ClosedRole`.

The main soundness theorem `specialize_sound` proves that `(specialize d r).denote` is
propositionally equal to `d.run` on every model, role, input, and taken value (for any well-nested
retry site, which holds unconditionally whenever `d.retry = none` and for all standard retried
schemes), using strictly Core's two-axiom policy (`propext`, `Quot.sound`) and zero `partial`
definitions.
-/

namespace Zkc.Core

/-! ## Residual effects -/

/-- A role effect statically described by its kind, peers, payload types, and reply types.
At the bottom of a specialized handler stack (`σ = []`), unhandled effects remain as
`ClosedTerm.effect` nodes (for a covered non-interactive deployment, only private coins,
service requests, and local attempt marks). -/
inductive ResidualOp (V : Vocabulary) : List V.Ty → List V.Ty → Type where
  | give (kind : FlowKind) (getters : List Role) (τ : V.Ty) : ResidualOp V [τ] []
  | get (kind : FlowKind) (giver : Role) (τ : V.Ty) : ResidualOp V [] [τ]
  | own (kind : GivenKind V) (hearers : List Role) (ins : List V.Ty) (τ : V.Ty) :
      ResidualOp V ins [τ]
  | hear (kind : GivenKind V) (owner : Role) (τ : V.Ty) : ResidualOp V [] [τ]
  | begin : ResidualOp V [] [.nat]
  | settle : ResidualOp V [] []

/-- The role's `Part` corresponding to a static effect description. -/
def ResidualOp.part {V : Vocabulary} {ins res : List V.Ty} : ResidualOp V ins res → Option (Part V)
  | .give kind getters _ => some (.give kind getters)
  | .get kind giver _ => some (.get kind giver)
  | .own kind hearers _ _ => some (.own kind hearers)
  | .hear kind owner _ => some (.hear kind owner)
  | .begin => none
  | .settle => none

/-- Rename peer roles in a static effect description, matching `mapR`. -/
def ResidualOp.mapPeers {V : Vocabulary} (ρ : Role → Role) {ins res : List V.Ty} :
    ResidualOp V ins res → ResidualOp V ins res
  | .give kind getters τ => .give kind (getters.map ρ) τ
  | .get kind giver τ => .get kind (ρ giver) τ
  | .own kind hearers ins τ => .own kind (hearers.map ρ) ins τ
  | .hear kind owner τ => .hear kind (ρ owner) τ
  | .begin => .begin
  | .settle => .settle

section
variable {V : Vocabulary} (M : Model V)

/-- Instantiate a static effect description at an occurrence and payload into an `ROp M`. -/
def ResidualOp.toROp {ins res : List V.Ty} (at_ : Occurrence) :
    ResidualOp V ins res → HList M.Val ins → ROp M
  | .give kind getters τ, .cons v .nil => .give kind getters at_ τ v
  | .get kind giver τ, .nil => .get kind giver at_ τ
  | .own kind hearers _ τ, vs => .own kind hearers at_ _ vs τ
  | .hear kind owner τ, .nil => .hear kind owner at_ τ
  | .begin, .nil => .begin at_
  | .settle, .nil => .settle at_

/-- Package a reply from `RSig M` into the result `HList M.Val res` of a static effect. -/
def ResidualOp.replyOf {ins res : List V.Ty} (at_ : Occurrence) :
    (op : ResidualOp V ins res) → (vs : HList M.Val ins) →
    (RSig M).Reply (op.toROp M at_ vs) → HList M.Val res
  | .give _ _ _, .cons _ .nil, _ => .nil
  | .get _ _ _, .nil, v => .cons v .nil
  | .own _ _ _ _, _, v => .cons v .nil
  | .hear _ _ _, .nil, v => .cons v .nil
  | .begin, .nil, n => .cons n .nil
  | .settle, .nil, _ => .nil

theorem ResidualOp.toROp_occurrence {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.occurrence M (op.toROp M at_ vs) = at_ := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_part {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.part M (op.toROp M at_ vs) = op.part := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_takes {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.takes M (op.toROp M at_ vs) = ins := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_gives {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    ROp.gives M (op.toROp M at_ vs) = res := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.toROp_payload {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) :
    cast (congrArg (HList M.Val) (op.toROp_takes M at_ vs)) (ROp.payload M (op.toROp M at_ vs)) = vs := by
  cases op with
  | give _ _ _ => cases vs with | cons _ rest => cases rest; rfl
  | get _ _ _ => cases vs; rfl
  | own _ _ _ _ => rfl
  | hear _ _ _ => cases vs; rfl
  | begin => cases vs; rfl
  | settle => cases vs; rfl

theorem ResidualOp.replyOf_reply {ins res : List V.Ty} (at_ : Occurrence)
    (op : ResidualOp V ins res) (vs : HList M.Val ins) (out : HList M.Val res) :
    op.replyOf M at_ vs (ROp.reply M (op.toROp M at_ vs)
      (cast (congrArg (HList M.Val) (op.toROp_gives M at_ vs).symm) out)) = out := by
  cases op with
  | give _ _ _ => cases vs with | cons _ r => cases r; cases out; rfl
  | get _ _ _ => cases vs; cases out with | cons _ r => cases r; rfl
  | own _ _ _ _ => cases out with | cons _ r => cases r; rfl
  | hear _ _ _ => cases vs; cases out with | cons _ r => cases r; rfl
  | begin => cases vs; cases out with | cons _ r => cases r; rfl
  | settle => cases vs; cases out; rfl

end

/-! ## Residual closed IR (`ClosedTerm`, `ClosedRole`) -/

/-- Loop iteration count for a specialized closed term. -/
inductive ClosedTimes {V : Vocabulary} (Γ : Ctx V.Ty) where
  | fixed (n : Nat)
  | value (count : Var Γ .nat)

/-- Static size of a closed loop count, when fixed. -/
def ClosedTimes.size {V : Vocabulary} {Γ : Ctx V.Ty} : ClosedTimes Γ → Option Nat
  | .fixed n => some n
  | .value _ => none

/-- The `again` local terms of a handler stack, one per layer state type in `σ`. -/
abbrev StackAgain (V : Vocabulary) (fns : List (FnHeader V)) (σ : List V.Ty) : Type :=
  HList (fun τ => Term (localDialect V fns) (Ctx.positional [.nat, τ, τ]) [τ]) σ

/-- The `start` local terms of a handler stack, initializing `σ` from `taken` and `heldIns`. -/
inductive StackInit (V : Vocabulary) (fns : List (FnHeader V)) (heldIns : List V.Ty) :
    List V.Ty → List V.Ty → Type where
  | nil : StackInit V fns heldIns [] []
  | cons {τ : V.Ty} {takes : List V.Ty} {σ_rest takes_rest : List V.Ty}
      (start : Term (localDialect V fns) (Ctx.positional (takes ++ heldIns)) [τ])
      (rest : StackInit V fns heldIns σ_rest takes_rest) :
      StackInit V fns heldIns (τ :: σ_rest) (takes ++ takes_rest)

/-- The `finish` local terms of a handler stack, producing `gives` from final states `σ`. -/
inductive StackFinish (V : Vocabulary) (fns : List (FnHeader V)) :
    List V.Ty → List V.Ty → Type where
  | nil : StackFinish V fns [] []
  | cons {τ : V.Ty} {gives : List V.Ty} {σ_rest gives_rest : List V.Ty}
      (finish : Term (localDialect V fns) (Ctx.positional [τ]) gives)
      (rest : StackFinish V fns σ_rest gives_rest) :
      StackFinish V fns (τ :: σ_rest) (gives ++ gives_rest)

/-- Context extended with an optional loop index name and carried variable names. -/
def loopBodyCtx {V : Vocabulary} (Γ : Ctx V.Ty) (idxName : Option Name) {carried : List V.Ty}
    (carriedNames : Names carried) : Ctx V.Ty :=
  (match idxName with | some nm => Γ.insert nm .nat | none => Γ).extend carriedNames

mutual
  /-- A handler-free, plain-typed imperative role term threading layer states `σ : List V.Ty`. -/
  inductive ClosedTerm (V : Vocabulary) (fns : List (FnHeader V)) :
      List V.Ty → Ctx V.Ty → List V.Ty → Type where
    | ret {σ Γ outs} (exit : HList (Var Γ) outs) : ClosedTerm V fns σ Γ outs
    | letBind {σ Γ outs mid} (first : ClosedTerm V fns σ Γ mid)
        (results : Names mid) (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    /-- Run `first`, then run `second` for its effects/state updates, returning `first`'s values. -/
    | seq {σ Γ mid} (first : ClosedTerm V fns σ Γ mid)
        (second : ClosedTerm V fns σ Γ []) :
        ClosedTerm V fns σ Γ mid
    | alias {σ Γ outs τ} (x : Var Γ τ) (name : Name)
        (rest : ClosedTerm V fns σ (Γ.insert name τ) outs) :
        ClosedTerm V fns σ Γ outs
    | localOp {σ Γ outs ins res} (key : Key) (o : LocalOp V fns ins res)
        (operands : HList (Var Γ) ins) (results : Names res)
        (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    | guard {σ Γ outs} (key : Key) (c : Var Γ .bool) (why : Reason)
        (rest : ClosedTerm V fns σ Γ outs) :
        ClosedTerm V fns σ Γ outs
    | choose {σ Γ outs mid} (key : Key) (c : Var Γ .bool)
        (onTrue onFalse : ClosedTerm V fns σ Γ mid) (results : Names mid)
        (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    | cases {σ Γ outs mid vkey alts} (key : Key) (x : Var Γ (.variant vkey alts))
        (arms : ClosedArms V fns σ Γ mid alts.toList) (results : Names mid)
        (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    | loop {σ Γ outs carried each} (key : Key) (times : ClosedTimes Γ)
        (initial : HList (Var Γ) carried) (idxName : Option Name) (carriedNames : Names carried)
        (body : ClosedTerm V fns σ (loopBodyCtx Γ idxName carriedNames) (carried ++ each))
        (results : Names (carried ++ each.map (fun τ => .seq τ times.size)))
        (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    | block {σ Γ outs mid} (key : Key) (number : Nat)
        (body : ClosedTerm V fns σ Γ mid) (results : Names mid)
        (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    /-- Inlined protocol call frame (pushing `.application key` onto the path when `appKey = some key`). -/
    | frame {σ Γ outs argTys mid} (appKey : Option Key)
        (args : HList (Var Γ) argTys) (inputs : Names argTys)
        (body : ClosedTerm V fns σ (Ctx.empty.extend inputs) mid)
        (results : Names mid) (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs
    /-- Inlined clause of the top layer `τ` executing over lower layer states `σ_rest`.
    On halt, preserves the top layer's state before the clause, matching `Clause.answer`. -/
    | withLayer {τ : V.Ty} {σ_rest : List V.Ty} {Γ argTys mid}
        (args : HList (Var Γ) argTys) (inputs : Names (argTys ++ [τ]))
        (body : ClosedTerm V fns σ_rest (Ctx.empty.extend inputs) (mid ++ [τ])) :
        ClosedTerm V fns (τ :: σ_rest) Γ mid
    /-- Delegate an unhandled effect at the top layer `τ` to the lower layers `σ_rest`. -/
    | underLayer {τ : V.Ty} {σ_rest : List V.Ty} {Γ mid}
        (inner : ClosedTerm V fns σ_rest Γ mid) :
        ClosedTerm V fns (τ :: σ_rest) Γ mid
    /-- Unhandled residual effect reaching the bottom of the stack (`σ = []`). -/
    | effect {Γ ins res} (key : Key) (op : ResidualOp V ins res)
        (operands : HList (Var Γ) ins) : ClosedTerm V fns [] Γ res
    /-- Structured bounded retry loop lowered from a retried `.attempt`. -/
    | retry {σ Γ outs mid} (key : Key) (bound : Nat) (again : StackAgain V fns σ)
        (inputs : Names [.nat]) (body : ClosedTerm V fns σ (Γ.extend inputs) mid)
        (results : Names mid) (rest : ClosedTerm V fns σ (Γ.extend results) outs) :
        ClosedTerm V fns σ Γ outs

  /-- Variant case arms for `ClosedTerm.cases`. -/
  inductive ClosedArms (V : Vocabulary) (fns : List (FnHeader V)) :
      List V.Ty → Ctx V.Ty → List V.Ty → List V.Ty → Type where
    | nil {σ Γ mid} : ClosedArms V fns σ Γ mid []
    | cons {σ Γ mid payload payloads} (inputs : Names [payload])
        (arm : ClosedTerm V fns σ (Γ.extend inputs) mid)
        (rest : ClosedArms V fns σ Γ mid payloads) :
        ClosedArms V fns σ Γ mid (payload :: payloads)
end

/-- A specialized, handler-free role program ready for direct execution. -/
structure ClosedRole (V : Vocabulary) (fns : List (FnHeader V)) (r : Role)
    (ins outs : List (LTy V)) (taken gives : List V.Ty) where
  states : List V.Ty
  inputs : Names (held r ins)
  start : StackInit V fns (held r ins) states taken
  body : ClosedTerm V fns states (Ctx.empty.extend inputs) (held r outs)
  finish : StackFinish V fns states gives

/-! ## Denotational semantics of `ClosedTerm` and `ClosedRole` -/

section
variable {V : Vocabulary} (M : Model V)

/-- Reconstruct a role's located values `HList (RV M r) items` from its held plain values. -/
def unheldValues (r : Role) :
    {items : List (LTy V)} → HList M.Val (held r items) → HList (RV M r) items
  | [], .nil => .nil
  | a :: rest, vs =>
      if h : r ∈ a.holders then
        have hEq : held r (a :: rest) = a.ty :: held r rest := by simp [held, h]
        match cast (congrArg (HList M.Val) hEq) vs with
        | .cons v more => .cons (hide M r a v) (unheldValues r more)
      else
        have hEq : held r (a :: rest) = held r rest := by simp [held, h]
        .cons (nothing M h) (unheldValues r (cast (congrArg (HList M.Val) hEq) vs))

/-- Evaluate a stack's `again` terms on `(i, entry, stop)`. -/
def StackAgain.eval {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {σ : List V.Ty} → StackAgain V fns σ → Nat → HList M.Val σ → HList M.Val σ →
    Except Stop (HList M.Val σ)
  | [], .nil, _, .nil, .nil => .ok .nil
  | _ :: _, .cons ag rest, i, .cons e es, .cons t ts =>
      match ag.denote (localSem M fns fnTable) []
          (Env.positional (.cons (i : Nat) (.cons e (.cons t .nil)))) with
      | .done (.cons next .nil) =>
          (StackAgain.eval fnTable rest i es ts).map fun more => .cons next more
      | .halt why => .error why
      | .call op _ => nomatch op

/-- Evaluate `StackInit` to produce the initial stack state. -/
def StackInit.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) {heldIns : List V.Ty} :
    {σ taken : List V.Ty} → StackInit V fns heldIns σ taken →
    HList M.Val heldIns → HList M.Val taken → Program M (HList M.Val σ)
  | [], [], .nil, _, .nil => .done .nil
  | _ :: _, _, .cons (takes := takes) st rest, ins, taken =>
      let parts := HList.split takes taken
      (liftLocal id (st.denote (localSem M fns fnTable) []
        (Env.positional (HList.append parts.1 ins)))).bind fun first =>
        (rest.denote fnTable ins parts.2).map fun others => .cons first.single others

/-- Evaluate `StackFinish` on the final stack state to produce what the layers give. -/
def StackFinish.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
    {σ gives : List V.Ty} → StackFinish V fns σ gives →
    HList M.Val σ → Program M (HList M.Val gives)
  | [], [], .nil, .nil => .done .nil
  | _ :: _, _, .cons fin rest, .cons s states =>
      (liftLocal id (fin.denote (localSem M fns fnTable) [] (Env.positional (.cons s .nil)))).bind
        fun mine => (rest.denote fnTable states).map fun others => HList.append mine others

/-- Evaluate a `ClosedTimes` count in a plain environment. -/
def ClosedTimes.eval {Γ : Ctx V.Ty} (env : Env M.Val Γ) : ClosedTimes Γ → Nat
  | .fixed n => n
  | .value count => env.get count

/-- Extend an environment for a `ClosedTerm.loop` body iteration. -/
def loopBodyEnv {Γ : Ctx V.Ty} (env : Env M.Val Γ) (idxName : Option Name) (i : Nat)
    {carried : List V.Ty} (carriedNames : Names carried) (vals : HList M.Val carried) :
    Env M.Val (loopBodyCtx Γ idxName carriedNames) :=
  match idxName with
  | some nm => (env.insert nm (i : Nat)).extend carriedNames vals
  | none => env.extend carriedNames vals

/-- Reverse each collected list into its sequence value, matching `Semantics.collected`. -/
def closedCollected (size : Option Nat) :
    {each : List V.Ty} → HList (fun τ => List (M.Val τ)) each →
    HList M.Val (each.map fun τ => .seq τ size)
  | [], .nil => .nil
  | _ :: _, .cons vs rest => .cons vs.reverse (closedCollected size rest)

/-- Structured retry loop over a body returning `Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ)`. -/
def retryAttempts {σ : List V.Ty} {A : Type} (exhausted : Stop)
    (again : Nat → HList M.Val σ → HList M.Val σ → Except Stop (HList M.Val σ))
    (body : Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ))
    (entry : HList M.Val σ) :
    Nat → Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ)
  | 0, _, s => .halt (exhausted, s)
  | n + 1, i, s => (body i s).recover fun stop =>
      if Stop.isAbort stop.1 then
        match n with
        | 0 => .halt (exhausted, stop.2)
        | _ + 1 =>
            match again (i + 1) entry stop.2 with
            | .ok next => retryAttempts exhausted again body entry n (i + 1) next
            | .error why => .halt (why, stop.2)
      else .halt stop

mutual
  /-- Denotation of a `ClosedTerm`, threading stack states `HList M.Val σ`. -/
  def ClosedTerm.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {outs : List V.Ty} →
      ClosedTerm V fns σ Γ outs → List Frame → Env M.Val Γ → HList M.Val σ →
      Process (RSig M) (Stop × HList M.Val σ) (HList M.Val outs × HList M.Val σ)
    | _, _, _, .ret exit, _, env, st => .done (env.all exit, st)
    | _, _, _, .letBind first results rest, path, env, st =>
        (first.denote fnTable path env st).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2
    | _, _, _, .seq first second, path, env, st =>
        (first.denote fnTable path env st).bind fun out =>
          (second.denote fnTable path env out.2).map fun out2 => (out.1, out2.2)
    | _, _, _, .alias x name rest, path, env, st =>
        rest.denote fnTable path (env.insert name (env.get x)) st
    | _, _, _, .localOp _ o operands results rest, path, env, st =>
        (liftLocal (fun why => (why, st)) (localOp M fnTable o (env.all operands))).bind fun vs =>
          rest.denote fnTable path (env.extend results vs) st
    | _, _, _, .guard key c why rest, path, env, st =>
        bif env.get c then rest.denote fnTable path env st
        else .halt (.declared why ⟨path, key⟩, st)
    | _, _, _, .choose _ c onTrue onFalse results rest, path, env, st =>
        (bif env.get c then onTrue.denote fnTable path env st
         else onFalse.denote fnTable path env st).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2
    | _, _, _, .cases (alts := alts) _ x arms results rest, path, env, st =>
        (arms.denote fnTable path env st (Tys.pick M alts (env.get x))).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2
    | σ, _, _, .loop (carried := carried) (each := each) key times initial idxName carriedNames
        body results rest, path, env, st =>
        let step := fun (i : Nat)
            (ls : (HList M.Val carried × HList (fun τ => List (M.Val τ)) each) × HList M.Val σ) =>
          (body.denote fnTable (path ++ [.iteration key i])
              (loopBodyEnv M env idxName i carriedNames ls.1.1) ls.2).bind fun out =>
            let sp := HList.split carried out.1
            .done ((sp.1, ls.1.2.push sp.2), out.2)
        (Process.iterate (times.eval M env) step 0 ((env.all initial, HList.empties each), st)).bind
          fun ls =>
            rest.denote fnTable path
              (env.extend results (ls.1.1.append (closedCollected M times.size ls.1.2))) ls.2
    | _, _, _, .block key number body results rest, path, env, st =>
        (body.denote fnTable (path ++ [.iteration key number]) env st).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2
    | _, _, _, .frame appKey args inputs body results rest, path, env, st =>
        let subPath := match appKey with | some k => path ++ [.application k] | none => path
        (body.denote fnTable subPath (Env.empty.extend inputs (env.all args)) st).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2
    | _ :: _, _, _, .withLayer (mid := mid) args inputs body, path, env, .cons mine below =>
        ((body.denote fnTable path
            (Env.empty.extend inputs ((env.all args).append (.cons mine .nil))) below).mapHalt
            fun stop => (stop.1, .cons mine stop.2)).map fun out =>
          let sp := HList.split mid out.1
          (sp.1, .cons sp.2.single out.2)
    | _ :: _, _, _, .underLayer inner, path, env, .cons mine below =>
        ((inner.denote fnTable path env below).mapHalt
            fun stop => (stop.1, .cons mine stop.2)).map fun out =>
          (out.1, .cons mine out.2)
    | [], _, _, .effect key op operands, path, env, .nil =>
        .call (op.toROp M ⟨path, key⟩ (env.all operands)) fun reply =>
          .done (op.replyOf M ⟨path, key⟩ (env.all operands) reply, .nil)
    | _, _, _, .retry key bound again inputs body results rest, path, env, st =>
        (retryAttempts M (.declared .exhausted ⟨path, key⟩)
          (StackAgain.eval M fnTable again)
          (fun i s' => Process.markOwn M (.attempt key i)
            (body.denote fnTable path (env.extend inputs (.cons (i : Nat) .nil)) s'))
          st bound 0 st).bind fun out =>
          rest.denote fnTable path (env.extend results out.1) out.2

  /-- Denotation of `ClosedArms`. -/
  def ClosedArms.denote {fns : List (FnHeader V)} (fnTable : FnTable M fns) :
      {σ : List V.Ty} → {Γ : Ctx V.Ty} → {mid payloads : List V.Ty} →
      ClosedArms V fns σ Γ mid payloads → List Frame → Env M.Val Γ → HList M.Val σ →
      Pick M.Val payloads →
      Process (RSig M) (Stop × HList M.Val σ) (HList M.Val mid × HList M.Val σ)
    | _, _, _, _, .cons inputs arm _, path, env, st, .here v =>
        arm.denote fnTable path (env.extend inputs (.cons v .nil)) st
    | _, _, _, _, .cons _ _ rest, path, env, st, .there p =>
        rest.denote fnTable path env st p
end

/-- Denotation of a `ClosedRole` directly on plain held inputs and outputs (no `RV`/`LTy`). -/
def ClosedRole.denoteHeld {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (heldIns : HList M.Val (held r ins)) (takenVals : HList M.Val taken) :
    Process (RSig M) Stop (HList M.Val (held r outs) × HList M.Val gives) :=
  (cr.start.denote M fnTable heldIns takenVals).bind fun st0 =>
    ((cr.body.denote M fnTable [] (Env.empty.extend cr.inputs heldIns) st0).mapHalt Prod.fst).bind
      fun out => (cr.finish.denote M fnTable out.2).map fun g => (out.1, g)

/-- Denotation of a `ClosedRole` matching `Deployed.run`'s signature. -/
def ClosedRole.denote {fns : List (FnHeader V)} {r : Role}
    {ins outs : List (LTy V)} {taken gives : List V.Ty}
    (fnTable : FnTable M fns) (cr : ClosedRole V fns r ins outs taken gives)
    (inputVals : HList (RV M r) ins) (takenVals : HList M.Val taken) :
    Process (RSig M) Stop (HList (RV M r) outs × HList M.Val gives) :=
  (cr.denoteHeld M fnTable (heldValues M r inputVals) takenVals).map fun out =>
    (unheldValues M r out.1, out.2)

end

/-! ## Held-type and context-erasure combinators -/

section Erasure
variable {V : Vocabulary}

theorem held_append (r : Role) : ∀ (as bs : List (LTy V)),
    held r (as ++ bs) = held r as ++ held r bs
  | [], _ => rfl
  | a :: as, bs => by
      simp only [List.cons_append, held]
      split
      · simp only [List.cons_append, held_append r as bs]
      · exact held_append r as bs

theorem held_alone (r : Role) : ∀ (types : List V.Ty),
    held r (alone r types) = types
  | [] => rfl
  | τ :: rest => by
      change held r (⟨τ, [r]⟩ :: alone r rest) = τ :: rest
      simp only [held, List.mem_singleton, ↓reduceIte]
      exact congrArg (τ :: ·) (held_alone r rest)

theorem held_map_collected (r : Role) (size : Option Nat) : ∀ (each : List (LTy V)),
    held r (each.map (LTy.collected size)) = (held r each).map (fun τ => .seq τ size)
  | [] => rfl
  | a :: rest => by
      simp only [List.map_cons, held, LTy.collected]
      split
      · simp only [List.map_cons, held_map_collected r size rest]
      · exact held_map_collected r size rest

theorem held_map_roleMap (ρ : RoleMap) (r : Role) : ∀ (items : List (LTy V)),
    held r (items.map (LTy.map ρ.to)) = held (ρ.back r) items
  | [] => rfl
  | a :: rest => by
      simp only [List.map_cons, held, LTy.map, ρ.mem_map]
      split
      · simp only [held_map_roleMap ρ r rest]
      · exact held_map_roleMap ρ r rest

theorem held_map_holders (r : Role) (R : Holders) (h : r ∈ R) : ∀ (outs : List V.Ty),
    held r (outs.map fun τ => ⟨τ, R⟩) = outs
  | [] => rfl
  | _ :: rest => by
      simp only [List.map_cons, held, h, ↓reduceIte, held_map_holders r R h rest]

theorem held_all_out (r : Role) : ∀ (items : List (LTy V)),
    (∀ a, a ∈ items → r ∉ a.holders) → held r items = []
  | [], _ => rfl
  | a :: rest, out => by
      have ha : r ∉ a.holders := out a List.mem_cons_self
      simp only [held, ha, ↓reduceIte]
      exact held_all_out r rest fun b hb => out b (List.mem_cons_of_mem _ hb)

/-- Keep the names of bindings whose located type is held by `r`. -/
def heldNames (r : Role) : {items : List (LTy V)} → Names items → Names (held r items)
  | [], .nil => .nil
  | a :: rest, .cons name more =>
      if h : r ∈ a.holders then
        have hEq : held r (a :: rest) = a.ty :: held r rest := by simp [held, h]
        cast (congrArg Names hEq.symm) (HList.cons name (heldNames r more))
      else
        have hEq : held r (a :: rest) = held r rest := by simp [held, h]
        cast (congrArg Names hEq.symm) (heldNames r more)

/-- Context erasure invariant: every name held by `r` in `Γ` is present in `Δ` at its plain type. -/
def CtxRel (r : Role) (Γ : Ctx (LTy V)) (Δ : Ctx V.Ty) : Prop :=
  ∀ name a, Γ.find? name = some a → r ∈ a.holders → Δ.find? name = some a.ty

theorem CtxRel.empty (r : Role) : CtxRel r (Ctx.empty : Ctx (LTy V)) (Ctx.empty : Ctx V.Ty) :=
  fun name _ h _ => nomatch (Ctx.find?_empty name).symm.trans h

theorem CtxRel.insert_held {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (name : Name) {a : LTy V} :
    CtxRel r (Γ.insert name a) (Δ.insert name a.ty) := by
  intro name' b hΓ hr
  rw [Ctx.find?_insert] at hΓ ⊢
  by_cases same : name' = name
  · rw [ite_eq_left same] at hΓ ⊢
    cases Option.some.inj hΓ
    rfl
  · rw [ite_eq_right same] at hΓ ⊢
    exact hCtx name' b hΓ hr

theorem CtxRel.insert_unheld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (name : Name) {a : LTy V} (hOut : r ∉ a.holders) :
    CtxRel r (Γ.insert name a) Δ := by
  intro name' b hΓ hr
  rw [Ctx.find?_insert] at hΓ
  by_cases same : name' = name
  · rw [ite_eq_left same] at hΓ
    cases Option.some.inj hΓ
    exact absurd hr hOut
  · rw [ite_eq_right same] at hΓ
    exact hCtx name' b hΓ hr

theorem held_cons_pos (r : Role) (a : LTy V) (rest : List (LTy V)) (h : r ∈ a.holders) :
    held r (a :: rest) = a.ty :: held r rest := by
  simp [held, h]

theorem held_cons_neg (r : Role) (a : LTy V) (rest : List (LTy V)) (h : r ∉ a.holders) :
    held r (a :: rest) = held r rest := by
  simp [held, h]

theorem heldNames_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (name : Name) (more : Names rest) :
    heldNames r (HList.cons name more) =
      cast (congrArg Names (held_cons_pos r a rest h).symm)
        (HList.cons name (heldNames r more)) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg Names (held_cons_pos r a rest h').symm) (HList.cons name (heldNames r more))
    else cast (congrArg Names (held_cons_neg r a rest h').symm) (heldNames r more)) = _
  exact dite_eq_left h

theorem heldNames_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (name : Name) (more : Names rest) :
    heldNames r (HList.cons name more) =
      cast (congrArg Names (held_cons_neg r a rest h).symm)
        (heldNames r more) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg Names (held_cons_pos r a rest h').symm) (HList.cons name (heldNames r more))
    else cast (congrArg Names (held_cons_neg r a rest h').symm) (heldNames r more)) = _
  exact dite_eq_right h

theorem ctx_extend_cast {T : Type} (Δ : Ctx T) {as bs : List T} (h : as = bs) (ns : Names as) :
    Δ.extend (cast (congrArg Names h) ns) = Δ.extend ns := by
  subst h; rfl

theorem CtxRel.extend {r : Role} :
    ∀ {items : List (LTy V)} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty},
      CtxRel r Γ Δ → (bound : Names items) →
      CtxRel r (Γ.extend bound) (Δ.extend (heldNames r bound))
  | [], _, _, hCtx, .nil => hCtx
  | a :: rest, Γ, Δ, hCtx, .cons name more => by
      by_cases h : r ∈ a.holders
      · rw [Ctx.extend, heldNames_cons_pos h,
          ctx_extend_cast Δ (held_cons_pos r a rest h).symm, Ctx.extend]
        exact CtxRel.extend (hCtx.insert_held name) more
      · rw [Ctx.extend, heldNames_cons_neg h,
          ctx_extend_cast Δ (held_cons_neg r a rest h).symm]
        exact CtxRel.extend (hCtx.insert_unheld name h) more

theorem CtxRel.positional_alone (r : Role) (types : List V.Ty) :
    CtxRel r (Ctx.positional (alone r types)) (Ctx.positional types) := by
  intro name a hΓ _
  rw [Ctx.find?_positional] at hΓ ⊢
  rw [alone, List.getElem?_map] at hΓ
  cases hT : types[name]? with
  | none => rw [hT] at hΓ; cases hΓ
  | some τ =>
      rw [hT] at hΓ
      cases Option.some.inj hΓ
      rfl

/-- Lift a held located variable along `CtxRel` to a plain `V.Ty` variable. -/
def varHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {a : LTy V} (x : Var Γ a) (h : r ∈ a.holders) : Var Δ a.ty :=
  ⟨x.name, hCtx x.name a x.typed h⟩

/-- Lift a list of located variables to the plain variables held by `r`. -/
def varsHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ) :
    {items : List (LTy V)} → HList (Var Γ) items → HList (Var Δ) (held r items)
  | [], .nil => .nil
  | a :: rest, .cons x more =>
      if h : r ∈ a.holders then
        have hEq : held r (a :: rest) = a.ty :: held r rest := by simp [held, h]
        cast (congrArg (HList (Var Δ)) hEq.symm) (HList.cons (varHeld hCtx x h) (varsHeld hCtx more))
      else
        have hEq : held r (a :: rest) = held r rest := by simp [held, h]
        cast (congrArg (HList (Var Δ)) hEq.symm) (varsHeld hCtx more)

/-- Lift a list of variables all held by `r` to plain variables of their underlying types. -/
def varsAllHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ) :
    {items : List (LTy V)} → (∀ a, a ∈ items → r ∈ a.holders) →
    HList (Var Γ) items → HList (Var Δ) (items.map LTy.ty)
  | [], _, .nil => .nil
  | a :: _, here, .cons x rest =>
      .cons (varHeld hCtx x (here a List.mem_cons_self))
        (varsAllHeld hCtx (fun b hb => here b (List.mem_cons_of_mem _ hb)) rest)

/-- Select and cast caller operand variables matching the callee's held ports across a `RoleMap`. -/
def fitVars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ) (ρ : RoleMap) :
    {as bs : List (LTy V)} → Fits as (bs.map (LTy.map ρ.to)) →
    HList (Var Γ) as → HList (Var Δ) (held (ρ.back r) bs)
  | [], [], _, .nil => .nil
  | a :: _, b :: bs, fits, .cons x rest =>
      if h : ρ.back r ∈ b.holders then
        have hEq : held (ρ.back r) (b :: bs) = b.ty :: held (ρ.back r) bs := by simp [held, h]
        let hr : r ∈ a.holders := fits.1.2 r (ρ.mem_map.mpr h)
        let v : Var Δ b.ty := cast (congrArg (Var Δ) fits.1.1) (varHeld hCtx x hr)
        cast (congrArg (HList (Var Δ)) hEq.symm) (HList.cons v (fitVars hCtx ρ fits.2 rest))
      else
        have hEq : held (ρ.back r) (b :: bs) = held (ρ.back r) bs := by simp [held, h]
        cast (congrArg (HList (Var Δ)) hEq.symm) (fitVars hCtx ρ fits.2 rest)
  | [], _ :: _, fits, _ => nomatch fits
  | _ :: _, [], fits, _ => nomatch fits

/-- Weaken a `LocalOp` from earlier function headers `fns₁` to the full program headers `fns₂`. -/
def LocalOp.lift {fns₁ fns₂ : List (FnHeader V)}
    (fnLift : ∀ {hdr}, Member fns₁ hdr → Member fns₂ hdr) :
    {ins res : List V.Ty} → LocalOp V fns₁ ins res → LocalOp V fns₂ ins res
  | _, _, .row key sig known => .row key sig known
  | _, _, .owned o => .owned o
  | _, _, .literal τ data reads => .literal τ data reads
  | _, _, .call callee => .call (fnLift callee)

end Erasure

/-! ## Specialization pass (`specialize`) -/

section Specializer
variable {V : Vocabulary}

/-- Static effect specializer targeting layer states `σ : List V.Ty`. -/
abbrev EffectSpecializer (V : Vocabulary) (fns : List (FnHeader V)) (σ : List V.Ty) : Type :=
  List Key → Key → {ins res : List V.Ty} →
    ResidualOp V ins res → {Δ : Ctx V.Ty} → HList (Var Δ) ins → ClosedTerm V fns σ Δ res

/-- Extract the `StackAgain` terms of a layer stack. -/
def stackAgain {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) → StackAgain V hs.fns (Stack.States layers)
  | [] => .nil
  | l :: rest => .cons l.again (stackAgain rest)

/-- Extract the `StackInit` terms of a layer stack. -/
def stackInit {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) →
    StackInit V hs.fns (held r ins) (Stack.States layers) (Stack.Takes layers)
  | [] => .nil
  | l :: rest => .cons l.start (stackInit rest)

/-- Extract the `StackFinish` terms of a layer stack. -/
def stackFinish {hs : Headers V} {r : Role} {ins : List (LTy V)} :
    (layers : List (Layer V hs r ins)) →
    StackFinish V hs.fns (Stack.States layers) (Stack.Gives layers)
  | [] => .nil
  | l :: rest => .cons l.finish (stackFinish rest)

/-- Cast a `ClosedTerm` across equal context and output types. -/
def ClosedTerm.castCT {fns : List (FnHeader V)} {σ : List V.Ty}
    {Γ₁ Γ₂ : Ctx V.Ty} {outs₁ outs₂ : List V.Ty}
    (hΓ : Γ₁ = Γ₂) (hOut : outs₁ = outs₂) (t : ClosedTerm V fns σ Γ₁ outs₁) :
    ClosedTerm V fns σ Γ₂ outs₂ :=
  hΓ ▸ hOut ▸ t

/-- Convert a role `Times` into a `ClosedTimes`. -/
def specializeTimes {hs : Headers V} {r : Role} {w : Holders} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) : Times (roleDialect V hs r) w Γ → ClosedTimes Δ
  | .fixed n => .fixed n
  | .value count ok => .value (cast (congrArg (Var Δ) ok.1) (varHeld hCtx count ok.2.1))

theorem specializeTimes_size {hs : Headers V} {r : Role} {w : Holders} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) (times : Times (roleDialect V hs r) w Γ) :
    (specializeTimes hCtx times).size = times.size := by
  cases times <;> rfl

/-! Specialize a single role term given an `EffectSpecializer`, optional retry configuration,
function-header lifting `fnLift`, and protocol-application specializer `specApply`. -/
section TermSpec
variable {fullFns : List (FnHeader V)} {σ : List V.Ty} {hs : Headers V}
  (specOp : EffectSpecializer V fullFns σ)
  (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
  (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
    {hdr : ProtocolHeader V} → Member hs.protocols hdr →
    List Key → (Role → Role) → (r : Role) →
    (inputs : Names (held r hdr.ins)) ×
      ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))

mutual
  def specializeTerm (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
      (through : List Key) (ρ : Role → Role) (r : Role) :
      {Γ : Ctx (LTy V)} → {Δ : Ctx V.Ty} → CtxRel r Γ Δ →
      {outs : List (LTy V)} → Term (roleDialect V hs r) Γ outs →
      ClosedTerm V fullFns σ Δ (held r outs)
    | _, _, hCtx, _, .ret exit => .ret (varsHeld hCtx exit)
    | _, Δ, hCtx, _, .op key o operands results rest =>
        match o with
        | .compute R lo _ types mine here =>
            let hRes : held r (List.map (fun τ => ⟨τ, R⟩) _) = _ :=
              held_map_holders r R mine _
            let resNames := cast (congrArg Names hRes) (heldNames r results)
            let args := cast (congrArg (HList (Var Δ)) types) (varsAllHeld hCtx here operands)
            let k := specializeTerm retryCfg through ρ r (hCtx.extend results) rest
            .localOp key (lo.lift fnLift) args resNames
              (k.castCT (ctx_extend_cast Δ hRes (heldNames r results)).symm rfl)
        | .absent items out =>
            let hEmpty : held r items = [] := held_all_out r items out
            let hExt : Δ.extend (heldNames r results) = Δ := by
              have hNil : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
                cases cast (congrArg Names hEmpty) (heldNames r results); rfl
              rw [← ctx_extend_cast Δ hEmpty (heldNames r results), hNil]; rfl
            (specializeTerm retryCfg through ρ r (hCtx.extend results) rest).castCT hExt rfl
        | .give (τ := τ) (H := H) kind getters here =>
            match operands, results with
            | .cons x .nil, .cons resName .nil =>
                let v := varHeld hCtx x here
                let hIn : r ∈ Holders.ofList (getters ++ H) :=
                  Holders.mem_ofList.mpr (List.mem_append_right _ here)
                let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ.insert resName τ := by
                  rw [heldNames_cons_pos hIn,
                    ctx_extend_cast Δ (held_cons_pos r _ [] hIn).symm]; rfl
                let k := (specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
                .letBind (specOp through key ((ResidualOp.give kind getters τ).mapPeers ρ) (.cons v .nil))
                  .nil (.alias v resName k)
        | .get τ H kind giver getters mine =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (getters ++ H) :=
                  Holders.mem_ofList.mpr (List.mem_append_left _ mine)
                let hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let k := specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key ((ResidualOp.get kind giver τ).mapPeers ρ) .nil)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .keep (τ := τ) (H := H) H' same =>
            match operands, results with
            | .cons x .nil, .cons resName .nil =>
                if h : r ∈ H then
                  let h' : r ∈ H' := same.mp h
                  let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ.insert resName τ := by
                    rw [heldNames_cons_pos h',
                      ctx_extend_cast Δ (held_cons_pos r _ [] h').symm]; rfl
                  let k := (specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
                  .alias (varHeld hCtx x h) resName k
                else
                  let h' : r ∉ H' := fun m => h (same.mpr m)
                  let hExt : Δ.extend (heldNames r (.cons resName .nil)) = Δ := by
                    rw [heldNames_cons_neg h',
                      ctx_extend_cast Δ (held_cons_neg r _ [] h').symm]; rfl
                  (specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl
        | .own kind hearers opTys τ _ here =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (r :: hearers) :=
                  Holders.mem_ofList.mpr List.mem_cons_self
                let hRes : held r [⟨τ, Holders.ofList (r :: hearers)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let args := varsAllHeld hCtx here operands
                let k := specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key
                    ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers ρ) args)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .hear kind owner hearers τ mine =>
            match results with
            | .cons resName .nil =>
                let hIn : r ∈ Holders.ofList (owner :: hearers) :=
                  Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)
                let hRes : held r [⟨τ, Holders.ofList (owner :: hearers)⟩] = [τ] := by
                  simp [held, hIn]
                let resNames := cast (congrArg Names hRes) (heldNames r (.cons resName .nil))
                let k := specializeTerm retryCfg through ρ r (hCtx.extend (.cons resName .nil)) rest
                .letBind (specOp through key ((ResidualOp.hear kind owner τ).mapPeers ρ) .nil)
                  resNames
                  (k.castCT (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl)
        | .apply callee roles distinct _ _ fits =>
            let rm := RoleMap.ofList roles distinct
            let r' := rm.back r
            let fitArgs := fitVars hCtx rm fits operands
            let hOut : held r (_ : List (LTy V)) = held r' _ := held_map_roleMap rm r _
            let resNames := cast (congrArg Names hOut) (heldNames r results)
            let ⟨calleeIns, calleeBody⟩ :=
              specApply retryCfg callee (through ++ [key]) (fun q => ρ (rm.to q)) r'
            let k := specializeTerm retryCfg through ρ r (hCtx.extend results) rest
            .frame (some key) fitArgs calleeIns calleeBody resNames
              (k.castCT (ctx_extend_cast Δ hOut (heldNames r results)).symm rfl)
    | _, Δ, hCtx, _, .guard key _ c ok why rest =>
        let cv : Var Δ .bool := cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)
        .guard key cv why (specializeTerm retryCfg through ρ r hCtx rest)
    | _, Δ, hCtx, _, .choose key _ c ok _ onTrue onFalse results rest =>
        let cv : Var Δ .bool := cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)
        .choose key cv
          (specializeTerm retryCfg through ρ r hCtx onTrue)
          (specializeTerm retryCfg through ρ r hCtx onFalse)
          (heldNames r results)
          (specializeTerm retryCfg through ρ r (hCtx.extend results) rest)
    | _, Δ, hCtx, _, .cases (t := t) (payloads := payloads) key ps x ok _ arms results rest =>
        let hv : ∃ k alts, t.ty = .variant k alts ∧ payloads = alts.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨k, alts, he, hp, _⟩ := ok; exact ⟨k, alts, he, hp⟩
        let hEq : t.ty = .variant t.ty.variantKey t.ty.alternatives := Ty.eq_variant hv
        let hPay : payloads = t.ty.alternatives.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨_, alts, he, hp⟩ := hv; rw [Ty.alternatives_of he, hp]
        let hrT : r ∈ t.holders := by obtain ⟨_, _, _, _, h1, _⟩ := ok; exact h1
        let hrPs : r ∈ ps := by obtain ⟨_, _, _, _, _, h2⟩ := ok; exact h2
        let xv : Var Δ (.variant t.ty.variantKey t.ty.alternatives) :=
          cast (congrArg (Var Δ) hEq) (varHeld hCtx x hrT)
        let armsC := specializeArms retryCfg through ρ r ps hrPs hCtx arms hPay
        .cases key xv armsC (heldNames r results)
          (specializeTerm retryCfg through ρ r (hCtx.extend results) rest)
    | Γ, Δ, hCtx, _, .loop (carried := carried) (each := each) key ps times _ initial inputs body results rest =>
        match inputs with
        | .cons idxNm carriedInNames =>
            let cTimes := specializeTimes hCtx times
            let hSize : cTimes.size = times.size := specializeTimes_size hCtx times
            let hBodyOut : held r (carried ++ each) = held r carried ++ held r each :=
              held_append r carried each
            let hResTy : held r (carried ++ each.map (LTy.collected times.size)) =
                held r carried ++ (held r each).map (fun τ => .seq τ cTimes.size) := by
              rw [held_append, held_map_collected, hSize]
            let cNames := heldNames r carriedInNames
            let resNames := cast (congrArg Names hResTy) (heldNames r results)
            let k := specializeTerm retryCfg through ρ r (hCtx.extend results) rest
            if hIn : r ∈ ps then
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
                  (loopBodyCtx Δ (some idxNm) cNames) := by
                simpa [Ctx.extend, loopBodyCtx, LTy.index] using
                  (hCtx.insert_held idxNm (a := LTy.index ps)).extend carriedInNames
              let bodyC := (specializeTerm retryCfg through ρ r hCtxB body).castCT rfl hBodyOut
              .loop key cTimes (varsHeld hCtx initial) (some idxNm) cNames bodyC resNames
                (k.castCT (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)
            else
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
                  (loopBodyCtx Δ none cNames) := by
                simpa [Ctx.extend, loopBodyCtx, LTy.index] using
                  (hCtx.insert_unheld idxNm (a := LTy.index ps) hIn).extend carriedInNames
              let bodyC := (specializeTerm retryCfg through ρ r hCtxB body).castCT rfl hBodyOut
              .loop key cTimes (varsHeld hCtx initial) none cNames bodyC resNames
                (k.castCT (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)
    | _, _, hCtx, _, .block key number body results rest =>
        .block key number
          (specializeTerm retryCfg through ρ r hCtx body)
          (heldNames r results)
          (specializeTerm retryCfg through ρ r (hCtx.extend results) rest)
    | Γ, Δ, hCtx, _, .attempt key w _ inputs body results rest =>
        match inputs with
        | .cons idxNm .nil =>
            let k := specializeTerm retryCfg through ρ r (hCtx.extend results) rest
            if hw : r ∈ w then
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm .nil)) (Δ.extend (.cons idxNm .nil)) := by
                simpa [Ctx.extend, LTy.index] using hCtx.insert_held idxNm (a := LTy.index w)
              match retryCfg with
              | some (bound, retrySite, again) =>
                  if ⟨through, key⟩ = retrySite then
                    let bodyC := specializeTerm none through ρ r hCtxB body
                    .retry key bound again (.cons idxNm .nil) bodyC (heldNames r results) k
                  else
                    let bodyC := specializeTerm retryCfg through ρ r hCtxB body
                    .letBind
                      (.letBind (specOp through key .begin .nil) (.cons idxNm .nil)
                        (.seq bodyC (specOp through key .settle .nil)))
                      (heldNames r results) k
              | none =>
                  let bodyC := specializeTerm none through ρ r hCtxB body
                  .letBind
                    (.letBind (specOp through key .begin .nil) (.cons idxNm .nil)
                      (.seq bodyC (specOp through key .settle .nil)))
                    (heldNames r results) k
            else
              let hCtxB : CtxRel r (Γ.extend (.cons idxNm .nil)) Δ := by
                simpa [Ctx.extend, LTy.index] using hCtx.insert_unheld idxNm (a := LTy.index w) hw
              let bodyC := specializeTerm retryCfg through ρ r hCtxB body
              .letBind bodyC (heldNames r results) k

  def specializeArms (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
      (through : List Key) (ρ : Role → Role) (r : Role) (ps : Holders) (hrPs : r ∈ ps) :
      {Γ : Ctx (LTy V)} → {Δ : Ctx V.Ty} → CtxRel r Γ Δ →
      {mid payloads : List (LTy V)} →
      Arms (roleDialect V hs r) Γ mid payloads →
      {alts : List V.Ty} → payloads = alts.map (fun τ => ⟨τ, ps⟩) →
      ClosedArms V fullFns σ Δ (held r mid) alts
    | _, _, _, _, _, .nil, [], _ => .nil
    | _, _, _, _, _, .nil, _ :: _, hPay => nomatch hPay
    | _, _, _, _, _, .cons _ _ _, [], hPay => nomatch hPay
    | Γ, Δ, hCtx, _, a :: _, .cons (.cons nm .nil) arm rest, τ :: _, hPay =>
        let hHead : a = ⟨τ, ps⟩ := (List.cons.inj hPay).1
        let hTail := (List.cons.inj hPay).2
        let hCtxA : CtxRel r (Γ.extend (.cons nm .nil)) (Δ.extend (.cons nm .nil)) := by
          rw [show Γ.extend (.cons nm .nil) = Γ.insert nm ⟨τ, ps⟩ by rw [Ctx.extend, Ctx.extend, hHead]]
          exact hCtx.insert_held nm (a := ⟨τ, ps⟩)
        .cons (.cons nm .nil)
          (specializeTerm retryCfg through ρ r hCtxA arm)
          (specializeArms retryCfg through ρ r ps hrPs hCtx rest hTail)
end

end TermSpec

/-- Middle structural recursion on `defs : Defs V hs`: specializes any referenced protocol in `defs`
by inlining all transitive protocol applications against `specOp`. -/
def specializeProtocolInDefs {fullFns : List (FnHeader V)} {σ : List V.Ty}
    (specOp : EffectSpecializer V fullFns σ) :
    {hs : Headers V} → Defs V hs →
    (∀ {hdr}, Member hs.fns hdr → Member fullFns hdr) →
    Option (Nat × Site × StackAgain V fullFns σ) →
    {hdr : ProtocolHeader V} → Member hs.protocols hdr →
    (through : List Key) → (ρ : Role → Role) → (r : Role) →
    (inputs : Names (held r hdr.ins)) ×
      ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs)
  | _, .nil, _, _, _, m, _, _, _ => nomatch m
  | _, .fn _ _ _ _ rest _, fnLift, retryCfg, _, m, through, ρ, r =>
      specializeProtocolInDefs specOp rest (fun f => fnLift (.tail f)) retryCfg m through ρ r
  | _, .protocol (hs := hsRest) _ inputs body _ rest, fnLift, retryCfg, _, .head, through, ρ, r =>
      ⟨heldNames r inputs,
        @specializeTerm V fullFns σ hsRest specOp fnLift
          (fun rc {_} m' th' ρ' r' => specializeProtocolInDefs specOp rest fnLift rc m' th' ρ' r')
          retryCfg through ρ r _ _ ((CtxRel.empty r).extend inputs) _ (project r body)⟩
  | _, .protocol _ _ _ _ rest, fnLift, retryCfg, _, .tail m, through, ρ, r =>
      specializeProtocolInDefs specOp rest fnLift retryCfg m through ρ r

/-- Walk a layer's clauses to find the first matching clause for `(through, key, op)` and inline
its body against the strictly shorter layer stack below. -/
def specializeClauses {hs : Headers V} (defs : Defs V hs) {r_top : Role} {state : V.Ty}
    {σ_rest : List V.Ty}
    (specBelow : EffectSpecializer V hs.fns σ_rest)
    (through : List Key) (key : Key) {ins res : List V.Ty} (op : ResidualOp V ins res)
    {Δ : Ctx V.Ty} (args : HList (Var Δ) ins) :
    List (Clause V hs r_top state) → ClosedTerm V hs.fns (state :: σ_rest) Δ res
  | [] => .underLayer (specBelow through key op args)
  | c :: cs =>
      if h : c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
          c.site.takes = ins ∧ c.site.gives = res then
        let hIn : Ctx.positional (c.site.takes ++ [state]) = Ctx.positional (ins ++ [state]) := by
          rw [h.2.2.1]
        let hOut : held r_top (alone r_top (c.site.gives ++ [state])) = res ++ [state] := by
          rw [held_alone, h.2.2.2]
        let bodyC : ClosedTerm V hs.fns σ_rest (Ctx.positional (ins ++ [state])) (res ++ [state]) :=
          (specializeTerm specBelow id
            (fun rc {_} m th ρ' r' => specializeProtocolInDefs specBelow defs id rc m th ρ' r')
            none through id r_top
            (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
            c.code).castCT hIn hOut
        .withLayer args (Names.counting 0 (ins ++ [state])) bodyC
      else
        specializeClauses defs specBelow through key op args cs

/-- Level 2: Outer structural recursion on the layer stack `layers`. -/
def specializeStack {hs : Headers V} (defs : Defs V hs) {r_top : Role} {ins_top : List (LTy V)} :
    (layers : List (Layer V hs r_top ins_top)) → EffectSpecializer V hs.fns (Stack.States layers)
  | [] => fun _ key {_ _} op {_} args => .effect key op args
  | l :: rest =>
      let specBelow := specializeStack defs rest
      fun through key {_ _} op {_} args => specializeClauses defs specBelow through key op args l.clauses

/-- Specialize a deployed scheme `d` for role `r` into a self-contained, handler-free `ClosedRole`. -/
def specialize (d : Deployed V) (r : Role) :
    ClosedRole V d.admitted.program.headers.fns r d.entry.ins d.entry.outs
      (Stack.Takes (d.stack r)) (Stack.Gives (d.stack r)) :=
  let specOp := specializeStack d.admitted.program.defs (d.stack r)
  let retryCfg := d.retry.map fun (bound, site) => (bound, site, stackAgain (d.stack r))
  let res :=
    specializeProtocolInDefs specOp d.admitted.program.defs id retryCfg d.callee [] id r
  { states := Stack.States (d.stack r)
    inputs := res.1
    start := stackInit (d.stack r)
    body := res.2
    finish := stackFinish (d.stack r) }

end Specializer

/-! ## Soundness proofs (`specialize_sound`) -/

section Soundness
variable {V : Vocabulary} (M : Model V)

/-! ### Value and environment erasure lemmas -/

private theorem hide_reveal {r : Role} {a : LTy V} (h : r ∈ a.holders) (v : RV M r a) :
    hide M r a (reveal M h v) = v := by
  simp [hide, reveal, h]

private theorem nothing_eq {r : Role} {a : LTy V} (h : r ∉ a.holders) (v : RV M r a) :
    nothing M h = v := by
  unfold nothing
  have hRV : RV M r a = Unit := by simp [RV, h]
  have h1 : cast hRV.symm (cast hRV v) = v := by rw [cast_cast, cast_eq]
  exact (congrArg (cast hRV.symm) (rfl : () = cast hRV v)).trans h1

private theorem hlist_cons_cast {α : Type} {F : α → Type} {a : α} {as bs : List α}
    (e : as = bs) (x : F a) (xs : HList F as) :
    HList.cons x (cast (congrArg (HList F) e) xs) =
      cast (congrArg (HList F) (congrArg (a :: ·) e)) (HList.cons x xs) := by
  subst e; rfl

private theorem hlist_append_cast {α : Type} {F : α → Type} {as bs cs : List α}
    (e : as = bs) (xs : HList F as) (ys : HList F cs) :
    (cast (congrArg (HList F) e) xs).append ys =
      cast (congrArg (HList F) (congrArg (· ++ cs) e)) (xs.append ys) := by
  subst e; rfl

private theorem heldValues_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (HList.cons v vs) =
      cast (congrArg (HList M.Val) (held_cons_pos r a rest h).symm)
        (HList.cons (reveal M h v) (heldValues M r vs)) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList M.Val) (held_cons_pos r a rest h').symm) (HList.cons (reveal M h' v) (heldValues M r vs))
    else cast (congrArg (HList M.Val) (held_cons_neg r a rest h').symm) (heldValues M r vs)) = _
  exact dite_eq_left h

private theorem heldValues_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (v : RV M r a) (vs : HList (RV M r) rest) :
    heldValues M r (HList.cons v vs) =
      cast (congrArg (HList M.Val) (held_cons_neg r a rest h).symm)
        (heldValues M r vs) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList M.Val) (held_cons_pos r a rest h').symm) (HList.cons (reveal M h' v) (heldValues M r vs))
    else cast (congrArg (HList M.Val) (held_cons_neg r a rest h').symm) (heldValues M r vs)) = _
  exact dite_eq_right h

private theorem unheldValues_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (vs : HList M.Val (held r (a :: rest))) :
    unheldValues M r vs =
      match cast (congrArg (HList M.Val) (held_cons_pos r a rest h)) vs with
      | HList.cons v more => HList.cons (hide M r a v) (unheldValues M r more) := by
  change (if h' : r ∈ a.holders then
    match cast (congrArg (HList M.Val) (held_cons_pos r a rest h')) vs with
    | HList.cons v more => HList.cons (hide M r a v) (unheldValues M r more)
    else HList.cons (nothing M h') (unheldValues M r (cast (congrArg (HList M.Val) (held_cons_neg r a rest h')) vs))) = _
  exact dite_eq_left h

private theorem unheldValues_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (vs : HList M.Val (held r (a :: rest))) :
    unheldValues M r vs =
      HList.cons (nothing M h) (unheldValues M r
        (cast (congrArg (HList M.Val) (held_cons_neg r a rest h)) vs)) := by
  change (if h' : r ∈ a.holders then
    match cast (congrArg (HList M.Val) (held_cons_pos r a rest h')) vs with
    | HList.cons v more => HList.cons (hide M r a v) (unheldValues M r more)
    else HList.cons (nothing M h') (unheldValues M r (cast (congrArg (HList M.Val) (held_cons_neg r a rest h')) vs))) = _
  exact dite_eq_right h

private theorem varsHeld_cons_pos {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) {a : LTy V} {rest : List (LTy V)} (h : r ∈ a.holders)
    (x : Var Γ a) (xs : HList (Var Γ) rest) :
    varsHeld hCtx (HList.cons x xs) =
      cast (congrArg (HList (Var Δ)) (held_cons_pos r a rest h).symm)
        (HList.cons (varHeld hCtx x h) (varsHeld hCtx xs)) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList (Var Δ)) (held_cons_pos r a rest h').symm) (HList.cons (varHeld hCtx x h') (varsHeld hCtx xs))
    else cast (congrArg (HList (Var Δ)) (held_cons_neg r a rest h').symm) (varsHeld hCtx xs)) = _
  exact dite_eq_left h

private theorem varsHeld_cons_neg {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) {a : LTy V} {rest : List (LTy V)} (h : r ∉ a.holders)
    (x : Var Γ a) (xs : HList (Var Γ) rest) :
    varsHeld hCtx (HList.cons x xs) =
      cast (congrArg (HList (Var Δ)) (held_cons_neg r a rest h).symm)
        (varsHeld hCtx xs) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList (Var Δ)) (held_cons_pos r a rest h').symm) (HList.cons (varHeld hCtx x h') (varsHeld hCtx xs))
    else cast (congrArg (HList (Var Δ)) (held_cons_neg r a rest h').symm) (varsHeld hCtx xs)) = _
  exact dite_eq_right h

private theorem fitVars_cons_pos {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) (ρ : RoleMap) {a b : LTy V} {as bs : List (LTy V)}
    (fits : Fits (a :: as) ((b :: bs).map (LTy.map ρ.to)))
    (h : ρ.back r ∈ b.holders) (x : Var Γ a) (xs : HList (Var Γ) as) :
    fitVars hCtx ρ fits (HList.cons x xs) =
      cast (congrArg (HList (Var Δ)) (held_cons_pos (ρ.back r) b bs h).symm)
        (HList.cons (cast (congrArg (Var Δ) fits.1.1) (varHeld hCtx x (fits.1.2 r (ρ.mem_map.mpr h))))
          (fitVars hCtx ρ fits.2 xs)) := by
  change (if h' : ρ.back r ∈ b.holders then
    cast (congrArg (HList (Var Δ)) (held_cons_pos (ρ.back r) b bs h').symm)
      (HList.cons (cast (congrArg (Var Δ) fits.1.1) (varHeld hCtx x (fits.1.2 r (ρ.mem_map.mpr h'))))
        (fitVars hCtx ρ fits.2 xs))
    else cast (congrArg (HList (Var Δ)) (held_cons_neg (ρ.back r) b bs h').symm)
      (fitVars hCtx ρ fits.2 xs)) = _
  exact dite_eq_left h

private theorem fitVars_cons_neg {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    (hCtx : CtxRel r Γ Δ) (ρ : RoleMap) {a b : LTy V} {as bs : List (LTy V)}
    (fits : Fits (a :: as) ((b :: bs).map (LTy.map ρ.to)))
    (h : ρ.back r ∉ b.holders) (x : Var Γ a) (xs : HList (Var Γ) as) :
    fitVars hCtx ρ fits (HList.cons x xs) =
      cast (congrArg (HList (Var Δ)) (held_cons_neg (ρ.back r) b bs h).symm)
        (fitVars hCtx ρ fits.2 xs) := by
  change (if h' : ρ.back r ∈ b.holders then
    cast (congrArg (HList (Var Δ)) (held_cons_pos (ρ.back r) b bs h').symm)
      (HList.cons (cast (congrArg (Var Δ) fits.1.1) (varHeld hCtx x (fits.1.2 r (ρ.mem_map.mpr h'))))
        (fitVars hCtx ρ fits.2 xs))
    else cast (congrArg (HList (Var Δ)) (held_cons_neg (ρ.back r) b bs h').symm)
      (fitVars hCtx ρ fits.2 xs)) = _
  exact dite_eq_right h

theorem unheldValues_heldValues (r : Role) :
    ∀ {items : List (LTy V)} (vs : HList (RV M r) items),
      unheldValues M r (heldValues M r vs) = vs
  | [], .nil => rfl
  | a :: rest, .cons v vs => by
      by_cases h : r ∈ a.holders
      · rw [unheldValues_cons_pos M h, heldValues_cons_pos M h, cast_cast, cast_eq]
        change HList.cons (hide M r a (reveal M h v)) (unheldValues M r (heldValues M r vs)) = _
        rw [hide_reveal M h v, unheldValues_heldValues r vs]
      · rw [unheldValues_cons_neg M h, heldValues_cons_neg M h, cast_cast, cast_eq,
          nothing_eq M h v, unheldValues_heldValues r vs]

theorem heldValues_unheldValues (r : Role) :
    ∀ {items : List (LTy V)} (vs : HList M.Val (held r items)),
      heldValues M r (unheldValues M r vs) = vs
  | [], .nil => rfl
  | a :: rest, vs => by
      by_cases h : r ∈ a.holders
      · rw [unheldValues_cons_pos M h]
        have hEq : held r (a :: rest) = a.ty :: held r rest := held_cons_pos r a rest h
        generalize hCast : cast (congrArg (HList M.Val) hEq) vs = vs'
        cases vs' with
        | cons v more =>
            change heldValues M r (HList.cons (hide M r a v) (unheldValues M r more)) = vs
            rw [heldValues_cons_pos M h, reveal_hide, heldValues_unheldValues r more,
              ← hCast, cast_cast, cast_eq]
      · rw [unheldValues_cons_neg M h, heldValues_cons_neg M h, heldValues_unheldValues r,
          cast_cast, cast_eq]

private theorem heldValues_append (r : Role) :
    ∀ {as bs : List (LTy V)} (xs : HList (RV M r) as) (ys : HList (RV M r) bs),
      heldValues M r (xs.append ys) =
        cast (congrArg (HList M.Val) (held_append r as bs).symm)
          ((heldValues M r xs).append (heldValues M r ys))
  | [], _, .nil, ys => rfl
  | a :: as, bs, .cons x xs, ys => by
      by_cases h : r ∈ a.holders
      · rw [HList.append, heldValues_cons_pos M h, heldValues_cons_pos M h,
          heldValues_append r xs ys,
          hlist_append_cast (held_cons_pos r a as h).symm, HList.append,
          hlist_cons_cast (held_append r as bs).symm, cast_cast, cast_cast]
      · rw [HList.append, heldValues_cons_neg M h, heldValues_cons_neg M h,
          heldValues_append r xs ys,
          hlist_append_cast (held_cons_neg r a as h).symm, cast_cast, cast_cast]

private theorem heldValues_aloneIn (r : Role) :
    ∀ {types : List V.Ty} (vs : HList M.Val types),
      heldValues M r (aloneIn M r vs) =
        cast (congrArg (HList M.Val) (held_alone r types).symm) vs
  | [], .nil => rfl
  | τ :: rest, .cons v vs => by
      change heldValues M r (.cons (hide M r ⟨τ, [r]⟩ v) (aloneIn M r vs)) = _
      rw [heldValues_cons_pos M (List.mem_singleton_self r), reveal_hide,
        heldValues_aloneIn r vs, hlist_cons_cast (held_alone r rest).symm, cast_cast]
      rfl

private theorem aloneOut_eq_heldValues (r : Role) :
    ∀ {types : List V.Ty} (vs : HList (RV M r) (alone r types)),
      aloneOut M r vs = cast (congrArg (HList M.Val) (held_alone r types)) (heldValues M r vs)
  | [], .nil => rfl
  | τ :: rest, .cons v vs => by
      have hStep := heldValues_cons_pos M (a := ⟨τ, [r]⟩) (rest := alone r rest)
        (List.mem_singleton_self r) v vs
      change HList.cons (reveal M (List.mem_singleton_self r) v) (aloneOut M r vs) =
        cast (congrArg (HList M.Val)
            (show held r (⟨τ, [r]⟩ :: alone r rest) = τ :: rest from held_alone r (τ :: rest)))
          (heldValues M r (HList.cons (V := RV M r) (a := ⟨τ, [r]⟩) (rest := alone r rest) v vs))
      rw [hStep, cast_cast, aloneOut_eq_heldValues r vs, hlist_cons_cast (held_alone r rest)]

private theorem heldValues_hideAll_located (r : Role) (R : Holders) (h : r ∈ R) :
    ∀ {outs : List V.Ty} (vs : HList M.Val outs),
      heldValues M r (hideAll M r (HList.located M R vs)) =
        cast (congrArg (HList M.Val) (held_map_holders r R h outs).symm) vs
  | [], .nil => rfl
  | τ :: rest, .cons v vs => by
      change heldValues M r (.cons (hide M r ⟨τ, R⟩ v) (hideAll M r (HList.located M R vs))) = _
      rw [heldValues_cons_pos M h, reveal_hide, heldValues_hideAll_located r R h vs,
        hlist_cons_cast (held_map_holders r R h rest).symm, cast_cast]

private theorem heldValues_nothings (r : Role) :
    ∀ {items : List (LTy V)} (out : ∀ a, a ∈ items → r ∉ a.holders),
      heldValues M r (nothings M out) =
        cast (congrArg (HList M.Val) (held_all_out r items out).symm) .nil
  | [], _ => rfl
  | a :: rest, out => by
      have ha : r ∉ a.holders := out a List.mem_cons_self
      change heldValues M r (.cons (nothing M ha) (nothings M fun b hb => out b (List.mem_cons_of_mem _ hb))) = _
      rw [heldValues_cons_neg M ha, heldValues_nothings r (fun b hb => out b (List.mem_cons_of_mem _ hb)),
        cast_cast]

private theorem heldValues_leaveAll (ρ : RoleMap) (r : Role) :
    ∀ {items : List (LTy V)} (vs : HList (RV M (ρ.back r)) items),
      heldValues M r (leaveAll M ρ r vs) =
        cast (congrArg (HList M.Val) (held_map_roleMap ρ r items).symm) (heldValues M (ρ.back r) vs)
  | [], .nil => rfl
  | a :: rest, .cons v vs => by
      by_cases h : ρ.back r ∈ a.holders
      · have h' : r ∈ (a.map ρ.to).holders := ρ.mem_map.mpr h
        rw [leaveAll, leave, dite_eq_left h, heldValues_cons_pos M h', heldValues_cons_pos M h,
          reveal_hide, heldValues_leaveAll ρ r vs,
          hlist_cons_cast (held_map_roleMap ρ r rest).symm, cast_cast, cast_cast]
      · have h' : r ∉ (a.map ρ.to).holders := fun m => h (ρ.mem_map.mp m)
        rw [leaveAll, leave, dite_eq_right h, heldValues_cons_neg M h', heldValues_cons_neg M h,
          heldValues_leaveAll ρ r vs, cast_cast, cast_cast]

/-- Environment erasure invariant corresponding to `CtxRel`. -/
def EnvRel (r : Role) {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) : Prop :=
  ∀ name a (hΓ : Γ.find? name = some a) (hr : r ∈ a.holders),
    cenv name a.ty (hCtx name a hΓ hr) = reveal M hr (env name a hΓ)

private theorem EnvRel.empty (r : Role) :
    EnvRel M r (CtxRel.empty r) Env.empty Env.empty :=
  fun name _ hΓ _ => nomatch (Ctx.find?_empty name).symm.trans hΓ

private theorem EnvRel.insert_held {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (name : Name) {a : LTy V} (hr : r ∈ a.holders)
    (v : RV M r a) :
    EnvRel M r (hCtx.insert_held name) (env.insert name v) (cenv.insert name (reveal M hr v)) := by
  intro name' b hΓ hrb
  by_cases same : name' = name
  · have hEq : a = b := by
      rw [Ctx.find?_insert, ite_eq_left same] at hΓ
      exact Option.some.inj hΓ
    subst hEq
    have h1 := Env.insert_at_bound cenv name (reveal M hr v) same (hCtx.insert_held name name' a hΓ hrb)
    have h2 := Env.insert_at_bound env name v same hΓ
    rw [eq_of_heq h1, eq_of_heq h2]
  · rw [Env.insert_at_other cenv name (reveal M hr v) same, Env.insert_at_other env name v same]
    exact hEnv name' b _ hrb

private theorem EnvRel.insert_unheld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (name : Name) {a : LTy V} (hOut : r ∉ a.holders)
    (v : RV M r a) :
    EnvRel M r (hCtx.insert_unheld name hOut) (env.insert name v) cenv := by
  intro name' b hΓ hrb
  by_cases same : name' = name
  · have hEq : a = b := by
      rw [Ctx.find?_insert, ite_eq_left same] at hΓ
      exact Option.some.inj hΓ
    subst hEq
    exact absurd hrb hOut
  · rw [Env.insert_at_other env name v same]
    exact hEnv name' b _ hrb

private theorem env_extend_cast {T : Type} {Val : T → Type} {Δ : Ctx T} (env : Env Val Δ)
    {as bs : List T} (h : as = bs) (ns : Names as) (vs : HList Val as) :
    HEq (env.extend (cast (congrArg Names h) ns) (cast (congrArg (HList Val) h) vs))
      (env.extend ns vs) := by
  subst h; exact HEq.rfl

private theorem EnvRel.extend {r : Role} :
    ∀ {items : List (LTy V)} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
      {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ},
      EnvRel M r hCtx env cenv → ∀ (bound : Names items) (vs : HList (RV M r) items),
      EnvRel M r (hCtx.extend bound) (env.extend bound vs)
        (cenv.extend (heldNames r bound) (heldValues M r vs))
  | [], _, _, _, _, _, hEnv, .nil, .nil => hEnv
  | a :: rest, Γ, Δ, hCtx, env, cenv, hEnv, .cons name more, .cons v moreV => by
      intro name' b hΓ hrb
      change cenv.extend (heldNames r (HList.cons (a := a) name more))
          (heldValues M r (HList.cons v moreV)) name' b.ty _ =
        reveal M hrb ((env.insert name v).extend more moreV name' b hΓ)
      by_cases h : r ∈ a.holders
      · have hEq : held r (a :: rest) = a.ty :: held r rest := held_cons_pos r a rest h
        have hCast : HEq
            (cenv.extend (heldNames r (HList.cons (a := a) name more)) (heldValues M r (HList.cons v moreV)))
            ((cenv.insert name (reveal M h v)).extend (heldNames r more) (heldValues M r moreV)) := by
          rw [heldNames_cons_pos h, heldValues_cons_pos M h]
          exact env_extend_cast cenv hEq.symm (HList.cons name (heldNames r more))
            (HList.cons (reveal M h v) (heldValues M r moreV))
        have hStep := EnvRel.extend (hEnv.insert_held M name h v) more moreV name' b hΓ hrb
        rw [← hStep]
        have hCtxEq : Δ.extend (heldNames r (HList.cons (a := a) name more)) =
            (Δ.insert name a.ty).extend (heldNames r more) := by
          rw [heldNames_cons_pos h, ctx_extend_cast Δ hEq.symm]; rfl
        have hApply : ∀ {Δ₁ Δ₂ : Ctx V.Ty} (e : Δ₁ = Δ₂) (e1 : Env M.Val Δ₁) (e2 : Env M.Val Δ₂),
            HEq e1 e2 → ∀ (p1 : Δ₁.find? name' = some b.ty) (p2 : Δ₂.find? name' = some b.ty),
              e1 name' b.ty p1 = e2 name' b.ty p2 := by
          intro _ _ e e1 e2 he p1 p2; subst e; cases eq_of_heq he; rfl
        exact hApply hCtxEq _ _ hCast _ _
      · have hEq : held r (a :: rest) = held r rest := held_cons_neg r a rest h
        have hCast : HEq
            (cenv.extend (heldNames r (HList.cons (a := a) name more)) (heldValues M r (HList.cons v moreV)))
            (cenv.extend (heldNames r more) (heldValues M r moreV)) := by
          rw [heldNames_cons_neg h, heldValues_cons_neg M h]
          exact env_extend_cast cenv hEq.symm (heldNames r more) (heldValues M r moreV)
        have hStep := EnvRel.extend (hEnv.insert_unheld M name h v) more moreV name' b hΓ hrb
        rw [← hStep]
        have hCtxEq : Δ.extend (heldNames r (HList.cons (a := a) name more)) = Δ.extend (heldNames r more) := by
          rw [heldNames_cons_neg h, ctx_extend_cast Δ hEq.symm]
        have hApply : ∀ {Δ₁ Δ₂ : Ctx V.Ty} (e : Δ₁ = Δ₂) (e1 : Env M.Val Δ₁) (e2 : Env M.Val Δ₂),
            HEq e1 e2 → ∀ (p1 : Δ₁.find? name' = some b.ty) (p2 : Δ₂.find? name' = some b.ty),
              e1 name' b.ty p1 = e2 name' b.ty p2 := by
          intro _ _ e e1 e2 he p1 p2; subst e; cases eq_of_heq he; rfl
        exact hApply hCtxEq _ _ hCast _ _

private theorem EnvRel.positional_alone (r : Role) :
    ∀ {types : List V.Ty} (vs : HList M.Val types),
      EnvRel M r (CtxRel.positional_alone r types) (Env.positional (aloneIn M r vs)) (Env.positional vs) := by
  intro types vs
  have hExt : ∀ (start : Nat) {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
      (env : Env (RV M r) Γ) (cenv : Env M.Val Δ),
      EnvRel M r hCtx env cenv →
      ∀ {ts : List V.Ty} (ws : HList M.Val ts)
        (hCtx' : CtxRel r (Γ.extend (Names.counting start (alone r ts))) (Δ.extend (Names.counting start ts))),
        EnvRel M r hCtx'
          (env.extend (Names.counting start (alone r ts)) (aloneIn M r ws))
          (cenv.extend (Names.counting start ts) ws) := by
    intro start Γ Δ hCtx env cenv hEnv ts ws
    induction ws generalizing start Γ Δ with
    | nil =>
        intro hCtx'
        exact hEnv
    | cons v rest ih =>
        intro hCtx'
        have hIns : EnvRel M r (hCtx.insert_held start)
            (env.insert start (hide M r ⟨_, [r]⟩ v))
            (cenv.insert start v) := by
          have h := hEnv.insert_held M start (a := ⟨_, [r]⟩) List.mem_cons_self (hide M r ⟨_, [r]⟩ v)
          rwa [reveal_hide] at h
        exact ih (start + 1) (hCtx.insert_held start) _ _ hIns hCtx'
  exact hExt 0 (CtxRel.empty r) Env.empty Env.empty (EnvRel.empty M r) vs (CtxRel.positional_alone r types)

private theorem env_get_varHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) {a : LTy V} (x : Var Γ a) (h : r ∈ a.holders) :
    cenv.get (varHeld hCtx x h) = reveal M h (env.get x) :=
  hEnv x.name a x.typed h

private theorem env_all_varsHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) :
    ∀ {items : List (LTy V)} (xs : HList (Var Γ) items),
      cenv.all (varsHeld hCtx xs) = heldValues M r (env.all xs)
  | [], .nil => rfl
  | a :: rest, .cons x xs => by
      have hCastAll : ∀ {as bs : List V.Ty} (e : as = bs) (ys : HList (Var Δ) as),
          cenv.all (cast (congrArg (HList (Var Δ)) e) ys) =
            cast (congrArg (HList M.Val) e) (cenv.all ys) := by
        intro _ _ e _; subst e; rfl
      by_cases h : r ∈ a.holders
      · rw [varsHeld_cons_pos hCtx h, Env.all, heldValues_cons_pos M h,
          hCastAll (held_cons_pos r a rest h).symm,
          Env.all, env_get_varHeld M hEnv x h, env_all_varsHeld hEnv xs]
      · rw [varsHeld_cons_neg hCtx h, Env.all, heldValues_cons_neg M h,
          hCastAll (held_cons_neg r a rest h).symm,
          env_all_varsHeld hEnv xs]

private theorem env_all_varsAllHeld {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) :
    ∀ {items : List (LTy V)} (here : ∀ a, a ∈ items → r ∈ a.holders) (xs : HList (Var Γ) items),
      cenv.all (varsAllHeld hCtx here xs) = HList.ofLocated M (revealAll M here (env.all xs))
  | [], _, .nil => rfl
  | a :: rest, here, .cons x xs => by
      simp only [varsAllHeld, Env.all, revealAll, HList.ofLocated,
        env_get_varHeld M hEnv x (here a List.mem_cons_self),
        env_all_varsAllHeld hEnv (fun b hb => here b (List.mem_cons_of_mem _ hb)) xs]

private theorem env_all_fitVars {r : Role} {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty}
    {hCtx : CtxRel r Γ Δ} {env : Env (RV M r) Γ} {cenv : Env M.Val Δ}
    (hEnv : EnvRel M r hCtx env cenv) (ρ : RoleMap) :
    ∀ {as bs : List (LTy V)} (fits : Fits as (bs.map (LTy.map ρ.to))) (xs : HList (Var Γ) as),
      cenv.all (fitVars hCtx ρ fits xs) =
        heldValues M (ρ.back r) (enterAll M ρ r (fitAllRV M fits (env.all xs)))
  | [], [], _, .nil => rfl
  | a :: as, b :: bs, fits, .cons x xs => by
      have hCastAll : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂) (ys : HList (Var Δ) ts₁),
          cenv.all (cast (congrArg (HList (Var Δ)) e) ys) =
            cast (congrArg (HList M.Val) e) (cenv.all ys) := by
        intro _ _ e _; subst e; rfl
      change cenv.all (fitVars hCtx ρ fits (.cons x xs)) =
        heldValues M (ρ.back r)
          (.cons (enter M ρ r b (coverRV M fits.1 (env.get x)))
            (enterAll M ρ r (fitAllRV M fits.2 (env.all xs))))
      by_cases h : ρ.back r ∈ b.holders
      · have h' : r ∈ (b.map ρ.to).holders := ρ.mem_map.mpr h
        rw [fitVars_cons_pos hCtx ρ fits h, heldValues_cons_pos M h, enter, coverRV,
          dite_eq_left h, dite_eq_left h', reveal_hide, reveal_hide,
          hCastAll (held_cons_pos (ρ.back r) b bs h).symm,
          Env.all, env_all_fitVars hEnv ρ fits.2 xs]
        have hGetCast : cenv.get (cast (congrArg (Var Δ) fits.1.1)
            (varHeld hCtx x (fits.1.2 r (ρ.mem_map.mpr h)))) =
            cover M fits.1 (reveal M (fits.1.2 r (ρ.mem_map.mpr h)) (env.get x)) := by
          unfold cover
          have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
              cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
            intro _ _ e _; subst e; rfl
          rw [hc fits.1.1, env_get_varHeld M hEnv x]
        rw [hGetCast]
      · rw [fitVars_cons_neg hCtx ρ fits h, heldValues_cons_neg M h,
          hCastAll (held_cons_neg (ρ.back r) b bs h).symm,
          env_all_fitVars hEnv ρ fits.2 xs]
  | [], _ :: _, fits, _ => nomatch fits
  | _ :: _, [], fits, _ => nomatch fits

/-! ### Process, `mapR`, `markOwn`, and `Handler` lemmas -/

private theorem mapHalt_bind {S : Sig} {H H' A B : Type} (f : H → H')
    (p : Process S H A) (k : A → Process S H B) :
    (p.bind k).mapHalt f = (p.mapHalt f).bind fun a => (k a).mapHalt f := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.bind, Process.mapHalt]
      congr 1; funext reply; exact ih reply

private theorem mapHalt_map {S : Sig} {H H' A B : Type} (f : H → H') (g : A → B)
    (p : Process S H A) :
    (p.map g).mapHalt f = (p.mapHalt f).map g := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.map, Process.mapHalt]
      congr 1; funext reply; exact ih reply

private theorem mapHalt_mapHalt {S : Sig} {H₁ H₂ H₃ A : Type} (f : H₁ → H₂) (g : H₂ → H₃)
    (p : Process S H₁ A) :
    (p.mapHalt f).mapHalt g = p.mapHalt fun h => g (f h) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      simp only [Process.mapHalt]
      congr 1; funext reply; exact ih reply

private theorem markOwn_bind (frame : Frame) {H A B : Type}
    (p : Process (RSig M) H A) (k : A → Process (RSig M) H B) :
    Process.markOwn M frame (p.bind k) =
      (Process.markOwn M frame p).bind fun a => Process.markOwn M frame (k a) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op with
      | own kind hearers _ _ _ _ =>
          cases kind with
          | coin _ =>
              cases hearers <;> (simp only [Process.bind, Process.markOwn]; congr 1; funext reply; exact ih reply)
          | request _ =>
              simp only [Process.bind, Process.markOwn]
              congr 1; funext reply; exact ih reply
      | give _ _ _ _ _ | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [Process.bind, Process.markOwn]
          congr 1; funext reply; exact ih reply

private theorem markOwn_map (frame : Frame) {H A B : Type} (f : A → B)
    (p : Process (RSig M) H A) :
    Process.markOwn M frame (p.map f) = (Process.markOwn M frame p).map f := by
  rw [Process.map_eq_bind, Process.map_eq_bind, markOwn_bind]
  rfl

private theorem markOwn_mapHalt (frame : Frame) {H H' A : Type} (f : H → H')
    (p : Process (RSig M) H A) :
    Process.markOwn M frame (p.mapHalt f) = (Process.markOwn M frame p).mapHalt f := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op with
      | own kind hearers _ _ _ _ =>
          cases kind with
          | coin _ =>
              cases hearers <;> (simp only [Process.mapHalt, Process.markOwn]; congr 1; funext reply; exact ih reply)
          | request _ =>
              simp only [Process.mapHalt, Process.markOwn]
              congr 1; funext reply; exact ih reply
      | give _ _ _ _ _ | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [Process.mapHalt, Process.markOwn]
          congr 1; funext reply; exact ih reply

private theorem mapR_id {A : Type} (p : Program M A) : mapR M id p = p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      cases op with
      | give _ getters _ _ _ =>
          dsimp only [mapR]
          have hM : getters.map id = getters := List.map_id getters
          generalize getters.map id = gs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | own _ hearers _ _ _ _ =>
          dsimp only [mapR]
          have hM : hearers.map id = hearers := List.map_id hearers
          generalize hearers.map id = hs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [mapR, id_eq]
          congr 1; funext reply; exact ih reply

private theorem mapR_comp (ρ₁ ρ₂ : Role → Role) {A : Type} (p : Program M A) :
    mapR M ρ₁ (mapR M ρ₂ p) = mapR M (fun q => ρ₁ (ρ₂ q)) p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      cases op with
      | give _ getters _ _ _ =>
          dsimp only [mapR]
          have hM : (getters.map ρ₂).map ρ₁ = getters.map (fun q => ρ₁ (ρ₂ q)) := List.map_map
          generalize (getters.map ρ₂).map ρ₁ = gs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | own _ hearers _ _ _ _ =>
          dsimp only [mapR]
          have hM : (hearers.map ρ₂).map ρ₁ = hearers.map (fun q => ρ₁ (ρ₂ q)) := List.map_map
          generalize (hearers.map ρ₂).map ρ₁ = hs at hM ⊢
          subst hM
          congr 1; funext reply; exact ih reply
      | get _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          simp only [mapR]
          congr 1; funext reply; exact ih reply

private theorem mapR_bind (ρ : Role → Role) {A B : Type} (p : Program M A) (k : A → Program M B) :
    mapR M ρ (p.bind k) = (mapR M ρ p).bind fun a => mapR M ρ (k a) := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      cases op <;> (simp only [Process.bind, mapR]; congr 1; funext reply; exact ih reply)

private theorem mapR_map (ρ : Role → Role) {A B : Type} (f : A → B) (p : Program M A) :
    mapR M ρ (p.map f) = (mapR M ρ p).map f := by
  rw [Process.map_eq_bind, Process.map_eq_bind, mapR_bind]
  rfl

private theorem mapR_liftLocal (ρ : Role → Role) {A : Type} (lp : Local A) :
    mapR M ρ (liftLocal (S := RSig M) id lp) = liftLocal (S := RSig M) id lp := by
  cases lp with
  | done _ => rfl
  | halt _ => rfl
  | call op _ => nomatch op

private theorem handler_run_liftLocal {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (retry : Retry (RSig M) (RSig M) Stop) {A B : Type}
    (lp : Local A) (k : A → Program M B) (s : HList M.Val σ) :
    h.run retry ((liftLocal (S := RSig M) id lp).bind k) s =
      (liftLocal (S := RSig M) (fun why => (why, s)) lp).bind fun a => h.run retry (k a) s := by
  cases lp with
  | done _ => rfl
  | halt _ => rfl
  | call op _ => nomatch op

private theorem handler_run_noRetry_bind {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ)) {A B : Type}
    (p : Program M A) (k : A → Program M B) (s : HList M.Val σ) :
    h.run (retryOf M none) (p.bind k) s =
      (h.run (retryOf M none) p s).bind fun out => h.run (retryOf M none) (k out.1) out.2 := by
  induction p generalizing s with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      dsimp only [Process.bind, Handler.run, retryOf]
      rw [Process.bind_assoc]
      congr 1; funext out
      exact ih out.1 out.2

private theorem handler_answer_mapHalt_const {σ : List V.Ty} {E A : Type}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (p : Program M A) (e : E) (s : HList M.Val σ) :
    h.answer (p.mapHalt fun why => (why, e)) e s =
      (h.run (retryOf M none) p s).mapHalt fun stop => (stop.1, e, stop.2) := by
  induction p generalizing s with
  | done _ => rfl
  | halt _ => rfl
  | call op next ih =>
      dsimp only [Process.mapHalt, Handler.answer, Handler.run, retryOf]
      rw [mapHalt_bind]
      congr 1; funext out
      exact ih out.1 out.2

private theorem recover_mapHalt_false {S : Sig} {H σ A : Type} (retriable : H → Bool)
    (onRetry : (Bool × H) × σ → Process S (H × σ) (A × σ))
    (p : Process S (H × σ) (A × σ)) :
    ((p.mapHalt fun s => ((false, s.1), s.2)).recover fun stop =>
      if stop.1.1 && retriable stop.1.2 then onRetry stop else .halt (stop.1.2, stop.2)) = p := by
  induction p with
  | done _ => rfl
  | halt _ => rfl
  | call op k ih =>
      simp only [Process.mapHalt, Process.recover]
      congr 1; funext reply; exact ih reply

/-- A role process emits no `.settle` at `site`. -/
def NoSettleAt (site : Site) {A : Type} : Program M A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k =>
      (match op with
       | .settle at_ => at_.site ≠ site
       | _ => True) ∧
      ∀ reply, NoSettleAt site (k reply)

private theorem noSettleAt_bind {site : Site} {A B : Type} {p : Program M A}
    {k : A → Program M B} (hp : NoSettleAt M site p) (hk : ∀ a, NoSettleAt M site (k a)) :
    NoSettleAt M site (p.bind k) := by
  induction p with
  | done a => exact hk a
  | halt _ => trivial
  | call op next ih =>
      cases op with
      | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

private theorem noSettleAt_map {site : Site} {A B : Type} (f : A → B) {p : Program M A}
    (hp : NoSettleAt M site p) : NoSettleAt M site (p.map f) := by
  rw [Process.map_eq_bind]
  exact noSettleAt_bind M hp fun _ => trivial

private theorem noSettleAt_mapR {site : Site} (ρ : Role → Role) {A : Type} {p : Program M A}
    (hp : NoSettleAt M site p) : NoSettleAt M site (mapR M ρ p) := by
  induction p with
  | done _ => trivial
  | halt _ => trivial
  | call op next ih =>
      cases op with
      | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ | settle _ =>
          exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

private theorem noSettleAt_liftLocal {site : Site} {A : Type} (lp : Local A) :
    NoSettleAt M site (liftLocal (S := RSig M) id lp) := by
  cases lp with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => nomatch op

private theorem noSettleAt_iterate {site : Site} {A : Type}
    {step : Nat → A → Program M A} (hStep : ∀ i a, NoSettleAt M site (step i a)) :
    ∀ n i a, NoSettleAt M site (Process.iterate n step i a)
  | 0, _, _ => trivial
  | n + 1, i, a => noSettleAt_bind M (hStep i a) fun a' => noSettleAt_iterate hStep n (i + 1) a'

private theorem handler_inside_settle_bind {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (bound : Nat) (site : Site) (i : Nat) {A B : Type}
    (p : Program M A) (hp : NoSettleAt M site p)
    (at_ : Occurrence) (hAt : at_.site = site)
    (k : A → Program M B) (s : HList M.Val σ) :
    h.inside (retryOf M (some (bound, site))) i
        (p.bind fun a => .call (.settle at_) fun _ => k a) s =
      ((Process.markOwn M (.attempt site.key i) (h.run (retryOf M none) p s)).mapHalt
          fun stop => ((true, stop.1), stop.2)).bind fun out =>
        (h.run (retryOf M (some (bound, site))) (k out.1) out.2).mapHalt
          fun stop => ((false, stop.1), stop.2) := by
  induction p generalizing s with
  | done a =>
      simp only [Process.bind, Handler.inside, retryOf, hAt, ↓reduceIte, Handler.run,
        Process.markOwn, Process.mapHalt]
  | halt why => rfl
  | call op next ih =>
      have hNotEnd : (retryOf M (some (bound, site))).ends op = none := by
        cases op with
        | settle at2 =>
            dsimp only [retryOf]
            rw [ite_eq_right hp.1]
        | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | «begin» _ => rfl
      rw [Process.bind, Handler.inside, Handler.run, hNotEnd]
      dsimp only [retryOf]
      rw [markOwn_bind, mapHalt_bind, Process.bind_assoc]
      congr 1; funext out
      exact ih out.1 (hp.2 out.1) out.2

private theorem attempts_bind_settle {σ : List V.Ty} {A B : Type}
    (exhausted : Stop)
    (again : Nat → HList M.Val σ → HList M.Val σ → Except Stop (HList M.Val σ))
    (body : Nat → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (A × HList M.Val σ))
    (after : A → HList M.Val σ → Process (RSig M) (Stop × HList M.Val σ) (B × HList M.Val σ))
    (entry : HList M.Val σ) :
    ∀ (n i : Nat) (s : HList M.Val σ),
      attempts Stop.isAbort exhausted again
          (fun j s' => ((body j s').mapHalt fun stop => ((true, stop.1), stop.2)).bind fun out =>
            (after out.1 out.2).mapHalt fun stop => ((false, stop.1), stop.2))
          entry n i s =
        (retryAttempts M exhausted again body entry n i s).bind fun out => after out.1 out.2
  | 0, _, _ => rfl
  | 1, i, s => by
      dsimp only [attempts, retryAttempts]
      generalize body i s = P
      induction P with
      | done out =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          exact recover_mapHalt_false Stop.isAbort (fun stop => .halt (exhausted, stop.2)) (after out.1 out.2)
      | halt stop =>
          simp only [Process.mapHalt, Process.bind, Process.recover, Bool.true_and]
          cases Stop.isAbort stop.1 <;> rfl
      | call op k ih =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          congr 1; funext reply; exact ih reply
  | m + 2, i, s => by
      conv => lhs; rw [attempts]
      conv => rhs; rw [retryAttempts]
      dsimp only
      generalize body i s = P
      induction P with
      | done out =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          exact recover_mapHalt_false Stop.isAbort _ (after out.1 out.2)
      | halt stop =>
          simp only [Process.mapHalt, Process.bind, Process.recover, Bool.true_and]
          cases Stop.isAbort stop.1
          · rfl
          · cases again (i + 1) entry stop.2 with
            | error why => rfl
            | ok next => exact attempts_bind_settle exhausted again body after entry (m + 1) (i + 1) next
      | call op k ih =>
          simp only [Process.mapHalt, Process.bind, Process.recover]
          congr 1; funext reply; exact ih reply

/-! ### `NoSettleAt` from `Shape.attemptSites` -/

private theorem not_mem_attemptSites_rest {hs : Headers V} (target : Site) (through : List Key)
    (key : Key) {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (sh : Shape V)
    (hNot : target ∉ (ProtocolOp.shape key o sh).attemptSites through) :
    target ∉ sh.attemptSites through := by
  cases o with
  | compute _ _ _ _ _ | narrow _ _ => exact hNot
  | flow _ _ _ _ _ | given _ _ _ _ _ _ _ _ => exact hNot
  | apply _ _ _ _ _ _ => exact fun h => hNot (List.mem_append_right _ h)

private theorem noSettleAt_project_op {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (target : Site) (r : Role)
    (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
        (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
        Frame.applications path = through →
        target ∉ hdr.shape.attemptSites through →
        NoSettleAt M target (rTable hdr m r' path ins))
    {Γ : Ctx (LTy V)} {outs ins res : List (LTy V)}
    (key : Key) (o : ProtocolOp V hs ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (sh : Shape V) (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
    (hP : Frame.applications path = through)
    (hNot : target ∉ (ProtocolOp.shape key o sh).attemptSites through)
    (hRest : ∀ env', NoSettleAt M target (rest.denote (roleSem M r fnTable rTable) path env')) :
    NoSettleAt M target
      ((ProtocolOp.project r key o operands results rest).denote
        (roleSem M r fnTable rTable) path env) := by
  cases o with
  | compute R lo opTys types held =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn, Term.denote_op]
        exact noSettleAt_bind M (noSettleAt_map M _ (noSettleAt_liftLocal M _)) fun _ => hRest _
      · rw [dite_eq_right hIn, Term.denote_op]
        exact hRest _
  | flow kind giver getters holds apart =>
      cases operands with
      | cons x hNil =>
          cases hNil
          dsimp only [ProtocolOp.project]
          by_cases hG : r = giver
          · rw [dite_eq_left hG, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact ⟨trivial, fun _ => hRest _⟩
          · rw [dite_eq_right hG]
            by_cases hM : r ∈ getters
            · rw [dite_eq_left hM, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
              exact ⟨trivial, fun _ => hRest _⟩
            · rw [dite_eq_right hM, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
              exact hRest _
  | given kind owner hearers opTys τ typed held apart =>
      dsimp only [ProtocolOp.project]
      by_cases hOwn : r = owner
      · rw [dite_eq_left hOwn]
        cases hOwn.symm
        rw [Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
        exact ⟨trivial, fun _ => hRest _⟩
      · rw [dite_eq_right hOwn]
        by_cases hH : r ∈ hearers
        · rw [dite_eq_left hH, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
          exact ⟨trivial, fun _ => hRest _⟩
        · rw [dite_eq_right hH, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
          exact hRest _
  | narrow R among =>
      cases operands with
      | cons x hNil =>
          cases hNil
          dsimp only [ProtocolOp.project]
          by_cases hIn : r ∈ R
          · rw [dite_eq_left hIn, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact hRest _
          · rw [dite_eq_right hIn, Term.denote_op]; dsimp only [roleSem, roleOp, Process.bind]
            exact hRest _
  | apply callee roles distinct covers opTys fits =>
      dsimp only [ProtocolOp.project, ProtocolOp.shape, Shape.attemptSites] at hNot ⊢
      rw [Term.denote_op]
      refine noSettleAt_bind M (noSettleAt_map M _ (noSettleAt_mapR M _ ?_)) fun _ => hRest _
      exact hProt callee _ (through ++ [key]) (path ++ [Frame.application key]) _
        (by rw [Frame.applications_append, hP]; rfl) (fun h => hNot (List.mem_append_left _ h))

private theorem noSettleAt_projectLoop {hs : Headers V}
    (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (target : Site) (r : Role) (key : Key) (ps : Holders) (hIn : r ∈ ps)
    {Γ : Ctx (LTy V)} {outs carried each : List (LTy V)}
    (times : Times (protocolDialect V hs) ps Γ) (init : HList (Var Γ) carried)
    (inputs : Names (LTy.index ps :: carried))
    (body : Term (roleDialect V hs r) (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (LTy.collected times.size)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (path : List Frame) (env : Env (RV M r) Γ)
    (hBody : ∀ i env', NoSettleAt M target (body.denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i]) env'))
    (hRest : ∀ env', NoSettleAt M target (rest.denote (roleSem M r fnTable rTable) path env')) :
    NoSettleAt M target
      ((projectLoop r key ps hIn times init inputs body results rest).denote
        (roleSem M r fnTable rTable) path env) := by
  cases inputs with
  | cons idxNm carriedInNames =>
      cases times with
      | fixed n =>
          dsimp only [projectLoop, Term.denote, Instr.denote, Semantics.loopStep]
          refine noSettleAt_bind M (noSettleAt_bind M (noSettleAt_iterate M ?_ _ _ _) fun _ => trivial) fun _ => hRest _
          intro i st
          exact noSettleAt_bind M (hBody i _) fun _ => trivial
      | value cnt ok =>
          dsimp only [projectLoop, Term.denote, Instr.denote, Semantics.loopStep]
          refine noSettleAt_bind M (noSettleAt_bind M (noSettleAt_iterate M ?_ _ _ _) fun _ => trivial) fun _ => hRest _
          intro i st
          exact noSettleAt_bind M (hBody i _) fun _ => trivial

mutual
  private theorem noSettleAt_project_term {hs : Headers V}
      (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (target : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
          Frame.applications path = through →
          target ∉ hdr.shape.attemptSites through →
          NoSettleAt M target (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs)
        (through : List Key) (path : List Frame) (env : Env (RV M r) Γ),
        Frame.applications path = through →
        target ∉ (shapeOf t).attemptSites through →
        NoSettleAt M target ((project r t).denote (roleSem M r fnTable rTable) path env)
    | _, _, .ret _, _, _, _, _, _ => trivial
    | _, _, .op key o operands results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf] at hNot ⊢
        have hNotRest := not_mem_attemptSites_rest target through key o (shapeOf rest) hNot
        exact noSettleAt_project_op M fnTable rTable target r hProt key o operands results
          (project r rest) (shapeOf rest) through path env hP hNot fun env' =>
            noSettleAt_project_term fnTable rTable target r hProt rest through path env' hP hNotRest
    | _, _, .guard key ps c ok why rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_guard]
          cases (roleSem M r fnTable rTable).holds _ (env.get c) with
          | false => trivial
          | true => exact noSettleAt_project_term fnTable rTable target r hProt rest through path env hP hNot
        · rw [dite_eq_right hIn]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path env hP hNot
    | _, _, .choose key ps c ok gives onTrue onFalse results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites, Shapes.attemptSites] at hNot ⊢
        have h1 : target ∉ (shapeOf onTrue).attemptSites through := fun h => hNot (by simp [h])
        have h2 : target ∉ (shapeOf onFalse).attemptSites through := fun h => hNot (by simp [h])
        have h3 : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (by simp [h])
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_choose]
          apply noSettleAt_bind M
          · cases (roleSem M r fnTable rTable).holds _ (env.get c) with
            | false => exact noSettleAt_project_term fnTable rTable target r hProt onFalse through path env hP h2
            | true => exact noSettleAt_project_term fnTable rTable target r hProt onTrue through path env hP h1
          · exact fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP h3
        · rw [dite_eq_right hIn, Term.denote_op]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP h3
    | _, _, .cases key ps x ok gives arms results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hA : target ∉ (shapesOf arms).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn, Term.denote_cases]
          refine noSettleAt_bind M
            (noSettleAt_project_arms fnTable rTable target r hProt arms through path env _ hP hA)
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
        · rw [dite_eq_right hIn, Term.denote_op]
          exact noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
    | _, _, .loop key ps times gives init inputs body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        have hBody : ∀ i env', NoSettleAt M target
            ((project r body).denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i]) env') :=
          fun i env' => noSettleAt_project_term fnTable rTable target r hProt body through
            (path ++ [Frame.iteration key i]) env'
            (by rw [Frame.applications_append, hP]; exact List.append_nil _) hB
        have hRest : ∀ env', NoSettleAt M target
            ((project r rest).denote (roleSem M r fnTable rTable) path env') :=
          fun env' => noSettleAt_project_term fnTable rTable target r hProt rest through path env' hP hR
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact noSettleAt_projectLoop M fnTable rTable target r key ps hIn times init inputs
            (project r body) results (project r rest) path env hBody hRest
        · rw [dite_eq_right hIn, Term.denote_op]
          exact hRest _
    | _, _, .block key num body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_append_left _ h)
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_append_right _ h)
        rw [Term.denote_block]
        refine noSettleAt_bind M (noSettleAt_project_term fnTable rTable target r hProt body through
          (path ++ [Frame.iteration key num]) env
          (by rw [Frame.applications_append, hP]; exact List.append_nil _) hB)
          fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR
    | _, _, .attempt key w owns inputs body results rest, through, path, env, hP, hNot => by
        dsimp only [project, shapeOf, Shape.attemptSites] at hNot ⊢
        have hNe : (⟨through, key⟩ : Site) ≠ target := fun h => hNot (by rw [h]; exact List.mem_cons_self)
        have hB : target ∉ (shapeOf body).attemptSites through := fun h => hNot (List.mem_cons_of_mem _ (List.mem_append_left _ h))
        have hR : target ∉ (shapeOf rest).attemptSites through := fun h => hNot (List.mem_cons_of_mem _ (List.mem_append_right _ h))
        rw [Term.denote_attempt]
        by_cases hw : r ∈ w
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              Process.call (ROp.begin ⟨path, key⟩) fun n => Process.done (hide M r (LTy.index w) n) := by
            dsimp only [roleSem]; exact ite_eq_left hw
          have hSet : (roleSem M r fnTable rTable).settle w key path =
              Process.call (ROp.settle ⟨path, key⟩) fun _ => Process.done () := by
            dsimp only [roleSem]; exact ite_eq_left hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          refine ⟨trivial, fun n => noSettleAt_bind M
            (noSettleAt_project_term fnTable rTable target r hProt body through path _ hP hB) fun _ => ?_⟩
          exact ⟨by simp [Occurrence.site, hP, hNe],
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR⟩
        · have hBeg : (roleSem M r fnTable rTable).begin w key path =
              Process.done (hide M r (LTy.index w) 0) := by
            dsimp only [roleSem]; exact ite_eq_right hw
          have hSet : (roleSem M r fnTable rTable).settle w key path = Process.done () := by
            dsimp only [roleSem]; exact ite_eq_right hw
          rw [hBeg, hSet]
          dsimp only [Process.bind]
          exact noSettleAt_bind M
            (noSettleAt_project_term fnTable rTable target r hProt body through path _ hP hB)
            fun _ => noSettleAt_project_term fnTable rTable target r hProt rest through path _ hP hR

  private theorem noSettleAt_project_arms {hs : Headers V}
      (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (target : Site) (r : Role)
      (hProt : ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r' : Role)
          (through : List Key) (path : List Frame) (ins : HList (RV M r') hdr.ins),
          Frame.applications path = through →
          target ∉ hdr.shape.attemptSites through →
          NoSettleAt M target (rTable hdr m r' path ins)) :
      ∀ {Γ : Ctx (LTy V)} {mid payloads : List (LTy V)}
        (as' : Arms (protocolDialect V hs) Γ mid payloads)
        (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
        (pk : Pick (RV M r) payloads),
        Frame.applications path = through →
        target ∉ (shapesOf as').attemptSites through →
        NoSettleAt M target ((projectArms r as').denote (roleSem M r fnTable rTable) path env pk)
    | _, _, _, .nil, _, _, _, pk, _, _ => nomatch pk
    | _, _, _, .cons _ arm _, through, path, _, .here _, hP, hNA =>
        noSettleAt_project_term fnTable rTable target r hProt arm through path _ hP
          (fun h => hNA (List.mem_append_left _ h))
    | _, _, _, .cons _ _ more, through, path, env, .there p, hP, hNA =>
        noSettleAt_project_arms fnTable rTable target r hProt more through path env p hP
          (fun h => hNA (List.mem_append_right _ h))
end

private theorem noSettleAt_defs {hs : Headers V} (defs : Defs V hs) (target : Site) :
    ∀ {hdr : ProtocolHeader V} (m : Member hs.protocols hdr) (r : Role)
      (through : List Key) (path : List Frame) (ins : HList (RV M r) hdr.ins),
      Frame.applications path = through →
      target ∉ hdr.shape.attemptSites through →
      NoSettleAt M target (Defs.rTable M defs hdr m r path ins) := by
  induction defs with
  | nil => intro _ m; exact nomatch m
  | fn _ _ _ _ _ _ ih => exact ih
  | protocol hdrP inputsP bodyP okP rest ih =>
      intro hdr m r through path ins hP hNot
      cases m with
      | head =>
          rw [okP.shaped] at hNot
          exact noSettleAt_project_term M (Defs.fnTable M rest) (Defs.rTable M rest) target r ih
            bodyP through path (Env.empty.extend inputsP ins) hP hNot
      | tail m' => exact ih m' r through path ins hP hNot

private theorem noSettleAt_project_of_shape {hs : Headers V} (defs : Defs V hs) (target : Site)
    {Γ : Ctx (LTy V)} {outs : List (LTy V)} (body : Term (protocolDialect V hs) Γ outs)
    (r : Role) (through : List Key) (path : List Frame) (env : Env (RV M r) Γ)
    (hP : Frame.applications path = through)
    (hNot : target ∉ (shapeOf body).attemptSites through) :
    NoSettleAt M target ((project r body).denote (roleSem M r (Defs.fnTable M defs) (Defs.rTable M defs)) path env) :=
  noSettleAt_project_term M (Defs.fnTable M defs) (Defs.rTable M defs) target r
    (noSettleAt_defs M defs target) body through path env hP hNot

/-! ### Level 1 soundness (`specializeTerm` & `specializeProtocolInDefs`) -/

/-- Soundness contract of an `EffectSpecializer` against a `Handler`. -/
def SpecOpSound {fns : List (FnHeader V)} (fnTable : FnTable M fns) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fns σ) : Prop :=
  ∀ (through : List Key) (key : Key) {ins res : List V.Ty}
    (op : ResidualOp V ins res) {Δ : Ctx V.Ty} (args : HList (Var Δ) ins)
    (path : List Frame) (cenv : Env M.Val Δ) (s : HList M.Val σ),
    Frame.applications path = through →
    (specOp through key op args).denote M fnTable path cenv s =
      (h.clause (op.toROp M ⟨path, key⟩ (cenv.all args)) s).map fun out =>
        (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1, out.2)

/-- Extract the `Retry` corresponding to an optional retry configuration. -/
def retryOfCfg {fns : List (FnHeader V)} {σ : List V.Ty} :
    Option (Nat × Site × StackAgain V fns σ) → Retry (RSig M) (RSig M) Stop
  | none => retryOf M none
  | some (bound, site, _) => retryOf M (some (bound, site))

/-- Consistency of `again` in `retryCfg` with `h.again`. -/
def RetryCfgOk {fns : List (FnHeader V)} (fnTable : FnTable M fns) {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ)) :
    Option (Nat × Site × StackAgain V fns σ) → Prop
  | none => True
  | some (_, _, ag) => StackAgain.eval M fnTable ag = h.again

/-- Whether a single role operation respects the well-nested retry condition. -/
def RoleOpWellNested {hs : Headers V} {r : Role} (site : Site) (through : List Key) (key : Key) :
    {ins outs : List (LTy V)} → RoleOp V hs r ins outs → Prop
  | _, _, .apply (hdr := hdr) _ _ _ _ _ _ => Shape.noNestedAttempt site (through ++ [key]) hdr.shape = true
  | _, _, _ => True

/-! Recursive nesting invariant on `Term (roleDialect V hs r)`. -/
mutual
  def RoleTermWellNested {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (r : Role) (site : Site) (through : List Key) :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (roleDialect V hs r) Γ outs → Prop
    | _, _, .ret _ => True
    | _, _, .op key o _ _ rest =>
        RoleOpWellNested site through key o ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .guard _ _ _ _ _ rest => RoleTermWellNested fnTable rTable r site through rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse _ rest =>
        RoleTermWellNested fnTable rTable r site through onTrue ∧
        RoleTermWellNested fnTable rTable r site through onFalse ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .cases _ _ _ _ _ arms _ rest =>
        RoleArmsWellNested fnTable rTable r site through arms ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .loop _ _ _ _ _ _ body _ rest =>
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .block _ _ body _ rest =>
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest
    | _, _, .attempt key w _ _ body _ rest =>
        (r ∈ w → ⟨through, key⟩ = site →
          ∀ (path : List Frame) (env : Env (RV M r) _),
            Frame.applications path = through →
            NoSettleAt M site (body.denote (roleSem M r fnTable rTable) path env)) ∧
        RoleTermWellNested fnTable rTable r site through body ∧
        RoleTermWellNested fnTable rTable r site through rest

  def RoleArmsWellNested {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (r : Role) (site : Site) (through : List Key) :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
      Arms (roleDialect V hs r) Γ mid payloads → Prop
    | _, _, _, .nil => True
    | _, _, _, .cons _ arm rest =>
        RoleTermWellNested fnTable rTable r site through arm ∧
        RoleArmsWellNested fnTable rTable r site through rest
end

private theorem noNestedAttempt_rest {hs : Headers V} (site : Site) (through : List Key)
    (key : Key) {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (sh : Shape V)
    (hWN : Shape.noNestedAttempt site through (ProtocolOp.shape key o sh) = true) :
    Shape.noNestedAttempt site through sh = true := by
  cases o with
  | compute _ _ _ _ _ | narrow _ _ | flow _ _ _ _ _ | given _ _ _ _ _ _ _ _ => exact hWN
  | apply _ _ _ _ _ _ =>
      dsimp only [ProtocolOp.shape, Shape.noNestedAttempt] at hWN
      exact (Bool.and_eq_true _ _ |>.mp hWN).2

private theorem roleTermWellNested_project_op {hs : Headers V} (defs : Defs V hs) (site : Site)
    (r : Role) (through : List Key) {Γ : Ctx (LTy V)} {outs ins res : List (LTy V)}
    (key : Key) (o : ProtocolOp V hs ins res) (operands : HList (Var Γ) ins)
    (results : Names res) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (sh : Shape V)
    (hWN : Shape.noNestedAttempt site through (ProtocolOp.shape key o sh) = true)
    (hRest : RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through rest) :
    RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through
      (ProtocolOp.project r key o operands results rest) := by
  cases o with
  | compute R _ _ _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hIn]; exact ⟨trivial, hRest⟩
  | narrow R _ =>
      dsimp only [ProtocolOp.project]
      by_cases hIn : r ∈ R
      · rw [dite_eq_left hIn]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hIn]; exact ⟨trivial, hRest⟩
  | flow _ giver getters _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hG : r = giver
      · rw [dite_eq_left hG]; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hG]
        by_cases hM : r ∈ getters
        · rw [dite_eq_left hM]; exact ⟨trivial, hRest⟩
        · rw [dite_eq_right hM]; exact ⟨trivial, hRest⟩
  | given _ owner hearers _ _ _ _ _ =>
      dsimp only [ProtocolOp.project]
      by_cases hOwn : r = owner
      · rw [dite_eq_left hOwn]; cases hOwn.symm; exact ⟨trivial, hRest⟩
      · rw [dite_eq_right hOwn]
        by_cases hH : r ∈ hearers
        · rw [dite_eq_left hH]; exact ⟨trivial, hRest⟩
        · rw [dite_eq_right hH]; exact ⟨trivial, hRest⟩
  | apply _ _ _ _ _ _ =>
      dsimp only [ProtocolOp.project, ProtocolOp.shape, Shape.noNestedAttempt] at hWN ⊢
      exact ⟨(Bool.and_eq_true _ _ |>.mp hWN).1, hRest⟩

mutual
  private theorem roleTermWellNested_of_shape {hs : Headers V} (defs : Defs V hs) (site : Site)
      (r : Role) (through : List Key) :
      ∀ {Γ : Ctx (LTy V)} {outs : List (LTy V)} (body : Term (protocolDialect V hs) Γ outs),
        Shape.noNestedAttempt site through (shapeOf body) = true →
        RoleTermWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through (project r body)
    | _, _, .ret _, _ => trivial
    | _, _, .op key o operands results rest, hWN => by
        dsimp only [project, shapeOf] at hWN ⊢
        have hRest := roleTermWellNested_of_shape defs site r through rest
          (noNestedAttempt_rest site through key o (shapeOf rest) hWN)
        exact roleTermWellNested_project_op M defs site r through key o operands results
          (project r rest) (shapeOf rest) hWN hRest
    | _, _, .guard _ ps _ _ _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]; exact roleTermWellNested_of_shape defs site r through rest hWN
        · rw [dite_eq_right hIn]; exact roleTermWellNested_of_shape defs site r through rest hWN
    | _, _, .choose _ ps _ _ _ onTrue onFalse _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt, Shapes.noNestedAttempt] at hWN ⊢
        simp only [Bool.and_eq_true, Bool.and_true] at hWN
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact ⟨roleTermWellNested_of_shape defs site r through onTrue hWN.1.1,
            roleTermWellNested_of_shape defs site r through onFalse hWN.1.2,
            roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .cases _ ps _ _ _ arms _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          exact ⟨roleArmsWellNested_of_shape defs site r through arms hWN.1,
            roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .loop _ ps times _ _ _ bodyL _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        have hBody := roleTermWellNested_of_shape defs site r through bodyL hWN.1
        have hRest := roleTermWellNested_of_shape defs site r through rest hWN.2
        by_cases hIn : r ∈ ps
        · rw [dite_eq_left hIn]
          cases times <;> exact ⟨hBody, hRest⟩
        · rw [dite_eq_right hIn]
          exact ⟨trivial, hRest⟩
    | _, _, .block _ _ bodyB _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        rw [Bool.and_eq_true] at hWN
        exact ⟨roleTermWellNested_of_shape defs site r through bodyB hWN.1,
          roleTermWellNested_of_shape defs site r through rest hWN.2⟩
    | _, _, .attempt key w _ _ bodyA _ rest, hWN => by
        dsimp only [project, shapeOf, Shape.noNestedAttempt] at hWN ⊢
        simp only [Bool.and_eq_true] at hWN
        refine ⟨fun _ hEq path env hP => ?_,
          roleTermWellNested_of_shape defs site r through bodyA hWN.1.2,
          roleTermWellNested_of_shape defs site r through rest hWN.2⟩
        have hNotMem : site ∉ (shapeOf bodyA).attemptSites through := by
          have h1 := hWN.1.1
          rw [ite_eq_left hEq, Bool.not_eq_true', decide_eq_false_iff_not] at h1
          exact h1
        exact noSettleAt_project_of_shape M defs site bodyA r through path env hP hNotMem

  private theorem roleArmsWellNested_of_shape {hs : Headers V} (defs : Defs V hs) (site : Site)
      (r : Role) (through : List Key) :
      ∀ {Γ : Ctx (LTy V)} {mid payloads : List (LTy V)}
        (as' : Arms (protocolDialect V hs) Γ mid payloads),
        Shapes.noNestedAttempt site through (shapesOf as') = true →
        RoleArmsWellNested M (Defs.fnTable M defs) (Defs.rTable M defs) r site through (projectArms r as')
    | _, _, _, .nil, _ => trivial
    | _, _, _, .cons _ arm more, hA => by
        dsimp only [shapesOf, Shapes.noNestedAttempt] at hA
        rw [Bool.and_eq_true] at hA
        exact ⟨roleTermWellNested_of_shape defs site r through arm hA.1,
          roleArmsWellNested_of_shape defs site r through more hA.2⟩
end

private theorem closedTerm_denote_castCT {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {σ : List V.Ty} {Γ₁ Γ₂ : Ctx V.Ty} {outs₁ outs₂ : List V.Ty}
    (hΓ : Γ₁ = Γ₂) (hOut : outs₁ = outs₂) (t : ClosedTerm V fns σ Γ₁ outs₁)
    (path : List Frame) (env : Env M.Val Γ₂) (s : HList M.Val σ) :
    (t.castCT hΓ hOut).denote M fnTable path env s =
      (t.denote M fnTable path (cast (congrArg (Env M.Val) hΓ.symm) env) s).map fun out =>
        (cast (congrArg (HList M.Val) hOut) out.1, out.2) := by
  subst hΓ; subst hOut
  exact (Process.map_id' _).symm

private theorem localOp_lift_eq {fns₁ fns₂ : List (FnHeader V)}
    (t₁ : FnTable M fns₁) (t₂ : FnTable M fns₂)
    (fnLift : ∀ {hdr}, Member fns₁ hdr → Member fns₂ hdr)
    (hLift : ∀ hdr (f : Member fns₁ hdr), t₂ hdr (fnLift f) = t₁ hdr f)
    {ins res : List V.Ty} (lo : LocalOp V fns₁ ins res) (args : HList M.Val ins) :
    localOp M t₂ (lo.lift fnLift) args = localOp M t₁ lo args := by
  cases lo with
  | row _ _ _ | owned _ | literal _ _ _ => rfl
  | call callee => exact congrFun (hLift _ callee) args

/-- Project a list-of-located-values loop accumulator to its held plain lists. -/
private def heldAcc (r : Role) :
    {each : List (LTy V)} → HList (fun a => List (RV M r a)) each →
    HList (fun τ => List (M.Val τ)) (held r each)
  | [], .nil => .nil
  | a :: rest, .cons vs tail =>
      if h : r ∈ a.holders then
        have hEq : held r (a :: rest) = a.ty :: held r rest := by simp [held, h]
        cast (congrArg (HList fun τ => List (M.Val τ)) hEq.symm)
          (HList.cons (vs.map (reveal M h)) (heldAcc r tail))
      else
        have hEq : held r (a :: rest) = held r rest := by simp [held, h]
        cast (congrArg (HList fun τ => List (M.Val τ)) hEq.symm) (heldAcc r tail)

private theorem heldAcc_cons_pos {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∈ a.holders) (vs : List (RV M r a)) (tail : HList (fun b => List (RV M r b)) rest) :
    heldAcc M r (HList.cons vs tail) =
      cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_pos r a rest h).symm)
        (HList.cons (vs.map (reveal M h)) (heldAcc M r tail)) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_pos r a rest h').symm)
      (HList.cons (vs.map (reveal M h')) (heldAcc M r tail))
    else cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_neg r a rest h').symm)
      (heldAcc M r tail)) = _
  exact dite_eq_left h

private theorem heldAcc_cons_neg {r : Role} {a : LTy V} {rest : List (LTy V)}
    (h : r ∉ a.holders) (vs : List (RV M r a)) (tail : HList (fun b => List (RV M r b)) rest) :
    heldAcc M r (HList.cons vs tail) =
      cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_neg r a rest h).symm)
        (heldAcc M r tail) := by
  change (if h' : r ∈ a.holders then
    cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_pos r a rest h').symm)
      (HList.cons (vs.map (reveal M h')) (heldAcc M r tail))
    else cast (congrArg (HList fun τ => List (M.Val τ)) (held_cons_neg r a rest h').symm)
      (heldAcc M r tail)) = _
  exact dite_eq_right h

private theorem heldAcc_empties (r : Role) :
    ∀ (each : List (LTy V)), heldAcc M r (HList.empties each) = HList.empties (held r each)
  | [] => rfl
  | a :: rest => by
      have hEmp : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂),
          cast (congrArg (HList fun τ => List (M.Val τ)) e) (HList.empties ts₁) = HList.empties ts₂ := by
        intro _ _ e; subst e; rfl
      by_cases h : r ∈ a.holders
      · rw [HList.empties, heldAcc_cons_pos M h, heldAcc_empties r rest]
        exact hEmp (held_cons_pos r a rest h).symm
      · rw [HList.empties, heldAcc_cons_neg M h, heldAcc_empties r rest]
        exact hEmp (held_cons_neg r a rest h).symm

private theorem heldAcc_push (r : Role) :
    ∀ {each : List (LTy V)} (acc : HList (fun a => List (RV M r a)) each)
      (vs : HList (RV M r) each),
      heldAcc M r (acc.push vs) = (heldAcc M r acc).push (heldValues M r vs)
  | [], .nil, .nil => rfl
  | a :: rest, .cons xs acc, .cons v vs => by
      have hPushCast : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂)
          (ha : HList (fun τ => List (M.Val τ)) ts₁) (hv : HList M.Val ts₁),
          cast (congrArg (HList fun τ => List (M.Val τ)) e) (ha.push hv) =
            (cast (congrArg (HList fun τ => List (M.Val τ)) e) ha).push
              (cast (congrArg (HList M.Val) e) hv) := by
        intro _ _ e _ _; subst e; rfl
      by_cases h : r ∈ a.holders
      · rw [HList.push, heldAcc_cons_pos M h, heldAcc_cons_pos M h, heldValues_cons_pos M h,
          heldAcc_push r acc vs]
        exact hPushCast (held_cons_pos r a rest h).symm
          (HList.cons (xs.map (reveal M h)) (heldAcc M r acc))
          (HList.cons (reveal M h v) (heldValues M r vs))
      · rw [HList.push, heldAcc_cons_neg M h, heldAcc_cons_neg M h, heldValues_cons_neg M h,
          heldAcc_push r acc vs]
        exact hPushCast (held_cons_neg r a rest h).symm (heldAcc M r acc) (heldValues M r vs)

private theorem heldValues_collected {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) (r : Role) (size : Option Nat) :
    ∀ {each : List (LTy V)} (acc : HList (fun a => List (RV M r a)) each),
      heldValues M r (Semantics.collected (roleSem M r fnTable rTable) size acc) =
        cast (congrArg (HList M.Val) (held_map_collected r size each).symm)
          (closedCollected M size (heldAcc M r acc))
  | [], .nil => rfl
  | a :: rest, .cons vs acc => by
      have hColCast : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂)
          (ha : HList (fun τ => List (M.Val τ)) ts₁),
          closedCollected M size (cast (congrArg (HList fun τ => List (M.Val τ)) e) ha) =
            cast (congrArg (HList M.Val) (congrArg (List.map fun τ => .seq τ size) e))
              (closedCollected M size ha) := by
        intro _ _ e _; subst e; rfl
      rw [Semantics.collected]
      change heldValues M r (HList.cons (collectRV M r size a vs.reverse)
          (Semantics.collected (roleSem M r fnTable rTable) size acc)) = _
      by_cases h : r ∈ a.holders
      · have hCol : r ∈ (LTy.collected size a).holders := h
        rw [heldValues_cons_pos M hCol, collectRV, dite_eq_left h, reveal_hide, List.map_reverse,
          heldValues_collected fnTable rTable r size acc, heldAcc_cons_pos M h,
          hColCast (held_cons_pos r a rest h).symm, closedCollected,
          hlist_cons_cast (held_map_collected r size rest).symm, cast_cast, cast_cast]
      · have hCol : r ∉ (LTy.collected size a).holders := h
        rw [heldValues_cons_neg M hCol, heldValues_collected fnTable rTable r size acc,
          heldAcc_cons_neg M h, hColCast (held_cons_neg r a rest h).symm,
          cast_cast, cast_cast]

private theorem heldValues_split (r : Role) :
    ∀ {as bs : List (LTy V)} (vs : HList (RV M r) (as ++ bs)),
      (HList.split (held r as) (cast (congrArg (HList M.Val) (held_append r as bs)) (heldValues M r vs))).1 =
        heldValues M r (HList.split as vs).1 ∧
      (HList.split (held r as) (cast (congrArg (HList M.Val) (held_append r as bs)) (heldValues M r vs))).2 =
        heldValues M r (HList.split as vs).2 := by
  intro as bs vs
  have hApp := heldValues_append M r (HList.split as vs).1 (HList.split as vs).2
  rw [split_append as vs] at hApp
  rw [hApp, cast_cast, cast_eq]
  have hSp : ∀ {ts₁ ts₂ : List V.Ty} (x : HList M.Val ts₁) (y : HList M.Val ts₂),
      HList.split ts₁ (x.append y) = (x, y) := by
    intro ts₁ ts₂ x y
    induction x with
    | nil => rfl
    | cons v xs ih => simp only [HList.append, HList.split, ih]
  rw [hSp]
  exact ⟨rfl, rfl⟩

/-- Helper: `Handler.run` on a single effect that is not `retry.begins`. -/
private theorem handler_run_call_nonBegin {σ : List V.Ty}
    (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (retry : Retry (RSig M) (RSig M) Stop) (op : ROp M)
    (hNotBeg : retry.begins op = none) {A : Type} (k : (RSig M).Reply op → Program M A)
    (s : HList M.Val σ) :
    h.run retry (.call op k) s = (h.clause op s).bind fun out => h.run retry (k out.1) out.2 := by
  rw [Handler.run, hNotBeg]

/-- Helper: `retryOfCfg` never begins on non-`begin` operations. -/
private theorem retryOfCfg_not_begin {fns : List (FnHeader V)} {σ : List V.Ty}
    (retryCfg : Option (Nat × Site × StackAgain V fns σ)) (op : ROp M)
    (h : match op with | .begin _ => False | _ => True) :
    (retryOfCfg M retryCfg).begins op = none := by
  cases retryCfg with
  | none => rfl
  | some cfg =>
      cases cfg with
      | mk b sr =>
          cases sr with
          | mk site ag =>
              cases op with
              | «begin» _ => exact nomatch h
              | give _ _ _ _ _ | get _ _ _ _ | own _ _ _ _ _ _ | hear _ _ _ _ | settle _ => rfl

/-- Helper: casting `Env.extend` and rewriting `ClosedTerm.denote`. -/
private theorem closedTerm_denote_castExt {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {σ : List V.Ty} {Δ : Ctx V.Ty} {as bs : List V.Ty} (h : as = bs)
    (ns : Names as) (vs : HList M.Val as) {outs : List V.Ty}
    (t : ClosedTerm V fns σ (Δ.extend ns) outs)
    (path : List Frame) (cenv : Env M.Val Δ) (s : HList M.Val σ) :
    (t.castCT (ctx_extend_cast Δ h ns).symm rfl).denote M fnTable path
        (cenv.extend (cast (congrArg Names h) ns) (cast (congrArg (HList M.Val) h) vs)) s =
      t.denote M fnTable path (cenv.extend ns vs) s := by
  subst h; rfl

private def liftPick (r : Role) (ps : Holders) :
    {l : List V.Ty} → Pick M.Val l → Pick (RV M r) (l.map fun τ => ⟨τ, ps⟩)
  | _ :: _, .here u => .here (hide M r ⟨_, ps⟩ u)
  | _ :: _, .there p => .there (liftPick r ps p)

private theorem pickAt_eq_liftPick (r : Role) (ps : Holders) :
    ∀ (altsT : Tys V.TypeKey) (u : altsT.Choice M.toCarriers),
      Tys.pickAt M ps (W := RV M r) (fun τ v => hide M r ⟨τ, ps⟩ v) altsT u =
        liftPick M r ps (Tys.pick M altsT u)
  | .nil, u => nomatch u
  | .cons _ _, .inl _ => rfl
  | .cons _ _, .inr v => congrArg Pick.there (pickAt_eq_liftPick r ps _ v)

/-! CPS soundness theorems for `specializeTerm` and `specializeArms`. -/

private def SpecTermHyp {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (t : Term (roleDialect V hs r) Γ outs) : Prop :=
  ∀ (path : List Frame) (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) (s : HList M.Val σ)
    {B : Type} (cont : HList (RV M r) outs → Program M B),
    EnvRel M r hCtx env cenv →
    Frame.applications path = through →
    (∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through t) →
    h.run (retryOfCfg M retryCfg)
      ((mapR M ρ (t.denote (roleSem M r fnTable rTable) path env)).bind cont) s =
      ((specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx t).denote
        M fullTable path cenv s).bind
        fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2

private theorem specializeTerm_sound_compute {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {insOp outsOp : List V.Ty} {outsTerm : List (LTy V)}
    (key : Key) (R : Holders) (lo : LocalOp V hs.fns insOp outsOp)
    (opTys : List (LTy V)) (types : opTys.map LTy.ty = insOp) (mine : r ∈ R)
    (here : ∀ a ∈ opTys, r ∈ a.holders)
    (operands : HList (Var Γ) opTys) (results : Names (outsOp.map fun τ => ⟨τ, R⟩))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outsTerm)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.compute R lo opTys types mine here) operands results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ (((liftLocal id (localOp M fnTable lo (computeArgs M types (revealAll M here (env.all operands))))).map
      fun outs => hideAll M r (HList.located M R outs)).bind fun vs =>
        rest.denote (roleSem M r fnTable rTable) path (env.extend results vs))).bind cont) s = _
  rw [mapR_bind, mapR_map, mapR_liftLocal, Process.bind_assoc, Process.bind_map,
    handler_run_liftLocal]
  have hArgs : cenv.all (cast (congrArg (HList (Var Δ)) types) (varsAllHeld hCtx here operands)) =
      computeArgs M types (revealAll M here (env.all operands)) := by
    unfold computeArgs
    rw [← env_all_varsAllHeld M hEnv here operands]
    have hc : ∀ {ts₁ ts₂ : List V.Ty} (e : ts₁ = ts₂) (xs : HList (Var Δ) ts₁),
        cenv.all (cast (congrArg (HList (Var Δ)) e) xs) =
          cast (congrArg (HList M.Val) e) (cenv.all xs) := by
      intro _ _ e _; subst e; rfl
    exact hc types _
  rw [hArgs, localOp_lift_eq M fnTable fullTable fnLift hLift, Process.bind_assoc]
  congr 1; funext vs
  have hRest' := hRest path
    (env.extend results (hideAll M r (HList.located M R vs)))
    (cenv.extend (heldNames r results) (heldValues M r (hideAll M r (HList.located M R vs))))
    s cont (hEnv.extend M results _) hPath hWNRest
  rw [hRest']
  have hRes : held r (outsOp.map fun τ => ⟨τ, R⟩) = outsOp := held_map_holders r R mine outsOp
  have hVs : cast (congrArg (HList M.Val) hRes) (heldValues M r (hideAll M r (HList.located M R vs))) = vs := by
    rw [heldValues_hideAll_located M r R mine vs, cast_cast, cast_eq]
  conv => rhs; rw [← hVs, closedTerm_denote_castExt M fullTable hRes (heldNames r results)]

private theorem specializeTerm_sound_absent {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (items : List (LTy V)) (out : ∀ a ∈ items, r ∉ a.holders)
    (results : Names items) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.absent items out) .nil results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ (rest.denote (roleSem M r fnTable rTable) path (env.extend results (nothings M out)))).bind cont) s = _
  have hEmpty : held r items = [] := held_all_out r items out
  have hExt : Δ.extend (heldNames r results) = Δ := by
    have hNil : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
      cases cast (congrArg Names hEmpty) (heldNames r results); rfl
    rw [← ctx_extend_cast Δ hEmpty (heldNames r results), hNil]; rfl
  have hCenv : cast (congrArg (Env M.Val) hExt.symm) cenv =
      cenv.extend (heldNames r results) (heldValues M r (nothings M out)) := by
    have hNilN : cast (congrArg Names hEmpty) (heldNames r results) = .nil := by
      cases cast (congrArg Names hEmpty) (heldNames r results); rfl
    have hHeq : HEq (cenv.extend (heldNames r results) (heldValues M r (nothings M out))) cenv := by
      rw [heldValues_nothings M r out]
      have h1 := env_extend_cast cenv hEmpty (heldNames r results)
        (cast (congrArg (HList M.Val) hEmpty.symm) .nil)
      rw [hNilN, cast_cast, cast_eq] at h1
      exact h1.symm
    exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
  rw [closedTerm_denote_castCT, Process.bind_map, hCenv]
  exact hRest path (env.extend results (nothings M out)) _ s cont (hEnv.extend M results _) hPath hWNRest

private theorem specializeTerm_sound_give {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {τ : V.Ty} {H : Holders}
    (key : Key) (kind : FlowKind) (getters : List Role) (here : r ∈ H)
    (x : Var Γ ⟨τ, H⟩) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.give (τ := τ) (H := H) kind getters here) (.cons x .nil) (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  have hIn : r ∈ Holders.ofList (getters ++ H) :=
    Holders.mem_ofList.mpr (List.mem_append_right _ here)
  have hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) =
      Δ.insert resName τ := by
    rw [heldNames_cons_pos hIn,
      ctx_extend_cast Δ (held_cons_pos r ⟨τ, Holders.ofList (getters ++ H)⟩ [] hIn).symm]; rfl
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx
        (.op key (.give (τ := τ) (H := H) kind getters here) (.cons x .nil) (.cons resName .nil) rest)).denote
        M fullTable path cenv s =
      ((specOp through key ((ResidualOp.give kind getters τ).mapPeers ρ) (.cons (varHeld hCtx x here) .nil)).denote
        M fullTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through ρ r
            (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl).denote
          M fullTable path ((cenv.extend .nil out.1).insert resName ((cenv.extend .nil out.1).get (varHeld hCtx x here))) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ ((Process.call (ROp.give kind getters ⟨path, key⟩ τ (reveal M (a := ⟨τ, H⟩) here (env.get x)))
      fun _ => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecG := hSpec through key ((ResidualOp.give kind getters τ).mapPeers ρ)
    (.cons (varHeld hCtx x here) .nil) path cenv s hPath
  rw [hSpecG, Process.bind_assoc, Process.bind_map]
  change _ = ((h.clause (ROp.give kind (getters.map ρ) ⟨path, key⟩ τ (cenv.get (varHeld hCtx x here))) s).bind fun a =>
    (((specializeTerm specOp fnLift specApply retryCfg through ρ r
        (hCtx.extend (.cons resName .nil)) rest).castCT hExt rfl).denote
      M fullTable path (cenv.insert resName (cenv.get (varHeld hCtx x here))) a.2).bind
      fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2)
  rw [env_get_varHeld M hEnv x here]
  congr 1; funext out
  have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) (cenv.insert resName (reveal M (a := ⟨τ, H⟩) here (env.get x))) =
      cenv.extend (heldNames r (.cons resName .nil))
        (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) .nil)) := by
    have hHeq : HEq
        (cenv.extend (heldNames r (.cons resName .nil))
          (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ (reveal M (a := ⟨τ, H⟩) here (env.get x))) .nil)))
        (cenv.insert resName (reveal M (a := ⟨τ, H⟩) here (env.get x))) := by
      rw [heldNames_cons_pos hIn, heldValues_cons_pos M hIn, reveal_hide]
      exact env_extend_cast cenv hRes.symm (HList.cons resName .nil)
        (HList.cons (reveal M (a := ⟨τ, H⟩) here (env.get x)) .nil)
    exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
  rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest

private theorem specializeTerm_sound_get {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (τ : V.Ty) (H : Holders)
    (kind : FlowKind) (giver : Role) (getters : List Role) (mine : r ∈ getters)
    (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (getters ++ H)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  have hIn : r ∈ Holders.ofList (getters ++ H) :=
    Holders.mem_ofList.mpr (List.mem_append_left _ mine)
  have hRes : held r [⟨τ, Holders.ofList (getters ++ H)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx
        (.op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest)).denote
        M fullTable path cenv s =
      ((specOp through key ((ResidualOp.get kind giver τ).mapPeers ρ) .nil).denote
        M fullTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through ρ r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ ((Process.call (ROp.get kind giver ⟨path, key⟩ τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecG := hSpec through key ((ResidualOp.get kind giver τ).mapPeers ρ)
    .nil path cenv s hPath
  rw [hSpecG, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, Env.all, ResidualOp.replyOf]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest

private theorem specializeTerm_sound_keep {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {τ : V.Ty} {H : Holders}
    (key : Key) (H' : Holders) (same : r ∈ H ↔ r ∈ H')
    (x : Var Γ ⟨τ, H⟩) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, H'⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.keep (τ := τ) (H := H) H' same) (.cons x .nil) (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
      (env.extend (.cons resName .nil) (.cons (carry M same (env.get x)) .nil)))).bind cont) s = _
  by_cases hIn : r ∈ H
  · rw [dite_eq_left hIn]
    conv => rhs; rw [ClosedTerm.denote]
    have hIn' : r ∈ H' := same.mp hIn
    have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil)) = Δ.insert resName τ := by
      rw [heldNames_cons_pos hIn', ctx_extend_cast Δ (held_cons_pos r ⟨τ, H'⟩ [] hIn').symm]; rfl
    have hRevCarry : reveal M hIn' (carry M same (env.get x)) = reveal M hIn (env.get x) := by
      simp [reveal, carry]
    have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) (cenv.insert resName (cenv.get (varHeld hCtx x hIn))) =
        cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
          (heldValues M r (.cons (carry M same (env.get x)) .nil)) := by
      rw [env_get_varHeld M hEnv x hIn, ← hRevCarry]
      have hHeq : HEq
          (cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
            (heldValues M r (.cons (carry M same (env.get x)) .nil)))
          (cenv.insert resName (reveal M hIn' (carry M same (env.get x)))) := by
        rw [heldNames_cons_pos hIn', heldValues_cons_pos M hIn']
        exact env_extend_cast cenv (held_cons_pos r ⟨τ, H'⟩ [] hIn').symm (HList.cons resName .nil)
          (HList.cons (reveal M hIn' (carry M same (env.get x))) .nil)
      exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
    rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
    exact hRest path _ _ s cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest
  · rw [dite_eq_right hIn]
    have hOut' : r ∉ H' := fun m => hIn (same.mpr m)
    have hExt : Δ.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil)) = Δ := by
      rw [heldNames_cons_neg hOut', ctx_extend_cast Δ (held_cons_neg r ⟨τ, H'⟩ [] hOut').symm]; rfl
    have hCenvEq : cast (congrArg (Env M.Val) hExt.symm) cenv =
        cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
          (heldValues M r (.cons (carry M same (env.get x)) .nil)) := by
      have hHeq : HEq
          (cenv.extend (heldNames r (.cons (a := ⟨τ, H'⟩) resName .nil))
            (heldValues M r (.cons (carry M same (env.get x)) .nil))) cenv := by
        rw [heldNames_cons_neg hOut', heldValues_cons_neg M hOut']
        exact env_extend_cast cenv (held_cons_neg r ⟨τ, H'⟩ [] hOut').symm .nil .nil
      exact eq_of_heq ((cast_heq _ _).trans hHeq.symm)
    rw [closedTerm_denote_castCT, Process.bind_map, hCenvEq]
    exact hRest path _ _ s cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest

private theorem specializeTerm_sound_own {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (kind : GivenKind V) (hearers : List Role)
    (opTys : List (LTy V)) (τ : V.Ty) (typed : kind.Typed (opTys.map LTy.ty) τ)
    (here : ∀ a ∈ opTys, r ∈ a.holders) (operands : HList (Var Γ) opTys) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (r :: hearers)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  have hIn : r ∈ Holders.ofList (r :: hearers) := Holders.mem_ofList.mpr List.mem_cons_self
  have hRes : held r [⟨τ, Holders.ofList (r :: hearers)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx
        (.op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest)).denote
        M fullTable path cenv s =
      ((specOp through key ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers ρ)
          (varsAllHeld hCtx here operands)).denote
        M fullTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through ρ r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ ((Process.call (ROp.own kind hearers ⟨path, key⟩ (opTys.map LTy.ty)
        (HList.ofLocated M (revealAll M here (env.all operands))) τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecO := hSpec through key
    ((ResidualOp.own kind hearers (opTys.map LTy.ty) τ).mapPeers ρ)
    (varsAllHeld hCtx here operands) path cenv s hPath
  rw [hSpecO, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, ResidualOp.replyOf]
  rw [env_all_varsAllHeld M hEnv here operands]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest

private theorem specializeTerm_sound_hear {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} (key : Key) (kind : GivenKind V) (owner : Role) (hearers : List Role)
    (τ : V.Ty) (mine : r ∈ hearers) (resName : Name)
    (rest : Term (roleDialect V hs r) (Γ.extend (.cons (a := ⟨τ, Holders.ofList (owner :: hearers)⟩) resName .nil)) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend (.cons resName .nil)) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  have hIn : r ∈ Holders.ofList (owner :: hearers) :=
    Holders.mem_ofList.mpr (List.mem_cons_of_mem _ mine)
  have hRes : held r [⟨τ, Holders.ofList (owner :: hearers)⟩] = [τ] := held_cons_pos r _ [] hIn
  have hRHS : (specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx
        (.op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest)).denote
        M fullTable path cenv s =
      ((specOp through key ((ResidualOp.hear kind owner τ).mapPeers ρ) .nil).denote
        M fullTable path cenv s).bind fun out =>
        ((specializeTerm specOp fnLift specApply retryCfg through ρ r
            (hCtx.extend (.cons resName .nil)) rest).castCT
          (ctx_extend_cast Δ hRes (heldNames r (.cons resName .nil))).symm rfl).denote
          M fullTable path
          (cenv.extend (cast (congrArg Names hRes) (heldNames r (.cons resName .nil))) out.1) out.2 := rfl
  rw [Term.denote_op, hRHS]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ ((Process.call (ROp.hear kind owner ⟨path, key⟩ τ)
      fun v => Process.done (HList.cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ v) HList.nil)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend (.cons resName .nil) vs))).bind cont) s = _
  rw [mapR_bind, Process.bind_assoc]
  dsimp only [mapR, Process.bind]
  rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial)]
  have hSpecH := hSpec through key ((ResidualOp.hear kind owner τ).mapPeers ρ)
    .nil path cenv s hPath
  rw [hSpecH, Process.bind_assoc, Process.bind_map]
  dsimp only [ResidualOp.mapPeers, ResidualOp.toROp, Env.all, ResidualOp.replyOf]
  congr 1; funext out
  have hOutEq : cast (congrArg (HList M.Val) hRes)
      (heldValues M r (.cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ out.1) .nil)) =
      .cons out.1 .nil := by
    rw [heldValues_cons_pos M hIn, reveal_hide, cast_cast]; rfl
  conv => rhs; rw [← hOutEq, closedTerm_denote_castExt M fullTable hRes (heldNames r (.cons resName .nil))]
  exact hRest path _ _ out.2 cont (hEnv.extend M (.cons resName .nil) _) hPath hWNRest

private theorem specializeTerm_sound_apply {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (hApply : ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
      RetryCfgOk M fullTable h retryCfg →
      ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
      (through : List Key) (ρ : Role → Role) (r : Role)
      (path : List Frame) (ins : HList (RV M r) hdr.ins)
      (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
      Frame.applications path = through →
      (∀ b site ag, retryCfg = some (b, site, ag) → Shape.noNestedAttempt site through hdr.shape = true) →
      h.run (retryOfCfg M retryCfg) ((mapR M ρ (rTable hdr callee r path ins)).bind cont) s =
        ((specApply retryCfg callee through ρ r).2.denote M fullTable path
          (Env.empty.extend (specApply retryCfg callee through ρ r).1 (heldValues M r ins)) s).bind
          fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2)
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    (hRC : RetryCfgOk M fullTable h retryCfg)
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs : List (LTy V)} {hdr : ProtocolHeader V}
    (key : Key) (callee : Member hs.protocols hdr) (roles : List Role)
    (distinct : roles.Nodup) (covers : roles.length = hdr.roles)
    (opTys : List (LTy V)) (fits : Fits opTys (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (operands : HList (Var Γ) opTys)
    (results : Names (hdr.outs.map (LTy.map (RoleMap.ofList roles distinct).to)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.op key (.apply callee roles distinct covers opTys fits) operands results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  have hWNRest : ∀ b site ag, retryCfg = some (b, site, ag) →
      RoleTermWellNested M fnTable rTable r site through rest :=
    fun b site ag hc => (hWN b site ag hc).2
  rw [Term.denote_op]
  conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
  let rm := RoleMap.ofList roles distinct
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ (((mapR M rm.to (rTable hdr callee (rm.back r) (path ++ [Frame.application key])
      (enterAll M rm r (fitAllRV M fits (env.all operands))))).map (leaveAll M rm r)).bind
      fun vs => rest.denote (roleSem M r fnTable rTable) path (env.extend results vs))).bind cont) s = _
  rw [mapR_bind, mapR_map, mapR_comp, Process.bind_assoc, Process.bind_map]
  have hPath' : Frame.applications (path ++ [Frame.application key]) = through ++ [key] := by
    rw [Frame.applications_append, hPath]; rfl
  have hCalWN : ∀ b site ag, retryCfg = some (b, site, ag) →
      Shape.noNestedAttempt site (through ++ [key]) hdr.shape = true :=
    fun b site ag hc => (hWN b site ag hc).1
  rw [env_all_fitVars M hEnv rm fits operands, Process.bind_assoc]
  have hApp := hApply retryCfg hRC callee (through ++ [key]) (fun q => ρ (rm.to q)) (rm.back r)
    (path ++ [Frame.application key]) (enterAll M rm r (fitAllRV M fits (env.all operands))) s
    (fun a => (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
      (env.extend results (leaveAll M rm r a)))).bind cont) hPath' hCalWN
  rw [hApp]
  congr 1; funext out
  have hOut : held r (hdr.outs.map (LTy.map rm.to)) = held (rm.back r) hdr.outs :=
    held_map_roleMap rm r hdr.outs
  have hLeave : cast (congrArg (HList M.Val) hOut)
      (heldValues M r (leaveAll M rm r (unheldValues M (rm.back r) out.1))) = out.1 := by
    rw [heldValues_leaveAll, heldValues_unheldValues, cast_cast, cast_eq]
  conv => rhs; rw [← hLeave, closedTerm_denote_castExt M fullTable hOut (heldNames r results)]
  exact hRest path (env.extend results (leaveAll M rm r (unheldValues M (rm.back r) out.1)))
    _ out.2 cont (hEnv.extend M results _) hPath hWNRest

private theorem specializeTerm_sound_choose {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs mid : List (LTy V)} {t : LTy V}
    (key : Key) (w : Holders) (c : Var Γ t) (ok : t.ty = .bool ∧ r ∈ t.holders ∧ r ∈ w)
    (gives : ∀ a, a ∈ mid → (roleDialect V hs r).Gives w a)
    (onTrue onFalse : Term (roleDialect V hs r) Γ mid)
    (results : Names mid) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hTrue : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx onTrue)
    (hFalse : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx onFalse)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.choose key w c ok gives onTrue onFalse results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  rw [Term.denote_choose]
  conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
  change h.run (retryOfCfg M retryCfg)
    ((mapR M ρ ((bif asBool M ok.1 (reveal M ok.2.1 (env.get c)) then
      onTrue.denote (roleSem M r fnTable rTable) path env
    else onFalse.denote (roleSem M r fnTable rTable) path env).bind
      fun mids => rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s = _
  have hBool : cenv.get (cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)) =
      asBool M ok.1 (reveal M ok.2.1 (env.get c)) := by
    unfold asBool
    rw [← env_get_varHeld M hEnv c ok.2.1]
    have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
        cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
      intro _ _ e _; subst e; rfl
    exact hc ok.1 _
  rw [hBool, mapR_bind, Process.bind_assoc, Process.bind_assoc]
  cases asBool M ok.1 (reveal M ok.2.1 (env.get c)) with
  | false =>
      dsimp only [cond]
      rw [hFalse path env cenv s _ hEnv hPath (fun b site ag hc => (hWN b site ag hc).2.1)]
      congr 1; funext out
      have hEx := hEnv.extend M results (unheldValues M r out.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ out.2 cont hEx hPath (fun b site ag hc => (hWN b site ag hc).2.2)
  | true =>
      dsimp only [cond]
      rw [hTrue path env cenv s _ hEnv hPath (fun b site ag hc => (hWN b site ag hc).1)]
      congr 1; funext out
      have hEx := hEnv.extend M results (unheldValues M r out.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ out.2 cont hEx hPath (fun b site ag hc => (hWN b site ag hc).2.2)

private theorem specializeTerm_sound_loop {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs carried each : List (LTy V)}
    (key : Key) (ps : Holders) (times : Times (roleDialect V hs r) ps Γ)
    (gives : ∀ a, a ∈ carried ++ each → (roleDialect V hs r).Gives ps a)
    (initial : HList (Var Γ) carried)
    (idxNm : Name) (carriedInNames : Names carried)
    (body : Term (roleDialect V hs r) (Γ.extend (.cons (a := LTy.index ps) idxNm carriedInNames)) (carried ++ each))
    (results : Names (carried ++ each.map (LTy.collected times.size)))
    (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hBody : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index ps) idxNm carriedInNames)) ΔB),
      SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtxB body)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.loop key ps times gives initial (.cons idxNm carriedInNames) body results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  rw [Term.denote_loop]
  conv => rhs; rw [specializeTerm]; dsimp only
  rw [mapR_bind, Process.bind_assoc]
  have hTimesEq : (specializeTimes hCtx times).eval M cenv =
      (roleSem M r fnTable rTable).times times env := by
    cases times with
    | fixed _ => rfl
    | value cnt ok =>
        dsimp only [specializeTimes, ClosedTimes.eval, Semantics.times, roleSem, asNat]
        rw [← env_get_varHeld M hEnv cnt ok.2.1]
        have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
            cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
          intro _ _ e _; subst e; rfl
        exact hc ok.1 _
  have hSize : (specializeTimes hCtx times).size = times.size := specializeTimes_size hCtx times
  have hBodyOut : held r (carried ++ each) = held r carried ++ held r each :=
    held_append r carried each
  have hResTy : held r (carried ++ each.map (LTy.collected times.size)) =
      held r carried ++ (held r each).map (fun τ => .seq τ (specializeTimes hCtx times).size) := by
    rw [held_append, held_map_collected, hSize]
  have hLoopProof : ∀ (idxOpt : Option Name)
      (hCtxB : CtxRel r (Γ.extend (.cons idxNm carriedInNames))
        (loopBodyCtx Δ idxOpt (heldNames r carriedInNames)))
      (hEnvStep : ∀ (i : Nat) (cv : HList (RV M r) carried),
        EnvRel M r hCtxB
          (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) cv))
          (loopBodyEnv M cenv idxOpt i (heldNames r carriedInNames) (heldValues M r cv))),
      h.run (retryOfCfg M retryCfg)
        ((mapR M ρ (Process.iterate ((roleSem M r fnTable rTable).times times env)
            ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
              (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
              key path env)
            0 (env.all initial, HList.empties each))).bind fun ls =>
          (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
            (env.extend results (ls.1.append ((roleSem M r fnTable rTable).collected times.size ls.2))))).bind cont) s =
      ((ClosedTerm.loop key (specializeTimes hCtx times) (varsHeld hCtx initial) idxOpt
          (heldNames r carriedInNames)
          ((specializeTerm specOp fnLift specApply retryCfg through ρ r hCtxB body).castCT rfl hBodyOut)
          (cast (congrArg Names hResTy) (heldNames r results))
          ((specializeTerm specOp fnLift specApply retryCfg through ρ r (hCtx.extend results) rest).castCT
            (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl)).denote
        M fullTable path cenv s).bind fun out =>
        h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 := by
    intro idxOpt hCtxB hEnvStep
    conv => rhs; rw [ClosedTerm.denote]
    rw [hTimesEq, env_all_varsHeld M hEnv initial, ← heldAcc_empties M r each, Process.bind_assoc]
    let n0 := (roleSem M r fnTable rTable).times times env
    suffices hIter : ∀ (n i : Nat)
        (ls : HList (RV M r) carried × HList (fun a => List (RV M r a)) each)
        (st0 : HList M.Val σ),
        h.run (retryOfCfg M retryCfg)
          ((mapR M ρ (Process.iterate n
              ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                key path env)
              i ls)).bind fun lsEnd =>
            (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
              (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont) st0 =
        (Process.iterate n
            (fun j (cls : (HList M.Val (held r carried) × HList (fun τ => List (M.Val τ)) (held r each)) × HList M.Val σ) =>
              (((specializeTerm specOp fnLift specApply retryCfg through ρ r hCtxB body).castCT rfl hBodyOut).denote
                  M fullTable (path ++ [Frame.iteration key j])
                  (loopBodyEnv M cenv idxOpt j (heldNames r carriedInNames) cls.1.1) cls.2).bind fun out =>
                let sp := HList.split (held r carried) out.1
                .done ((sp.1, cls.1.2.push sp.2), out.2))
            i ((heldValues M r ls.1, heldAcc M r ls.2), st0)).bind fun clsEnd =>
          (((specializeTerm specOp fnLift specApply retryCfg through ρ r (hCtx.extend results) rest).castCT
              (ctx_extend_cast Δ hResTy (heldNames r results)).symm rfl).denote
            M fullTable path
            (cenv.extend (cast (congrArg Names hResTy) (heldNames r results))
              (clsEnd.1.1.append (closedCollected M (specializeTimes hCtx times).size clsEnd.1.2)))
            clsEnd.2).bind fun out =>
            h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 from
      hIter n0 0 (env.all initial, HList.empties each) s
    intro n
    induction n with
    | zero =>
        intro i ls st0
        dsimp only [Process.iterate, mapR, Process.bind]
        have hValEq : cast (congrArg (HList M.Val) hResTy)
            (heldValues M r (ls.1.append ((roleSem M r fnTable rTable).collected times.size ls.2))) =
            (heldValues M r ls.1).append (closedCollected M (specializeTimes hCtx times).size (heldAcc M r ls.2)) := by
          rw [heldValues_append, heldValues_collected M fnTable rTable]
          have hValCast : ∀ {s1 s2 : Option Nat} (hs : s2 = s1)
              {ts1 ts2 : List V.Ty}
              (h1 : ts1 = held r carried ++ ts2)
              (h2 : ts2 = (held r each).map (fun τ => .seq τ s1))
              (hr : ts1 = held r carried ++ (held r each).map (fun τ => .seq τ s2))
              (x : HList M.Val (held r carried)) (y : HList (fun τ => List (M.Val τ)) (held r each)),
              cast (congrArg (HList M.Val) hr)
                (cast (congrArg (HList M.Val) h1.symm)
                  (x.append (cast (congrArg (HList M.Val) h2.symm) (closedCollected M s1 y)))) =
                x.append (closedCollected M s2 y) := by
            intro _ _ hs _ _ h1 h2 hr _ _; subst hs; subst h2; subst h1; rfl
          exact hValCast hSize (held_append _ _ _) (held_map_collected _ _ _) hResTy _ _
        rw [← hValEq, closedTerm_denote_castExt M fullTable hResTy (heldNames r results)]
        exact hRest path _ _ st0 cont (hEnv.extend M results _) hPath (fun b site ag hc => (hWN b site ag hc).2)
    | succ m ihM =>
        intro i ls st0
        dsimp only [Process.iterate, Semantics.loopStep]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M ρ (((body.denote (roleSem M r fnTable rTable) (path ++ [Frame.iteration key i])
              (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) ls.1))).bind
            fun a => Process.done ((HList.split carried a).1, ls.2.push (HList.split carried a).2)).bind
            fun a2 => Process.iterate m
              ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                key path env) (i + 1) a2)).bind fun lsEnd =>
            (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
              (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont) st0 = _
        rw [mapR_bind, mapR_bind, Process.bind_assoc, Process.bind_assoc, Process.bind_assoc,
          closedTerm_denote_castCT, cast_eq, Process.bind_map, Process.bind_assoc]
        have hPathI : Frame.applications (path ++ [Frame.iteration key i]) = through := by
          rw [Frame.applications_append, hPath]; exact List.append_nil _
        have hStepBody := hBody hCtxB (path ++ [Frame.iteration key i])
          (env.extend (.cons idxNm carriedInNames) (.cons (hide M r (LTy.index ps) i) ls.1))
          (loopBodyEnv M cenv idxOpt i (heldNames r carriedInNames) (heldValues M r ls.1)) st0
          (fun a =>
            (mapR M ρ (Process.done ((HList.split carried a).1, ls.2.push (HList.split carried a).2))).bind fun a2 =>
              (mapR M ρ (Process.iterate m
                ((roleSem M r fnTable rTable).loopStep ps (.cons idxNm carriedInNames)
                  (fun path' env' => body.denote (roleSem M r fnTable rTable) path' env')
                  key path env) (i + 1) a2)).bind fun lsEnd =>
                (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path
                  (env.extend results (lsEnd.1.append ((roleSem M r fnTable rTable).collected times.size lsEnd.2))))).bind cont)
          (hEnvStep i ls.1) hPathI (fun b site ag hc => (hWN b site ag hc).1)
        rw [hStepBody]
        congr 1; funext out
        dsimp only [mapR, Process.bind]
        have hSp := heldValues_split M r (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hSp
        rw [hSp.1, hSp.2, ← heldAcc_push M r ls.2]
        exact ihM (i + 1) _ out.2
  by_cases hIn : r ∈ ps
  · rw [dite_eq_left hIn]
    refine hLoopProof (some idxNm) _ fun i cv => ?_
    have h1 := (hEnv.insert_held M idxNm (a := LTy.index ps) hIn (hide M r (LTy.index ps) i)).extend M carriedInNames cv
    rw [reveal_hide] at h1
    exact h1
  · rw [dite_eq_right hIn]
    refine hLoopProof none _ fun i cv => ?_
    exact (hEnv.insert_unheld M idxNm (a := LTy.index ps) hIn (hide M r (LTy.index ps) i)).extend M carriedInNames cv

private theorem specializeTerm_sound_attempt {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
    {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
    (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
    (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
      {hdr : ProtocolHeader V} → Member hs.protocols hdr →
      List Key → (Role → Role) → (r : Role) →
      (inputs : Names (held r hdr.ins)) ×
        ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
    (through : List Key) (ρ : Role → Role) (r : Role)
    (retryCfg : Option (Nat × Site × StackAgain V fullFns σ))
    (hRC : RetryCfgOk M fullTable h retryCfg)
    {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
    {outs mid : List (LTy V)} (key : Key) (w : Holders) (owns : (roleDialect V hs r).Attempt w)
    (idxNm : Name)
    (body : Term (roleDialect V hs r) (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) mid)
    (results : Names mid) (rest : Term (roleDialect V hs r) (Γ.extend results) outs)
    (hBody : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) ΔB),
      SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtxB body)
    (hBodyNone : ∀ {ΔB : Ctx V.Ty} (hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) ΔB),
      SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r none hCtxB body)
    (hRest : SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg
      (hCtx.extend results) rest) :
    SpecTermHyp M fullTable h specOp fnTable rTable fnLift specApply through ρ r retryCfg hCtx
      (.attempt key w owns (.cons idxNm .nil) body results rest) := by
  intro path env cenv s _ cont hEnv hPath hWN
  rw [Term.denote_attempt]
  conv => rhs; rw [specializeTerm]; dsimp only
  rw [mapR_bind, Process.bind_assoc]
  by_cases hw : r ∈ w
  · have hBeg : (roleSem M r fnTable rTable).begin w key path =
        Process.call (ROp.begin ⟨path, key⟩) fun n => Process.done (hide M r (LTy.index w) n) := by
      dsimp only [roleSem]; exact ite_eq_left hw
    have hSet : (roleSem M r fnTable rTable).settle w key path =
        Process.call (ROp.settle ⟨path, key⟩) fun _ => Process.done () := by
      dsimp only [roleSem]; exact ite_eq_left hw
    rw [hBeg, hSet, dite_eq_left hw]
    dsimp only [mapR, Process.bind]
    have hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil))
        (Δ.extend (.cons (a := Ty.nat) idxNm .nil)) :=
      hCtx.insert_held idxNm (a := LTy.index w)
    have hNonRetry : ∀ (hNotBeg : (retryOfCfg M retryCfg).begins (.begin ⟨path, key⟩) = none),
        h.run (retryOfCfg M retryCfg)
          (.call (.begin ⟨path, key⟩) fun n =>
            (mapR M ρ (body.denote (roleSem M r fnTable rTable) path
              (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) n) .nil)))).bind
              fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s =
        ((ClosedTerm.letBind
            (.letBind (specOp through key .begin .nil) (.cons (a := Ty.nat) idxNm .nil)
              (.seq (specializeTerm specOp fnLift specApply retryCfg through ρ r hCtxB body)
                (specOp through key .settle .nil)))
            (heldNames r results)
            (specializeTerm specOp fnLift specApply retryCfg through ρ r (hCtx.extend results) rest)).denote
          M fullTable path cenv s).bind fun out =>
          h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2 := by
      intro hNotBeg
      rw [handler_run_call_nonBegin M h _ _ hNotBeg]
      dsimp only [ClosedTerm.denote]
      rw [hSpec through key .begin .nil path cenv s hPath, Process.bind_assoc,
        Process.bind_assoc, Process.bind_map]
      dsimp only [ResidualOp.toROp, Env.all, ResidualOp.replyOf]
      congr 1; funext outB
      have hInsEnv : EnvRel M r hCtxB
          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) outB.1) .nil))
          (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons outB.1 .nil)) := by
        have h1 := hEnv.insert_held M idxNm hw (hide M r (LTy.index w) outB.1)
        rw [reveal_hide] at h1
        exact h1
      rw [Process.bind_assoc,
        hBody hCtxB path _ _ outB.2 _ hInsEnv hPath (fun b site ag hc => (hWN b site ag hc).2.1)]
      congr 1; funext outM
      rw [handler_run_call_nonBegin M h _ _ (retryOfCfg_not_begin M retryCfg _ trivial),
        hSpec through key .settle .nil path _ outM.2 hPath,
        Process.bind_map, Process.bind_map]
      dsimp only [ResidualOp.toROp, Env.all, ResidualOp.replyOf]
      congr 1; funext outS
      have hEx := hEnv.extend M results (unheldValues M r outM.1)
      rw [heldValues_unheldValues] at hEx
      exact hRest path _ _ outS.2 cont hEx hPath (fun b site ag hc => (hWN b site ag hc).2.2)
    cases retryCfg with
    | none =>
        dsimp only
        simpa only [mapR_bind, mapR, Process.bind_assoc, Process.bind] using hNonRetry rfl
    | some cfg =>
        cases cfg with
        | mk bound sr =>
            cases sr with
            | mk retrySite again =>
                dsimp only
                by_cases hSite : (⟨through, key⟩ : Site) = retrySite
                · rw [ite_eq_left hSite]
                  have hOccSite : (⟨path, key⟩ : Occurrence).site = retrySite := by
                    simpa [Occurrence.site, hPath] using hSite
                  have hBegHit : (retryOf M (some (bound, retrySite))).begins (.begin ⟨path, key⟩) =
                      some (.declared .exhausted ⟨path, key⟩, fun i => i) := by
                    dsimp only [retryOf]; exact ite_eq_left hOccSite
                  dsimp only [ClosedTerm.denote, retryOfCfg]
                  conv => lhs; rw [Handler.run, hBegHit]
                  dsimp only
                  have hRetr : (retryOf M (some (bound, retrySite))).retriable = Stop.isAbort := rfl
                  have hBnd : (retryOf M (some (bound, retrySite))).bound = bound := rfl
                  rw [hRetr, hBnd]
                  dsimp only [RetryCfgOk] at hRC
                  rw [← hRC]
                  have hKeyEq : retrySite.key = key := by
                    cases hSite; rfl
                  have hBodyEq : ∀ (i : Nat) (s' : HList M.Val σ),
                      h.inside (retryOf M (some (bound, retrySite))) i
                        ((mapR M ρ ((body.denote (roleSem M r fnTable rTable) path
                            (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))).bind
                          fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                            rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s' =
                      ((Process.markOwn M (.attempt key i)
                          ((specializeTerm specOp fnLift specApply none through ρ r hCtxB body).denote
                            M fullTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) s')).mapHalt
                          fun stop => ((true, stop.1), stop.2)).bind fun outM =>
                        (((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                            through ρ r (hCtx.extend results) rest).denote
                          M fullTable path (cenv.extend (heldNames r results) outM.1) outM.2).bind fun outR =>
                          h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2).mapHalt
                          fun stop => ((false, stop.1), stop.2) := by
                    intro i s'
                    rw [mapR_bind, Process.bind_assoc]
                    dsimp only [mapR, Process.bind]
                    have hNoS : NoSettleAt M retrySite
                        (mapR M ρ (body.denote (roleSem M r fnTable rTable) path
                          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil)))) :=
                      noSettleAt_mapR M ρ ((hWN bound retrySite again rfl).1 hw hSite path _ hPath)
                    rw [handler_inside_settle_bind M h bound retrySite i _ hNoS ⟨path, key⟩ hOccSite _ s',
                      hKeyEq]
                    have hInsEnv : EnvRel M r hCtxB
                        (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))
                        (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) := by
                      have h1 := hEnv.insert_held M idxNm hw (hide M r (LTy.index w) i)
                      rw [reveal_hide] at h1
                      exact h1
                    have hBodyPure := hBodyNone hCtxB path _ _ s'
                      Process.done hInsEnv hPath (fun _ _ _ hc => nomatch hc)
                    rw [Process.bind_pure] at hBodyPure
                    dsimp only [retryOfCfg] at hBodyPure
                    rw [hBodyPure, markOwn_bind, mapHalt_bind, Process.bind_assoc]
                    congr 1; funext outM
                    dsimp only [Handler.run, Process.markOwn, Process.mapHalt, Process.bind, mapR]
                    congr 1
                    have hEx := hEnv.extend M results (unheldValues M r outM.1)
                    rw [heldValues_unheldValues] at hEx
                    exact hRest path _ _ outM.2 cont hEx hPath (fun b' s' ag' hc => by
                      cases hc; exact (hWN bound retrySite again rfl).2.2)
                  have hFun : (fun i s' => h.inside (retryOf M (some (bound, retrySite))) i
                      ((mapR M ρ ((body.denote (roleSem M r fnTable rTable) path
                          (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) i) .nil))).bind
                        fun mids => .call (.settle ⟨path, key⟩) fun _ =>
                          rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s') =
                      (fun i s' => ((Process.markOwn M (.attempt key i)
                          ((specializeTerm specOp fnLift specApply none through ρ r hCtxB body).denote
                            M fullTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (i : Nat) .nil)) s')).mapHalt
                          fun stop => ((true, stop.1), stop.2)).bind fun outM =>
                        (((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                            through ρ r (hCtx.extend results) rest).denote
                          M fullTable path (cenv.extend (heldNames r results) outM.1) outM.2).bind fun outR =>
                          h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2).mapHalt
                          fun stop => ((false, stop.1), stop.2)) := by
                    funext i s'; exact hBodyEq i s'
                  rw [hFun, Process.bind_assoc]
                  exact attempts_bind_settle M (.declared .exhausted ⟨path, key⟩)
                    (StackAgain.eval M fullTable again)
                    (fun j s' => Process.markOwn M (.attempt key j)
                      ((specializeTerm specOp fnLift specApply none through ρ r hCtxB body).denote
                        M fullTable path (cenv.extend (.cons (a := Ty.nat) idxNm .nil) (.cons (j : Nat) .nil)) s'))
                    (fun a st => ((specializeTerm specOp fnLift specApply (some (bound, retrySite, again))
                        through ρ r (hCtx.extend results) rest).denote
                      M fullTable path (cenv.extend (heldNames r results) a) st).bind fun outR =>
                      h.run (retryOf M (some (bound, retrySite))) (cont (unheldValues M r outR.1)) outR.2)
                    s bound 0 s
                · rw [ite_eq_right hSite]
                  have hOccNe : (⟨path, key⟩ : Occurrence).site ≠ retrySite := by
                    simpa [Occurrence.site, hPath] using hSite
                  have hNotBeg : (retryOfCfg M (some (bound, retrySite, again))).begins (.begin ⟨path, key⟩) = none := by
                    dsimp only [retryOfCfg, retryOf]
                    exact ite_eq_right hOccNe
                  simpa only [mapR_bind, mapR, Process.bind_assoc, Process.bind] using hNonRetry hNotBeg
  · have hBeg : (roleSem M r fnTable rTable).begin w key path =
        Process.done (hide M r (LTy.index w) 0) := by
      dsimp only [roleSem]; exact ite_eq_right hw
    have hSet : (roleSem M r fnTable rTable).settle w key path = Process.done () := by
      dsimp only [roleSem]; exact ite_eq_right hw
    rw [hBeg, hSet, dite_eq_right hw]
    conv => rhs; rw [ClosedTerm.denote]
    dsimp only [mapR, Process.bind]
    rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
    have hCtxB : CtxRel r (Γ.extend (.cons (a := LTy.index w) idxNm .nil)) Δ :=
      hCtx.insert_unheld idxNm (a := LTy.index w) hw
    have hInsEnv : EnvRel M r hCtxB
        (env.extend (.cons (a := LTy.index w) idxNm .nil) (.cons (hide M r (LTy.index w) (0 : Nat)) .nil)) cenv :=
      hEnv.insert_unheld M idxNm hw (hide M r (LTy.index w) (0 : Nat))
    rw [hBody hCtxB path _ cenv s _ hInsEnv hPath (fun b site ag hc => (hWN b site ag hc).2.1)]
    congr 1; funext outM
    have hEx := hEnv.extend M results (unheldValues M r outM.1)
    rw [heldValues_unheldValues] at hEx
    exact hRest path _ _ outM.2 cont hEx hPath (fun b site ag hc => (hWN b site ag hc).2.2)

mutual
  private theorem specializeTerm_sound {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
      {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
      (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
      {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
      (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
        {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → (Role → Role) → (r : Role) →
        (inputs : Names (held r hdr.ins)) ×
          ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
      (hApply : ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
        (through : List Key) (ρ : Role → Role) (r : Role)
        (path : List Frame) (ins : HList (RV M r) hdr.ins)
        (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
        Frame.applications path = through →
        (∀ b site ag, retryCfg = some (b, site, ag) → Shape.noNestedAttempt site through hdr.shape = true) →
        h.run (retryOfCfg M retryCfg) ((mapR M ρ (rTable hdr callee r path ins)).bind cont) s =
          ((specApply retryCfg callee through ρ r).2.denote M fullTable path
            (Env.empty.extend (specApply retryCfg callee through ρ r).1 (heldValues M r ins)) s).bind
            fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2)
      (through : List Key) (ρ : Role → Role) (r : Role) :
      ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        ∀ {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
          {outs : List (LTy V)} (t : Term (roleDialect V hs r) Γ outs)
          (path : List Frame) (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) (s : HList M.Val σ)
          {B : Type} (cont : HList (RV M r) outs → Program M B),
          EnvRel M r hCtx env cenv →
          Frame.applications path = through →
          (∀ b site ag, retryCfg = some (b, site, ag) →
            RoleTermWellNested M fnTable rTable r site through t) →
          h.run (retryOfCfg M retryCfg)
            ((mapR M ρ (t.denote (roleSem M r fnTable rTable) path env)).bind cont) s =
            ((specializeTerm specOp fnLift specApply retryCfg through ρ r hCtx t).denote
              M fullTable path cenv s).bind
              fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
    | retryCfg, _, Γ, Δ, hCtx, _, .ret exit, path, env, cenv, s, _, cont, hEnv, _, _ => by
        rw [Term.denote_ret, specializeTerm, ClosedTerm.denote]
        dsimp only [mapR, Process.bind]
        rw [env_all_varsHeld M hEnv exit, unheldValues_heldValues]
    | retryCfg, hRC, Γ, Δ, hCtx, _, .op key (.compute R lo opTys types mine here) operands results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_compute M fullTable h specOp fnTable rTable fnLift hLift specApply
          through ρ r retryCfg hCtx key R lo opTys types mine here operands results rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _, .op key (.absent items out) .nil results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_absent M fullTable h specOp fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key items out results rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.give kind getters here) (.cons x .nil) (.cons resName .nil) rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_give M fullTable h specOp hSpec fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key kind getters here x resName rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend (.cons resName .nil)) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.get τ H kind giver getters mine) .nil (.cons resName .nil) rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_get M fullTable h specOp hSpec fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key τ H kind giver getters mine resName rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend (.cons resName .nil)) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.keep H' same) (.cons x .nil) (.cons resName .nil) rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_keep M fullTable h specOp fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key H' same x resName rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend (.cons resName .nil)) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.own kind hearers opTys τ typed here) operands (.cons resName .nil) rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_own M fullTable h specOp hSpec fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key kind hearers opTys τ typed here operands resName rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend (.cons resName .nil)) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.hear kind owner hearers τ mine) .nil (.cons resName .nil) rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_hear M fullTable h specOp hSpec fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key kind owner hearers τ mine resName rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend (.cons resName .nil)) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .op key (.apply callee roles distinct covers opTys fits) operands results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_apply M fullTable h specOp fnTable rTable fnLift specApply hApply
          through ρ r retryCfg hRC hCtx key callee roles distinct covers opTys fits operands results rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _, .guard key w c ok why rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN => by
        rw [Term.denote_guard]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M ρ (bif asBool M ok.1 (reveal M ok.2.1 (env.get c)) then
            rest.denote (roleSem M r fnTable rTable) path env
          else Process.halt (.declared why ⟨path, key⟩))).bind cont) s = _
        have hBool : cenv.get (cast (congrArg (Var Δ) ok.1) (varHeld hCtx c ok.2.1)) =
            asBool M ok.1 (reveal M ok.2.1 (env.get c)) := by
          unfold asBool
          rw [← env_get_varHeld M hEnv c ok.2.1]
          have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
              cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
            intro _ _ e _; subst e; rfl
          exact hc ok.1 _
        rw [hBool]
        cases asBool M ok.1 (reveal M ok.2.1 (env.get c)) with
        | false => rfl
        | true =>
            exact specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
              through ρ r retryCfg hRC hCtx rest path env cenv s cont hEnv hPath
              (fun b site ag hc => hWN b site ag hc)
    | retryCfg, hRC, Γ, Δ, hCtx, _, .choose key w c ok gives onTrue onFalse results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_choose M fullTable h specOp fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key w c ok gives onTrue onFalse results rest
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC hCtx onTrue)
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC hCtx onFalse)
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .cases (t := t) (payloads := payloads) key ps x ok gives arms results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN => by
        rw [Term.denote_cases]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        change h.run (retryOfCfg M retryCfg)
          ((mapR M ρ ((arms.denote (roleSem M r fnTable rTable) path env (rolePick M r ok (env.get x))).bind
            fun mids => rest.denote (roleSem M r fnTable rTable) path (env.extend results mids))).bind cont) s = _
        rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
        have hv : ∃ k alts, t.ty = .variant k alts ∧ payloads = alts.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨k, alts, he, hp, _⟩ := ok; exact ⟨k, alts, he, hp⟩
        have hEq : t.ty = .variant t.ty.variantKey t.ty.alternatives := Ty.eq_variant hv
        have hPay : payloads = t.ty.alternatives.toList.map (fun τ => ⟨τ, ps⟩) := by
          obtain ⟨_, alts, he, hp⟩ := hv; rw [Ty.alternatives_of he, hp]
        have hrT : r ∈ t.holders := by obtain ⟨_, _, _, _, h1, _⟩ := ok; exact h1
        have hrPs : r ∈ ps := by obtain ⟨_, _, _, _, _, h2⟩ := ok; exact h2
        have hVal : cenv.get (cast (congrArg (Var Δ) hEq) (varHeld hCtx x hrT)) =
            cast (congrArg M.Val hEq) (reveal M hrT (env.get x)) := by
          rw [← env_get_varHeld M hEnv x hrT]
          have hc : ∀ {τ₁ τ₂ : V.Ty} (e : τ₁ = τ₂) (v : Var Δ τ₁),
              cenv.get (cast (congrArg (Var Δ) e) v) = cast (congrArg M.Val e) (cenv.get v) := by
            intro _ _ e _; subst e; rfl
          exact hc hEq _
        rw [hVal]
        have hPickEq : rolePick M r ok (env.get x) =
            cast (congrArg (Pick (RV M r)) hPay.symm)
              (liftPick M r ps (Tys.pick M t.ty.alternatives
                (cast (congrArg M.Val hEq) (reveal M hrT (env.get x))))) := by
          dsimp only [rolePick, locatedPick]
          rw [pickAt_eq_liftPick M r ps]
        rw [hPickEq]
        rw [specializeArms_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
          through ρ r retryCfg hRC ps hrPs hCtx arms hPay path env cenv s _ _ hEnv hPath
          (fun b site ag hc => (hWN b site ag hc).1)]
        congr 1; funext out
        have hEx := hEnv.extend M results (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hEx
        exact specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
          through ρ r retryCfg hRC (hCtx.extend results) rest path _ _ out.2 cont
          hEx hPath (fun b site ag hc => (hWN b site ag hc).2)
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .loop key ps times gives initial (.cons idxNm carriedInNames) body results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_loop M fullTable h specOp fnTable rTable fnLift specApply
          through ρ r retryCfg hCtx key ps times gives initial idxNm carriedInNames body results rest
          (fun hCtxB => specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC hCtxB body)
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN
    | retryCfg, hRC, Γ, Δ, hCtx, _, .block key number body results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN => by
        rw [Term.denote_block]
        conv => rhs; rw [specializeTerm]; dsimp only; rw [ClosedTerm.denote]
        rw [mapR_bind, Process.bind_assoc, Process.bind_assoc]
        have hPathB : Frame.applications (path ++ [Frame.iteration key number]) = through := by
          rw [Frame.applications_append, hPath]; exact List.append_nil _
        have hBodyS := specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
          through ρ r retryCfg hRC hCtx body (path ++ [Frame.iteration key number]) env cenv s
          (fun a => (mapR M ρ (rest.denote (roleSem M r fnTable rTable) path (env.extend results a))).bind cont)
          hEnv hPathB (fun b site ag hc => (hWN b site ag hc).1)
        rw [hBodyS]
        congr 1; funext out
        have hEx := hEnv.extend M results (unheldValues M r out.1)
        rw [heldValues_unheldValues] at hEx
        exact specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
          through ρ r retryCfg hRC (hCtx.extend results) rest path _ _ out.2 cont
          hEx hPath (fun b site ag hc => (hWN b site ag hc).2)
    | retryCfg, hRC, Γ, Δ, hCtx, _,
        .attempt key w owns (.cons idxNm .nil) body results rest,
        path, env, cenv, s, _, cont, hEnv, hPath, hWN =>
        specializeTerm_sound_attempt M fullTable h specOp hSpec fnTable rTable fnLift specApply
          through ρ r retryCfg hRC hCtx key w owns idxNm body results rest
          (fun hCtxB => specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC hCtxB body)
          (fun hCtxB => specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r none trivial hCtxB body)
          (specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
            through ρ r retryCfg hRC (hCtx.extend results) rest)
          path env cenv s cont hEnv hPath hWN

  private theorem specializeArms_sound {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
      {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
      (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp)
      {hs : Headers V} (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr)
      (hLift : ∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = fnTable hdr f)
      (specApply : Option (Nat × Site × StackAgain V fullFns σ) →
        {hdr : ProtocolHeader V} → Member hs.protocols hdr →
        List Key → (Role → Role) → (r : Role) →
        (inputs : Names (held r hdr.ins)) ×
          ClosedTerm V fullFns σ (Ctx.empty.extend inputs) (held r hdr.outs))
      (hApply : ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
        (through : List Key) (ρ : Role → Role) (r : Role)
        (path : List Frame) (ins : HList (RV M r) hdr.ins)
        (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
        Frame.applications path = through →
        (∀ b site ag, retryCfg = some (b, site, ag) → Shape.noNestedAttempt site through hdr.shape = true) →
        h.run (retryOfCfg M retryCfg) ((mapR M ρ (rTable hdr callee r path ins)).bind cont) s =
          ((specApply retryCfg callee through ρ r).2.denote M fullTable path
            (Env.empty.extend (specApply retryCfg callee through ρ r).1 (heldValues M r ins)) s).bind
            fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2)
      (through : List Key) (ρ : Role → Role) (r : Role) :
      ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        ∀ (ps : Holders) (hrPs : r ∈ ps)
          {Γ : Ctx (LTy V)} {Δ : Ctx V.Ty} (hCtx : CtxRel r Γ Δ)
          {mid payloads : List (LTy V)} (arms : Arms (roleDialect V hs r) Γ mid payloads)
          {alts : List V.Ty} (hPay : payloads = alts.map fun τ => ⟨τ, ps⟩)
          (path : List Frame) (env : Env (RV M r) Γ) (cenv : Env M.Val Δ) (s : HList M.Val σ)
          (pkVal : Pick M.Val alts)
          {B : Type} (cont : HList (RV M r) mid → Program M B),
          EnvRel M r hCtx env cenv →
          Frame.applications path = through →
          (∀ b site ag, retryCfg = some (b, site, ag) →
            RoleArmsWellNested M fnTable rTable r site through arms) →
          h.run (retryOfCfg M retryCfg)
            ((mapR M ρ (arms.denote (roleSem M r fnTable rTable) path env
              (cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps pkVal)))).bind cont) s =
            ((specializeArms specOp fnLift specApply retryCfg through ρ r ps hrPs hCtx arms hPay).denote
              M fullTable path cenv s pkVal).bind
              fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
    | _, _, _, _, _, _, _, _, _, .nil, [], _, _, _, _, _, pkVal, _, _, _, _, _ => nomatch pkVal
    | _, _, _, _, _, _, _, _, _, .nil, _ :: _, hPay, _, _, _, _, _, _, _, _, _, _ => nomatch hPay
    | _, _, _, _, _, _, _, _, _, .cons _ _ _, [], hPay, _, _, _, _, _, _, _, _, _, _ => nomatch hPay
    | retryCfg, hRC, ps, hrPs, Γ, Δ, hCtx, _, a :: restP,
        .cons (.cons nm .nil) arm more, τ :: altsRest, hPay, path, env, cenv, s, pkVal, _, cont,
        hEnv, hPath, hWNA => by
        have hHead : a = ⟨τ, ps⟩ := (List.cons.inj hPay).1
        have hTail : restP = altsRest.map (fun τ => ⟨τ, ps⟩) := (List.cons.inj hPay).2
        cases pkVal with
        | here v =>
            have hCtxA : CtxRel r (Γ.extend (.cons (a := a) nm .nil))
                (Δ.extend (.cons (a := τ) nm .nil)) := by
              rw [show Γ.extend (.cons (a := a) nm .nil) = Γ.insert nm ⟨τ, ps⟩ by rw [Ctx.extend, Ctx.extend, hHead]]
              exact hCtx.insert_held nm (a := ⟨τ, ps⟩)
            have hPickH : cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps (.here v)) =
                Pick.here (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) := by
              cases hHead; cases hTail; rfl
            rw [hPickH]
            dsimp only [Arms.denote]
            conv => rhs; rw [specializeArms]; dsimp only; rw [ClosedArms.denote]
            have hInsEnv : EnvRel M r hCtxA
                (env.extend (.cons (a := a) nm .nil)
                  (.cons (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) .nil))
                (cenv.extend (.cons (a := τ) nm .nil) (.cons v .nil)) := by
              intro name' b hΓ hrb
              have hBase := hEnv.insert_held M nm hrPs (hide M r ⟨τ, ps⟩ v)
              rw [reveal_hide] at hBase
              have hEqEnv : HEq
                  (env.extend (.cons (a := a) nm .nil)
                    (.cons (cast (congrArg (RV M r) hHead.symm) (hide M r ⟨τ, ps⟩ v)) .nil))
                  (env.insert nm (hide M r ⟨τ, ps⟩ v)) := by
                cases hHead; exact HEq.rfl
              have hCtxEq : Γ.extend (.cons (a := a) nm .nil) = Γ.insert nm ⟨τ, ps⟩ := by
                rw [Ctx.extend, Ctx.extend, hHead]
              have hGet : ∀ {Γ₁ Γ₂ : Ctx (LTy V)} (e : Γ₁ = Γ₂) (e1 : Env (RV M r) Γ₁) (e2 : Env (RV M r) Γ₂),
                  HEq e1 e2 → ∀ (p1 : Γ₁.find? name' = some b) (p2 : Γ₂.find? name' = some b),
                    e1 name' b p1 = e2 name' b p2 := by
                intro _ _ e e1 e2 he p1 p2; subst e; cases eq_of_heq he; rfl
              have hΓ' : (Γ.insert nm ⟨τ, ps⟩).find? name' = some b := by rw [← hCtxEq]; exact hΓ
              rw [hGet hCtxEq _ _ hEqEnv hΓ hΓ']
              exact hBase name' b hΓ' hrb
            exact specializeTerm_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
              through ρ r retryCfg hRC hCtxA arm path _ _ s cont hInsEnv hPath
              (fun b site ag hc => (hWNA b site ag hc).1)
        | there pk' =>
            have hPickT : cast (congrArg (Pick (RV M r)) hPay.symm) (liftPick M r ps (.there pk')) =
                Pick.there (cast (congrArg (Pick (RV M r)) hTail.symm) (liftPick M r ps pk')) := by
              cases hHead; cases hTail; rfl
            rw [hPickT]
            dsimp only [Arms.denote]
            conv => rhs; rw [specializeArms]; dsimp only; rw [ClosedArms.denote]
            exact specializeArms_sound fullTable h specOp hSpec fnTable rTable fnLift hLift specApply hApply
              through ρ r retryCfg hRC ps hrPs hCtx more hTail path env cenv s pk' cont hEnv hPath
              (fun b site ag hc => (hWNA b site ag hc).2)
end

/-- Middle-level soundness: `specializeProtocolInDefs` matches `Defs.rTable` under `Handler.run`. -/
private theorem specializeProtocolInDefs_sound {fullFns : List (FnHeader V)} (fullTable : FnTable M fullFns)
    {σ : List V.Ty} (h : Handler (RSig M) (RSig M) Stop (HList M.Val σ))
    (specOp : EffectSpecializer V fullFns σ) (hSpec : SpecOpSound M fullTable h specOp) :
    ∀ {hs : Headers V} (defs : Defs V hs)
      (fnLift : ∀ {hdr}, Member hs.fns hdr → Member fullFns hdr),
      (∀ hdr (f : Member hs.fns hdr), fullTable hdr (fnLift f) = Defs.fnTable M defs hdr f) →
      ∀ (retryCfg : Option (Nat × Site × StackAgain V fullFns σ)),
        RetryCfgOk M fullTable h retryCfg →
        ∀ {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
          (through : List Key) (ρ : Role → Role) (r : Role)
          (path : List Frame) (ins : HList (RV M r) hdr.ins)
          (s : HList M.Val σ) {B : Type} (cont : HList (RV M r) hdr.outs → Program M B),
          Frame.applications path = through →
          (∀ b site ag, retryCfg = some (b, site, ag) → Shape.noNestedAttempt site through hdr.shape = true) →
          h.run (retryOfCfg M retryCfg) ((mapR M ρ (Defs.rTable M defs hdr callee r path ins)).bind cont) s =
            ((specializeProtocolInDefs specOp defs fnLift retryCfg callee through ρ r).2.denote
              M fullTable path
              (Env.empty.extend (specializeProtocolInDefs specOp defs fnLift retryCfg callee through ρ r).1
                (heldValues M r ins)) s).bind
              fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
  | _, .nil, _, _, _, _, _, m, _, _, _, _, _, _, _, _, _, _ => nomatch m
  | _, .fn _ _ _ _ rest _, fnLift, hLift, retryCfg, hRC, _, m, through, ρ, r, path, ins, s, _, cont, hP, hWN =>
      specializeProtocolInDefs_sound fullTable h specOp hSpec rest (fun f => fnLift (.tail f))
        (fun hdr f => hLift hdr (.tail f)) retryCfg hRC m through ρ r path ins s cont hP hWN
  | _, .protocol (hs := hsRest) hdrP inputsP bodyP okP rest, fnLift, hLift, retryCfg, hRC, _, .head, through, ρ, r, path, ins, s, _, cont, hP, hWN => by
      change h.run (retryOfCfg M retryCfg)
          ((mapR M ρ ((project r bodyP).denote (roleSem M r (Defs.fnTable M rest) (Defs.rTable M rest))
            path (Env.empty.extend inputsP ins))).bind cont) s =
        ((@specializeTerm V fullFns σ hsRest specOp fnLift
            (fun rc {_} m' th' ρ' r' => specializeProtocolInDefs specOp rest fnLift rc m' th' ρ' r')
            retryCfg through ρ r _ _ ((CtxRel.empty r).extend inputsP) _ (project r bodyP)).denote
          M fullTable path (Env.empty.extend (heldNames r inputsP) (heldValues M r ins)) s).bind
          fun out => h.run (retryOfCfg M retryCfg) (cont (unheldValues M r out.1)) out.2
      refine specializeTerm_sound M fullTable h specOp hSpec (Defs.fnTable M rest) (Defs.rTable M rest)
        fnLift hLift
        (fun rc {_} m' th' ρ' r' => specializeProtocolInDefs specOp rest fnLift rc m' th' ρ' r')
        (fun rc hRC' {_} callee' th' ρ' r' path' ins' s' _ cont' hP' hWN' =>
          specializeProtocolInDefs_sound fullTable h specOp hSpec rest fnLift hLift rc hRC' callee'
            th' ρ' r' path' ins' s' cont' hP' hWN')
        through ρ r retryCfg hRC ((CtxRel.empty r).extend inputsP) (project r bodyP)
        path (Env.empty.extend inputsP ins) _ s cont
        ((EnvRel.empty M r).extend M inputsP ins) hP ?_
      intro b site ag hc
      have hSh := hWN b site ag hc
      rw [okP.shaped] at hSh
      exact roleTermWellNested_of_shape M rest site r through bodyP hSh
  | _, .protocol _ _ _ _ rest, fnLift, hLift, retryCfg, hRC, _, .tail m, through, ρ, r, path, ins, s, _, cont, hP, hWN =>
      specializeProtocolInDefs_sound fullTable h specOp hSpec rest fnLift hLift retryCfg hRC m through ρ r path ins s cont hP hWN

/-! ### Level 2 soundness (`specializeStack`, `StackInit`, `StackFinish`, `StackAgain`) -/

private theorem specializeClauses_sound {hs : Headers V} (defs : Defs V hs) {r_top : Role} {state : V.Ty}
    {σ_rest : List V.Ty}
    (hBelow : Handler (RSig M) (RSig M) Stop (HList M.Val σ_rest))
    (specBelow : EffectSpecializer V hs.fns σ_rest)
    (hSpecBelow : SpecOpSound M (Defs.fnTable M defs) hBelow specBelow)
    (through : List Key) (key : Key) {ins res : List V.Ty} (op : ResidualOp V ins res)
    {Δ : Ctx V.Ty} (args : HList (Var Δ) ins) (path : List Frame) (cenv : Env M.Val Δ)
    (mine : M.Val state) (below : HList M.Val σ_rest) (hPath : Frame.applications path = through) :
    ∀ (cs : List (Clause V hs r_top state)),
      (specializeClauses defs specBelow through key op args cs).denote M (Defs.fnTable M defs)
          path cenv (.cons mine below) =
        (((hBelow.answer (Clause.answer M (Defs.fnTable M defs) (Defs.rTable M defs) cs
              (op.toROp M ⟨path, key⟩ (cenv.all args)) mine) mine below).mapHalt
            fun stop => (stop.1, .cons stop.2.1 stop.2.2)).map
          fun out => (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1.1, .cons out.1.2 out.2))
  | [] => by
      change (((specBelow through key op args).denote M (Defs.fnTable M defs) path cenv below).mapHalt
          fun stop => (stop.1, HList.cons mine stop.2)).map (fun out => (out.1, HList.cons mine out.2)) = _
      rw [hSpecBelow through key op args path cenv below hPath, Clause.answer, Handler.answer]
      dsimp only [Handler.answer]
      rw [mapHalt_map, Process.map_map, mapHalt_bind, mapHalt_mapHalt, Process.map_bind]
      simp only [Process.map_eq_bind]
      rfl
  | c :: cs => by
      dsimp only [specializeClauses, Clause.answer]
      let rop := op.toROp M ⟨path, key⟩ (cenv.all args)
      have hSiteEq : (ROp.occurrence M rop).site = ⟨through, key⟩ := by
        rw [op.toROp_occurrence M ⟨path, key⟩ (cenv.all args)]
        simp [Occurrence.site, hPath]
      have hPartEq : ROp.part M rop = op.part := op.toROp_part M ⟨path, key⟩ (cenv.all args)
      have hTakesEq : ROp.takes M rop = ins := op.toROp_takes M ⟨path, key⟩ (cenv.all args)
      have hGivesEq : ROp.gives M rop = res := op.toROp_gives M ⟨path, key⟩ (cenv.all args)
      have hIff : (c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
            c.site.takes = ins ∧ c.site.gives = res) ↔
          (c.site.site = (ROp.occurrence M rop).site ∧ some c.site.part = ROp.part M rop ∧
            c.site.takes = ROp.takes M rop ∧ c.site.gives = ROp.gives M rop) := by
        rw [hSiteEq, hPartEq, hTakesEq, hGivesEq]
      by_cases hM : c.site.site = ⟨through, key⟩ ∧ some c.site.part = op.part ∧
          c.site.takes = ins ∧ c.site.gives = res
      · have hM' := hIff.mp hM
        rw [dite_eq_left hM, dite_eq_left hM']
        have hPosEq : Ctx.positional (c.site.takes ++ [state]) =
            Ctx.empty.extend (Names.counting 0 (ins ++ [state])) := by
          unfold Ctx.positional; rw [hM.2.2.1]
        change Process.map (fun out => let sp := HList.split res out.1; (sp.1, HList.cons sp.2.single out.2))
            (Process.mapHalt (fun stop => (stop.1, HList.cons mine stop.2))
              (((specializeTerm specBelow id
                  (fun rc {_} m th ρ' r' => specializeProtocolInDefs specBelow defs id rc m th ρ' r')
                  none through id r_top
                  (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
                  c.code).castCT hPosEq (by rw [held_alone, hM.2.2.2])).denote
                M (Defs.fnTable M defs) path
                (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil)))
                below)) = _
        rw [closedTerm_denote_castCT, mapHalt_map, Process.map_map]
        have hPathClause : (ROp.occurrence M rop).path = path := by
          rw [op.toROp_occurrence M ⟨path, key⟩ (cenv.all args)]
        have hPayload : cast (congrArg (HList M.Val) hM'.2.2.1.symm) (ROp.payload M rop) =
            cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args) := by
          have hP := op.toROp_payload M ⟨path, key⟩ (cenv.all args)
          rw [← hP, cast_cast]
        have hEnvPos : EnvRel M r_top (CtxRel.positional_alone r_top (c.site.takes ++ [state]))
            (Env.positional (aloneIn M r_top (HList.append
              (cast (congrArg (HList M.Val) hM'.2.2.1.symm) (ROp.payload M rop)) (.cons mine .nil))))
            (cast (congrArg (Env M.Val) hPosEq.symm)
              (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil)))) := by
          rw [hPayload]
          have hBase := EnvRel.positional_alone M r_top
            (HList.append (cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args)) (.cons mine .nil))
          have hEqEnv : cast (congrArg (Env M.Val) hPosEq.symm)
              (Env.empty.extend (Names.counting 0 (ins ++ [state])) ((cenv.all args).append (.cons mine .nil))) =
              Env.positional (HList.append (cast (congrArg (HList M.Val) hM.2.2.1.symm) (cenv.all args)) (.cons mine .nil)) := by
            have hT := hM.2.2.1
            generalize hPosEq = hp
            generalize hT = ht at hp ⊢
            subst ht
            rfl
          rw [hEqEnv]
          exact hBase
        have hCode := specializeTerm_sound M (Defs.fnTable M defs) hBelow specBelow hSpecBelow
          (Defs.fnTable M defs) (Defs.rTable M defs) id (fun _ _ => rfl)
          (fun rc {_} m th ρ' r' => specializeProtocolInDefs specBelow defs id rc m th ρ' r')
          (fun rc hRC' {_} callee' th' ρ' r' path' ins' s' _ cont' hP' hWN' =>
            specializeProtocolInDefs_sound M (Defs.fnTable M defs) hBelow specBelow hSpecBelow
              defs id (fun _ _ => rfl) rc hRC' callee' th' ρ' r' path' ins' s' cont' hP' hWN')
          through id r_top none trivial
          (CtxRel.positional_alone r_top (c.site.takes ++ [state])) c.code
          path _ _ below Process.done hEnvPos hPath (fun _ _ _ hc => nomatch hc)
        rw [mapR_id, Process.bind_pure] at hCode
        dsimp only [retryOfCfg] at hCode
        have hAnsMap : ∀ {T U : Sig} {H τ X Y E : Type} (hb : Handler T U H τ)
            (f : X → Y) (p : Process T (H × E) X) (e : E) (t : τ),
            hb.answer (p.map f) e t = (hb.answer p e t).map fun out => (f out.1, out.2) := by
          intro _ _ _ _ _ _ _ hb f p e t
          induction p generalizing t with
          | done _ => rfl
          | halt _ => rfl
          | call op k ih =>
              simp only [Process.map, Handler.answer, Process.map_bind]
              congr 1; funext out; exact ih out.1 out.2
        rw [hPathClause, hAnsMap, handler_answer_mapHalt_const, mapHalt_map, mapHalt_mapHalt,
          Process.map_map, hCode, Process.map_eq_bind, Process.map_eq_bind, mapHalt_bind,
          Process.bind_assoc]
        congr 1; funext out
        dsimp only [Handler.run, Process.bind, Process.mapHalt]
        congr 1
        have hAlone : aloneOut M r_top (unheldValues M r_top out.1) =
            cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1 := by
          rw [aloneOut_eq_heldValues, heldValues_unheldValues]
        rw [hAlone]
        have hSplitCast : ∀ {g₁ g₂ : List V.Ty} (eg : g₁ = g₂)
            (es : held r_top (alone r_top (g₁ ++ [state])) = g₁ ++ [state])
            (v : HList M.Val (held r_top (alone r_top (g₁ ++ [state])))),
            let s1 := HList.split g₂ (cast (congrArg (HList M.Val) (by rw [es, eg])) v)
            let s2 := HList.split g₁ (cast (congrArg (HList M.Val) es) v)
            s1.1 = cast (congrArg (HList M.Val) eg) s2.1 ∧ s1.2.single = s2.2.single := by
          intro g₁ g₂ eg es v
          subst eg
          exact ⟨rfl, rfl⟩
        have hSC := hSplitCast hM.2.2.2 (held_alone r_top (c.site.gives ++ [state])) out.1
        have hRep : op.replyOf M ⟨path, key⟩ (cenv.all args)
            (ROp.reply M rop (cast (congrArg (HList M.Val) hM'.2.2.2)
              (HList.split c.site.gives (cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1)).1)) =
            (HList.split res (cast (congrArg (HList M.Val) (by rw [held_alone, hM.2.2.2])) out.1)).1 := by
          rw [hSC.1]
          have h1 := op.replyOf_reply M ⟨path, key⟩ (cenv.all args)
            (cast (congrArg (HList M.Val) hM.2.2.2)
              (HList.split c.site.gives (cast (congrArg (HList M.Val) (held_alone r_top (c.site.gives ++ [state]))) out.1)).1)
          simpa [rop, cast_cast] using h1
        rw [hRep, hSC.2]
      · have hNM' : ¬ (c.site.site = (ROp.occurrence M rop).site ∧ some c.site.part = ROp.part M rop ∧
            c.site.takes = ROp.takes M rop ∧ c.site.gives = ROp.gives M rop) := fun h' => hM (hIff.mpr h')
        rw [dite_eq_right hM, dite_eq_right hNM']
        exact specializeClauses_sound defs hBelow specBelow hSpecBelow through key op args path cenv mine below hPath cs

private theorem specializeStack_sound {hs : Headers V} (defs : Defs V hs) {r_top : Role}
    {ins_top : List (LTy V)} :
    ∀ (layers : List (Layer V hs r_top ins_top)),
      SpecOpSound M (Defs.fnTable M defs)
        (Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) layers)
        (specializeStack defs layers)
  | [] => by
      intro through key ins res op Δ args path cenv s hPath
      cases s
      rfl
  | l :: rest => by
      intro through key ins res op Δ args path cenv s hPath
      cases s with
      | cons mine below =>
          change (specializeClauses defs (specializeStack defs rest) through key op args l.clauses).denote
              M (Defs.fnTable M defs) path cenv (HList.cons mine below) =
            Process.map (fun out => (op.replyOf M ⟨path, key⟩ (cenv.all args) out.1, out.2))
              (Process.map (fun out => (out.1, HList.cons out.2.1 out.2.2))
                (Process.mapHalt (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
                  ((Process.mapHalt (fun stop => (stop.1, stop.2.1, stop.2.2))
                    ((Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) rest).answer
                      (Clause.answer M (Defs.fnTable M defs) (Defs.rTable M defs) l.clauses
                        (op.toROp M ⟨path, key⟩ (cenv.all args)) mine) mine below)).bind
                    fun out => Process.done (out.1.1, out.1.2, out.2))))
          rw [specializeClauses_sound M defs
            (Stack.handler M (Defs.fnTable M defs) (Defs.rTable M defs) rest)
            (specializeStack defs rest)
            (specializeStack_sound defs rest)
            through key op args path cenv mine below hPath l.clauses]
          rw [mapHalt_bind, mapHalt_mapHalt, Process.map_bind, Process.map_eq_bind, Process.map_eq_bind,
            Process.bind_assoc]
          rfl

private theorem stackAgain_eval_cons {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (l : Layer V hs r ins) (rest : List (Layer V hs r ins))
    (i : Nat) (e t : M.Val l.state) (es ts : HList M.Val (Stack.States rest))
    (hRec : StackAgain.eval M fnTable (stackAgain rest) i es ts =
      (Stack.handler M fnTable rTable rest).again i es ts) :
    StackAgain.eval M fnTable (stackAgain (l :: rest)) i (.cons e es) (.cons t ts) =
      (Stack.handler M fnTable rTable (l :: rest)).again i (.cons e es) (.cons t ts) := by
  change StackAgain.eval M fnTable (HList.cons l.again (stackAgain rest)) i (.cons e es) (.cons t ts) =
    (((Layer.handler M fnTable rTable l).over (Stack.handler M fnTable rTable rest)).again
      i (e, es) (t, ts)).map fun next => .cons next.1 next.2
  rw [StackAgain.eval, hRec]
  dsimp only [Handler.over, Layer.handler]
  cases l.again.denote (localSem M hs.fns fnTable) []
      (Env.positional (.cons (i : Nat) (.cons e (.cons t .nil)))) with
  | done res =>
      cases res with
      | cons next rNil =>
          cases rNil
          cases (Stack.handler M fnTable rTable rest).again i es ts <;> rfl
  | halt why => rfl
  | call op _ => nomatch op

private theorem stackAgain_eval {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)),
      StackAgain.eval M fnTable (stackAgain layers) =
        (Stack.handler M fnTable rTable layers).again
  | [] => by
      funext i entry stop
      cases entry; cases stop; rfl
  | l :: rest => by
      funext i entry stop
      cases entry with
      | cons e es =>
          cases stop with
          | cons t ts =>
              exact stackAgain_eval_cons M fnTable rTable l rest i e t es ts
                (congrFun (congrFun (congrFun (stackAgain_eval fnTable rTable rest) i) es) ts)

private theorem stackInit_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)) (inputVals : HList (RV M r) ins)
      (takenVals : HList M.Val (Stack.Takes layers)),
      (stackInit layers).denote M fnTable (heldValues M r inputVals) takenVals =
        Stack.start M fnTable layers inputVals takenVals
  | [], _, .nil => rfl
  | l :: rest, inputVals, takenVals => by
      change (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes takenVals).1.append (heldValues M r inputVals))))).bind
          (fun first => ((stackInit rest).denote M fnTable (heldValues M r inputVals)
            (HList.split l.takes takenVals).2).map fun others => HList.cons first.single others) =
        (liftLocal id (l.start.denote (localSem M hs.fns fnTable) []
          (Env.positional ((HList.split l.takes takenVals).1.append (heldValues M r inputVals))))).bind
          (fun first => (Stack.start M fnTable rest inputVals
            (HList.split l.takes takenVals).2).map fun others => HList.cons first.single others)
      congr 1; funext first
      rw [stackInit_denote fnTable rest inputVals (HList.split l.takes takenVals).2]

private theorem stackFinish_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} :
    ∀ (layers : List (Layer V hs r ins)) (states : HList M.Val (Stack.States layers)),
      (stackFinish layers).denote M fnTable states = Stack.finish M fnTable layers states
  | [], .nil => rfl
  | l :: rest, .cons s states => by
      change (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
          (fun mine => ((stackFinish rest).denote M fnTable states).map fun others => HList.append mine others) =
        (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
          (fun mine => (Stack.finish M fnTable rest states).map fun others => HList.append mine others)
      congr 1; funext mine
      rw [stackFinish_denote fnTable rest states]

unseal roleMeaning in
private theorem roleMeaning_eq_rTable (p : Typed V) {hdr : ProtocolHeader V}
    (x : Member p.headers.protocols hdr) (r : Role) (path : List Frame)
    (ins : HList (RV M r) hdr.ins) :
    roleMeaning M p x r path ins = Defs.rTable M p.defs hdr x r path ins := rfl

private theorem closedRole_denote_eq {fns : List (FnHeader V)} (fnTable : FnTable M fns)
    {r : Role} {ins outs : List (LTy V)} {takes gives : List V.Ty}
    (cr : ClosedRole V fns r ins outs takes gives)
    (inputVals : HList (RV M r) ins) (takenVals : HList M.Val takes) :
    cr.denote M fnTable inputVals takenVals =
      ((cr.start.denote M fnTable (heldValues M r inputVals) takenVals).bind fun st0 =>
        ((cr.body.denote M fnTable [] (Env.empty.extend cr.inputs (heldValues M r inputVals)) st0).mapHalt Prod.fst).bind
          fun out => (cr.finish.denote M fnTable out.2).map fun g => (out.1, g)).map
        fun out => (unheldValues M r out.1, out.2) := rfl

private theorem deployed_run_unfold (d : Deployed V) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    d.run M r ins taken =
      (Stack.start M (Defs.fnTable M d.admitted.program.defs) (d.stack r) ins taken).bind fun first =>
        (((Stack.handler M (Defs.fnTable M d.admitted.program.defs) (Defs.rTable M d.admitted.program.defs)
            (d.stack r)).run (retryOf M d.retry) (roleMeaning M d.admitted.program d.callee r [] ins) first).mapHalt
          Prod.fst).bind fun out =>
          (Stack.finish M (Defs.fnTable M d.admitted.program.defs) (d.stack r) out.2).map
            fun gives => (out.1, gives) := rfl

/-! ### Main soundness theorem (`specialize_sound`) -/

/-- **Handler specialization soundness.**
For any deployed scheme `d` with well-nested retry (satisfied whenever `d.retry = none`
and for every scheme returned by `deploy` or `deployIdeal`), the specialized `ClosedRole`
has the exact same denotation as `d.run` on every model `M`, role `r`, inputs `ins`, and
taken values `taken`. -/
theorem specialize_sound (d : Deployed V) (r : Role)
    (hRetry : d.WellNestedRetry)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken := by
  let retryCfg := d.retry.map fun (bound, site) => (bound, site, stackAgain (d.stack r))
  have hInit : (stackInit (d.stack r)).denote M (Defs.fnTable M d.admitted.program.defs)
      (heldValues M r ins) taken =
      Stack.start M (Defs.fnTable M d.admitted.program.defs) (d.stack r) ins taken :=
    stackInit_denote M (Defs.fnTable M d.admitted.program.defs) (d.stack r) ins taken
  rw [closedRole_denote_eq, deployed_run_unfold]
  dsimp only [specialize]
  erw [hInit, Process.map_bind]
  congr 1; funext st0
  rw [Process.map_bind]
  have hSpec := specializeStack_sound M d.admitted.program.defs (d.stack r)
  let hStack := Stack.handler M (Defs.fnTable M d.admitted.program.defs)
    (Defs.rTable M d.admitted.program.defs) (d.stack r)
  have hRC : RetryCfgOk M (Defs.fnTable M d.admitted.program.defs) hStack retryCfg := by
    cases hR : d.retry with
    | none => simp [retryCfg, hR, RetryCfgOk]
    | some bs =>
        simp only [retryCfg, hR, Option.map_some, RetryCfgOk]
        exact stackAgain_eval M (Defs.fnTable M d.admitted.program.defs)
          (Defs.rTable M d.admitted.program.defs) (d.stack r)
  have hRetEq : retryOfCfg M retryCfg = retryOf M d.retry := by
    cases hR : d.retry <;> simp [retryCfg, hR, retryOfCfg, retryOf]
  have hWN : ∀ b site ag, retryCfg = some (b, site, ag) →
      Shape.noNestedAttempt site [] d.entry.shape = true := by
    intro b site ag hc
    cases hR : d.retry with
    | none => simp [retryCfg, hR] at hc
    | some bs =>
        cases bs with
        | mk b0 s0 =>
            simp only [retryCfg, hR, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨_, rfl, _⟩ := hc
            exact hRetry b0 s0 hR
  have hBody := specializeProtocolInDefs_sound M (Defs.fnTable M d.admitted.program.defs)
    hStack (specializeStack d.admitted.program.defs (d.stack r)) hSpec
    d.admitted.program.defs id (fun _ _ => rfl) retryCfg hRC d.callee [] id r [] ins st0
    Process.done rfl hWN
  rw [mapR_id, Process.bind_pure, hRetEq, ← roleMeaning_eq_rTable] at hBody
  have hBodyMap : (hStack.run (retryOf M d.retry) (roleMeaning M d.admitted.program d.callee r [] ins) st0).mapHalt Prod.fst =
      (((specializeProtocolInDefs (specializeStack d.admitted.program.defs (d.stack r))
          d.admitted.program.defs id retryCfg d.callee [] id r).2.denote
        M (Defs.fnTable M d.admitted.program.defs) []
        (Env.empty.extend (specializeProtocolInDefs (specializeStack d.admitted.program.defs (d.stack r))
            d.admitted.program.defs id retryCfg d.callee [] id r).1
          (heldValues M r ins)) st0).mapHalt Prod.fst).map fun out => (unheldValues M r out.1, out.2) := by
    rw [hBody]
    dsimp only [Handler.run]
    rw [← Process.map_eq_bind, mapHalt_map]
  rw [hBodyMap, Process.bind_map]
  congr 1; funext out
  rw [stackFinish_denote M (Defs.fnTable M d.admitted.program.defs) (d.stack r) out.2, Process.map_map]

/-- Corollary of `specialize_sound` for deployments without retry (`d.retry = none`). -/
theorem specialize_sound_noRetry (d : Deployed V) (r : Role) (hNoRetry : d.retry = none)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (fun _ _ h => by rw [hNoRetry] at h; cases h) ins taken

/-- **Handler specialization soundness for every scheme returned by `deploy`.**
Because `deploy` rejects nested self-retry in `checkNonInteractiveScope` and forbids retry in
`checkInteractiveScope`, every deployed scheme satisfies `Deployed.WellNestedRetry`. -/
theorem specialize_deploy_sound (enc : VocabEncoder V) (a : Admitted V) (declaration : Declaration)
    (d : Deployed V) (hDep : deploy enc a declaration = .ok d) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (deploy_wellNestedRetry enc a declaration d hDep) ins taken

/-- **Handler specialization soundness for every scheme returned by `deployIdeal`.** -/
theorem specialize_deployIdeal_sound (enc : VocabEncoder V) (serviceKey : Key) (a : Admitted V)
    (declaration : Declaration) (d : Deployed V)
    (hDep : deployIdeal enc serviceKey a declaration = .ok d) (r : Role)
    (ins : HList (RV M r) d.entry.ins) (taken : HList M.Val (Stack.Takes (d.stack r))) :
    (specialize d r).denote M (Defs.fnTable M d.admitted.program.defs) ins taken =
      d.run M r ins taken :=
  specialize_sound M d r (deployIdeal_wellNestedRetry enc serviceKey a declaration d hDep) ins taken

end Soundness

end Zkc.Core


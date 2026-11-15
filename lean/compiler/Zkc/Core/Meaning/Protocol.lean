module

public import Zkc.Core.Meaning.Local

@[expose] public section

/-!
The meaning of a protocol: the semantics of the protocol dialect.

A protocol is one process of all its roles. A value of a located type is a value of its type.
A computation by the roles `R` runs the local operation; when it stops, `R` stop. A guard by
`ps` that fails stops `ps`. An event happens at the occurrence of its key under the path that
reached it. An application runs the callee at the path extended by the application's key,
with its roles renamed by the role map.

The table of callees gives each callee's results with the record of its run. `Term.observe`
is the process of a term that also returns the record of its run, of the type that the
term's shape gives; without the record it is `Term.denote`.
-/

namespace Zkc.Core


section
variable {V : Vocabulary} (M : Model V)

/-- A function's process inside a process with effects: it has none, and `f` says what its
stop carries there. -/
def liftLocal {S : Sig} {H A : Type} (f : Stop → H) : Local A → Process S H A
  | .done a => .done a
  | .halt why => .halt (f why)
  | .call op _ => nomatch op

/-! ## Values of located types -/

/-- The values of located types, as values of their types. -/
def HList.ofLocated : {items : List (LTy V)} → HList (LVal M) items →
    HList M.Val (items.map LTy.ty)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons v (HList.ofLocated rest)

/-- Values of types, as values held by `R`. -/
def HList.located (R : Holders) : {outs : List V.Ty} → HList M.Val outs →
    HList (LVal M) (outs.map fun τ => ⟨τ, R⟩)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons v (HList.located R rest)

/-- The operands of a computation, as the arguments of its local operation. -/
def computeArgs {operands : List (LTy V)} {ins : List V.Ty} (types : operands.map (·.ty) = ins)
    (vs : HList (LVal M) operands) : HList M.Val ins :=
  cast (congrArg (HList M.Val) types) (HList.ofLocated M vs)

/-- A value used where a located type that it covers is asked. -/
def cover {a b : LTy V} (h : a.Covers b) (v : LVal M a) : LVal M b :=
  cast (congrArg M.Val h.1) v

/-- The operands of an application, at its ports. -/
def fitAll : {as bs : List (LTy V)} → Fits as bs → HList (LVal M) as → HList (LVal M) bs
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, h, .cons v rest => .cons (cover M h.1 v) (fitAll h.2 rest)
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

/-- The values of the ports of a callee, out of the values that the caller gives at them. -/
def unmapAll (ρ : Role → Role) : {items : List (LTy V)} →
    HList (LVal M) (items.map (LTy.map ρ)) → HList (LVal M) items
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons v (unmapAll ρ rest)

/-- The values of the results of a callee, as the caller has them. -/
def remapAll (ρ : Role → Role) : {items : List (LTy V)} →
    HList (LVal M) items → HList (LVal M) (items.map (LTy.map ρ))
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons v (remapAll ρ rest)

/-! ## A role map on a protocol's process -/

/-- The process of a callee as the caller's roles perform it: every role that takes part in
an event or stops is renamed. -/
def mapG (ρ : Role → Role) {A : Type} : Protocol M A → Protocol M A
  | .done a => .done a
  | .halt (who, why) => .halt (who.map ρ, why)
  | .call (.flow kind giver getters at_ τ x) k =>
      .call (.flow kind (ρ giver) (getters.map ρ) at_ τ x) fun u => mapG ρ (k u)
  | .call (.given kind owner hearers at_ ins payload τ) k =>
      .call (.given kind (ρ owner) (hearers.map ρ) at_ ins payload τ) fun v => mapG ρ (k v)

/-! ## The semantics -/

/-- The processes of the protocols that a region may apply: each returns its results and
the record of its run. -/
abbrev GTable (protocols : List (ProtocolHeader V)) : Type :=
  ∀ hdr, Var protocols hdr → List Frame → HList (LVal M) hdr.ins →
    Protocol M (HList (LVal M) hdr.outs × hdr.record.Val M)

/-- The meaning of an operation of a protocol, at its key. -/
def protocolOp {hs : Headers V} (fnTable : FnTable M hs.fns) (gTable : GTable M hs.protocols)
    (key : Key) :
    {ins res : List (LTy V)} → ProtocolOp V hs ins res → List Frame → HList (LVal M) ins →
      Protocol M (HList (LVal M) res)
  | _, _, .compute R o _ types _, _, vs =>
      (liftLocal (fun why => (R, why)) (localOp M fnTable o (computeArgs M types vs))).map
        (HList.located M R)
  | _, _, .flow (τ := τ) kind giver getters _ _, path, .cons v .nil =>
      .call (.flow kind giver getters ⟨path, key⟩ τ v) fun _ => .done (.cons v .nil)
  | _, _, .given kind owner hearers operands τ _ _ _, path, vs =>
      .call (.given kind owner hearers ⟨path, key⟩ (operands.map LTy.ty) (HList.ofLocated M vs) τ)
        fun v => .done (.cons v .nil)
  | _, _, .narrow _ _, _, .cons v .nil => .done (.cons v .nil)
  | _, _, .apply callee roles distinct _ _ fits, path, vs =>
      (mapG M (RoleMap.ofList roles distinct).to
        (gTable _ callee (path ++ [.application key])
          (unmapAll M (RoleMap.ofList roles distinct).to (fitAll M fits vs)))).map
        fun out => remapAll M (RoleMap.ofList roles distinct).to out.1

/-- The alternative of a value of a variant whose payloads are held by `ps`. -/
def Tys.pickAt {W : LTy V → Type} (ps : Holders) (f : ∀ τ, M.Val τ → W ⟨τ, ps⟩) :
    (alternatives : Tys V.TypeKey) → alternatives.Choice M.toCarriers →
      Pick W (alternatives.toList.map fun τ => ⟨τ, ps⟩)
  | .nil, v => nomatch v
  | .cons head _, .inl v => .here (f head v)
  | .cons _ rest, .inr v => .there (Tys.pickAt ps f rest v)

/-- The alternative of a variant whose payloads are held by `ps`, with its payload. -/
def locatedPick {W : LTy V → Type} (ps : Holders) (f : ∀ τ, M.Val τ → W ⟨τ, ps⟩) {τ : V.Ty}
    {payloads : List (LTy V)}
    (h : ∃ key alternatives, τ = .variant key alternatives ∧
      payloads = alternatives.toList.map fun τ => ⟨τ, ps⟩)
    (v : M.Val τ) : Pick W payloads :=
  cast
    (congrArg (Pick W) (by
      obtain ⟨_, _, e, p⟩ := h
      rw [Ty.alternatives_of e, p]))
    (Tys.pickAt M ps f τ.alternatives
      (cast (congrArg M.Val (Ty.eq_variant (P := fun alternatives =>
        payloads = alternatives.toList.map fun τ => ⟨τ, ps⟩) h)) v))

/-- The semantics of the protocol dialect. -/
@[reducible] def protocolSem {hs : Headers V} (fnTable : FnTable M hs.fns)
    (gTable : GTable M hs.protocols) : Semantics (protocolDialect V hs) where
  Val := LVal M
  S := GSig M
  H := List Role × Stop
  op := fun {_ _} key o path vs => protocolOp M fnTable gTable key o path vs
  holds := fun {_ _} ok v => asBool M ok.1 v
  stop := fun ps why at_ => (ps, .declared why at_)
  pick := fun {ps _ _} ok v =>
    locatedPick M ps (W := LVal M) (fun _ u => u)
      (by obtain ⟨key, alternatives, e, p, _⟩ := ok; exact ⟨key, alternatives, e, p⟩) v
  count := fun {_ _} ok v => asNat M ok.1 v
  index := fun _ i => i
  begin := fun _ _ _ => .done (0 : Nat)
  settle := fun _ _ _ => .done ()
  collect := fun _ _ vs => vs

/-- An attempt in the protocol as written: its body runs once, with the number `0`, and then
the rest. -/
theorem attempt_denote {hs : Headers V} (fnTable : FnTable M hs.fns)
    (gTable : GTable M hs.protocols) {Γ outs mid : List (LTy V)} (key : Key) (w : Holders)
    (owns : (protocolDialect V hs).Attempt w)
    (body : Term (protocolDialect V hs) (LTy.index w :: Γ) mid)
    (rest : Term (protocolDialect V hs) (mid ++ Γ) outs) (path : List Frame)
    (env : Env (LVal M) Γ) :
    (Term.attempt key w owns body rest).denote (protocolSem M fnTable gTable) path env =
      (body.denote (protocolSem M fnTable gTable) path
          (Env.cons (V := LVal M) (a := LTy.index w) (0 : Nat) env)).bind fun mids =>
        rest.denote (protocolSem M fnTable gTable) path (Env.extend mids env) := rfl

/-! ## The record of a run -/

namespace Fields

def join : {fs gs : Fields V} → fs.Val M → gs.Val M → (fs.append gs).Val M
  | .nil, _, _, y => y
  | .cons _ _ _, _, (x, xs), y => (x, join xs y)

/-- The fields of an arm that ran. -/
def present : {fs : Fields V} → fs.Val M → (fs.map .opt).Val M
  | .nil, _ => ()
  | .cons _ _ _, (x, xs) => (some x, present xs)

/-- The fields of an arm that did not run. -/
def absent : (fs : Fields V) → (fs.map .opt).Val M
  | .nil => ()
  | .cons _ _ rest => (none, absent rest)

/-- The fields of a loop before its first iteration. -/
def empty : (fs : Fields V) → (fs.map .many).Val M
  | .nil => ()
  | .cons _ _ rest => ([], empty rest)

/-- The fields of a loop after one more iteration. -/
def push : {fs : Fields V} → (fs.map .many).Val M → fs.Val M → (fs.map .many).Val M
  | .nil, _, _ => ()
  | .cons _ _ _, (xs, rest), (x, more) => (xs ++ [x], push rest more)

end Fields

/-- The fields of arms none of which ran. -/
def Shapes.absent : (arms : Shapes V) → arms.fields.Val M
  | .nil => ()
  | .cons arm rest => Fields.join M (Fields.absent M arm.fields) (Shapes.absent rest)

section
variable {hs : Headers V} (fnTable : FnTable M hs.fns) (gTable : GTable M hs.protocols)

/-- An operation with the part of the record that it is, before the rest of the run. -/
def observeOp (key : Key) {outs : List (LTy V)} {s : Shape V} :
    {ins res : List (LTy V)} → (o : ProtocolOp V hs ins res) → List Frame →
      HList (LVal M) ins → (HList (LVal M) res → Protocol M (HList (LVal M) outs × s.fields.Val M)) →
      Protocol M (HList (LVal M) outs × (ProtocolOp.shape key o s).fields.Val M)
  | _, _, .compute R o operands types held, path, vs, k =>
      (protocolOp M fnTable gTable key (.compute R o operands types held) path vs).bind k
  | _, _, .flow (τ := τ) kind giver getters _ _, path, .cons v .nil, k =>
      .call (.flow kind giver getters ⟨path, key⟩ τ v) fun _ =>
        (k (.cons v .nil)).map fun out => (out.1, (v, out.2))
  | _, _, .given (.coin law) owner (first :: others) operands τ _ _ _, path, vs, k =>
      .call (.given (.coin law) owner (first :: others) ⟨path, key⟩
          (operands.map LTy.ty) (HList.ofLocated M vs) τ) fun v =>
        (k (.cons v .nil)).map fun out => (out.1, (v, out.2))
  | _, _, .given (.request service) owner hearers operands τ _ _ _, path, vs, k =>
      .call (.given (.request service) owner hearers ⟨path, key⟩ (operands.map LTy.ty)
          (HList.ofLocated M vs) τ) fun v =>
        (k (.cons v .nil)).map fun out => (out.1, (v, out.2))
  | _, _, .given (.coin law) owner [] operands τ _ _ _, path, vs, k =>
      .call (.given (.coin law) owner [] ⟨path, key⟩ (operands.map LTy.ty)
          (HList.ofLocated M vs) τ) fun v => k (.cons v .nil)
  | _, _, .narrow R among, path, vs, k =>
      (protocolOp M fnTable gTable key (.narrow R among) path vs).bind k
  | _, _, .apply callee roles distinct _ _ fits, path, vs, k =>
      (mapG M (RoleMap.ofList roles distinct).to
        (gTable _ callee (path ++ [.application key])
          (unmapAll M (RoleMap.ofList roles distinct).to (fitAll M fits vs)))).bind
        fun inner => (k (remapAll M (RoleMap.ofList roles distinct).to inner.1)).map fun out =>
          (out.1, (inner.2, out.2))

mutual
  /-- The process of a term that returns its results and the record of its run. -/
  def Term.observe : {Γ outs : List (LTy V)} → (t : Term (protocolDialect V hs) Γ outs) →
      List Frame → Env (LVal M) Γ → Protocol M (HList (LVal M) outs × (shapeOf t).fields.Val M)
    | _, _, .ret xs, _, env => .done (env.all xs, ())
    | _, _, .op key o args rest, path, env =>
        observeOp M fnTable gTable key o path (env.all args) fun results =>
          Term.observe rest path (Env.extend results env)
    | _, _, .guard key ps c ok why rest, path, env =>
        bif (protocolSem M fnTable gTable).holds ok (env _ c) then Term.observe rest path env
        else .halt (ps, .declared why ⟨path, key⟩)
    | _, _, .choose (mid := mid) _ _ c ok _ onTrue onFalse rest, path, env =>
        ((bif (protocolSem M fnTable gTable).holds ok (env _ c) then
            (Term.observe onTrue path env).map fun arm =>
              (arm.1, Fields.join M (Fields.present M arm.2)
                (Shapes.absent M (.cons (shapeOf onFalse) .nil)))
          else
            (Term.observe onFalse path env).map fun arm =>
              (arm.1, Fields.join M (Fields.absent M (shapeOf onTrue).fields)
                (Fields.join M (Fields.present M arm.2) (Shapes.absent M .nil)))) :
          Protocol M (HList (LVal M) mid ×
            (Shapes.fields (.cons (shapeOf onTrue) (.cons (shapeOf onFalse) .nil))).Val M)).bind
          fun arms =>
            (Term.observe rest path (Env.extend arms.1 env)).map fun out =>
              (out.1, Fields.join M arms.2 out.2)
    | _, _, .cases _ _ x ok _ arms rest, path, env =>
        (Arms.observe arms path env ((protocolSem M fnTable gTable).pick ok (env _ x))).bind
          fun chosen =>
            (Term.observe rest path (Env.extend chosen.1 env)).map fun out =>
              (out.1, Fields.join M chosen.2 out.2)
    | _, _, .loop (carried := carried) (each := each) key ps times _ init body rest, path, env =>
        (Process.iterate ((protocolSem M fnTable gTable).times times env)
          (fun i (state : (protocolSem M fnTable gTable).LoopState carried each ×
              ((shapeOf body).fields.map .many).Val M) =>
            (Term.observe body (path ++ [.iteration key i])
              (Env.cons ((protocolSem M fnTable gTable).index ps i)
                (Env.extend state.1.1 env))).map fun out =>
              (((HList.split carried out.1).1, state.1.2.push (HList.split carried out.1).2),
                Fields.push M state.2 out.2))
          0 ((env.all init, HList.empties each), Fields.empty M (shapeOf body).fields)).bind
          fun state =>
            (Term.observe rest path
              (Env.extend (state.1.1.append
                ((protocolSem M fnTable gTable).collected times.size state.1.2)) env)).map
              fun out => (out.1, Fields.join M state.2 out.2)
    | _, _, .block key number body rest, path, env =>
        (Term.observe body (path ++ [.iteration key number]) env).bind fun inner =>
          (Term.observe rest path (Env.extend inner.1 env)).map fun out =>
            (out.1, (inner.2, out.2))
    | _, _, .attempt _ w _ body rest, path, env =>
        (Term.observe body path (Env.cons (V := LVal M) (a := LTy.index w) (0 : Nat) env)).bind
          fun inner =>
            (Term.observe rest path (Env.extend inner.1 env)).map fun out =>
              (out.1, Fields.join M inner.2 out.2)
  /-- The process of the region of the alternative that a variant is, with the record of the
  arms: the fields of the arm that ran, and none for the others. -/
  def Arms.observe : {Γ mid payloads : List (LTy V)} →
      (arms : Arms (protocolDialect V hs) Γ mid payloads) → List Frame → Env (LVal M) Γ →
        Pick (LVal M) payloads → Protocol M (HList (LVal M) mid × (shapesOf arms).fields.Val M)
    | _, _, _, .cons arm rest, path, env, .here v =>
        (Term.observe arm path (Env.cons v env)).map fun out =>
          (out.1, Fields.join M (Fields.present M out.2) (Shapes.absent M (shapesOf rest)))
    | _, _, _, .cons arm rest, path, env, .there p =>
        (Arms.observe rest path env p).map fun out =>
          (out.1, Fields.join M (Fields.absent M (shapeOf arm).fields) out.2)
end

/-- An operation with its part of the record, without the record, is the operation. -/
theorem observeOp_fst (key : Key) {outs : List (LTy V)} {s : Shape V} :
    ∀ {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (path : List Frame)
      (vs : HList (LVal M) ins)
      (k : HList (LVal M) res → Protocol M (HList (LVal M) outs × s.fields.Val M)),
      (observeOp M fnTable gTable key o path vs k).map Prod.fst =
        (protocolOp M fnTable gTable key o path vs).bind fun results => (k results).map Prod.fst
  | _, _, .compute R o operands types held, path, vs, k => Process.map_bind k Prod.fst _
  | _, _, .flow kind giver getters _ _, path, .cons v .nil, k => by
      simp only [observeOp, protocolOp, Process.map, Process.bind, Process.map_map]
  | _, _, .given (.coin law) owner (first :: others) operands τ _ _ _, path, vs, k => by
      simp only [observeOp, protocolOp, Process.map, Process.bind, Process.map_map]
  | _, _, .given (.request service) owner hearers operands τ _ _ _, path, vs, k => by
      simp only [observeOp, protocolOp, Process.map, Process.bind, Process.map_map]
  | _, _, .given (.coin law) owner [] operands τ _ _ _, path, vs, k => rfl
  | _, _, .narrow R among, path, vs, k => Process.map_bind k Prod.fst _
  | _, _, .apply callee roles distinct _ _ fits, path, vs, k => by
      simp only [observeOp, protocolOp]
      rw [Process.map_bind, Process.bind_map]
      congr 1
      funext inner
      rw [Process.map_map]

mutual
  /-- The process with the record, without the record, is the process of the term. -/
  theorem Term.observe_fst : ∀ {Γ outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs)
      (path : List Frame) (env : Env (LVal M) Γ),
      (Term.observe M fnTable gTable t path env).map Prod.fst =
        t.denote (protocolSem M fnTable gTable) path env
    | _, _, .ret _, _, _ => rfl
    | _, _, .op key o args rest, path, env => by
        refine (observeOp_fst M fnTable gTable key o path (env.all args)
          fun results => Term.observe M fnTable gTable rest path (Env.extend results env)).trans ?_
        simp only [Term.denote]
        congr 1
        funext results
        exact Term.observe_fst rest path _
    | _, _, .guard key ps c ok why rest, path, env => by
        simp only [Term.observe, Term.denote]
        cases asBool M ok.1 (env _ c)
        · rfl
        · exact Term.observe_fst rest path env
    | _, _, .choose _ _ c ok _ onTrue onFalse rest, path, env => by
        simp only [Term.observe, Term.denote]
        rw [Process.map_bind]
        cases asBool M ok.1 (env _ c)
        · simp only [Bool.cond_false]
          rw [← Term.observe_fst onFalse path env, Process.bind_map, Process.bind_map]
          congr 1
          funext arm
          rw [Process.map_map]
          exact Term.observe_fst rest path _
        · simp only [Bool.cond_true]
          rw [← Term.observe_fst onTrue path env, Process.bind_map, Process.bind_map]
          congr 1
          funext arm
          rw [Process.map_map]
          exact Term.observe_fst rest path _
    | _, _, .cases _ _ x ok _ arms rest, path, env => by
        simp only [Term.observe, Term.denote]
        rw [Process.map_bind, ← Arms.observe_fst arms path env, Process.bind_map]
        congr 1
        funext chosen
        rw [Process.map_map]
        exact Term.observe_fst rest path _
    | _, _, .loop key ps times _ init body rest, path, env => by
        simp only [Term.observe, Term.denote]
        rw [Process.map_bind]
        refine Process.bind_iterate_fst ?_ ?_ _ _ _ _
        · intro i a x
          simp only [Semantics.loopStep]
          rw [Process.map_map, ← Term.observe_fst body, Process.bind_map, Process.map_eq_bind]
        · intro state
          rw [Process.map_map]
          exact Term.observe_fst rest path _
    | _, _, .block key number body rest, path, env => by
        simp only [Term.observe, Term.denote]
        rw [Process.map_bind, ← Term.observe_fst body, Process.bind_map]
        congr 1
        funext inner
        rw [Process.map_map]
        exact Term.observe_fst rest path _
    | _, _, .attempt key w owns body rest, path, env => by
        rw [attempt_denote]
        simp only [Term.observe]
        rw [Process.map_bind, ← Term.observe_fst body, Process.bind_map]
        congr 1
        funext inner
        rw [Process.map_map]
        exact Term.observe_fst rest path _
  theorem Arms.observe_fst : ∀ {Γ mid payloads : List (LTy V)}
      (arms : Arms (protocolDialect V hs) Γ mid payloads) (path : List Frame)
      (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
      (Arms.observe M fnTable gTable arms path env p).map Prod.fst =
        arms.denote (protocolSem M fnTable gTable) path env p
    | _, _, _, .nil, _, _, p => nomatch p
    | _, _, _, .cons arm rest, path, env, .here v => by
        simp only [Arms.observe]
        rw [Process.map_map]
        exact Term.observe_fst arm path _
    | _, _, _, .cons arm rest, path, env, .there p => by
        simp only [Arms.observe]
        rw [Process.map_map]
        exact Arms.observe_fst rest path env p
end

end

end

end Zkc.Core

#print axioms Zkc.Core.Term.observe_fst

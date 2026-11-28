module

public import Zkc.Core.Scheme.Proof.Completeness

@[expose] public section

/-!
Completeness for `.derived` compact proof layouts (`layout.recover ≠ []`, with optional `carry`).

On any straight-line protocol whose suite, layout codec, and message-recovery functions satisfy
their semantic laws (`Deployed.SuiteLawfulFor`, `Deployed.LayoutLawful`, `Deployed.RecoveryLawful`):
- `protocolMeaning_followsEvents` establishes exact 1-to-1 lockstep ordering between the protocol's
  execution events and `entry.shape.events [] id`;
- `buildCompactParse_reads` and `compactLayoutVStart_reads` prove that parsing the prover's compact
  proof buffer reconstructs the exact tuple state `(stmtVals..., wireVals...)`;
- `deploy_complete_compact` proves end-to-end completeness for compact deployments, handling both
  omitted messages reconstructed by `compactRecoverClause` and carried draws checked by
  `compactCompareClause`.
-/

namespace Zkc.Core

open LayerBuild

section CompactCompleteness

variable {V : Vocabulary} (M : Model V)

/-! ## Generic `HList` / `Tys` indexing and sigma-list helpers -/

/-- Pack a heterogeneous list of dependent pairs into an `HList`. -/
def HList.ofSigmaList {α : Type} {F : α → Type} :
    (xs : List ((a : α) × F a)) → HList F (xs.map Sigma.fst)
  | [] => .nil
  | ⟨_, v⟩ :: rest => .cons v (HList.ofSigmaList rest)

/-- Index into an `HList` via a typed `Member` proof. -/
def HList.getAtMember {α : Type} {F : α → Type} :
    ∀ {xs : List α} {a : α}, HList F xs → Member xs a → F a
  | _ :: _, _, .cons v _, .head => v
  | _ :: _, _, .cons _ rest, .tail m => HList.getAtMember rest m

theorem tys_getAt_ofHList :
    ∀ (ts : Tys V.TypeKey) (xs : HList M.Val ts.toList) {τ : V.Ty} (m : Member ts.toList τ),
      Tys.getAt M ts m (Tys.ofHList M ts xs) = HList.getAtMember xs m
  | .nil, _, _, m => nomatch m
  | .cons _ _, .cons _ _, _, .head => rfl
  | .cons _ rest, .cons _ xs, _, .tail m => tys_getAt_ofHList rest xs m

theorem hlist_getAtMember_append_right {α : Type} {F : α → Type} :
    ∀ {as bs : List α} (xs : HList F as) (ys : HList F bs) {a : α} (m : Member bs a),
      HList.getAtMember (HList.append xs ys) (memberAppendRight as m) = HList.getAtMember ys m
  | [], _, .nil, _, _, _ => rfl
  | _ :: _, _, .cons _ rest, ys, _, m => hlist_getAtMember_append_right rest ys m

theorem hlist_getAtMember_cast {α : Type} {F : α → Type} {as bs : List α} (h : as = bs)
    (xs : HList F as) {a : α} (m : Member bs a) :
    HList.getAtMember (cast (congrArg (HList F) h) xs) m =
      HList.getAtMember xs (cast (congrArg (fun l => Member l a) h.symm) m) := by
  subst h; rfl

theorem memberAppendRight_assoc {α : Type} :
    ∀ (as bs : List α) {cs : List α} {a : α} (m : Member cs a),
      cast (congrArg (fun l => Member l a) (List.append_assoc as bs cs).symm)
        (memberAppendRight as (memberAppendRight bs m)) =
        memberAppendRight (as ++ bs) m
  | [], _, _, _, _ => rfl
  | _ :: as, bs, _, a, m => by
      have ih := memberAppendRight_assoc as bs m
      have hTail : ∀ {l₁ l₂ : List α} (heq : l₁ = l₂) {x : α} (k : Member l₁ a),
          cast (congrArg (fun l => Member (x :: l) a) heq) (.tail k) =
            .tail (cast (congrArg (fun l => Member l a) heq) k) := by
        intro _ _ heq _ _; subst heq; rfl
      exact (hTail (List.append_assoc as bs _).symm _).trans (congrArg Member.tail ih)

theorem hlist_append_assoc {α : Type} {F : α → Type} :
    ∀ {as bs cs : List α} (xs : HList F as) (ys : HList F bs) (zs : HList F cs),
      HList.append (HList.append xs ys) zs =
        cast (congrArg (HList F) (List.append_assoc as bs cs).symm)
          (HList.append xs (HList.append ys zs))
  | [], _, _, .nil, _, _ => rfl
  | u :: as', bs, cs, .cons x xs, ys, zs => by
      have ih := hlist_append_assoc xs ys zs
      have hCons : ∀ {l₁ l₂ : List α} (heq : l₁ = l₂) (v : F u) (t : HList F l₁),
          HList.cons v (cast (congrArg (HList F) heq) t) =
            cast (congrArg (HList F) (congrArg (u :: ·) heq)) (HList.cons v t) := by
        intro _ _ heq _ _; subst heq; rfl
      exact (congrArg (HList.cons x) ih).trans (hCons (List.append_assoc as' bs cs).symm x _)

theorem hlist_ofSigmaList_append {α : Type} {F : α → Type} :
    ∀ (xs ys : List ((a : α) × F a)),
      HList.ofSigmaList (xs ++ ys) =
        cast (congrArg (HList F) (List.map_append (f := Sigma.fst) (l₁ := xs) (l₂ := ys)).symm)
          (HList.append (HList.ofSigmaList xs) (HList.ofSigmaList ys))
  | [], _ => rfl
  | ⟨u, v⟩ :: xs, ys => by
      have ih := hlist_ofSigmaList_append xs ys
      have hCons : ∀ {l₁ l₂ : List α} (heq : l₁ = l₂) (x : F u) (t : HList F l₁),
          HList.cons x (cast (congrArg (HList F) heq) t) =
            cast (congrArg (HList F) (congrArg (u :: ·) heq)) (HList.cons x t) := by
        intro _ _ heq _ _; subst heq; rfl
      exact (congrArg (HList.cons v) ih).trans
        (hCons (List.map_append (f := Sigma.fst) (l₁ := xs) (l₂ := ys)).symm v _)

theorem listNodupBool_true_iff {α : Type} [DecidableEq α] :
    ∀ (xs : List α), listNodupBool xs = true ↔ xs.Nodup
  | [] => by simp [listNodupBool]
  | x :: xs => by
      simp only [listNodupBool, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.nodup_cons]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (listNodupBool_true_iff xs).mp h2⟩,
             fun ⟨h1, h2⟩ => ⟨h1, (listNodupBool_true_iff xs).mpr h2⟩⟩

/-! ## Compact state extraction and `Deployed.RecoveryLawful` -/

/-- Public statement input arguments `(a.ty, v)` visible to both `prover` and `verifier` in
signature order. -/
def compactStmtArgs (prover verifier : Role) :
    {ins : List (LTy V)} → HList (LVal M) ins → List ((τ : V.Ty) × M.Val τ)
  | [], .nil => []
  | a :: _, .cons v rest =>
      (if prover ∈ a.holders ∧ verifier ∈ a.holders then [⟨a.ty, v⟩] else []) ++
        compactStmtArgs prover verifier rest

/-- Wire values serialized by a compact layout from a protocol run's event trace `evs`:
retained prover→verifier flows (`layout.recover.lookup at_.site = none`) and carried
verifier→prover heard coins (`at_.site ∈ layout.carry`) in exact run order. -/
def compactWireArgs (prover verifier : Role) (layout : Layout) :
    List (Event M) → List ((τ : V.Ty) × M.Val τ)
  | [] => []
  | .flow _ giver getters at_ τ v :: rest =>
      (if giver = prover ∧ verifier ∈ getters ∧ layout.recover.lookup at_.site = none
       then [⟨τ, v⟩] else []) ++ compactWireArgs prover verifier layout rest
  | .given (.coin _) owner hearers at_ τ v :: rest =>
      (if owner = verifier ∧ prover ∈ hearers ∧ at_.site ∈ layout.carry
       then [⟨τ, v⟩] else []) ++ compactWireArgs prover verifier layout rest
  | _ :: rest => compactWireArgs prover verifier layout rest

/-- Semantic recovery law for a compact proof layout (`layout.recover ≠ []`) in model `M`:
for every honest returning protocol run on valid inputs, every omitted prover→verifier message `x`
at a `recover` site is reconstructed by its declared recovery function from the compact verifier's
pre-parsed tuple state `(stmtVals..., wireVals...)`. -/
def Deployed.RecoveryLawful (d : Deployed V) : Prop :=
  ∀ layout prover verifier,
    d.declaration.layout = some layout →
    d.roles = some (prover, verifier) →
    ∀ (ins : HList (LVal M) d.entry.ins),
      ins.All (fun a v => M.Valid a.ty v) →
      ∀ (source : Source M) (evs : List (Event M)) (out),
        Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) →
        GRun M source (protocolMeaning M d.admitted.program d.callee [] ins) evs (.returned out) →
        let args := compactStmtArgs M prover verifier ins ++ compactWireArgs M prover verifier layout evs
        ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (x : M.Val τ)
          (recKey : Key),
          Event.flow kind prover getters at_ τ x ∈ evs →
          verifier ∈ getters →
          layout.recover.lookup at_.site = some recKey →
          ∀ (hdr : FnHeader V) (f : Member d.admitted.program.headers.fns hdr),
            d.admitted.program.find recKey = some (.fn f) →
            ∀ (hIn : hdr.ins = args.map Sigma.fst) (hOut : hdr.outs = [τ]),
              Defs.fnTable M d.admitted.program.defs hdr f
                (cast (congrArg (HList M.Val) hIn.symm) (HList.ofSigmaList args)) =
                .done (cast (congrArg (HList M.Val) hOut.symm) (.cons x .nil))

/-! ## Straight-line protocol lockstep event ordering (`Protocol.FollowsEvents`) -/

/-- A protocol process executes the exact event list `events` in 1-to-1 lockstep order on every
non-halting path (and may halt at any point). -/
def Protocol.FollowsEvents {A : Type} : List (ShapeEvent V) → Protocol M A → Prop
  | [], .done _ => True
  | _, .halt _ => True
  | e :: rest, .call (.flow kind giver getters at_ τ _) k =>
      e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind giver getters ∧
      Protocol.FollowsEvents rest (k ())
  | e :: rest, .call (.given kind owner hearers at_ _ _ τ) k =>
      e.site = at_.site ∧ e.τ = τ ∧ e.cls = .given kind owner hearers ∧
      ∀ v, Protocol.FollowsEvents rest (k v)
  | _, _ => False

private theorem followsEvents_bind {A B : Type} :
    ∀ {es₁ es₂ : List (ShapeEvent V)} (p : Protocol M A) (f : A → Protocol M B),
      Protocol.FollowsEvents M es₁ p →
      (∀ a, Protocol.FollowsEvents M es₂ (f a)) →
      Protocol.FollowsEvents M (es₁ ++ es₂) (p.bind f)
  | [], _, .done a, f, _, hf => hf a
  | _ :: _, _, .done _, _, h, _ => nomatch h
  | [], _, .halt _, _, _, _ => by cases ‹List (ShapeEvent V)› <;> trivial
  | _ :: _, _, .halt _, _, _, _ => trivial
  | [], _, .call (.flow ..) _, _, h, _ => nomatch h
  | [], _, .call (.given ..) _, _, h, _ => nomatch h
  | e :: rest, es₂, .call (.flow ..) k, f, ⟨h1, h2, h3, hk⟩, hf =>
      ⟨h1, h2, h3, followsEvents_bind (k ()) f hk hf⟩
  | e :: rest, es₂, .call (.given ..) k, f, ⟨h1, h2, h3, hk⟩, hf =>
      ⟨h1, h2, h3, fun v => followsEvents_bind (k v) f (hk v) hf⟩

private theorem followsEvents_map {A B : Type} (g : A → B) :
    ∀ {es : List (ShapeEvent V)} (p : Protocol M A),
      Protocol.FollowsEvents M es p → Protocol.FollowsEvents M es (p.map g)
  | [], .done _, _ => trivial
  | _ :: _, .done _, h => nomatch h
  | [], .halt _, _ => trivial
  | _ :: _, .halt _, _ => trivial
  | [], .call (.flow ..) _, h => nomatch h
  | [], .call (.given ..) _, h => nomatch h
  | _ :: _, .call (.flow ..) k, ⟨h1, h2, h3, hk⟩ => ⟨h1, h2, h3, followsEvents_map g (k ()) hk⟩
  | _ :: _, .call (.given ..) k, ⟨h1, h2, h3, hk⟩ =>
      ⟨h1, h2, h3, fun v => followsEvents_map g (k v) (hk v)⟩

private theorem followsEvents_liftLocal {A : Type} (who : List Role) :
    ∀ (p : Local A), Protocol.FollowsEvents M [] (liftLocal (fun w => (who, w)) p)
  | .done _ => trivial
  | .halt _ => trivial
  | .call op _ => nomatch op

private theorem followsEvents_mapG {A : Type} (ρ : Role → Role) :
    ∀ {es : List (ShapeEvent V)} (p : Protocol M A),
      Protocol.FollowsEvents M es p →
      Protocol.FollowsEvents M (es.map fun e => ⟨e.site, e.cls.rename ρ, e.τ⟩) (mapG M ρ p)
  | [], .done _, _ => trivial
  | _ :: _, .done _, h => nomatch h
  | [], .halt _, _ => trivial
  | _ :: _, .halt _, _ => trivial
  | [], .call (.flow ..) _, h => nomatch h
  | [], .call (.given ..) _, h => nomatch h
  | _ :: _, .call (.flow ..) k, ⟨h1, h2, h3, hk⟩ =>
      ⟨h1, h2, by simp [h3, EventClass.rename], followsEvents_mapG ρ (k ()) hk⟩
  | _ :: _, .call (.given ..) k, ⟨h1, h2, h3, hk⟩ =>
      ⟨h1, h2, by simp [h3, EventClass.rename], fun v => followsEvents_mapG ρ (k v) (hk v)⟩

private theorem list_getD_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat) (d : α) (h : i < xs.length), xs.getD i d = xs[i]'h
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, d, h => list_getD_of_lt xs i d (Nat.lt_of_succ_lt_succ h)

private theorem frame_applications_append' :
    ∀ (xs ys : List Frame), Frame.applications (xs ++ ys) = Frame.applications xs ++ Frame.applications ys
  | [], _ => rfl
  | .application _ :: xs, ys => congrArg (_ :: ·) (frame_applications_append' xs ys)
  | .iteration _ _ :: xs, ys => frame_applications_append' xs ys
  | .attempt _ _ :: xs, ys => frame_applications_append' xs ys

private theorem eventClass_rename_id' (c : EventClass V) : c.rename id = c := by
  cases c <;> simp [EventClass.rename]

private theorem eventClass_rename_comp' (f g : Role → Role) (c : EventClass V) :
    (c.rename g).rename f = c.rename (fun r => f (g r)) := by
  cases c <;> simp [EventClass.rename, List.map_map, Function.comp_def]

mutual
  private theorem shape_events_map' (through : List Key) (rename : Role → Role) :
      ∀ (s : Shape V),
        s.events through rename =
          (s.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .event key cls τ rest => by
        simp only [Shape.events, List.map_cons, List.append_nil, eventClass_rename_id']
        exact congrArg (_ :: ·) (shape_events_map' through rename rest)
    | .choice _ _ arms rest => by
        simp only [Shape.events, List.map_append]
        rw [shapes_events_map' through rename arms, shape_events_map' through rename rest]
    | .loop _ _ body rest => by
        simp only [Shape.events, List.map_append]
        rw [shape_events_map' through rename body, shape_events_map' through rename rest]
    | .apply key _ roles inner rest => by
        simp only [Shape.events, List.map_append, List.nil_append, id_eq]
        rw [shape_events_map' (through ++ [key]) (fun j => rename (roles.getD j j)) inner,
            shape_events_map' [key] (fun j => roles.getD j j) inner,
            List.map_map, shape_events_map' through rename rest]
        congr 1
        apply List.map_congr_left
        intro e _
        simp only [Function.comp_def, List.append_assoc, eventClass_rename_comp']
    | .block _ _ body rest => by
        simp only [Shape.events, List.map_append]
        rw [shape_events_map' through rename body, shape_events_map' through rename rest]
    | .guard _ _ _ rest => shape_events_map' through rename rest
    | .attempt _ _ body rest => by
        simp only [Shape.events, List.map_append]
        rw [shape_events_map' through rename body, shape_events_map' through rename rest]

  private theorem shapes_events_map' (through : List Key) (rename : Role → Role) :
      ∀ (ss : Shapes V),
        ss.events through rename =
          (ss.events [] id).map fun e =>
            ⟨⟨through ++ e.site.through, e.site.key⟩, e.cls.rename rename, e.τ⟩
    | .nil => rfl
    | .cons arm rest => by
        simp only [Shapes.events, List.map_append]
        rw [shape_events_map' through rename arm, shapes_events_map' through rename rest]
end

private def eventClassAllIn (parts : List Role) : EventClass V → Prop
  | .flow _ giver getters => giver ∈ parts ∧ ∀ g ∈ getters, g ∈ parts
  | .given _ owner hearers => owner ∈ parts ∧ ∀ h ∈ hearers, h ∈ parts

private theorem eventClass_rename_congr' {parts : List Role} {f g : Role → Role}
    (h : ∀ r ∈ parts, f r = g r) {c : EventClass V} (hc : eventClassAllIn parts c) :
    c.rename f = c.rename g := by
  cases c with
  | flow _ giver getters =>
      simp only [EventClass.rename]
      rw [h giver hc.1, List.map_congr_left fun r hr => h r (hc.2 r hr)]
  | given _ owner hearers =>
      simp only [EventClass.rename]
      rw [h owner hc.1, List.map_congr_left fun r hr => h r (hc.2 r hr)]

private theorem shape_events_within' {hs : Headers V}
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, eventClassAllIn (List.range hdr.roles) e.cls) :
    ∀ {parts : List Role} {Γ outs} (t : Term (protocolDialect V hs) Γ outs),
      Within parts t → ∀ e ∈ (shapeOf t).events [] id, eventClassAllIn parts e.cls
  | _, _, _, .ret _, _, _, he => nomatch he
  | parts, _, _, .op key o _ _ rest, w, e, he => by
      have hRest := shape_events_within' hProt rest w.2
      cases o with
      | compute | narrow => exact hRest e he
      | flow kind giver getters =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · rw [eventClass_rename_id']; exact ⟨w.1.1, fun g hg => w.1.2 g hg⟩
          · exact hRest e he
      | given kind owner hearers =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_cons] at he
          rcases he with rfl | he
          · rw [eventClass_rename_id']; exact ⟨w.1.1, fun h hh => w.1.2 h hh⟩
          · exact hRest e he
      | @apply hdr callee peers _ covers _ _ =>
          simp only [shapeOf, ProtocolOp.shape, Shape.events, List.mem_append] at he
          rcases he with he | he
          · rw [shape_events_map'] at he
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
            have hall := hProt hdr (Member.mem callee) e0 he0
            have hMap : ∀ j ∈ List.range hdr.roles, peers.getD j j ∈ parts := by
              intro j hj
              have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
              rw [list_getD_of_lt peers j j hlt]
              exact w.1 _ (List.getElem_mem hlt)
            cases hC : e0.cls with
            | flow _ giver getters =>
                rw [hC] at hall; simp only [EventClass.rename, eventClassAllIn]
                exact ⟨hMap _ hall.1, fun g hg => by
                  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg; exact hMap _ (hall.2 _ hg0)⟩
            | given _ owner hearers =>
                rw [hC] at hall; simp only [EventClass.rename, eventClassAllIn]
                exact ⟨hMap _ hall.1, fun h hh => by
                  obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh; exact hMap _ (hall.2 _ hh0)⟩
          · exact hRest e he
  | _, _, _, .guard _ _ _ _ _ rest, w, e, he => shape_events_within' hProt rest w.2 e he
  | _, _, _, .choose _ _ _ _ _ onTrue onFalse _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, Shapes.events, List.append_nil, List.mem_append] at he
      rcases he with (he | he) | he
      · exact shape_events_within' hProt onTrue w.2.1 e he
      · exact shape_events_within' hProt onFalse w.2.2.1 e he
      · exact shape_events_within' hProt rest w.2.2.2 e he
  | _, _, _, .cases _ _ _ _ _ arms _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact arms_events_within' hProt arms w.2.1 e he
      · exact shape_events_within' hProt rest w.2.2 e he
  | _, _, _, .loop _ _ _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within' hProt body w.2.1 e he
      · exact shape_events_within' hProt rest w.2.2 e he
  | _, _, _, .block _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within' hProt body w.1 e he
      · exact shape_events_within' hProt rest w.2 e he
  | _, _, _, .attempt _ _ _ _ body _ rest, w, e, he => by
      simp only [shapeOf, Shape.events, List.mem_append] at he
      rcases he with he | he
      · exact shape_events_within' hProt body w.2.1 e he
      · exact shape_events_within' hProt rest w.2.2 e he
where
  arms_events_within' {hs : Headers V}
      (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, eventClassAllIn (List.range hdr.roles) e.cls) :
      ∀ {parts : List Role} {Γ mid payloads} (arms : Arms (protocolDialect V hs) Γ mid payloads),
        WithinArms parts arms → ∀ e ∈ (shapesOf arms).events [] id, eventClassAllIn parts e.cls
    | _, _, _, _, .nil, _, _, he => nomatch he
    | _, _, _, _, .cons _ arm rest, w, e, he => by
        simp only [shapesOf, Shapes.events, List.mem_append] at he
        rcases he with he | he
        · exact shape_events_within' hProt arm w.1 e he
        · exact arms_events_within' hProt rest w.2 e he

private theorem shape_events_rename_eq {hs : Headers V}
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, eventClassAllIn (List.range hdr.roles) e.cls)
    {hdr : ProtocolHeader V} (callee : Member hs.protocols hdr)
    (peers : List Role) (distinct : peers.Nodup) (covers : peers.length = hdr.roles)
    (through : List Key) :
    (hdr.shape.events through id).map (fun e => ⟨e.site, e.cls.rename (RoleMap.ofList peers distinct).to, e.τ⟩) =
      hdr.shape.events through (fun j => peers.getD j j) := by
  rw [shape_events_map', shape_events_map' (through := through) (rename := fun j => peers.getD j j),
      List.map_map]
  apply List.map_congr_left
  intro e0 he0
  dsimp only [Function.comp_def]
  rw [eventClass_rename_id']
  have hall := hProt hdr (Member.mem callee) e0 he0
  have hCong := eventClass_rename_congr' (parts := List.range hdr.roles)
    (f := (RoleMap.ofList peers distinct).to) (g := fun j => peers.getD j j) (fun j hj => by
      have hlt : j < peers.length := covers.symm ▸ List.mem_range.mp hj
      rw [list_getD_of_lt peers j j hlt, RoleMap.ofList_to peers distinct j hlt]) hall
  exact congrArg (fun c => ShapeEvent.mk _ c e0.τ) hCong

private theorem term_observe_followsEvents {hs : Headers V}
    (fns : FnTable M hs.fns) (gTable : GTable M hs.protocols)
    (hProt : ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, eventClassAllIn (List.range hdr.roles) e.cls)
    (hCallee : ∀ hdr (callee : Member hs.protocols hdr) (path : List Frame)
      (args : HList (LVal M) hdr.ins),
      hdr.shape.isStraightLine = true →
      Protocol.FollowsEvents M (hdr.shape.events (Frame.applications path) id)
        (gTable hdr callee path args)) :
    ∀ {Γ outs} (t : Term (protocolDialect V hs) Γ outs),
      ∀ (path : List Frame) (env : Env (LVal M) Γ),
        (shapeOf t).isStraightLine = true →
        Protocol.FollowsEvents M ((shapeOf t).events (Frame.applications path) id)
          (Term.observe M fns gTable t path env)
  | _, _, .ret _ => fun _ _ _ => trivial
  | _, _, .op key o args results rest => fun path env hSL => by
      have hRest : ∀ (ys : HList (LVal M) _), (shapeOf rest).isStraightLine = true →
          Protocol.FollowsEvents M ((shapeOf rest).events (Frame.applications path) id)
            (Term.observe M fns gTable rest path (env.extend results ys)) :=
        fun ys h => term_observe_followsEvents fns gTable hProt hCallee rest path (env.extend results ys) h
      cases o with
      | compute R op operands types held =>
          simp only [shapeOf, ProtocolOp.shape] at hSL ⊢
          simp only [Term.observe, observeOp, protocolOp]
          exact followsEvents_bind M (es₁ := []) _ _
            (followsEvents_map M _ _ (followsEvents_liftLocal M R _))
            (fun ys => hRest ys hSL)
      | narrow R among =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [shapeOf, ProtocolOp.shape] at hSL ⊢
          simp only [Term.observe, observeOp, protocolOp]
          exact hRest _ hSL
      | flow kind giver getters holds unique =>
          obtain ⟨x, rfl⟩ := HList.one args
          simp only [shapeOf, ProtocolOp.shape, Shape.isStraightLine] at hSL
          simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
          refine ⟨rfl, rfl, eventClass_rename_id' (.flow kind giver getters), ?_⟩
          exact followsEvents_map M _ _ (hRest _ hSL)
      | given kind owner hearers operands τ typed held unique =>
          simp only [shapeOf, ProtocolOp.shape, Shape.isStraightLine] at hSL
          cases kind with
          | coin law =>
              cases hearers with
              | nil =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨rfl, rfl, eventClass_rename_id' (.given (.coin law) owner []), fun v => ?_⟩
                  exact hRest _ hSL
              | cons h0 hs0 =>
                  simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
                  refine ⟨rfl, rfl, eventClass_rename_id' (.given (.coin law) owner (h0 :: hs0)), fun v => ?_⟩
                  exact followsEvents_map M _ _ (hRest _ hSL)
          | request service =>
              simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
              refine ⟨rfl, rfl, eventClass_rename_id' (.given (.request service) owner hearers), fun v => ?_⟩
              exact followsEvents_map M _ _ (hRest _ hSL)
      | @apply hdr callee peers distinct covers operands fits =>
          simp only [shapeOf, ProtocolOp.shape, Shape.isStraightLine, Bool.and_eq_true] at hSL
          simp only [Term.observe, observeOp, shapeOf, ProtocolOp.shape, Shape.events]
          let ρ := RoleMap.ofList peers distinct
          have hApp : Frame.applications (path ++ [.application key]) = Frame.applications path ++ [key] := by
            rw [frame_applications_append']; rfl
          have hCall := hCallee hdr callee (path ++ [.application key])
            (unmapAll M ρ.to (fitAll M fits (env.all args))) hSL.1
          rw [hApp] at hCall
          have hMapped := followsEvents_mapG M ρ.to _ hCall
          rw [shape_events_rename_eq hProt callee peers distinct covers (Frame.applications path ++ [key])] at hMapped
          exact followsEvents_bind M _ _ hMapped fun ys =>
            followsEvents_map M _ _ (hRest _ hSL.2)
  | _, _, .guard key ps c ok why rest => fun path env hSL => by
      simp only [shapeOf, Shape.isStraightLine] at hSL
      simp only [Term.observe, shapeOf, Shape.events]
      cases asBool M ok.1 (env.get c)
      · cases (shapeOf rest).events (Frame.applications path) id <;> trivial
      · exact term_observe_followsEvents fns gTable hProt hCallee rest path env hSL
  | _, _, .choose .. => fun _ _ hSL => by simp [shapeOf, Shape.isStraightLine] at hSL
  | _, _, .cases .. => fun _ _ hSL => by simp [shapeOf, Shape.isStraightLine] at hSL
  | _, _, .loop .. => fun _ _ hSL => by simp [shapeOf, Shape.isStraightLine] at hSL
  | _, _, .block key number body results rest => fun path env hSL => by
      simp only [shapeOf, Shape.isStraightLine, Bool.and_eq_true] at hSL
      simp only [Term.observe, shapeOf, Shape.events]
      have hApp : Frame.applications (path ++ [.iteration key number]) = Frame.applications path := by
        rw [frame_applications_append']; simp [Frame.applications]
      have hBody := term_observe_followsEvents fns gTable hProt hCallee body
        (path ++ [.iteration key number]) env hSL.1
      rw [hApp] at hBody
      exact followsEvents_bind M _ _ hBody fun out =>
        followsEvents_map M _ _
          (term_observe_followsEvents fns gTable hProt hCallee rest path (env.extend results out.1) hSL.2)
  | _, _, .attempt key ps ok inputs body results rest => fun path env hSL => by
      simp only [shapeOf, Shape.isStraightLine, Bool.and_eq_true] at hSL
      simp only [Term.observe, shapeOf, Shape.events]
      exact followsEvents_bind M _ _
        (term_observe_followsEvents fns gTable hProt hCallee body path
          (env.extend inputs (.cons 0 .nil)) hSL.1)
        fun out =>
          followsEvents_map M _ _
            (term_observe_followsEvents fns gTable hProt hCallee rest path
              (env.extend results out.1) hSL.2)

private theorem defs_allIn :
    ∀ {hs : Headers V}, Defs V hs →
      ∀ hdr ∈ hs.protocols, ∀ e ∈ hdr.shape.events [] id, eventClassAllIn (List.range hdr.roles) e.cls
  | _, .nil => fun _ h => nomatch h
  | _, .fn _ _ _ _ rest _ => fun h hm => defs_allIn rest h hm
  | _, .protocol hdr _ body ok rest => fun h hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [ok.shaped]
        exact shape_events_within' (defs_allIn rest) body ok.within
      · exact defs_allIn rest h hm

private theorem defs_gTable_followsEvents :
    ∀ {hs : Headers V} (defs : Defs V hs) (hdr : ProtocolHeader V)
      (callee : Member hs.protocols hdr) (path : List Frame) (args : HList (LVal M) hdr.ins),
      hdr.shape.isStraightLine = true →
      Protocol.FollowsEvents M (hdr.shape.events (Frame.applications path) id)
        (Defs.gTable M defs hdr callee path args)
  | _, .nil, _, p, _, _, _ => nomatch p
  | _, .fn _ _ _ _ rest _, hdr, callee, path, args, hSL =>
      defs_gTable_followsEvents rest hdr callee path args hSL
  | _, .protocol hdr inputs body ok rest, _, callee, path, args, hSL => by
      cases callee with
      | head =>
          rw [ok.shaped] at hSL ⊢
          exact followsEvents_map M _ _
            (term_observe_followsEvents M (Defs.fnTable M rest) (Defs.gTable M rest)
              (defs_allIn rest) (defs_gTable_followsEvents rest) body path
              (Env.empty.extend inputs args) hSL)
      | tail callee => exact defs_gTable_followsEvents rest _ callee path args hSL

unseal protocolMeaning in
/-- Every straight-line protocol (`hdr.shape.isStraightLine = true`) executes the exact event list
`hdr.shape.events (Frame.applications path) id` in 1-to-1 lockstep order. -/
theorem protocolMeaning_followsEvents (p : Typed V) {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (path : List Frame)
    (args : HList (LVal M) hdr.ins) (hSL : hdr.shape.isStraightLine = true) :
    Protocol.FollowsEvents M (hdr.shape.events (Frame.applications path) id)
      (protocolMeaning M p callee path args) :=
  defs_gTable_followsEvents M p.defs hdr callee path args hSL

/-! ## Compact wire trace and `compactLayoutVStart_reads` -/

/-- Exact trace of wire values and serialized chunks written by the prover matching `specs`. -/
inductive WireTrace (d : Deployed V) (layout : Layout) {unitTy : V.Ty} :
    (specs : List (WireSpec V d.admitted.program.headers.fns unitTy)) →
    HList M.Val (specs.map (·.ty)) → List (List (M.Val unitTy)) → Prop where
  | nil : WireTrace d layout [] .nil []
  | cons {s : WireSpec V d.admitted.program.headers.fns unitTy}
      {rest : List (WireSpec V d.admitted.program.headers.fns unitTy)}
      {wRef : TypedFnRef V d.admitted.program.headers.fns [s.ty] [.seq unitTy none]}
      {v : M.Val s.ty} {vs : HList M.Val (rest.map (·.ty))}
      {chunk : List (M.Val unitTy)} {chunks : List (List (M.Val unitTy))}
      (hW : findLayoutWrite d.admitted layout.module unitTy s.ty = some wRef)
      (hR : findLayoutRead d.admitted layout.module unitTy s.ty = some s.readRef)
      (hV : M.Valid s.ty v)
      (hEval : wRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil) = .done (.cons chunk .nil))
      (hChunkV : ∀ u ∈ chunk, M.Valid unitTy u)
      (hRest : WireTrace d layout rest vs chunks) :
      WireTrace d layout (s :: rest) (.cons v vs) (chunk :: chunks)

private theorem wireTrace_flatten_valid {d : Deployed V} {layout : Layout} {unitTy : V.Ty} :
    ∀ {specs : List (WireSpec V d.admitted.program.headers.fns unitTy)}
      {vals : HList M.Val (specs.map (·.ty))} {chunks : List (List (M.Val unitTy))},
      WireTrace M d layout specs vals chunks → ∀ u ∈ chunks.flatten, M.Valid unitTy u
  | _, _, _, .nil, _, hu => nomatch hu
  | _, _, _, .cons _ _ _ _ hChV hRest, u, hu => by
      rcases List.mem_append.mp hu with h1 | h2
      · exact hChV u h1
      · exact wireTrace_flatten_valid hRest u h2

/-- Convert a `WireSpec`-indexed `HList` into the corresponding sigma list. -/
def wireSigmaList {fns : List (FnHeader V)} {unitTy : V.Ty} :
    (specs : List (WireSpec V fns unitTy)) → HList M.Val (specs.map (·.ty)) →
    List ((τ : V.Ty) × M.Val τ)
  | [], .nil => []
  | s :: rest, .cons v vs => ⟨s.ty, v⟩ :: wireSigmaList rest vs

private theorem wireSigmaList_map_fst {fns : List (FnHeader V)} {unitTy : V.Ty} :
    ∀ (specs : List (WireSpec V fns unitTy)) (vals : HList M.Val (specs.map (·.ty))),
      (wireSigmaList M specs vals).map Sigma.fst = specs.map (·.ty)
  | [], .nil => rfl
  | _ :: rest, .cons _ vs => congrArg (_ :: ·) (wireSigmaList_map_fst rest vs)

private theorem ofSigmaList_wireSigmaList {fns : List (FnHeader V)} {unitTy : V.Ty} :
    ∀ (specs : List (WireSpec V fns unitTy)) (vals : HList M.Val (specs.map (·.ty))),
      HList.ofSigmaList (wireSigmaList M specs vals) =
        cast (congrArg (HList M.Val) (wireSigmaList_map_fst M specs vals).symm) vals
  | [], .nil => rfl
  | s :: rest, .cons v vs => by
      have ih := ofSigmaList_wireSigmaList rest vs
      have hCons : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (x : M.Val s.ty) (t : HList M.Val l₁),
          HList.cons x (cast (congrArg (HList M.Val) heq) t) =
            cast (congrArg (HList M.Val) (congrArg (s.ty :: ·) heq)) (HList.cons x t) := by
        intro _ _ heq _ _; subst heq; rfl
      exact (congrArg (HList.cons v) ih).trans (hCons (wireSigmaList_map_fst M rest vs).symm v vs)

private theorem env_all_reindex_insert2 {Γ : Ctx V.Ty} (env : Env M.Val Γ) {fresh : Nat}
    (hfresh : FreshFrom Γ fresh) {τ₁ τ₂ : V.Ty} (v₁ : M.Val τ₁) (v₂ : M.Val τ₂) :
    ∀ {ts : List V.Ty} (vars : HList (Var Γ) ts),
      ((env.insert fresh v₁).insert (fresh + 1) v₂).all
        (vars.reindex ((hfresh.within τ₁).trans ((hfresh.insert τ₁).within τ₂))) = env.all vars
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show HList.cons (((env.insert fresh v₁).insert (fresh + 1) v₂).get _) _ = HList.cons (env.get x) (env.all xs)
      rw [env_get_insert2_reindex env hfresh _ _ _ x, env_all_reindex_insert2 env hfresh v₁ v₂ xs]

private theorem env_all_reindex_insert1 {Γ : Ctx V.Ty} (env : Env M.Val Γ) {fresh : Nat}
    (hfresh : FreshFrom Γ fresh) {τ₁ : V.Ty} (v₁ : M.Val τ₁) :
    ∀ {ts : List V.Ty} (vars : HList (Var Γ) ts),
      (env.insert fresh v₁).all (vars.reindex (hfresh.within τ₁)) = env.all vars
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show HList.cons ((env.insert fresh v₁).get _) _ = HList.cons (env.get x) (env.all xs)
      rw [env_get_insert_reindex env hfresh, env_all_reindex_insert1 env hfresh v₁ xs]

private theorem env_all_append_local {Γ : Ctx V.Ty} (env : Env M.Val Γ) :
    ∀ {as bs : List V.Ty} (xs : HList (Var Γ) as) (ys : HList (Var Γ) bs),
      env.all (HList.append xs ys) = HList.append (env.all xs) (env.all ys)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ xs, ys => congrArg (HList.cons _) (env_all_append_local env xs ys)

private theorem env_all_cast_local {Γ : Ctx V.Ty} (env : Env M.Val Γ) {as bs : List V.Ty}
    (h : as = bs) (xs : HList (Var Γ) as) :
    env.all (cast (congrArg (HList (Var Γ)) h) xs) = cast (congrArg (HList M.Val) h) (env.all xs) := by
  subst h; rfl

/-- Exact dual of `buildCompactParse_written`: on any canonical proof buffer `pre ++ chunks.flatten`
matching `WireTrace`, `buildCompactParse` succeeds and returns the exact tuple
`Tys.ofHList (accVals ++ wireVals)`. -/
theorem buildCompactParse_reads {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (wireTys : List V.Ty) :
    ∀ {specs : List (WireSpec V d.admitted.program.headers.fns unitTy)}
      {wireVals : HList M.Val (specs.map (·.ty))}
      {chunks : List (List (M.Val unitTy))},
      WireTrace M d layout specs wireVals chunks →
      ∀ {Γ : Ctx V.Ty} (fresh : Nat) (hfresh : FreshFrom Γ fresh) (env : Env M.Val Γ)
        (bufVar : Var Γ (.seq unitTy none)) (offVar : Var Γ .nat)
        (parsedAcc : List V.Ty) (accVars : HList (Var Γ) parsedAcc)
        (pre : List (M.Val unitTy)),
        (∀ u ∈ pre, M.Valid unitTy u) →
        env.get bufVar = pre ++ chunks.flatten →
        env.get offVar = pre.length →
        ∀ (hMatch : parsedAcc ++ (specs.map fun ws => (⟨ws.ty, ws.readRef⟩ :
          (τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat])).map Sigma.fst = wireTys),
        have hEqAll : parsedAcc ++ specs.map (·.ty) = wireTys := by
          simpa [List.map_map, Function.comp_def] using hMatch
        (buildCompactParse unitTy hfree guardKey wireTys fresh hfresh bufVar offVar
            parsedAcc accVars (specs.map fun ws => (⟨ws.ty, ws.readRef⟩ :
              (τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat])) hMatch).denote
          (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) [] env =
          .done (.cons (Tys.ofHList M (tysOfList wireTys)
            (cast (congrArg (HList M.Val) ((tysOfList_toList wireTys).trans hEqAll.symm).symm)
              (HList.append (env.all accVars) wireVals))) .nil)
  | _, _, _, .nil, Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, pre, _, hBuf, hOff, hMatch => by
      intro hEqAll
      simp only [List.map_nil]
      unfold buildCompactParse
      rw [letOp1_local_owned_denote]
      simp only [Env.all]
      rw [ownedOp_seqLength]
      simp only [Process.bind, HList.single]
      rw [letOp1_local_owned_denote]
      simp only [Env.all]
      rw [env_get_insert_reindex env hfresh, env_get_insert_self, ownedOp_natEqual]
      simp only [Process.bind, HList.single]
      erw [Term.denote_guard, env_get_insert_self, localSem_holds]
      have hBufPre : env.get bufVar = pre := by simpa using hBuf
      rw [hOff, hBufPre, Nat.beq_refl]
      simp only [Bool.cond_true]
      rw [letOp1_local_owned_denote]
      rw [env_all_cast_local M _ (by simpa [tysOfList_toList] using hEqAll), env_all_reindex_insert2 M env hfresh]
      rw [ownedOp_makeTuple]
      simp only [Process.bind, HList.single]
      erw [Term.denote_ret]
      simp only [Env.all, env_get_insert_self]
      congr 1; congr 1; congr 1
      have hNil : ∀ {ts : List V.Ty} (xs : HList M.Val ts),
          HList.append xs (.nil : HList M.Val []) = cast (congrArg (HList M.Val) (List.append_nil ts).symm) xs := by
        intro ts xs
        induction xs with
        | nil => rfl
        | cons v vs ih =>
            have hC : ∀ {τ : V.Ty} {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (u : M.Val τ) (t : HList M.Val l₁),
                HList.cons u (cast (congrArg (HList M.Val) heq) t) =
                  cast (congrArg (HList M.Val) (congrArg (τ :: ·) heq)) (HList.cons u t) := by
              intro _ _ _ heq _ _; subst heq; rfl
            exact (congrArg (HList.cons v) ih).trans (hC (List.append_nil _).symm v vs)
      rw [hNil (env.all accVars), cast_cast]
  | s :: rest, .cons v vs, chunk :: restChunks, .cons hW hR hV hWEval hChV hRest,
      Γ, fresh, hfresh, env, bufVar, offVar, parsedAcc, accVars, pre, hPre, hBuf, hOff, hMatch => by
      intro hEqAll
      simp only [List.map_cons]
      unfold buildCompactParse
      erw [letOp2_denote, localSem_op]
      simp only [Env.all]
      change (s.readRef.eval M (Defs.fnTable M d.admitted.program.defs)
          (.cons (env.get bufVar) (.cons (env.get offVar) .nil))).bind _ = _
      have hBufSplit : env.get bufVar = pre ++ chunk ++ restChunks.flatten := by
        simpa [List.append_assoc] using hBuf
      have hRT := layoutLawful_roundTrip M hLayOpt hLayLaw hW hR hV hPre
        (wireTrace_flatten_valid M hRest) hWEval
      rw [hBufSplit, hOff, hRT]
      dsimp only [Process.bind]
      let env2 := (env.insert fresh v).insert (τ := Ty.nat) (fresh + 1) (pre.length + chunk.length)
      have hBuf2 : env2.get (bufVar.reindex ((hfresh.within s.ty).trans ((hfresh.insert s.ty).within .nat))) =
          (pre ++ chunk) ++ restChunks.flatten := by
        rw [env_get_insert2_reindex env hfresh _ _ _ bufVar, hBufSplit]
      have hOff2 : env2.get (freshVar (Γ.insert fresh s.ty) (fresh + 1) .nat) = (pre ++ chunk).length := by
        rw [env_get_insert_self, List.length_append]
      have hPreCh : ∀ u ∈ pre ++ chunk, M.Valid unitTy u := fun u hu => by
        rcases List.mem_append.mp hu with h1 | h2
        · exact hPre u h1
        · exact hChV u h2
      have hAcc2 : env2.all (HList.append
          (accVars.reindex ((hfresh.within s.ty).trans ((hfresh.insert s.ty).within .nat)))
          (.cons ((freshVar Γ fresh s.ty).reindex ((hfresh.insert s.ty).within .nat)) .nil)) =
          HList.append (env.all accVars) (.cons v .nil) := by
        rw [env_all_append_local M, env_all_reindex_insert2 M env hfresh]
        congr 1
        show HList.cons (env2.get _) .nil = HList.cons v .nil
        congr 1
        rw [env_get_insert_reindex _ (hfresh.insert s.ty), env_get_insert_self]
      have ih := buildCompactParse_reads hLayOpt hLayLaw unitTy hfree guardKey wireTys hRest
        (fresh + 2) ((hfresh.insert s.ty).insert .nat) env2
        (bufVar.reindex ((hfresh.within s.ty).trans ((hfresh.insert s.ty).within .nat)))
        (freshVar (Γ.insert fresh s.ty) (fresh + 1) .nat)
        (parsedAcc ++ [s.ty])
        (HList.append
          (accVars.reindex ((hfresh.within s.ty).trans ((hfresh.insert s.ty).within .nat)))
          (.cons ((freshVar Γ fresh s.ty).reindex ((hfresh.insert s.ty).within .nat)) .nil))
        (pre ++ chunk) hPreCh hBuf2 hOff2 (by simpa [List.append_assoc] using hMatch)
      change Term.denote (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) _ [] env2 = _
      rw [ih, hAcc2]
      congr 1; congr 1; congr 1
      rw [hlist_append_assoc, cast_cast]; rfl

/-- Evaluate a list of typed variables in `env` into a sigma list of typed values. -/
def evalVarList {Γ : Ctx V.Ty} (env : Env M.Val Γ) :
    List ((τ : V.Ty) × Var Γ τ) → List ((τ : V.Ty) × M.Val τ)
  | [] => []
  | ⟨τ, v⟩ :: rest => ⟨τ, env.get v⟩ :: evalVarList env rest

theorem evalVarList_map_fst {Γ : Ctx V.Ty} (env : Env M.Val Γ) :
    ∀ (xs : List ((τ : V.Ty) × Var Γ τ)),
      (evalVarList M env xs).map Sigma.fst = xs.map Sigma.fst
  | [] => rfl
  | ⟨_, _⟩ :: rest => congrArg (_ :: ·) (evalVarList_map_fst env rest)

theorem evalVarList_stmtPos_go (prover verifier : Role) (unitTy : V.Ty) :
    ∀ (sIdx : Nat) {ins : List (LTy V)} (vals : HList (LVal M) ins) (proof : List (M.Val unitTy)),
      let vTys := .seq unitTy none :: held verifier ins
      let stmtItems : List ((τ : V.Ty) × Var (Ctx.positional vTys) τ) :=
        (statementPositions.go verifier prover verifier (.inr rfl) sIdx ins).map fun sp =>
          ⟨sp.ty, posVar vTys (sp.heldIndex + 1) (by simpa [vTys] using sp.atHeld)⟩
      evalVarList M
        (Env.positional (.cons (a := .seq unitTy none) proof (heldValues M verifier (hideAll M verifier vals))))
        stmtItems = compactStmtArgs M prover verifier vals
  | _, [], .nil, _ => rfl
  | sIdx, a :: rest, .cons v vs, proof => by
      have hGet : ∀ {ts : List V.Ty} (xs : HList M.Val ts) (k : Nat) {τ : V.Ty} (hk : ts[k]? = some τ),
          (Env.positional xs).get (posVar ts k hk) = HList.getAt xs k hk := by
        intro ts xs k τ hk; exact env_get_positional xs k hk
      have hGetCons : ∀ {t0 : V.Ty} {ts : List V.Ty} (x0 : M.Val t0) (xs : HList M.Val ts)
          (k : Nat) {τ : V.Ty} (hk : ts[k]? = some τ),
          HList.getAt (HList.cons x0 xs) (k + 1) (by simpa using hk) = HList.getAt xs k hk := by
        intro _ _ _ _ _ _ _; rfl
      have hEvalMap : ∀ {Γ : Ctx V.Ty} (env : Env M.Val Γ) {α : Type} (f : α → (τ : V.Ty) × Var Γ τ)
          (xs : List α),
          evalVarList M env (xs.map f) = xs.map fun x => ⟨(f x).1, env.get (f x).2⟩ := by
        intro Γ env α f xs
        induction xs with
        | nil => rfl
        | cons _ _ ih => exact congrArg (_ :: ·) ih
      have hGetAtCast : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂) (xs : HList M.Val ts₁)
          (k : Nat) {τ : V.Ty} (hk : ts₂[k]? = some τ),
          HList.getAt (cast (congrArg (HList M.Val) heq) xs) k hk =
            HList.getAt xs k (heq ▸ hk) := by
        intro _ _ heq _ _ _ _; subst heq; rfl
      simp only [statementPositions.go, compactStmtArgs]
      by_cases hBoth : prover ∈ a.holders ∧ verifier ∈ a.holders
      · rw [dite_eq_left hBoth, ite_eq_left hBoth]
        have hV : verifier ∈ a.holders := hBoth.2
        have ih := evalVarList_stmtPos_go prover verifier unitTy (sIdx + 1) vs proof
        dsimp only at ih
        rw [hEvalMap] at ih ⊢
        simp only [List.map_cons, List.map_map, List.cons_append, List.nil_append]
        congr 1
        · rw [hGet, hGetCons _ _ 0 (by simp [held, hV])]
          show (⟨a.ty, HList.getAt (heldValues M verifier (.cons (hide M verifier a v) (hideAll M verifier vs))) 0 _⟩ :
            (τ : V.Ty) × M.Val τ) = ⟨a.ty, v⟩
          rw [heldValues_cons_in M verifier hV, hGetAtCast (by simp [held, hV])]
          simp only [HList.getAt, reveal_hide]
        · rw [← ih]
          apply List.map_congr_left
          intro p _
          dsimp only [Function.comp_def]
          rw [hGet, hGet, hGetCons _ _ (p.heldIndex + 1) (by simp [held, hV]; exact p.atHeld),
            hGetCons _ _ p.heldIndex p.atHeld]
          show (⟨p.ty, HList.getAt (heldValues M verifier (.cons (hide M verifier a v) (hideAll M verifier vs)))
            (p.heldIndex + 1) _⟩ : (τ : V.Ty) × M.Val τ) =
            ⟨p.ty, HList.getAt (heldValues M verifier (hideAll M verifier vs)) p.heldIndex p.atHeld⟩
          rw [heldValues_cons_in M verifier hV, hGetAtCast (by simp [held, hV])]
          rfl
      · rw [dite_eq_right hBoth, ite_eq_right hBoth, List.nil_append]
        have ih := evalVarList_stmtPos_go prover verifier unitTy sIdx vs proof
        dsimp only at ih
        rw [hEvalMap] at ih ⊢
        by_cases hV : verifier ∈ a.holders
        · rw [dite_eq_left hV, List.map_map, ← ih]
          apply List.map_congr_left
          intro p _
          dsimp only [Function.comp_def]
          rw [hGet, hGet, hGetCons _ _ (p.heldIndex + 1) (by simp [held, hV]; exact p.atHeld),
            hGetCons _ _ p.heldIndex p.atHeld]
          show (⟨p.ty, HList.getAt (heldValues M verifier (.cons (hide M verifier a v) (hideAll M verifier vs)))
            (p.heldIndex + 1) _⟩ : (τ : V.Ty) × M.Val τ) =
            ⟨p.ty, HList.getAt (heldValues M verifier (hideAll M verifier vs)) p.heldIndex p.atHeld⟩
          rw [heldValues_cons_in M verifier hV, hGetAtCast (by simp [held, hV])]
          rfl
        · rw [dite_eq_right hV, List.map_map, ← ih]
          apply List.map_congr_left
          intro p _
          dsimp only [Function.comp_def]
          rw [hGet, hGet, hGetCons _ _ p.heldIndex (by simp [held, hV]; exact p.atHeld),
            hGetCons _ _ p.heldIndex p.atHeld]
          show (⟨p.ty, HList.getAt (heldValues M verifier (.cons (hide M verifier a v) (hideAll M verifier vs)))
            p.heldIndex _⟩ : (τ : V.Ty) × M.Val τ) =
            ⟨p.ty, HList.getAt (heldValues M verifier (hideAll M verifier vs)) p.heldIndex p.atHeld⟩
          rw [heldValues_cons_out M verifier hV, hGetAtCast (by simp [held, hV])]

/-- Evaluating `compactLayoutVStart` on a prover's canonical compact proof buffer `chunks.flatten`
and verifier's statement inputs reconstructs the exact tuple state
`Tys.ofHList (stmtVals ++ wireVals)`. -/
theorem compactLayoutVStart_reads {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    (prover verifier : Role) {ins : List (LTy V)}
    (unitTy : V.Ty) (hfree : Ty.isLinear V unitTy = false) (guardKey : Key)
    (vals : HList (LVal M) ins)
    {specs : List (WireSpec V d.admitted.program.headers.fns unitTy)}
    {wireVals : HList M.Val (specs.map (·.ty))}
    {chunks : List (List (M.Val unitTy))}
    (hTrace : WireTrace M d layout specs wireVals chunks) :
    let vTys := .seq unitTy none :: held verifier ins
    let stmtItems : List ((τ : V.Ty) × Var (Ctx.positional vTys) τ) :=
      (statementPositions verifier prover verifier (.inr rfl) ins).map fun sp =>
        ⟨sp.ty, posVar vTys (sp.heldIndex + 1) (by simpa [vTys] using sp.atHeld)⟩
    let readers : List ((τ : V.Ty) × SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]) :=
      specs.map fun ws => ⟨ws.ty, ws.readRef⟩
    have hStmtTys : stmtItems.map Sigma.fst = (compactStmtArgs M prover verifier vals).map Sigma.fst :=
      (evalVarList_map_fst M _ stmtItems).symm.trans
        (congrArg (List.map Sigma.fst) (evalVarList_stmtPos_go M prover verifier unitTy 0 vals chunks.flatten))
    have hReadersTys : readers.map Sigma.fst = specs.map (·.ty) := by simp [readers]
    (compactLayoutVStart unitTy hfree guardKey stmtItems readers).denote
      (localSem M d.admitted.program.headers.fns (Defs.fnTable M d.admitted.program.defs)) []
      (Env.positional (.cons (a := .seq unitTy none) chunks.flatten
        (heldValues M verifier (hideAll M verifier vals)))) =
      .done (.cons (Tys.ofHList M (tysOfList (stmtItems.map Sigma.fst ++ readers.map Sigma.fst))
        (cast (congrArg (HList M.Val) (by rw [tysOfList_toList, hReadersTys]))
          (HList.append
            (cast (congrArg (HList M.Val) hStmtTys.symm) (HList.ofSigmaList (compactStmtArgs M prover verifier vals)))
            wireVals))) .nil) := by
  intro vTys stmtItems readers hStmtTys hReadersTys
  unfold compactLayoutVStart
  erw [letOp1_denote, localSem_op_literal]
  simp only [Process.bind, HList.single, Ty.readLiteral, Ty.read]
  let env0 := Env.positional (.cons (a := Ty.seq unitTy none) chunks.flatten
    (heldValues M verifier (hideAll M verifier vals)))
  let env1 := env0.insert (τ := Ty.nat) vTys.length (0 : Nat)
  have hBuf1 : env1.get ((posVar vTys 0 rfl).reindex ((positional_freshFrom vTys).within .nat)) =
      [] ++ chunks.flatten := by
    rw [env_get_insert_reindex _ (positional_freshFrom _)]
    exact env_get_positional (HList.cons (V := M.Val) (a := Ty.seq unitTy none) chunks.flatten _) 0 rfl
  have hOff1 : env1.get (freshVar (Ctx.positional vTys) vTys.length .nat) = ([] : List (M.Val unitTy)).length :=
    env_get_insert_self _ _ _
  have hPackEval : ∀ (xs : List ((τ : V.Ty) × Var (Ctx.positional vTys) τ)),
      env1.all (compactLayoutVStart.packStmts (fns := d.admitted.program.headers.fns)
          (r := verifier) (ins := ins) unitTy
          ((Ctx.positional vTys).insert vTys.length .nat) ((positional_freshFrom vTys).within .nat) xs) =
        cast (congrArg (HList M.Val) (evalVarList_map_fst M env0 xs))
          (HList.ofSigmaList (evalVarList M env0 xs)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p rest ih =>
        cases p with | mk τ var =>
        show HList.cons (env1.get (var.reindex _)) _ = _
        rw [env_get_insert_reindex env0 (positional_freshFrom vTys), ih]
        have hCons : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (u : M.Val τ) (t : HList M.Val l₁),
            HList.cons u (cast (congrArg (HList M.Val) heq) t) =
              cast (congrArg (HList M.Val) (congrArg (τ :: ·) heq)) (HList.cons u t) := by
          intro _ _ heq _ _; subst heq; rfl
        exact hCons (evalVarList_map_fst M env0 rest) (env0.get var) _
  have hRun := buildCompactParse_reads M hLayOpt hLayLaw unitTy hfree guardKey
    (stmtItems.map Sigma.fst ++ readers.map Sigma.fst) hTrace
    (vTys.length + 1) ((positional_freshFrom vTys).insert .nat) env1
    ((posVar vTys 0 rfl).reindex ((positional_freshFrom vTys).within .nat))
    (freshVar (Ctx.positional vTys) vTys.length .nat)
    (stmtItems.map Sigma.fst)
    (compactLayoutVStart.packStmts (fns := d.admitted.program.headers.fns)
      (r := verifier) (ins := ins) unitTy
      ((Ctx.positional vTys).insert vTys.length .nat) ((positional_freshFrom vTys).within .nat) stmtItems)
    [] (fun _ h => nomatch h) hBuf1 hOff1 rfl
  have hPack : env1.all (compactLayoutVStart.packStmts (fns := d.admitted.program.headers.fns)
      (r := verifier) (ins := ins) unitTy
      ((Ctx.positional vTys).insert vTys.length .nat) ((positional_freshFrom vTys).within .nat) stmtItems) =
      cast (congrArg (HList M.Val) hStmtTys.symm) (HList.ofSigmaList (compactStmtArgs M prover verifier vals)) := by
    rw [hPackEval stmtItems]
    have hEv := evalVarList_stmtPos_go M prover verifier unitTy 0 vals chunks.flatten
    have hGen : ∀ {xs ys : List ((τ : V.Ty) × M.Val τ)} (hxy : xs = ys)
        (h1 : xs.map Sigma.fst = stmtItems.map Sigma.fst)
        (h2 : ys.map Sigma.fst = stmtItems.map Sigma.fst),
        cast (congrArg (HList M.Val) h1) (HList.ofSigmaList xs) =
          cast (congrArg (HList M.Val) h2) (HList.ofSigmaList ys) := by
      intro _ _ hxy _ _; subst hxy; rfl
    exact hGen hEv (evalVarList_map_fst M env0 stmtItems) hStmtTys.symm
  rw [hPack] at hRun
  exact hRun

/-! ## Compact clause answering, splitting, and wire-slot lookup lemmas -/

private theorem list_nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: _, hN, 0, j + 1, _, hj, hEq => by
      simp only [List.nodup_cons] at hN
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hN.1
  | _ :: _, hN, i + 1, 0, hi, _, hEq => by
      simp only [List.nodup_cons] at hN
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hN.1
  | _ :: _, hN, i + 1, j + 1, hi, hj, hEq => by
      simp only [List.nodup_cons] at hN
      exact congrArg (· + 1) (list_nodup_getElem_inj hN.2
        (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hEq)

private theorem clause_answer_append_right {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {st : V.Ty}
    (op : ROp M) (s : M.Val st) :
    ∀ (cs₁ cs₂ : List (Clause V hs r st)),
      (∀ c ∈ cs₁, ¬ ClauseMatches M c op) →
      Clause.answer M fnTable rTable (cs₁ ++ cs₂) op s =
        Clause.answer M fnTable rTable cs₂ op s
  | [], _, _ => rfl
  | c :: rest, cs₂, hNo => by
      have hHead := hNo c List.mem_cons_self
      have hTail := clause_answer_append_right fnTable rTable op s rest cs₂
        (fun c' hc' => hNo c' (List.mem_cons_of_mem _ hc'))
      rw [List.cons_append]
      conv => lhs; unfold Clause.answer
      exact (dite_eq_right hHead).trans hTail

private theorem compactReadSlotClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) (at_ : Occurrence) (hSite : site = at_.site)
    (st : stateTys.Val M.toCarriers)
    (cs : List (Clause V hs verifier (.tuple stateTys))) :
    Clause.answer M fnTable rTable
        (compactReadSlotClause htfree verifier prover site kind pos :: cs)
        (.get kind prover at_ τ) st =
      .done (Tys.getAt M stateTys pos st, st) := by
  unfold Clause.answer
  split
  · have hDen := compactReadSlotClause_denote M fnTable rTable htfree verifier prover site kind pos at_.path st
    have hMapArg : Process.mapHalt (fun why => (why, st))
        ((compactReadSlotClause (hs := hs) htfree verifier prover site kind pos).code.denote
          (roleSem M verifier fnTable rTable) at_.path
          (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))) =
        .done (aloneIn M verifier (.cons (Tys.getAt M stateTys pos st) (.cons (a := Ty.tuple stateTys) st .nil))) := by
      rw [hDen]; rfl
    erw [hMapArg]
    dsimp only [Process.map]
    erw [aloneOut_aloneIn]
    rfl
  · rename_i hNo
    exact absurd ⟨hSite, rfl, rfl, rfl⟩ hNo

private theorem compactRecoverClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recoverRef : SafeFnRef V hs.fns stateTys.toList [τ])
    (at_ : Occurrence) (hSite : site = at_.site)
    (st : stateTys.Val M.toCarriers) (val : M.Val τ)
    (hRec : recoverRef.eval M fnTable (Tys.toHList M stateTys st) = .done (.cons val .nil))
    (cs : List (Clause V hs verifier (.tuple stateTys))) :
    Clause.answer M fnTable rTable
        (compactRecoverClause verifier prover site kind recoverRef :: cs)
        (.get kind prover at_ τ) st =
      .done (val, st) := by
  unfold Clause.answer
  split
  · have hDen : (compactRecoverClause (hs := hs) verifier prover site kind recoverRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil))) =
        .done (aloneIn M verifier (.cons val (.cons (a := Ty.tuple stateTys) st .nil))) := by
      rw [compactRecoverClause_denote, hRec]; rfl
    have hMapArg : Process.mapHalt (fun why => (why, st))
        ((compactRecoverClause (hs := hs) verifier prover site kind recoverRef).code.denote
          (roleSem M verifier fnTable rTable) at_.path
          (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)))) =
        .done (aloneIn M verifier (.cons val (.cons (a := Ty.tuple stateTys) st .nil))) := by
      rw [hDen]; rfl
    erw [hMapArg]
    dsimp only [Process.map]
    erw [aloneOut_aloneIn]
    rfl
  · rename_i hNo
    exact absurd ⟨hSite, rfl, rfl, rfl⟩ hNo

private theorem compactCompareClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ)
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (at_ : Occurrence) (hSite : toldSite = at_.site)
    (derived : M.Val τ) (st : stateTys.Val M.toCarriers)
    (hEq : eqRef.eval M fnTable (.cons derived (.cons (Tys.getAt M stateTys pos st) .nil)) =
      .done (.cons true .nil))
    (cs : List (Clause V hs verifier (.tuple stateTys))) :
    Clause.answer M fnTable rTable
        (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef :: cs)
        (.give .message [prover] at_ τ derived) st =
      .done ((), st) := by
  unfold Clause.answer
  split
  · have hDen : (compactCompareClause (hs := hs) htfree verifier prover toldSite guardKey pos eqRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons derived (.cons (a := Ty.tuple stateTys) st .nil)))) =
        .done (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)) := by
      rw [compactCompareClause_denote, hEq]; rfl
    have hMapArg : Process.mapHalt (fun why => (why, st))
        ((compactCompareClause (hs := hs) htfree verifier prover toldSite guardKey pos eqRef).code.denote
          (roleSem M verifier fnTable rTable) at_.path
          (Env.positional (aloneIn M verifier (.cons derived (.cons (a := Ty.tuple stateTys) st .nil))))) =
        .done (aloneIn M verifier (.cons (a := Ty.tuple stateTys) st .nil)) := by
      rw [hDen]; rfl
    erw [hMapArg]
    dsimp only [Process.map]
    erw [aloneOut_aloneIn]
    rfl
  · rename_i hNo
    exact absurd ⟨hSite, rfl, rfl, rfl⟩ hNo

private theorem findWireMember_append_right {fns : List (FnHeader V)} {unitTy : V.Ty}
    (targetSite : Site) (targetTy : V.Ty) :
    ∀ (pref rem : List (WireSpec V fns unitTy)) {m : Member (rem.map (·.ty)) targetTy},
      targetSite ∉ pref.map (·.site) →
      findWireMember targetSite targetTy rem = some m →
      findWireMember targetSite targetTy (pref ++ rem) =
        some (cast (congrArg (fun l => Member l targetTy) (List.map_append (f := (·.ty)) (l₁ := pref) (l₂ := rem)).symm)
          (memberAppendRight (pref.map (·.ty)) m))
  | [], _, _, _, hFind => hFind
  | s :: pref, rem, m, hNotIn, hFind => by
      have hNe : s.site ≠ targetSite := fun heq => hNotIn (heq ▸ List.mem_cons_self)
      have ih := findWireMember_append_right targetSite targetTy pref rem
        (fun hm => hNotIn (List.mem_cons_of_mem _ hm)) hFind
      show (if h : s.site = targetSite ∧ s.ty = targetTy then _ else
        (findWireMember targetSite targetTy (pref ++ rem)).map Member.tail) = _
      rw [dite_eq_right (fun hm => hNe hm.1), ih]
      dsimp only [Option.map]
      congr 1
      have hTail : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (k : Member l₁ targetTy),
          Member.tail (b := s.ty) (cast (congrArg (fun l => Member l targetTy) heq) k) =
            cast (congrArg (fun l => Member (s.ty :: l) targetTy) heq) (Member.tail k) := by
        intro _ _ heq _; subst heq; rfl
      exact hTail (List.map_append (f := (·.ty)) (l₁ := pref) (l₂ := rem)).symm (memberAppendRight (pref.map (·.ty)) m)

private theorem collectCompactWire_split {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (l₁ l₂ : List (ShapeEvent V)) {wAll pAll},
      collectCompactWire a layout unitTy prover verifier declKey events idx (l₁ ++ l₂) = .ok (wAll, pAll) →
      ∃ w₁ p₁ w₂ p₂,
        collectCompactWire a layout unitTy prover verifier declKey events idx l₁ = .ok (w₁, p₁) ∧
        collectCompactWire a layout unitTy prover verifier declKey events (idx + l₁.length) l₂ = .ok (w₂, p₂) ∧
        wAll = w₁ ++ w₂ ∧ pAll = p₁ ++ p₂
  | idx, [], l₂, wAll, pAll, h => ⟨[], [], wAll, pAll, rfl, by simpa using h, rfl, rfl⟩
  | idx, e :: rest, l₂, wAll, pAll, h => by
      rw [List.cons_append] at h
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) (rest ++ l₂) with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨w₁, p₁, w₂, p₂, h1, h2, hwEq, hpEq⟩ := collectCompactWire_split (idx + 1) rest l₂ hRec
          have h2' : collectCompactWire a layout unitTy prover verifier declKey events (idx + (e :: rest).length) l₂ =
              .ok (w₂, p₂) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; cases h
                    refine ⟨w₁, _ :: p₁, w₂, p₂, ?_, h2', hwEq, by rw [hpEq]; rfl⟩
                    unfold collectCompactWire
                    rw [h1]; dsimp only [bind, Except.bind]
                    rw [hCls]; dsimp only; rw [ite_eq_left hPV, hLk]
                | none =>
                    rw [hLk] at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      refine ⟨⟨e.site, e.τ, _⟩ :: w₁, _ :: p₁, w₂, p₂, ?_, h2', by rw [hwEq]; rfl, by rw [hpEq]; rfl⟩
                      unfold collectCompactWire
                      rw [h1]; dsimp only [bind, Except.bind]
                      rw [hCls]; dsimp only; rw [ite_eq_left hPV, hLk, hW, hR]
              · rename_i hNotPV
                cases h
                refine ⟨w₁, p₁, w₂, p₂, ?_, h2', hwEq, hpEq⟩
                unfold collectCompactWire
                rw [h1]; dsimp only [bind, Except.bind]
                rw [hCls]; dsimp only; rw [ite_eq_right hNotPV]
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ =>
                  cases h
                  refine ⟨w₁, p₁, w₂, p₂, ?_, h2', hwEq, hpEq⟩
                  unfold collectCompactWire
                  rw [h1]; dsimp only [bind, Except.bind]; rw [hCls]
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    split at h
                    · rename_i hCar
                      cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨⟨⟨e.site.through, drawToldKey events idx⟩, e.τ, _⟩ :: w₁, _ :: p₁,
                          w₂, p₂, ?_, h2', by rw [hwEq]; rfl, by rw [hpEq]; rfl⟩
                        unfold collectCompactWire
                        rw [h1]; dsimp only [bind, Except.bind]
                        rw [hCls]; dsimp only; rw [ite_eq_left hCoin, ite_eq_left hCar, hW, hR]
                    · rename_i hNotCar
                      cases h
                      refine ⟨w₁, _ :: p₁, w₂, p₂, ?_, h2', hwEq, by rw [hpEq]; rfl⟩
                      unfold collectCompactWire
                      rw [h1]; dsimp only [bind, Except.bind]
                      rw [hCls]; dsimp only; rw [ite_eq_left hCoin, ite_eq_right hNotCar]
                  · rename_i hNotCoin
                    cases h
                    refine ⟨w₁, p₁, w₂, p₂, ?_, h2', hwEq, hpEq⟩
                    unfold collectCompactWire
                    rw [h1]; dsimp only [bind, Except.bind]
                    rw [hCls]; dsimp only; rw [ite_eq_right hNotCoin]

private theorem buildCompactVClauses_split {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (l₁ l₂ : List (ShapeEvent V)) {vAll},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
        idx (l₁ ++ l₂) = .ok vAll →
      ∃ v₁ v₂,
        buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
          idx l₁ = .ok v₁ ∧
        buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
          (idx + l₁.length) l₂ = .ok v₂ ∧
        vAll = v₁ ++ v₂
  | idx, [], l₂, vAll, h => ⟨[], vAll, rfl, by simpa using h, rfl⟩
  | idx, e :: rest, l₂, vAll, h => by
      rw [List.cons_append] at h
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
          htfree (idx + 1) (rest ++ l₂) with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨v₁, v₂, h1, h2, hvEq⟩ := buildCompactVClauses_split (idx + 1) rest l₂ hRec
          have h2' : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
              htfree (idx + (e :: rest).length) l₂ = .ok v₂ := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecF : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecF] at h; cases h
                    | some recRef =>
                        rw [hRecF] at h; cases h
                        refine ⟨_ :: v₁, v₂, ?_, h2', by rw [hvEq]; rfl⟩
                        unfold buildCompactVClauses
                        rw [h1]; dsimp only [bind, Except.bind]
                        rw [hCls]; dsimp only; rw [ite_eq_left hPV, hLk]; dsimp only; rw [hRecF]
                | none =>
                    rw [hLk] at h
                    cases hMem : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hMem] at h; cases h
                    | some mWire =>
                        rw [hMem] at h; cases h
                        refine ⟨_ :: v₁, v₂, ?_, h2', by rw [hvEq]; rfl⟩
                        unfold buildCompactVClauses
                        rw [h1]; dsimp only [bind, Except.bind]
                        rw [hCls]; dsimp only; rw [ite_eq_left hPV, hLk]; dsimp only; rw [hMem]
              · rename_i hNotPV
                cases h
                refine ⟨v₁, v₂, ?_, h2', hvEq⟩
                unfold buildCompactVClauses
                rw [h1]; dsimp only [bind, Except.bind]
                rw [hCls]; dsimp only; rw [ite_eq_right hNotPV]
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ =>
                  cases h
                  refine ⟨v₁, v₂, ?_, h2', hvEq⟩
                  unfold buildCompactVClauses
                  rw [h1]; dsimp only [bind, Except.bind]; rw [hCls]
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    split at h
                    · rename_i hCar
                      cases hMem : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEqR : findLayoutEqual a layout.module e.τ <;>
                        simp only [hMem, hEqR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨_ :: v₁, v₂, ?_, h2', by rw [hvEq]; rfl⟩
                        unfold buildCompactVClauses
                        rw [h1]; dsimp only [bind, Except.bind]
                        rw [hCls]; dsimp only; rw [ite_eq_left hCoin, ite_eq_left hCar, hMem, hEqR]
                    · rename_i hNotCar
                      cases h
                      refine ⟨_ :: v₁, v₂, ?_, h2', by rw [hvEq]; rfl⟩
                      unfold buildCompactVClauses
                      rw [h1]; dsimp only [bind, Except.bind]
                      rw [hCls]; dsimp only; rw [ite_eq_left hCoin, ite_eq_right hNotCar]
                  · rename_i hNotCoin
                    cases h
                    refine ⟨v₁, v₂, ?_, h2', hvEq⟩
                    unfold buildCompactVClauses
                    rw [h1]; dsimp only [bind, Except.bind]
                    rw [hCls]; dsimp only; rw [ite_eq_right hNotCoin]

private theorem collectCompactWire_sites {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {ws ps},
      collectCompactWire a layout unitTy prover verifier declKey events idx es = .ok (ws, ps) →
      (∀ w ∈ ws, w.site ∈ es.map (·.site) ∨ ∃ k < es.length, w.site.key = drawToldKey events (idx + k)) ∧
      (∀ c ∈ ps, c.site.site ∈ es.map (·.site) ∨ ∃ k < es.length, c.site.site.key = drawToldKey events (idx + k))
  | _, [], _, _, h => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, ws, ps, h => by
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihW, ihP⟩ := collectCompactWire_sites (idx + 1) rest hRec
          have liftW : ∀ w ∈ pair.1,
              w.site ∈ (e :: rest).map (·.site) ∨ ∃ k < (e :: rest).length, w.site.key = drawToldKey events (idx + k) := by
            intro w hw
            rcases ihW w hw with h1 | ⟨k, hk, hkey⟩
            · exact .inl (List.mem_cons_of_mem _ h1)
            · exact .inr ⟨k + 1, Nat.add_lt_add_right hk 1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkey⟩
          have liftP : ∀ c ∈ pair.2,
              c.site.site ∈ (e :: rest).map (·.site) ∨ ∃ k < (e :: rest).length, c.site.site.key = drawToldKey events (idx + k) := by
            intro c hc
            rcases ihP c hc with h1 | ⟨k, hk, hkey⟩
            · exact .inl (List.mem_cons_of_mem _ h1)
            · exact .inr ⟨k + 1, Nat.add_lt_add_right hk 1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkey⟩
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some _ =>
                    rw [hLk] at h; cases h
                    refine ⟨liftW, fun c hc => ?_⟩
                    rcases List.mem_cons.mp hc with rfl | hm
                    · exact .inl List.mem_cons_self
                    · exact liftP c hm
                | none =>
                    rw [hLk] at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      refine ⟨fun w hw => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hw with rfl | hm
                        · exact .inl List.mem_cons_self
                        · exact liftW w hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact .inl List.mem_cons_self
                        · exact liftP c hm
              · cases h; exact ⟨liftW, liftP⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact ⟨liftW, liftP⟩
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨fun w hw => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hw with rfl | hm
                          · exact .inr ⟨0, Nat.zero_lt_succ _, rfl⟩
                          · exact liftW w hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact .inr ⟨0, Nat.zero_lt_succ _, rfl⟩
                          · exact liftP c hm
                    · cases h
                      refine ⟨liftW, fun c hc => ?_⟩
                      rcases List.mem_cons.mp hc with rfl | hm
                      · exact .inr ⟨0, Nat.zero_lt_succ _, rfl⟩
                      · exact liftP c hm
                  · cases h; exact ⟨liftW, liftP⟩

private theorem buildCompactVClauses_sites {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {vs},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
        idx es = .ok vs →
      ∀ c ∈ vs, c.site.site ∈ es.map (·.site) ∨ ∃ k < es.length, c.site.site.key = drawToldKey events (idx + k)
  | _, [], _, h => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, vs, h => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
          htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := buildCompactVClauses_sites (idx + 1) rest hRec
          have liftV : ∀ c ∈ vRest,
              c.site.site ∈ (e :: rest).map (·.site) ∨ ∃ k < (e :: rest).length, c.site.site.key = drawToldKey events (idx + k) := by
            intro c hc
            rcases ih c hc with h1 | ⟨k, hk, hkey⟩
            · exact .inl (List.mem_cons_of_mem _ h1)
            · exact .inr ⟨k + 1, Nat.add_lt_add_right hk 1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkey⟩
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecF : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecF] at h; cases h
                    | some _ =>
                        rw [hRecF] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact .inl List.mem_cons_self
                        · exact liftV c hm
                | none =>
                    rw [hLk] at h
                    cases hMem : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hMem] at h; cases h
                    | some _ =>
                        rw [hMem] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact .inl List.mem_cons_self
                        · exact liftV c hm
              · cases h; exact liftV
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact liftV
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hMem : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEqR : findLayoutEqual a layout.module e.τ <;>
                        simp only [hMem, hEqR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · exact .inr ⟨0, Nat.zero_lt_succ _, rfl⟩
                        · exact liftV c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · exact .inr ⟨0, Nat.zero_lt_succ _, rfl⟩
                      · exact liftV c hm
                  · cases h; exact liftV

private theorem collectCompactWire_unmatched_closed {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {ws ps},
      collectCompactWire a layout unitTy prover verifier declKey events idx es = .ok (ws, ps) →
      ∀ op, ROp.IsClosed M op → ∀ c ∈ ps, ¬ ClauseMatches M c op
  | _, [], _, _, h, _, _ => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, ws, ps, h, op, hCl => by
      unfold collectCompactWire at h
      cases hRec : collectCompactWire a layout unitTy prover verifier declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := collectCompactWire_unmatched_closed (idx + 1) rest hRec op hCl
          have hNotGive : ∀ k gs, some (Part.give k gs) ≠ ROp.part M op := by
            intro k gs hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          cases hCls : e.cls with
          | flow kind _ getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some _ =>
                    rw [hLk] at h; cases h
                    intro c hc
                    rcases List.mem_cons.mp hc with rfl | hm
                    · intro hM; exact hNotGive kind getters hM.2.1
                    · exact ih c hm
                | none =>
                    rw [hLk] at h
                    cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro hM; exact hNotGive kind getters hM.2.1
                      · exact ih c hm
              · cases h; exact ih
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact ih
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                        simp only [hW, hR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM; exact hNotGive .message [verifier] hM.2.1
                        · exact ih c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro hM; exact hNotGive .message [verifier] hM.2.1
                      · exact ih c hm
                  · cases h; exact ih

private theorem buildCompactVClauses_unmatched_closed {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {vs},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
        idx es = .ok vs →
      ∀ op, ROp.IsClosed M op → ∀ c ∈ vs, ¬ ClauseMatches M c op
  | _, [], _, h, _, _ => by cases h; exact fun _ hc => nomatch hc
  | idx, e :: rest, vs, h, op, hCl => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs
          htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := buildCompactVClauses_unmatched_closed (idx + 1) rest hRec op hCl
          have hNotGive : ∀ k gs, some (Part.give k gs) ≠ ROp.part M op := by
            intro k gs hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          have hNotGet : ∀ k g, some (Part.get k g) ≠ ROp.part M op := by
            intro k g hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          cases hCls : e.cls with
          | flow kind _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRecF : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRecF] at h; cases h
                    | some _ =>
                        rw [hRecF] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM; exact hNotGet kind prover hM.2.1
                        · exact ih c hm
                | none =>
                    rw [hLk] at h
                    cases hMem : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hMem] at h; cases h
                    | some _ =>
                        rw [hMem] at h; cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM; exact hNotGet kind prover hM.2.1
                        · exact ih c hm
              · cases h; exact ih
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | request _ => cases h; exact ih
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hMem : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs <;>
                      cases hEqR : findLayoutEqual a layout.module e.τ <;>
                        simp only [hMem, hEqR] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        intro c hc
                        rcases List.mem_cons.mp hc with rfl | hm
                        · intro hM; exact hNotGive .message [prover] hM.2.1
                        · exact ih c hm
                    · cases h
                      intro c hc
                      rcases List.mem_cons.mp hc with rfl | hm
                      · intro hM; exact hNotGive .message [prover] hM.2.1
                      · exact ih c hm
                  · cases h; exact ih

private theorem site_not_in_prefix_of_nodup {events pref rest : List (ShapeEvent V)} {e : ShapeEvent V}
    (hSplit : events = pref ++ e :: rest) (hNodup : (events.map (·.site)).Nodup) :
    e.site ∉ pref.map (·.site) ∧
    ∀ j < pref.length, e.site.key ≠ drawToldKey events j := by
  have hMap : events.map (·.site) = pref.map (·.site) ++ e.site :: rest.map (·.site) := by
    rw [hSplit, List.map_append]; rfl
  rw [hMap] at hNodup
  refine ⟨?_, ?_⟩
  · intro hIn
    have hDisj := List.nodup_append.mp hNodup |>.2.2
    exact hDisj e.site hIn e.site List.mem_cons_self rfl
  · intro j _ hEq
    have hEIn : e ∈ events := by rw [hSplit]; exact List.mem_append_right _ List.mem_cons_self
    have hLe := event_key_le_max events e.site.key (List.mem_map.mpr ⟨e, hEIn, rfl⟩)
    have hNum : e.site.key.number = (drawToldKey events j).number := congrArg Key.number hEq
    simp only [drawToldKey] at hNum; omega

private theorem toldSite_not_in_prefix {events pref rest : List (ShapeEvent V)} {e : ShapeEvent V}
    (hSplit : events = pref ++ e :: rest) :
    ∀ (s : Site),
      (s ∈ pref.map (·.site) ∨ ∃ k < pref.length, s.key = drawToldKey events (0 + k)) →
      s ≠ ⟨e.site.through, drawToldKey events pref.length⟩ := by
  intro s hS hEq
  have hNum : s.key.number = (drawToldKey events pref.length).number :=
    congrArg (fun x : Site => x.key.number) hEq
  rcases hS with hIn | ⟨k, hk, hKey⟩
  · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp hIn
    have he0Ev : e0 ∈ events := by rw [hSplit]; exact List.mem_append_left _ he0
    have hLe := event_key_le_max events e0.site.key (List.mem_map.mpr ⟨e0, he0Ev, rfl⟩)
    simp only [drawToldKey] at hNum; omega
  · have hK : s.key.number = (drawToldKey events (0 + k)).number := congrArg Key.number hKey
    rw [hK] at hNum
    simp only [drawToldKey] at hNum; omega

private theorem eventsWithAbsorb_mem_at
    {events : List (ShapeEvent V)} {eventsAbs : List (ShapeEvent V × Bool)}
    (hFst : eventsAbs.map Prod.fst = events) {e : ShapeEvent V} (hE : e ∈ events) :
    ∃ b, (e, b) ∈ eventsAbs := by
  rw [← hFst] at hE
  obtain ⟨⟨e₀, b₀⟩, hIn, hEq⟩ := List.mem_map.mp hE
  dsimp only at hEq; subst hEq
  exact ⟨b₀, hIn⟩

private theorem eventsWithAbsorb_draw_index
    {events : List (ShapeEvent V)} {eventsAbs : List (ShapeEvent V × Bool)}
    (hFst : eventsAbs.map Prod.fst = events) {pref rest : List (ShapeEvent V)} {e : ShapeEvent V}
    (hSplit : events = pref ++ e :: rest) :
    ∃ b, eventsAbs[pref.length]? = some (e, b) := by
  have hLen : eventsAbs.length = events.length := by
    rw [← List.length_map Prod.fst, hFst]
  have hLt : pref.length < eventsAbs.length := by
    rw [hLen, hSplit, List.length_append, List.length_cons]; omega
  refine ⟨(eventsAbs[pref.length]'hLt).2, ?_⟩
  rw [List.getElem?_eq_getElem hLt]
  congr 1
  have hFstAt : (eventsAbs.map Prod.fst)[pref.length]? = some (eventsAbs[pref.length]'hLt).1 := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hLt]; rfl
  have hEvAt : events[pref.length]? = some e := by
    rw [hSplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  rw [hFst, hEvAt] at hFstAt
  have h1 : e = (eventsAbs[pref.length]'hLt).1 := Option.some.inj hFstAt
  exact Prod.ext h1.symm rfl

/-! ## Coupled prover-verifier-protocol simulation for compact `.derived` layouts -/

private theorem collectCompactWire_prefix_step {a : Admitted V} {layout : Layout} {unitTy : V.Ty}
    {prover verifier : Role} {declKey : Key} {events pref rest : List (ShapeEvent V)} {e : ShapeEvent V}
    (hSplit : events = pref ++ e :: rest)
    {allSpecs prefSpecs headSpecs tailSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {allP tailP : List (Clause V a.program.headers prover (.seq unitTy none))}
    (hCW : collectCompactWire a layout unitTy prover verifier declKey events 0 events = .ok (allSpecs, allP))
    (hTail : collectCompactWire a layout unitTy prover verifier declKey events (pref.length + 1) rest = .ok (tailSpecs, tailP))
    (hEq : allSpecs = (prefSpecs ++ headSpecs) ++ tailSpecs) :
    ∃ prefP', collectCompactWire a layout unitTy prover verifier declKey events 0 (pref ++ [e]) =
      .ok (prefSpecs ++ headSpecs, prefP') := by
  have hSplit' : events = (pref ++ [e]) ++ rest := by simpa [List.append_assoc] using hSplit
  have hCW' : collectCompactWire a layout unitTy prover verifier declKey events 0 ((pref ++ [e]) ++ rest) =
      .ok (allSpecs, allP) := by rw [← hSplit']; exact hCW
  obtain ⟨wA, pA, wB, pB, hA, hB, hwEq, _⟩ := collectCompactWire_split 0 (pref ++ [e]) rest hCW'
  have hB' : collectCompactWire a layout unitTy prover verifier declKey events (pref.length + 1) rest = .ok (wB, pB) := by
    simpa [List.length_append] using hB
  have hPair : (wB, pB) = (tailSpecs, tailP) := Except.ok.inj (hB'.symm.trans hTail)
  have hwB : wB = tailSpecs := congrArg Prod.fst hPair
  subst hwB
  have hwA : wA = prefSpecs ++ headSpecs := List.append_cancel_right (hwEq.symm.trans hEq)
  exact ⟨pA, hwA ▸ hA⟩

private theorem simulate_compact_derived {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)} {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {startRef : TypedFnRef V d.admitted.program.headers.fns [bytesTy] [stateTy]}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    (stmtTys : List V.Ty)
    (allSpecs : List (WireSpec V d.admitted.program.headers.fns unitTy))
    (htfree : Tys.anyLinear V (tysOfList (stmtTys ++ allSpecs.map (·.ty))) = false)
    (cPClauses : List (Clause V d.admitted.program.headers prover stateTy))
    (cVClauses : List (Clause V d.admitted.program.headers verifier stateTy))
    (lPClauses : List (Clause V d.admitted.program.headers prover (.seq unitTy none)))
    (lVClauses : List (Clause V d.admitted.program.headers verifier (.tuple (tysOfList (stmtTys ++ allSpecs.map (·.ty))))))
    (conP' : Layer V d.admitted.program.headers prover d.entry.ins)
    (conV' : Layer V d.admitted.program.headers verifier d.entry.ins)
    (layP' : Layer V d.admitted.program.headers prover d.entry.ins)
    (layV' : Layer V d.admitted.program.headers verifier d.entry.ins)
    (hCPSt : conP'.state = stateTy) (hCVSt : conV'.state = stateTy)
    (hLPSt : layP'.state = .seq unitTy none)
    (hLVSt : layV'.state = .tuple (tysOfList (stmtTys ++ allSpecs.map (·.ty))))
    (hCPCl : hCPSt ▸ conP'.clauses = cPClauses) (hCVCl : hCVSt ▸ conV'.clauses = cVClauses)
    (hLPCl : hLPSt ▸ layP'.clauses = lPClauses) (hLVCl : hLVSt ▸ layV'.clauses = lVClauses)
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hStart : findSuiteStart d.admitted suite = some ⟨stateTy, startRef⟩)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M)
    (hNodup : ((d.entry.shape.events [] id).map (·.site)).Nodup)
    (hCC : buildConstructionClauses.go enc d.admitted suite stateTy suiteUnitTy absRef prover verifier
      declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) = .ok (cPClauses, cVClauses))
    (hCW : collectCompactWire d.admitted layout unitTy prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) = .ok (allSpecs, lPClauses))
    (hCV : buildCompactVClauses d.admitted layout unitTy prover verifier declKey
      (d.entry.shape.events [] id) stmtTys allSpecs htfree 0 (d.entry.shape.events [] id) = .ok lVClauses) :
    let stateTys := tysOfList (stmtTys ++ allSpecs.map (·.ty))
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pref rem : List (ShapeEvent V)) (_hEvSplit : d.entry.shape.events [] id = pref ++ rem)
      (prefSpecs remSpecs : List (WireSpec V d.admitted.program.headers.fns unitTy))
      (hSpecSplit : allSpecs = prefSpecs ++ remSpecs)
      (_hPrefW : ∃ prefP, collectCompactWire d.admitted layout unitTy prover verifier declKey
        (d.entry.shape.events [] id) 0 pref = .ok (prefSpecs, prefP))
      (_hRemW : ∃ remP, collectCompactWire d.admitted layout unitTy prover verifier declKey
        (d.entry.shape.events [] id) pref.length rem = .ok (remSpecs, remP))
      (pP : Program M BP) (pV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
      Protocol.FollowsEvents M rem p →
      Proj M prover postP p pP → Proj M verifier postV p pV →
      pP.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pV.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      pP.SafeWith M (fun _ _ => True) (ROp.MatchesShape M prover (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      pV.SafeWith M (fun _ _ => True) (ROp.MatchesShape M verifier (d.entry.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      Protocol.MatchesShape M (d.entry.shape.events [] id) p →
      Protocol.UniqueOccs M p →
      LawfulPrivate M source p →
      Fed M source p →
      (∀ source₁, Lawful M source₁ p →
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source₁ at_ τ = source at_ τ) →
        ∀ e, GExec M source₁ p e → ∃ a, e = .returned a) →
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
        (wireVals : HList M.Val (remSpecs.map (·.ty)))
        (chunks : List (List (M.Val unitTy)))
        (recP : List (Happened M)) (source' : Source M) (evs : List (Event M)),
        WireTrace M d layout remSpecs wireVals chunks ∧
        compactWireArgs M prover verifier layout evs = wireSigmaList M remSpecs wireVals ∧
        Alone M source prover
          ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
            (Defs.rTable M d.admitted.program.defs) [conP', layP']).run (retryOf M none) pP
              (.cons (hCPSt.symm ▸ st) (.cons (hLPSt.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hCPSt.symm ▸ finalSt) (.cons (hLPSt.symm ▸ (buf ++ chunks.flatten)) .nil))) ∧
        (∀ (stV : stateTys.Val M.toCarriers),
          (∀ {τ} (mRem : Member (remSpecs.map (·.ty)) τ),
            Tys.getAt M stateTys
              (cast (congrArg (fun l => Member l τ) (by rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]))
                (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) mRem)) stV =
              HList.getAtMember wireVals mRem) →
          (∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (x : M.Val τ)
              (recKey : Key) (recRef : SafeFnRef V d.admitted.program.headers.fns stateTys.toList [τ]),
            Event.flow kind prover getters at_ τ x ∈ evs →
            verifier ∈ getters →
            layout.recover.lookup at_.site = some recKey →
            findSafeFnRef d.admitted recKey stateTys.toList [τ] = some recRef →
            recRef.eval M (Defs.fnTable M d.admitted.program.defs) (Tys.toHList M stateTys stV) =
              .done (.cons x .nil)) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [conV', layV']).run (retryOf M none) pV
                (.cons (hCVSt.symm ▸ st) (.cons (hLVSt.symm ▸ stV) .nil)))
            recV (.returned (outV, .cons (hCVSt.symm ▸ finalSt) (.cons (hLVSt.symm ▸ stV) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GRun M source' p evs (.returned a) := by
  intro stateTys
  cases conP' with | mk cPLine cPSt cPTakes cPGives cPCl cPAgain cPStart cPFin =>
  cases conV' with | mk cVLine cVSt cVTakes cVGives cVCl cVAgain cVStart cVFin =>
  cases layP' with | mk lPLine lPSt lPTakes lPGives lPCl lPAgain lPStart lPFin =>
  cases layV' with | mk lVLine lVSt lVTakes lVGives lVCl lVAgain lVStart lVFin =>
  dsimp only at hCPSt hCVSt hLPSt hLVSt
  subst cPSt; subst cVSt; subst lPSt; subst lVSt
  dsimp only at hCPCl hCVCl hLPCl hLVCl
  subst hCPCl; subst hCVCl; subst hLPCl; subst hLVCl
  let conP0 : Layer V d.admitted.program.headers prover d.entry.ins :=
    ⟨cPLine, stateTy, cPTakes, cPGives, cPCl, cPAgain, cPStart, cPFin⟩
  let conV0 : Layer V d.admitted.program.headers verifier d.entry.ins :=
    ⟨cVLine, stateTy, cVTakes, cVGives, cVCl, cVAgain, cVStart, cVFin⟩
  let layP0 : Layer V d.admitted.program.headers prover d.entry.ins :=
    ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPCl, lPAgain, lPStart, lPFin⟩
  let layV0 : Layer V d.admitted.program.headers verifier d.entry.ins :=
    ⟨lVLine, .tuple stateTys, lVTakes, lVGives, lVCl, lVAgain, lVStart, lVFin⟩
  let fnTable := Defs.fnTable M d.admitted.program.defs
  let rTable := Defs.rTable M d.admitted.program.defs
  let events := d.entry.shape.events [] id
  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
  have hFst : eventsAbs.map Prod.fst = events :=
    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
  have hConUnm := fun op hCl => construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
  have hLayPUnm := fun op hCl => collectCompactWire_unmatched_closed M 0 events hCW op hCl
  have hLayVUnm := fun op hCl => buildCompactVClauses_unmatched_closed M 0 events hCV op hCl
  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
      ROp.IsClosed M op →
      (Stack.handler M fnTable rTable [conP0, layP0]).clause op (.cons st (.cons buf .nil)) =
        .call op fun reply => .done (reply, .cons st (.cons buf .nil)) := fun op st buf hCl =>
    stack2_clause_pass M fnTable rTable conP0 layP0 op st buf
      (clause_answer_unmatched_all M fnTable rTable op st cPCl (hConUnm op hCl).1)
      (clause_answer_unmatched_all M fnTable rTable op buf lPCl (hLayPUnm op hCl))
  have hPassV : ∀ op (st : M.Val stateTy) (stV : stateTys.Val M.toCarriers),
      ROp.IsClosed M op →
      (Stack.handler M fnTable rTable [conV0, layV0]).clause op (.cons st (.cons stV .nil)) =
        .call op fun reply => .done (reply, .cons st (.cons stV .nil)) := fun op st stV hCl =>
    stack2_clause_pass M fnTable rTable conV0 layV0 op st stV
      (clause_answer_unmatched_all M fnTable rTable op st cVCl (hConUnm op hCl).2)
      (clause_answer_unmatched_all M fnTable rTable op stV lVCl (hLayVUnm op hCl))
  have hEventDisc : ∀ e ∈ events,
      match e.cls with
      | .flow _ giver getters =>
          (giver = prover ∧ getters = [verifier]) ∨
          (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
      | .given (.coin law) owner hearers =>
          (owner = verifier ∧ hearers = [prover] ∧
            ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
          hearers = []
      | .given (.request _) owner hearers =>
          (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
    intro e he
    rw [← hFst] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact construction_event_disc 0 eventsAbs hCC p hp
  intro A BP BV p
  induction p with
  | done a =>
      intro postP postV pref rem hEvSplit prefSpecs remSpecs hSpecSplit hPrefW hRemW
        pP pV st buf source hStV hBufV hFol hPP hPV hSP hSV hShP hShV _ _ _ _ _
      cases rem with
      | cons _ _ => cases hFol
      | nil =>
          obtain ⟨remP, hRW⟩ := hRemW
          cases hRW
          refine peelMarks_alone M
            (h := Stack.handler M fnTable rTable [conP0, layP0])
            (fun op s hM =>
              match s with
              | .cons s1 (.cons s2v .nil) =>
                  hPassP op s1 s2v (by rcases hM with h | h <;> rw [h] <;> trivial))
            (fun qP => ∃ outP outV recP,
              Alone M source prover ((Stack.handler M fnTable rTable [conP0, layP0]).run (retryOf M none) qP
                (.cons st (.cons buf .nil))) recP (.returned (outP, .cons st (.cons (buf ++ [].flatten) .nil))) ∧
              (∀ (stV : stateTys.Val M.toCarriers),
                ∃ recV, Alone M source verifier ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none) pV
                  (.cons st (.cons stV .nil))) recV (.returned (outV, .cons st (.cons stV .nil)))) ∧
              postP a outP ∧ postV a outV)
            (fun qP hNotMP hPP' _ _ => by
              cases hPP' with
              | begins _ => exact False.elim (hNotMP trivial)
              | settles _ => exact False.elim (hNotMP trivial)
              | done hPostP =>
                  refine peelMarks_alone M
                    (h := Stack.handler M fnTable rTable [conV0, layV0])
                    (fun op s hM =>
                      match s with
                      | .cons s1 (.cons s2v .nil) =>
                          hPassV op s1 s2v (by rcases hM with h | h <;> rw [h] <;> trivial))
                    (fun qV => ∃ outP outV recP,
                      Alone M source prover ((Stack.handler M fnTable rTable [conP0, layP0]).run (retryOf M none) (.done _)
                        (.cons st (.cons buf .nil))) recP (.returned (outP, .cons st (.cons (buf ++ [].flatten) .nil))) ∧
                      (∀ (stV : stateTys.Val M.toCarriers),
                        ∃ recV, Alone M source verifier ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none) qV
                          (.cons st (.cons stV .nil))) recV (.returned (outV, .cons st (.cons stV .nil)))) ∧
                      postP a outP ∧ postV a outV)
                    (fun qV hNotMV hPV' _ _ => by
                      cases hPV' with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | done hPostV =>
                          exact ⟨_, _, [], by rw [List.flatten_nil, List.append_nil]; exact .done,
                            fun _ => ⟨[], .done⟩, hPostP, hPostV⟩)
                    (fun at_ kV ⟨oP, oV, rP, hAP, hAV, hpP, hpV⟩ =>
                      ⟨oP, oV, rP, hAP, fun stV => by
                        obtain ⟨rV, hV⟩ := hAV stV
                        exact ⟨.began verifier at_ :: rV,
                          by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hV⟩,
                        hpP, hpV⟩)
                    (fun at_ kV ⟨oP, oV, rP, hAP, hAV, hpP, hpV⟩ =>
                      ⟨oP, oV, rP, hAP, fun stV => by
                        obtain ⟨rV, hV⟩ := hAV stV
                        exact ⟨.settled verifier at_ :: rV,
                          by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hV⟩,
                        hpP, hpV⟩)
                    hPV hSV hShV)
            (fun at_ kP ⟨oP, oV, rP, hAP, hAV, hpP, hpV⟩ =>
              ⟨oP, oV, .began prover at_ :: rP,
                by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin hAP,
                hAV, hpP, hpV⟩)
            (fun at_ kP ⟨oP, oV, rP, hAP, hAV, hpP, hpV⟩ =>
              ⟨oP, oV, .settled prover at_ :: rP,
                by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle hAP,
                hAV, hpP, hpV⟩)
            hPP hSP hShP |> fun ⟨outP, outV, recP, hAP, hAV, hpP, hpV⟩ =>
            ⟨a, outP, outV, st, .nil, [], recP, source, [], .nil, rfl, hAP,
              fun stV _ _ => hAV stV, hpP, hpV, trivial, fun _ _ _ => rfl, .done⟩
  | halt hw =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ _ hNoHalt
      obtain ⟨_, hEq⟩ := hNoHalt source trivial (fun _ _ _ => rfl) _ ⟨[], .halt⟩
      cases hEq
  | call op k ih =>
      intro postP postV pref rem hEvSplit prefSpecs remSpecs hSpecSplit hPrefW hRemW
        pP pV st buf source hStV hBufV hFol hPP hPV hSP hSV hShP hShV hPShape hUniq hLP hFed hNoHalt
      -- Peel prover and verifier attempt marks first
      refine peelMarks_alone M
        (h := Stack.handler M fnTable rTable [conP0, layP0])
        (fun op' s hM =>
          match s with
          | .cons s1 (.cons s2v .nil) =>
              hPassP op' s1 s2v (by rcases hM with h | h <;> rw [h] <;> trivial))
        (fun qP =>
          ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
            (wireVals : HList M.Val (remSpecs.map (·.ty)))
            (chunks : List (List (M.Val unitTy)))
            (recP : List (Happened M)) (source' : Source M) (evs : List (Event M)),
            WireTrace M d layout remSpecs wireVals chunks ∧
            compactWireArgs M prover verifier layout evs = wireSigmaList M remSpecs wireVals ∧
            Alone M source prover
              ((Stack.handler M fnTable rTable [conP0, layP0]).run (retryOf M none) qP (.cons st (.cons buf .nil)))
              recP (.returned (outP, .cons finalSt (.cons (buf ++ chunks.flatten) .nil))) ∧
            (∀ (stV : stateTys.Val M.toCarriers),
              (∀ {τ} (mRem : Member (remSpecs.map (·.ty)) τ),
                Tys.getAt M stateTys
                  (cast (congrArg (fun l => Member l τ) (by rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]))
                    (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) mRem)) stV =
                  HList.getAtMember wireVals mRem) →
              (∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (x : M.Val τ)
                  (recKey : Key) (recRef : SafeFnRef V d.admitted.program.headers.fns stateTys.toList [τ]),
                Event.flow kind prover getters at_ τ x ∈ evs →
                verifier ∈ getters →
                layout.recover.lookup at_.site = some recKey →
                findSafeFnRef d.admitted recKey stateTys.toList [τ] = some recRef →
                recRef.eval M fnTable (Tys.toHList M stateTys stV) = .done (.cons x .nil)) →
              ∃ recV, Alone M source verifier
                ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none) pV (.cons st (.cons stV .nil)))
                recV (.returned (outV, .cons finalSt (.cons stV .nil)))) ∧
            postP a outP ∧ postV a outV ∧
            Lawful M source' (.call op k) ∧
            (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
            GRun M source' (.call op k) evs (.returned a))
        (fun qP hNotMP hPP hSP hShP =>
          peelMarks_alone M
            (h := Stack.handler M fnTable rTable [conV0, layV0])
            (fun op' s hM =>
              match s with
              | .cons s1 (.cons s2v .nil) =>
                  hPassV op' s1 s2v (by rcases hM with h | h <;> rw [h] <;> trivial))
            (fun qV =>
              ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                (wireVals : HList M.Val (remSpecs.map (·.ty)))
                (chunks : List (List (M.Val unitTy)))
                (recP : List (Happened M)) (source' : Source M) (evs : List (Event M)),
                WireTrace M d layout remSpecs wireVals chunks ∧
                compactWireArgs M prover verifier layout evs = wireSigmaList M remSpecs wireVals ∧
                Alone M source prover
                  ((Stack.handler M fnTable rTable [conP0, layP0]).run (retryOf M none) qP (.cons st (.cons buf .nil)))
                  recP (.returned (outP, .cons finalSt (.cons (buf ++ chunks.flatten) .nil))) ∧
                (∀ (stV : stateTys.Val M.toCarriers),
                  (∀ {τ} (mRem : Member (remSpecs.map (·.ty)) τ),
                    Tys.getAt M stateTys
                      (cast (congrArg (fun l => Member l τ) (by rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]))
                        (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) mRem)) stV =
                      HList.getAtMember wireVals mRem) →
                  (∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (x : M.Val τ)
                      (recKey : Key) (recRef : SafeFnRef V d.admitted.program.headers.fns stateTys.toList [τ]),
                    Event.flow kind prover getters at_ τ x ∈ evs →
                    verifier ∈ getters →
                    layout.recover.lookup at_.site = some recKey →
                    findSafeFnRef d.admitted recKey stateTys.toList [τ] = some recRef →
                    recRef.eval M fnTable (Tys.toHList M stateTys stV) = .done (.cons x .nil)) →
                  ∃ recV, Alone M source verifier
                    ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none) qV (.cons st (.cons stV .nil)))
                    recV (.returned (outV, .cons finalSt (.cons stV .nil)))) ∧
                postP a outP ∧ postV a outV ∧
                Lawful M source' (.call op k) ∧
                (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
                GRun M source' (.call op k) evs (.returned a))
            (fun qV hNotMV hPV hSV hShV => by
              cases rem with
              | nil => cases op <;> cases hFol
              | cons e rest =>
                  have hEIn : e ∈ events := by dsimp only [events]; rw [hEvSplit]; exact List.mem_append_right _ List.mem_cons_self
                  have hEvSplit' : events = (pref ++ [e]) ++ rest := by
                    simpa [events, List.append_assoc] using hEvSplit
                  obtain ⟨prefP, hPrefW'⟩ := hPrefW
                  obtain ⟨remP, hRemW'⟩ := hRemW
                  have hCWSplit : collectCompactWire d.admitted layout unitTy prover verifier declKey
                      events 0 (pref ++ e :: rest) = .ok (allSpecs, lPCl) := by
                    dsimp only [events]; rw [← hEvSplit]; exact hCW
                  have hCW2 := collectCompactWire_split 0 pref (e :: rest) hCWSplit
                  obtain ⟨w1', p1', w2', p2', hW1, hW2, hwAllEq, hpAllEq⟩ := hCW2
                  have hEq1 : (w1', p1') = (prefSpecs, prefP) := Except.ok.inj (hW1.symm.trans hPrefW')
                  have hW2' : collectCompactWire d.admitted layout unitTy prover verifier declKey
                      events pref.length (e :: rest) = .ok (w2', p2') := by simpa using hW2
                  have hEq2 : (w2', p2') = (remSpecs, remP) := Except.ok.inj (hW2'.symm.trans hRemW')
                  have hw1Eq : w1' = prefSpecs := congrArg Prod.fst hEq1
                  have hp1Eq : p1' = prefP := congrArg Prod.snd hEq1
                  have hw2Eq : w2' = remSpecs := congrArg Prod.fst hEq2
                  have hp2Eq : p2' = remP := congrArg Prod.snd hEq2
                  subst w1'; subst p1'; subst w2'; subst p2'
                  have hCVSplit : buildCompactVClauses d.admitted layout unitTy prover verifier declKey
                      events stmtTys allSpecs htfree 0 (pref ++ e :: rest) = .ok lVCl := by
                    dsimp only [events]; rw [← hEvSplit]; exact hCV
                  have hCV2 := buildCompactVClauses_split 0 pref (e :: rest) hCVSplit
                  obtain ⟨v1', v2', hV1, hV2, hvAllEq⟩ := hCV2
                  have hV2' : buildCompactVClauses d.admitted layout unitTy prover verifier declKey
                      events stmtTys allSpecs htfree pref.length (e :: rest) = .ok v2' := by
                    simpa using hV2
                  have ⟨hNotInPref, hKeyNePref⟩ := site_not_in_prefix_of_nodup hEvSplit hNodup
                  have ⟨hPrefWSites, hPrefPSites⟩ := collectCompactWire_sites 0 pref hW1
                  have hPrefVSites := buildCompactVClauses_sites 0 pref hV1
                  have hNotInPrefW : e.site ∉ prefSpecs.map (·.site) := by
                    intro hIn
                    obtain ⟨ws0, hws0, hEqS⟩ := List.mem_map.mp hIn
                    rcases hPrefWSites ws0 hws0 with h1 | ⟨j, hj, hKey⟩
                    · exact hNotInPref (hEqS ▸ h1)
                    · exact hKeyNePref j hj (by rw [← hEqS, hKey, Nat.zero_add])
                  have hNoMatchPrefP_site : ∀ op', (ROp.occurrence M op').site = e.site →
                      ∀ c ∈ prefP, ¬ ClauseMatches M c op' := by
                    intro op' hSiteOp c hc hM
                    rcases hPrefPSites c hc with h1 | ⟨j, hj, hKey⟩
                    · exact hNotInPref (hSiteOp ▸ hM.1 ▸ h1)
                    · exact hKeyNePref j hj (by rw [← hSiteOp, ← hM.1, hKey, Nat.zero_add])
                  have hNoMatchPrefV_site : ∀ op', (ROp.occurrence M op').site = e.site →
                      ∀ c ∈ v1', ¬ ClauseMatches M c op' := by
                    intro op' hSiteOp c hc hM
                    rcases hPrefVSites c hc with h1 | ⟨j, hj, hKey⟩
                    · exact hNotInPref (hSiteOp ▸ hM.1 ▸ h1)
                    · exact hKeyNePref j hj (by rw [← hSiteOp, ← hM.1, hKey, Nat.zero_add])
                  have hNoMatchPrefP_told : ∀ op', (ROp.occurrence M op').site = ⟨e.site.through, drawToldKey events pref.length⟩ →
                      ∀ c ∈ prefP, ¬ ClauseMatches M c op' := by
                    intro op' hSiteOp c hc hM
                    exact toldSite_not_in_prefix hEvSplit c.site.site (hPrefPSites c hc) (hM.1.trans hSiteOp)
                  have hNoMatchPrefV_told : ∀ op', (ROp.occurrence M op').site = ⟨e.site.through, drawToldKey events pref.length⟩ →
                      ∀ c ∈ v1', ¬ ClauseMatches M c op' := by
                    intro op' hSiteOp c hc hM
                    exact toldSite_not_in_prefix hEvSplit c.site.site (hPrefVSites c hc) (hM.1.trans hSiteOp)
                  have hNotInPrefW_told : (⟨e.site.through, drawToldKey events pref.length⟩ : Site) ∉ prefSpecs.map (·.site) := by
                    intro hIn
                    obtain ⟨ws0, hws0, hEqS⟩ := List.mem_map.mp hIn
                    exact toldSite_not_in_prefix hEvSplit ws0.site (hPrefWSites ws0 hws0) hEqS
                  cases op with
                  | flow kind giver getters at_ τ x =>
                      obtain ⟨hESite, hETy, hECls, hFolRest⟩ := hFol
                      subst hETy
                      have hDisc := hEventDisc e hEIn
                      rw [hECls] at hDisc
                      have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                          (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                          ∀ e', GExec M source₁ (k ()) e' → ∃ a, e' = .returned a := by
                        intro s₁ hL₁ hAg₁ e' ⟨evs', hRun'⟩
                        exact hNoHalt s₁ hL₁ hAg₁ e' ⟨_, .flow hRun'⟩
                      rcases hDisc with ⟨hGeqP, hGsEq⟩ | ⟨hGNeP, hGNeV, hPOut, hVOut⟩
                      · -- Prover → Verifier flow
                        subst giver; subst getters
                        have hVin : verifier ∈ [verifier] := List.mem_singleton_self verifier
                        cases hPP with
                        | begins _ => exact False.elim (hNotMP trivial)
                        | settles _ => exact False.elim (hNotMP trivial)
                        | got hNeSelf _ _ => exact absurd rfl hNeSelf
                        | passed hNeSelf _ _ => exact absurd rfl hNeSelf
                        | gave hNotIn hPP' =>
                            rename_i kP'
                            cases hPV with
                            | begins _ => exact False.elim (hNotMV trivial)
                            | settles _ => exact False.elim (hNotMV trivial)
                            | gave _ _ => exact absurd rfl hNe
                            | passed _ hOut _ => exact absurd hVin hOut
                            | got hGNe hVin' hPV' =>
                                rename_i kV'
                                have hMsgV : M.Valid e.τ x := hSP.1
                                -- Unpack `collectCompactWire` and `buildCompactVClauses` at head `e`
                                unfold collectCompactWire at hRemW'
                                cases hRemRec : collectCompactWire d.admitted layout unitTy prover verifier
                                    declKey events (pref.length + 1) rest with
                                | error _ => rw [hRemRec] at hRemW'; cases hRemW'
                                | ok remPair =>
                                    rw [hRemRec] at hRemW'; dsimp only [bind, Except.bind] at hRemW'
                                    rw [hECls] at hRemW'; dsimp only at hRemW'
                                    rw [ite_eq_left ⟨rfl, rfl⟩] at hRemW'
                                    unfold buildCompactVClauses at hV2'
                                    cases hVRec : buildCompactVClauses d.admitted layout unitTy prover verifier
                                        declKey events stmtTys allSpecs htfree (pref.length + 1) rest with
                                    | error _ => rw [hVRec] at hV2'; cases hV2'
                                    | ok vRest =>
                                        rw [hVRec] at hV2'; dsimp only [bind, Except.bind] at hV2'
                                        rw [hECls] at hV2'; dsimp only at hV2'
                                        rw [ite_eq_left ⟨rfl, rfl⟩] at hV2'
                                        -- Check whether `e` is absorbed by construction layer
                                        obtain ⟨needAbs, hNeedAbs⟩ := eventsWithAbsorb_mem_at hFst hEIn
                                        have hStepCon : ∀ (st' : M.Val stateTy) (hConStep :
                                              (needAbs = true →
                                                ∃ encRef encVal,
                                                  findSuiteEncode d.admitted suite suiteUnitTy e.τ = some encRef ∧
                                                  encRef.eval M fnTable (.cons x .nil) = .done (.cons encVal .nil) ∧
                                                  absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encVal .nil))) =
                                                    .done (.cons st' .nil) ∧
                                                  Clause.answer M fnTable rTable cPCl (.give kind [verifier] at_ e.τ x) st =
                                                    .call (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x)
                                                      (fun _ => .done ((), st')) ∧
                                                  Clause.answer M fnTable rTable cVCl (.get kind prover at_ e.τ) st =
                                                    .call (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) fun msg =>
                                                      (((liftLocal id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
                                                        (liftLocal id (absRef.eval M fnTable
                                                          (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                                                          fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
                                                        let values := HList.split [e.τ] (aloneOut M verifier out)
                                                        (values.1.single, values.2.single)) ∧
                                              (needAbs = false →
                                                st' = st ∧
                                                Clause.answer M fnTable rTable cPCl (.give kind [verifier] at_ e.τ x) st =
                                                  .call (.give kind [verifier] at_ e.τ x) (fun u => .done (u, st)) ∧
                                                Clause.answer M fnTable rTable cVCl (.get kind prover at_ e.τ) st =
                                                  .call (.get kind prover at_ e.τ) (fun m => .done (m, st)))),
                                            M.Valid stateTy st' →
                                            ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy)
                                              (wireVals : HList M.Val (remSpecs.map (·.ty)))
                                              (chunks : List (List (M.Val unitTy)))
                                              (recP : List (Happened M)) (source' : Source M) (evs : List (Event M)),
                                              WireTrace M d layout remSpecs wireVals chunks ∧
                                              compactWireArgs M prover verifier layout evs = wireSigmaList M remSpecs wireVals ∧
                                              Alone M source prover
                                                ((Stack.handler M fnTable rTable [conP0, layP0]).run (retryOf M none)
                                                  (.call (.give kind [verifier] at_ e.τ x) kP')
                                                  (.cons st (.cons buf .nil)))
                                                recP (.returned (outP, .cons finalSt (.cons (buf ++ chunks.flatten) .nil))) ∧
                                              (∀ (stV : stateTys.Val M.toCarriers),
                                                (∀ {τ'} (mRem : Member (remSpecs.map (·.ty)) τ'),
                                                  Tys.getAt M stateTys
                                                    (cast (congrArg (fun l => Member l τ') (by rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]))
                                                      (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) mRem)) stV =
                                                    HList.getAtMember wireVals mRem) →
                                                (∀ (k0 : FlowKind) (gs0 : List Role) (at0 : Occurrence) (τ0 : V.Ty) (x0 : M.Val τ0)
                                                    (rKey0 : Key) (rRef0 : SafeFnRef V d.admitted.program.headers.fns stateTys.toList [τ0]),
                                                  Event.flow k0 prover gs0 at0 τ0 x0 ∈ evs →
                                                  verifier ∈ gs0 →
                                                  layout.recover.lookup at0.site = some rKey0 →
                                                  findSafeFnRef d.admitted rKey0 stateTys.toList [τ0] = some rRef0 →
                                                  rRef0.eval M fnTable (Tys.toHList M stateTys stV) = .done (.cons x0 .nil)) →
                                                ∃ recV, Alone M source verifier
                                                  ((Stack.handler M fnTable rTable [conV0, layV0]).run (retryOf M none)
                                                    (.call (.get kind prover at_ e.τ) kV')
                                                    (.cons st (.cons stV .nil)))
                                                  recV (.returned (outV, .cons finalSt (.cons stV .nil)))) ∧
                                              postP a outP ∧ postV a outV ∧
                                              Lawful M source' (.call (.flow kind prover [verifier] at_ e.τ x) k) ∧
                                              (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source' at' τ' = source at' τ') ∧
                                              GRun M source' (.call (.flow kind prover [verifier] at_ e.τ x) k) evs (.returned a) := by
                                          intro st' ⟨hNeedT, hNeedF⟩ hSt'V
                                          have hConP_to_step : ∀ (buf' : List (M.Val unitTy)),
                                              Clause.answer M fnTable rTable lPCl
                                                (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x) buf =
                                                .done ((), buf') →
                                              (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                                (.give kind [verifier] at_ e.τ x) (.cons st (.cons buf .nil)) =
                                                .done ((), .cons st' (.cons buf' .nil)) := by
                                            intro buf' hLayP
                                            cases needAbs with
                                            | true =>
                                                obtain ⟨_, _, _, _, _, hCP, _⟩ := hNeedT rfl
                                                exact stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st' buf buf'
                                                  () () _ hCP hLayP rfl
                                            | false =>
                                                obtain ⟨hStEq, hCP, _⟩ := hNeedF rfl
                                                subst st'
                                                exact stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st buf buf'
                                                  () () _ hCP (by exact hLayP) rfl
                                          have hConV_to_step : ∀ (stV : stateTys.Val M.toCarriers),
                                              Clause.answer M fnTable rTable lVCl
                                                (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) stV =
                                                .done (x, stV) →
                                              (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                                (.get kind prover at_ e.τ) (.cons st (.cons stV .nil)) =
                                                .done (x, .cons st' (.cons stV .nil)) := by
                                            intro stV hLayV
                                            cases needAbs with
                                            | true =>
                                                obtain ⟨encRef, encVal, _, hEncD, hAbsD, _, hCVA⟩ := hNeedT rfl
                                                exact stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st' stV stV
                                                  x x _ hCVA hLayV (by
                                                    have hInner :
                                                        (liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons x .nil))).bind
                                                          (fun enc =>
                                                            (liftLocal id (absRef.eval M fnTable
                                                              (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                                                              fun nextSt => aloneIn M verifier (.cons x nextSt)) =
                                                          .done (aloneIn M verifier (.cons x (.cons st' .nil))) := by
                                                      rw [hEncD, liftLocal_done]
                                                      change (liftLocal (S := RSig M) id
                                                        (absRef.eval M fnTable (.cons st (.cons (msgLabel at_.site) (.cons encVal .nil))))).map _ = _
                                                      rw [hAbsD, liftLocal_done]; rfl
                                                    rw [hInner]; dsimp only [Process.mapHalt, Process.map]
                                                    rw [aloneOut_aloneIn]; rfl)
                                            | false =>
                                                obtain ⟨hStEq, _, hCVA⟩ := hNeedF rfl
                                                subst st'
                                                exact stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st stV stV
                                                  x x _ hCVA (by exact hLayV) rfl
                                          cases hLk : layout.recover.lookup e.site with
                                          | some recKey =>
                                              -- Omitted (recovered) message!
                                              rw [hLk] at hRemW' hV2'; dsimp only at hV2'
                                              cases hRemW'
                                              cases hRecF : findSafeFnRef d.admitted recKey stateTys.toList [e.τ] with
                                              | none =>
                                                  have hRecF' : findSafeFnRef d.admitted recKey
                                                      (tysOfList (stmtTys ++ allSpecs.map (·.ty))).toList [e.τ] = none := hRecF
                                                  rw [hRecF'] at hV2'; cases hV2'
                                              | some recRef =>
                                                  have hRecF' : findSafeFnRef d.admitted recKey
                                                      (tysOfList (stmtTys ++ allSpecs.map (·.ty))).toList [e.τ] = some recRef := hRecF
                                                  rw [hRecF'] at hV2'; cases hV2'
                                                  have hPrefWNext : ∃ prefP', collectCompactWire d.admitted layout unitTy prover verifier
                                                      declKey events 0 (pref ++ [e]) = .ok (prefSpecs, prefP') := by
                                                    simpa using collectCompactWire_prefix_step (headSpecs := []) hEvSplit hCW hRemRec (by simpa using hSpecSplit)
                                                  have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                                      declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                                    ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                                  obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                                    hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                                    ih () (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                                      hPrefWNext hRemWNext _ _ st' buf source hSt'V hBufV hFolRest
                                                      hPP' hPV' (hSP.2 () trivial) (hSV.2 x hMsgV)
                                                      (hShP.2 () trivial) (hShV.2 x trivial)
                                                      (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                                  have hLayPAns : Clause.answer M fnTable rTable lPCl
                                                      (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x) buf = .done ((), buf) := by
                                                    rw [hpAllEq]
                                                    rw [clause_answer_append_right M fnTable rTable _ buf prefP _
                                                      (hNoMatchPrefP_site (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x) hESite.symm)]
                                                    exact layoutDropClause_answer M fnTable rTable prover e.site kind [verifier]
                                                      ⟨at_.path, at_.site.key⟩ hESite x buf remPair.2
                                                  have hStepP := hConP_to_step buf hLayPAns
                                                  refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                                    Event.flow kind prover [verifier] at_ e.τ x :: evs',
                                                    hTr, ?_, ?_, ?_, hpP, hpV, hLSrc', hAgSrc', .flow hRun'⟩
                                                  · simp only [compactWireArgs, ← hESite, hLk]
                                                    rw [ite_eq_right (fun hm => by cases hm.2.2)]
                                                    exact hWArgs
                                                  · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                                    exact hAlP
                                                  · intro stV hSlot hRecEv
                                                    have hRecEval : recRef.eval M fnTable (Tys.toHList M stateTys stV) = .done (.cons x .nil) :=
                                                      hRecEv kind [verifier] at_ e.τ x recKey recRef List.mem_cons_self hVin
                                                        (hESite ▸ hLk) hRecF
                                                    have hLayVAns : Clause.answer M fnTable rTable lVCl
                                                        (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) stV = .done (x, stV) := by
                                                      rw [hvAllEq]
                                                      rw [clause_answer_append_right M fnTable rTable _ stV v1' _
                                                        (hNoMatchPrefV_site (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) hESite.symm)]
                                                      exact compactRecoverClause_answer M fnTable rTable verifier prover e.site kind
                                                        recRef ⟨at_.path, at_.site.key⟩ hESite stV x hRecEval vRest
                                                    have hStepV := hConV_to_step stV hLayVAns
                                                    obtain ⟨recV, hAV⟩ := hAlV stV hSlot
                                                      (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm => hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                                    exact ⟨recV, by rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]; exact hAV⟩
                                          | none =>
                                              -- Retained message serialized on wire!
                                              rw [hLk] at hRemW' hV2'
                                              cases hW : findLayoutWrite d.admitted layout.module unitTy e.τ <;>
                                              cases hR : findLayoutRead d.admitted layout.module unitTy e.τ <;>
                                                simp only [hW, hR] at hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                                rename_i wRef rRef
                                                have hFindHead : findWireMember e.site e.τ (⟨e.site, e.τ, rRef⟩ :: remPair.1) =
                                                    some Member.head := by
                                                  unfold findWireMember; rw [dite_eq_left ⟨rfl, rfl⟩]
                                                have hFindAll0 := findWireMember_append_right e.site e.τ prefSpecs
                                                  (⟨e.site, e.τ, rRef⟩ :: remPair.1) hNotInPrefW hFindHead
                                                have hFindAll : findWireMember e.site e.τ allSpecs =
                                                    some (cast (congrArg (fun l => Member l e.τ) (by rw [hSpecSplit, List.map_append]; rfl))
                                                      (memberAppendRight (prefSpecs.map (·.ty))
                                                        (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))) := by
                                                  have hG : ∀ {l₁ l₂ : List (WireSpec V d.admitted.program.headers.fns unitTy)}
                                                      (hl : l₁ = l₂) (m : Member (l₂.map (·.ty)) e.τ),
                                                      findWireMember e.site e.τ l₂ = some m →
                                                      findWireMember e.site e.τ l₁ =
                                                        some (cast (congrArg (fun l => Member l e.τ) (by rw [hl])) m) := by
                                                    intro _ _ hl _ h; subst hl; exact h
                                                  rw [hG hSpecSplit _ hFindAll0]; congr 1; exact cast_cast _ _ _
                                                rw [hFindAll] at hV2'; cases hV2'
                                                obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M d.admitted (.cons x .nil) ⟨hMsgV, trivial⟩
                                                obtain ⟨chunk, rfl⟩ := HList.one chH
                                                have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu => by
                                                  rcases List.mem_append.mp hu with h1 | h2
                                                  · exact hBufV u h1
                                                  · exact hChV.1.1 u h2
                                                have hSpecSplitNext : allSpecs = (prefSpecs ++ [⟨e.site, e.τ, rRef⟩]) ++ remPair.1 := by
                                                  simpa [List.append_assoc] using hSpecSplit
                                                have hPrefWNext := collectCompactWire_prefix_step hEvSplit hCW hRemRec hSpecSplitNext
                                                have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                                    declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                                  ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                                obtain ⟨a, outP, outV, finalSt, restWireVals, restChunks, recP, src', evs',
                                                  hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                                  ih () (pref ++ [e]) rest hEvSplit' (prefSpecs ++ [⟨e.site, e.τ, rRef⟩]) remPair.1
                                                    hSpecSplitNext hPrefWNext hRemWNext _ _ st' (buf ++ chunk) source hSt'V hBufChV
                                                    hFolRest hPP' hPV' (hSP.2 () trivial) (hSV.2 x hMsgV)
                                                    (hShP.2 () trivial) (hShV.2 x trivial)
                                                    (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                                have hLayPAns : Clause.answer M fnTable rTable lPCl
                                                    (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x) buf = .done ((), buf ++ chunk) := by
                                                  rw [hpAllEq]
                                                  rw [clause_answer_append_right M fnTable rTable _ buf prefP _
                                                    (hNoMatchPrefP_site (.give kind [verifier] ⟨at_.path, at_.site.key⟩ e.τ x) hESite.symm)]
                                                  exact layoutPWriteClause_answer M fnTable rTable prover e.site kind [verifier] wRef
                                                    ⟨at_.path, at_.site.key⟩ hESite x buf chunk hWD remPair.2
                                                have hStepP := hConP_to_step (buf ++ chunk) hLayPAns
                                                refine ⟨a, outP, outV, finalSt, .cons x restWireVals, chunk :: restChunks, recP, src',
                                                  Event.flow kind prover [verifier] at_ e.τ x :: evs',
                                                  .cons hW hR hMsgV hWD hChV.1.1 hTr, ?_, ?_, ?_, hpP, hpV, hLSrc', hAgSrc', .flow hRun'⟩
                                                · simp only [compactWireArgs, ← hESite, hLk, hVin, and_self, ite_true,
                                                    List.singleton_append, wireSigmaList]
                                                  exact congrArg (_ :: ·) hWArgs
                                                · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                                  simpa [List.append_assoc] using hAlP
                                                · intro stV hSlot hRecEv
                                                  let curSpec : WireSpec V d.admitted.program.headers.fns unitTy := ⟨e.site, e.τ, rRef⟩
                                                  have hEq1 : prefSpecs.map (·.ty) ++ e.τ :: remPair.1.map (·.ty) = allSpecs.map (·.ty) := by
                                                    rw [hSpecSplit, List.map_append]; rfl
                                                  have hEq2 : (stmtTys ++ prefSpecs.map (·.ty)) ++ e.τ :: remPair.1.map (·.ty) = stateTys.toList := by
                                                    rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]; rfl
                                                  have hSlotHead : Tys.getAt M stateTys
                                                      (Eq.mpr (congrArg (fun l => Member l e.τ) (tysOfList_toList (stmtTys ++ allSpecs.map (·.ty))))
                                                        (memberAppendRight stmtTys
                                                          (cast (congrArg (fun l => Member l e.τ) hEq1)
                                                            (memberAppendRight (prefSpecs.map (·.ty))
                                                              (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))))) stV = x := by
                                                    have hM := hSlot (mRem := Member.head)
                                                    have hMemEq :
                                                        (Eq.mpr (congrArg (fun l => Member l e.τ) (tysOfList_toList (stmtTys ++ allSpecs.map (·.ty))))
                                                          (memberAppendRight stmtTys
                                                            (cast (congrArg (fun l => Member l e.τ) hEq1)
                                                              (memberAppendRight (prefSpecs.map (·.ty))
                                                                (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))))) =
                                                        cast (congrArg (fun l => Member l e.τ) hEq2)
                                                          (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty))
                                                            (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ)) := by
                                                      have hMpr : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (k : Member l₂ e.τ),
                                                          Eq.mpr (congrArg (fun l => Member l e.τ) heq) k = cast (congrArg (fun l => Member l e.τ) heq.symm) k := by
                                                        intro _ _ heq _; subst heq; rfl
                                                      have hLift : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (k : Member l₁ e.τ),
                                                          memberAppendRight stmtTys (cast (congrArg (fun l => Member l e.τ) heq) k) =
                                                            cast (congrArg (fun l => Member l e.τ) (congrArg (stmtTys ++ ·) heq))
                                                              (memberAppendRight stmtTys k) := by
                                                        intro _ _ heq _; subst heq; rfl
                                                      rw [hMpr (tysOfList_toList _), hLift hEq1, cast_cast, ← memberAppendRight_assoc, cast_cast]
                                                    rw [hMemEq]; exact hM
                                                  have hLayVAns : Clause.answer M fnTable rTable lVCl
                                                      (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) stV = .done (x, stV) := by
                                                    rw [hvAllEq]
                                                    rw [clause_answer_append_right M fnTable rTable _ stV v1' _
                                                      (hNoMatchPrefV_site (.get kind prover ⟨at_.path, at_.site.key⟩ e.τ) hESite.symm)]
                                                    exact (compactReadSlotClause_answer M fnTable rTable htfree verifier prover
                                                      e.site kind _ ⟨at_.path, at_.site.key⟩ hESite stV vRest).trans (by rw [hSlotHead])
                                                  have hStepV := hConV_to_step stV hLayVAns
                                                  have hEqNext : (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) ++ remPair.1.map (·.ty) = stateTys.toList := by
                                                    rw [tysOfList_toList, hSpecSplitNext]; simp [curSpec, List.map_append, List.append_assoc]
                                                  have hEqCur : (stmtTys ++ prefSpecs.map (·.ty)) ++ (curSpec :: remPair.1).map (·.ty) = stateTys.toList := by
                                                    rw [tysOfList_toList, hSpecSplit]; simp [curSpec, List.map_append, List.append_assoc]
                                                  have hSlotRest : ∀ {τ'} (mRest : Member (remPair.1.map (·.ty)) τ'),
                                                      Tys.getAt M stateTys
                                                        (cast (congrArg (fun l => Member l τ') hEqNext)
                                                          (memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest)) stV =
                                                      HList.getAtMember restWireVals mRest := by
                                                    intro τ' mRest
                                                    have hM := hSlot (mRem := Member.tail mRest)
                                                    have hMemEq :
                                                        cast (congrArg (fun l => Member l τ') hEqNext)
                                                          (memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest) =
                                                        cast (congrArg (fun l => Member l τ') hEqCur)
                                                          (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) (Member.tail (b := e.τ) mRest)) := by
                                                      have hStepM : ∀ (as : List V.Ty) {b : V.Ty} {bs : List V.Ty} (k : Member bs τ'),
                                                          cast (congrArg (fun l => Member l τ') (by simp [List.append_assoc]))
                                                            (memberAppendRight (as ++ [b]) k) =
                                                            memberAppendRight as (Member.tail (b := b) k) := by
                                                        intro as b bs k
                                                        induction as with
                                                        | nil => rfl
                                                        | cons a0 as' iha =>
                                                            have hT : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (m : Member l₁ τ'),
                                                                cast (congrArg (fun l => Member (a0 :: l) τ') heq) (.tail m) =
                                                                  .tail (cast (congrArg (fun l => Member l τ') heq) m) := by
                                                              intro _ _ heq _; subst heq; rfl
                                                            exact (hT (by simp [List.append_assoc]) (memberAppendRight (as' ++ [b]) k)).trans (congrArg Member.tail iha)
                                                      have hM1 : memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest =
                                                          cast (congrArg (fun l => Member l τ') (by simp [curSpec, List.map_append, List.append_assoc]))
                                                            (memberAppendRight ((stmtTys ++ prefSpecs.map (·.ty)) ++ [e.τ]) mRest) := by
                                                        have hEqL : stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty) =
                                                            (stmtTys ++ prefSpecs.map (·.ty)) ++ [e.τ] := by simp [curSpec, List.map_append, List.append_assoc]
                                                        have hG : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂),
                                                            memberAppendRight l₁ mRest =
                                                              cast (congrArg (fun l => Member (l ++ remPair.1.map (·.ty)) τ') heq.symm)
                                                                (memberAppendRight l₂ mRest) := by
                                                          intro _ _ heq; subst heq; rfl
                                                        exact hG hEqL
                                                      rw [hM1, cast_cast, ← hStepM (stmtTys ++ prefSpecs.map (·.ty)) mRest, cast_cast]
                                                    rw [hMemEq]; exact hM
                                                  obtain ⟨recV, hAV⟩ := hAlV stV hSlotRest
                                                    (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm => hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                                  exact ⟨recV, by rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]; exact hAV⟩
                                        -- Now dispatch `needAbs = true` vs `needAbs = false`
                                        cases needAbs with
                                        | true =>
                                            obtain ⟨encP, encVal, st', hEncFindP, hEncD, hAbsD, hSt'V, hConPAns⟩ :=
                                              construction_clauses_answer_prover_flow_abs M 0 eventsAbs hCC
                                                kind [verifier] at_ e.τ x st hMsgV hStV ⟨e, hNeedAbs, hESite, rfl, hECls⟩
                                            obtain ⟨encV, hEncFindV, hConVAns⟩ :=
                                              construction_clauses_answer_verifier_flow_abs M 0 eventsAbs hCC
                                                kind at_ e.τ st ⟨e, hNeedAbs, hESite, rfl, hECls⟩
                                            have hEncEq : encP = encV := Option.some.inj (hEncFindP.symm.trans hEncFindV)
                                            subst hEncEq
                                            exact hStepCon st' ⟨fun _ => ⟨encP, encVal, hEncFindP, hEncD, hAbsD, hConPAns, hConVAns⟩,
                                              fun h => by cases h⟩ hSt'V
                                        | false =>
                                            have hNoAbsAll : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site → e'.τ = e.τ →
                                                e'.cls = .flow kind prover [verifier] → b' = false := by
                                              intro e' b' hm' hS' hT' hC'
                                              exact eventsWithAbsorb_flow_consistent prover verifier [] id false d.entry.shape
                                                hm' hNeedAbs (hS'.trans hESite.symm) hT' hC' hECls
                                            obtain ⟨hConPUnm, hConVUnm⟩ := construction_clauses_unmatched_elided_flow M 0 eventsAbs hCC
                                              kind [verifier] at_ e.τ x hNoAbsAll
                                            exact hStepCon st ⟨(fun h => by cases h), fun _ => ⟨rfl,
                                              clause_answer_unmatched_all M fnTable rTable _ st cPCl hConPUnm,
                                              clause_answer_unmatched_all M fnTable rTable _ st cVCl hConVUnm⟩⟩ hStV
                      · -- Flow involving neither prover nor verifier
                        cases hPP with
                        | begins _ => exact False.elim (hNotMP trivial)
                        | settles _ => exact False.elim (hNotMP trivial)
                        | gave _ _ => exact absurd rfl hGNeP
                        | got _ hIn _ => exact absurd hIn hPOut
                        | passed _ _ hPP' =>
                            cases hPV with
                            | begins _ => exact False.elim (hNotMV trivial)
                            | settles _ => exact False.elim (hNotMV trivial)
                            | gave _ _ => exact absurd rfl hGNeV
                            | got _ hIn _ => exact absurd hIn hVOut
                            | passed _ _ hPV' =>
                                unfold collectCompactWire at hRemW'
                                cases hRemRec : collectCompactWire d.admitted layout unitTy prover verifier
                                    declKey events (pref.length + 1) rest with
                                | error _ => rw [hRemRec] at hRemW'; cases hRemW'
                                | ok remPair =>
                                    rw [hRemRec] at hRemW'; dsimp only [bind, Except.bind] at hRemW'
                                    rw [hECls] at hRemW'; dsimp only at hRemW'
                                    rw [ite_eq_right (fun hm => hGNeP hm.1)] at hRemW'; cases hRemW'
                                    have hPrefWNext : ∃ prefP', collectCompactWire d.admitted layout unitTy prover verifier
                                        declKey events 0 (pref ++ [e]) = .ok (prefSpecs, prefP') := by
                                      simpa using collectCompactWire_prefix_step (headSpecs := []) hEvSplit hCW hRemRec (by simpa using hSpecSplit)
                                    have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                        declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                      ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                    obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                      hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                      ih () (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                        hPrefWNext hRemWNext _ _ st buf source hStV hBufV hFolRest
                                        hPP' hPV' hSP hSV hShP hShV
                                        (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                    refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                      Event.flow kind giver getters at_ e.τ x :: evs',
                                      hTr, ?_, hAlP, ?_, hpP, hpV, hLSrc', hAgSrc', .flow hRun'⟩
                                    · unfold compactWireArgs
                                      rw [ite_eq_right (fun hm => hGNeP hm.1)]
                                      exact hWArgs
                                    · intro stV hSlot hRecEv
                                      exact hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                        hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                  | given gkind owner hearers at_ gIns payload τ =>
                      obtain ⟨hESite, hETy, hECls, hFolRest⟩ := hFol
                      subst hETy
                      have hDisc := hEventDisc e hEIn
                      rw [hECls] at hDisc
                      cases gkind with
                      | coin law =>
                          rcases hDisc with ⟨hOwnEqV, hHEq, sig, hLawSig, hSigOut, hSigIns⟩ | hNil
                          · -- Verifier → Prover heard coin draw (derived from transcript!)
                            subst owner; subst hearers
                            have hPin : prover ∈ [prover] := List.mem_singleton_self prover
                            have hGInsNil : gIns = [] := by
                              cases hPP with
                              | begins _ => exact False.elim (hNotMP trivial)
                              | settles _ => exact False.elim (hNotMP trivial)
                              | owned _ => exact absurd rfl hNe.symm
                              | unheard _ hOut _ => exact absurd hPin hOut
                              | heard _ _ _ =>
                                  cases hPV with
                                  | begins _ => exact False.elim (hNotMV trivial)
                                  | settles _ => exact False.elim (hNotMV trivial)
                                  | heard hNeSelf _ _ => exact absurd rfl hNeSelf
                                  | unheard hNeSelf _ _ => exact absurd rfl hNeSelf
                                  | owned _ =>
                                      obtain ⟨_, _, _, _, _, sig', hLaw', hI', _⟩ := hShV.1
                                      have hSigEq : sig' = sig := Option.some.inj (hLaw'.symm.trans hLawSig)
                                      rw [hSigEq, hSigIns] at hI'; exact hI'.symm
                            subst hGInsNil; cases payload
                            cases hPP with
                            | begins _ => exact False.elim (hNotMP trivial)
                            | settles _ => exact False.elim (hNotMP trivial)
                            | owned _ => exact absurd rfl hNe.symm
                            | unheard _ hOut _ => exact absurd hPin hOut
                            | heard _ _ hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | heard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | unheard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | owned hPV' =>
                                    obtain ⟨bDraw, hDrawAt⟩ := eventsWithAbsorb_draw_index hFst hEvSplit
                                    have hSuf0 : ∀ k0 p0, eventsAbs[k0]? = some p0 → events[0 + k0]? = some p0.1 := by
                                      intro k0 p0 hk0
                                      rw [Nat.zero_add, ← hFst, List.getElem?_map, hk0]; rfl
                                    have hDrawMem : (e, bDraw) ∈ eventsAbs := List.mem_of_getElem? hDrawAt
                                    obtain ⟨idxP, ⟨ePSite, ePCls, ePτ⟩, derP, coinP, stP', hIdxP, hSiteP, hTyP,
                                      hClsP, hDerFindP, hDerDP, hCoinPV, hStP'V, hConPAns⟩ :=
                                      construction_clauses_answer_prover_coin M 0 eventsAbs hSuf0 hCC
                                        law at_ e.τ st hStV
                                        ⟨(e, bDraw), hDrawMem, hESite, rfl, hECls⟩
                                    obtain ⟨idxV, ⟨eV'Site, eV'Cls, eV'τ⟩, derV, coinV, stV', hIdxV, hSiteV', hTyV',
                                      hClsV', hLawV', hDerFindV, hDerDV, hCoinVV, hStV'V, hConVAns⟩ :=
                                      construction_clauses_answer_verifier_coin M 0 eventsAbs hSuf0 hCC
                                        law [prover] at_ e.τ st hStV
                                        ⟨(e, bDraw), hDrawMem, hESite, rfl, rfl, hECls⟩
                                    dsimp only at hSiteP hTyP hClsP hSiteV' hTyV' hClsV'
                                    subst ePτ; subst eV'τ
                                    have hDerEq : derP = derV := Option.some.inj (hDerFindP.symm.trans hDerFindV)
                                    subst hDerEq
                                    have hEvalEq : Process.done (HList.cons coinP (HList.cons stP' HList.nil)) =
                                        .done (.cons coinV (.cons stV' .nil)) := hDerDP.symm.trans hDerDV
                                    cases hEvalEq
                                    have hAtPref : (d.entry.shape.events [] id)[pref.length]? = some e := by
                                      rw [hEvSplit, List.getElem?_append_right (Nat.le_refl _)]
                                      simp
                                    have hIdxPEq : idxP = pref.length := by
                                      have ⟨hiP, hEqP⟩ := List.getElem?_eq_some_iff.mp hIdxP
                                      have ⟨hiE, hEqE⟩ := List.getElem?_eq_some_iff.mp hAtPref
                                      exact list_nodup_getElem_inj hNodup (by simpa using hiP) (by simpa using hiE)
                                        (by simp only [List.getElem_map]; rw [hEqP, hEqE, hSiteP, hESite])
                                    have hIdxVEq : idxV = pref.length := by
                                      have ⟨hiV, hEqV⟩ := List.getElem?_eq_some_iff.mp hIdxV
                                      have ⟨hiE, hEqE⟩ := List.getElem?_eq_some_iff.mp hAtPref
                                      exact list_nodup_getElem_inj hNodup (by simpa using hiV) (by simpa using hiE)
                                        (by simp only [List.getElem_map]; rw [hEqV, hEqE, hSiteV', hESite])
                                    subst hIdxPEq; subst hIdxVEq
                                    let coin := coinP
                                    let st' := stP'
                                    have hCoinV : M.Valid e.τ coin := hCoinPV
                                    have hSt'V : M.Valid stateTy st' := hStP'V
                                    have hAllows : Allows M (.coin law) [] .nil e.τ coin :=
                                      suiteLawful_allows M hConDecl hSuiteLaw hStart hDerFindV
                                        (List.mem_of_getElem? hIdxV) hClsV' rfl hLawV'
                                        hStV (drawLabel_bytes at_.site) hDerDV
                                    have hAtHeard : at_.site ∈ d.entry.shape.heardCoins := by
                                      rw [← hESite]; exact mem_heardCoins_of_event hEIn hECls
                                    have hLP' : LawfulPrivate M source (k coin) := hLP coin hAllows
                                    have hFed' : Fed M source (k coin) := hFed coin hAllows
                                    have hOccK : Protocol.OccsIn M (· ≠ at_) (k coin) := (hUniq coin).1
                                    have hNoHalt' : ∀ source₁, Lawful M source₁ (k coin) →
                                        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                                        ∀ e', GExec M source₁ (k coin) e' → ∃ a, e' = .returned a := by
                                      intro s₁ hL₁ hAg₁ e' ⟨evs', hRun'⟩
                                      let s₂ := patchSource M s₁ at_ e.τ coin
                                      have hAg12 : ∀ at' τ', at' ≠ at_ → s₁ at' τ' = s₂ at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M s₁ at_ e.τ coin hne τ').symm
                                      have hL₂ : Lawful M s₂ (.call (.given (.coin law) verifier [prover] at_ [] .nil e.τ) k) := by
                                        intro v hv; dsimp only [s₂] at hv; rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllows, lawful_of_agree M hAg12 hOccK hL₁⟩
                                      have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → s₂ at' τ' = source at' τ' := by
                                        intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [s₂]; rw [patchSource_ne M s₁ at_ e.τ coin hne τ']; exact hAg₁ at' τ' hNotIn
                                      exact hNoHalt s₂ hL₂ hAg₂ e' ⟨_, .given (patchSource_self M s₁ at_ e.τ coin)
                                        (grun_of_agree M hAg12 hOccK hRun')⟩
                                    -- Unpack compact wire & V clauses at `e`
                                    unfold collectCompactWire at hRemW'
                                    cases hRemRec : collectCompactWire d.admitted layout unitTy prover verifier
                                        declKey events (pref.length + 1) rest with
                                    | error _ => rw [hRemRec] at hRemW'; cases hRemW'
                                    | ok remPair =>
                                        rw [hRemRec] at hRemW'; dsimp only [bind, Except.bind] at hRemW'
                                        rw [hECls] at hRemW'; dsimp only at hRemW'
                                        rw [ite_eq_left ⟨rfl, rfl⟩] at hRemW'
                                        unfold buildCompactVClauses at hV2'
                                        cases hVRec : buildCompactVClauses d.admitted layout unitTy prover verifier
                                            declKey events stmtTys allSpecs htfree (pref.length + 1) rest with
                                        | error _ => rw [hVRec] at hV2'; cases hV2'
                                        | ok vRest =>
                                            rw [hVRec] at hV2'; dsimp only [bind, Except.bind] at hV2'
                                            rw [hECls] at hV2'; dsimp only at hV2'
                                            rw [ite_eq_left ⟨rfl, rfl⟩] at hV2'
                                            have hToldSiteEq : (⟨e.site.through, drawToldKey events pref.length⟩ : Site) =
                                                (⟨at_.path, drawToldKey events pref.length⟩ : Occurrence).site := by
                                              have hTh : e.site.through = Frame.applications at_.path :=
                                                congrArg Site.through hESite
                                              exact congrArg (fun th => Site.mk th (drawToldKey events pref.length)) hTh
                                            by_cases hCar : e.site ∈ layout.carry
                                            · -- Carried draw!
                                              rw [ite_eq_left hCar] at hRemW' hV2'
                                              cases hW : findLayoutWrite d.admitted layout.module unitTy e.τ <;>
                                              cases hR : findLayoutRead d.admitted layout.module unitTy e.τ <;>
                                                simp only [hW, hR] at hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                              · cases hRemW'
                                                rename_i wRef rRef
                                                have hFindHead : findWireMember ⟨e.site.through, drawToldKey events pref.length⟩ e.τ
                                                    (⟨⟨e.site.through, drawToldKey events pref.length⟩, e.τ, rRef⟩ :: remPair.1) =
                                                    some Member.head := by
                                                  unfold findWireMember; rw [dite_eq_left ⟨rfl, rfl⟩]
                                                have hFindAll0 := findWireMember_append_right _ e.τ prefSpecs
                                                  (⟨⟨e.site.through, drawToldKey events pref.length⟩, e.τ, rRef⟩ :: remPair.1)
                                                  hNotInPrefW_told hFindHead
                                                have hFindAll : findWireMember ⟨e.site.through, drawToldKey events pref.length⟩ e.τ allSpecs =
                                                    some (cast (congrArg (fun l => Member l e.τ) (by rw [hSpecSplit, List.map_append]; rfl))
                                                      (memberAppendRight (prefSpecs.map (·.ty))
                                                        (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))) := by
                                                  have hG : ∀ {l₁ l₂ : List (WireSpec V d.admitted.program.headers.fns unitTy)}
                                                      (hl : l₁ = l₂) (m : Member (l₂.map (·.ty)) e.τ),
                                                      findWireMember ⟨e.site.through, drawToldKey events pref.length⟩ e.τ l₂ = some m →
                                                      findWireMember ⟨e.site.through, drawToldKey events pref.length⟩ e.τ l₁ =
                                                        some (cast (congrArg (fun l => Member l e.τ) (by rw [hl])) m) := by
                                                    intro _ _ hl _ h; subst hl; exact h
                                                  rw [hG hSpecSplit _ hFindAll0]; congr 1; exact cast_cast _ _ _
                                                rw [hFindAll] at hV2'
                                                cases hEqR : findLayoutEqual d.admitted layout.module e.τ with
                                                | none => rw [hEqR] at hV2'; cases hV2'
                                                | some eqRef =>
                                                    rw [hEqR] at hV2'; cases hV2'
                                                    obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M d.admitted (.cons coin .nil) ⟨hCoinV, trivial⟩
                                                    obtain ⟨chunk, rfl⟩ := HList.one chH
                                                    have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := fun u hu => by
                                                      rcases List.mem_append.mp hu with h1 | h2
                                                      · exact hBufV u h1
                                                      · exact hChV.1.1 u h2
                                                    have hSpecSplitNext : allSpecs = (prefSpecs ++ [⟨⟨e.site.through, drawToldKey events pref.length⟩, e.τ, rRef⟩]) ++ remPair.1 := by
                                                      simpa [List.append_assoc] using hSpecSplit
                                                    have hPrefWNext := collectCompactWire_prefix_step hEvSplit hCW hRemRec hSpecSplitNext
                                                    have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                                        declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                                      ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                                    obtain ⟨a, outP, outV, finalSt, restWireVals, restChunks, recP, src', evs',
                                                      hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                                      ih coin (pref ++ [e]) rest hEvSplit'
                                                        (prefSpecs ++ [⟨⟨e.site.through, drawToldKey events pref.length⟩, e.τ, rRef⟩])
                                                        remPair.1 hSpecSplitNext hPrefWNext hRemWNext
                                                        _ _ st' (buf ++ chunk) source hSt'V hBufChV
                                                        (hFolRest coin) (hPP' coin) (hPV' coin)
                                                        (hSP.2 coin hCoinV) (hSV.2 coin hCoinV)
                                                        (hShP.2 coin trivial) (hShV.2 coin trivial)
                                                        (hPShape.2 coin) (hUniq coin).2 hLP' hFed' hNoHalt'
                                                    have hLayPAns : Clause.answer M fnTable rTable lPCl
                                                        (.give .message [verifier] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) buf =
                                                        .done ((), buf ++ chunk) := by
                                                      rw [hpAllEq]
                                                      rw [clause_answer_append_right M fnTable rTable _ buf prefP _
                                                        (hNoMatchPrefP_told (.give .message [verifier] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) hToldSiteEq.symm)]
                                                      exact layoutPWriteClause_answer M fnTable rTable prover _ .message [verifier] wRef
                                                        ⟨at_.path, drawToldKey events pref.length⟩ hToldSiteEq coin buf chunk hWD remPair.2
                                                    have hStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                                        (.hear (.coin law) verifier at_ e.τ) (.cons st (.cons buf .nil)) =
                                                        .done (coin, .cons st' (.cons (buf ++ chunk) .nil)) :=
                                                      stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st' buf (buf ++ chunk)
                                                        () coin _ (by simpa using hConPAns) hLayPAns rfl
                                                    let src'' := patchSource M src' at_ e.τ coin
                                                    have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                                      fun at' τ' hne => (patchSource_ne M src' at_ e.τ coin hne τ').symm
                                                    refine ⟨a, outP, outV, finalSt, .cons coin restWireVals, chunk :: restChunks,
                                                      recP, src'', Event.given (.coin law) verifier [prover] at_ e.τ coin :: evs',
                                                      .cons hW hR hCoinV hWD hChV.1.1 hTr, ?_, ?_, ?_, hpP, hpV, ?_, ?_,
                                                      .given (patchSource_self M src' at_ e.τ coin) (grun_of_agree M hAgPatch hOccK hRun')⟩
                                                    · simp only [compactWireArgs, ← hESite, hPin, hCar, and_self, ite_true,
                                                        List.singleton_append, wireSigmaList]
                                                      exact congrArg (_ :: ·) hWArgs
                                                    · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                                      simpa [List.append_assoc] using hAlP
                                                    · intro stV hSlot hRecEv
                                                      let curSpec : WireSpec V d.admitted.program.headers.fns unitTy :=
                                                        ⟨⟨e.site.through, drawToldKey events pref.length⟩, e.τ, rRef⟩
                                                      have hEq1 : prefSpecs.map (·.ty) ++ e.τ :: remPair.1.map (·.ty) = allSpecs.map (·.ty) := by
                                                        rw [hSpecSplit, List.map_append]; rfl
                                                      have hEq2 : (stmtTys ++ prefSpecs.map (·.ty)) ++ e.τ :: remPair.1.map (·.ty) = stateTys.toList := by
                                                        rw [tysOfList_toList, hSpecSplit, List.map_append, List.append_assoc]; rfl
                                                      have hSlotHead : Tys.getAt M stateTys
                                                          (Eq.mpr (congrArg (fun l => Member l e.τ) (tysOfList_toList (stmtTys ++ allSpecs.map (·.ty))))
                                                            (memberAppendRight stmtTys
                                                              (cast (congrArg (fun l => Member l e.τ) hEq1)
                                                                (memberAppendRight (prefSpecs.map (·.ty))
                                                                  (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))))) stV = coin := by
                                                        have hM := hSlot (mRem := Member.head)
                                                        have hMemEq :
                                                            (Eq.mpr (congrArg (fun l => Member l e.τ) (tysOfList_toList (stmtTys ++ allSpecs.map (·.ty))))
                                                              (memberAppendRight stmtTys
                                                                (cast (congrArg (fun l => Member l e.τ) hEq1)
                                                                  (memberAppendRight (prefSpecs.map (·.ty))
                                                                    (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ))))) =
                                                            cast (congrArg (fun l => Member l e.τ) hEq2)
                                                              (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty))
                                                                (Member.head : Member (e.τ :: remPair.1.map (·.ty)) e.τ)) := by
                                                          have hMpr : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (k : Member l₂ e.τ),
                                                              Eq.mpr (congrArg (fun l => Member l e.τ) heq) k = cast (congrArg (fun l => Member l e.τ) heq.symm) k := by
                                                            intro _ _ heq _; subst heq; rfl
                                                          have hLift : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (k : Member l₁ e.τ),
                                                              memberAppendRight stmtTys (cast (congrArg (fun l => Member l e.τ) heq) k) =
                                                                cast (congrArg (fun l => Member l e.τ) (congrArg (stmtTys ++ ·) heq))
                                                                  (memberAppendRight stmtTys k) := by
                                                            intro _ _ heq _; subst heq; rfl
                                                          rw [hMpr (tysOfList_toList _), hLift hEq1, cast_cast, ← memberAppendRight_assoc, cast_cast]
                                                        rw [hMemEq]; exact hM
                                                      have hEqRefl := layoutLawful_equal_refl M hLayDecl hLayLaw hEqR hCoinV
                                                      have hLayVAns : Clause.answer M fnTable rTable lVCl
                                                          (.give .message [prover] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) stV =
                                                          .done ((), stV) := by
                                                        rw [hvAllEq]
                                                        rw [clause_answer_append_right M fnTable rTable _ stV v1' _
                                                          (hNoMatchPrefV_told (.give .message [prover] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) hToldSiteEq.symm)]
                                                        exact compactCompareClause_answer M fnTable rTable htfree verifier prover _ _ _ eqRef
                                                          ⟨at_.path, drawToldKey events pref.length⟩ hToldSiteEq coin stV
                                                          (by rw [hSlotHead]; exact hEqRefl) vRest
                                                      have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                                          (.own (.coin law) [prover] at_ [] .nil e.τ) (.cons st (.cons stV .nil)) =
                                                          .done (coin, .cons st' (.cons stV .nil)) :=
                                                        stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st' stV stV
                                                          () coin _ (by simpa using hConVAns) hLayVAns rfl
                                                      have hEqNext : (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) ++ remPair.1.map (·.ty) = stateTys.toList := by
                                                        rw [tysOfList_toList, hSpecSplitNext]; simp [curSpec, List.map_append, List.append_assoc]
                                                      have hEqCur : (stmtTys ++ prefSpecs.map (·.ty)) ++ (curSpec :: remPair.1).map (·.ty) = stateTys.toList := by
                                                        rw [tysOfList_toList, hSpecSplit]; simp [curSpec, List.map_append, List.append_assoc]
                                                      have hSlotRest : ∀ {τ'} (mRest : Member (remPair.1.map (·.ty)) τ'),
                                                          Tys.getAt M stateTys
                                                            (cast (congrArg (fun l => Member l τ') hEqNext)
                                                              (memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest)) stV =
                                                          HList.getAtMember restWireVals mRest := by
                                                        intro τ' mRest
                                                        have hM := hSlot (mRem := Member.tail mRest)
                                                        have hMemEq :
                                                            cast (congrArg (fun l => Member l τ') hEqNext)
                                                              (memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest) =
                                                            cast (congrArg (fun l => Member l τ') hEqCur)
                                                              (memberAppendRight (stmtTys ++ prefSpecs.map (·.ty)) (Member.tail (b := e.τ) mRest)) := by
                                                          have hStepM : ∀ (as : List V.Ty) {b : V.Ty} {bs : List V.Ty} (k : Member bs τ'),
                                                              cast (congrArg (fun l => Member l τ') (by simp [List.append_assoc]))
                                                                (memberAppendRight (as ++ [b]) k) =
                                                                memberAppendRight as (Member.tail (b := b) k) := by
                                                            intro as b bs k
                                                            induction as with
                                                            | nil => rfl
                                                            | cons a0 as' iha =>
                                                                have hT : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂) (m : Member l₁ τ'),
                                                                    cast (congrArg (fun l => Member (a0 :: l) τ') heq) (.tail m) =
                                                                      .tail (cast (congrArg (fun l => Member l τ') heq) m) := by
                                                                  intro _ _ heq _; subst heq; rfl
                                                                exact (hT (by simp [List.append_assoc]) (memberAppendRight (as' ++ [b]) k)).trans (congrArg Member.tail iha)
                                                          have hM1 : memberAppendRight (stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty)) mRest =
                                                              cast (congrArg (fun l => Member l τ') (by simp [curSpec, List.map_append, List.append_assoc]))
                                                                (memberAppendRight ((stmtTys ++ prefSpecs.map (·.ty)) ++ [e.τ]) mRest) := by
                                                            have hEqL : stmtTys ++ (prefSpecs ++ [curSpec]).map (·.ty) =
                                                                (stmtTys ++ prefSpecs.map (·.ty)) ++ [e.τ] := by simp [curSpec, List.map_append, List.append_assoc]
                                                            have hG : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂),
                                                                memberAppendRight l₁ mRest =
                                                                  cast (congrArg (fun l => Member (l ++ remPair.1.map (·.ty)) τ') heq.symm)
                                                                    (memberAppendRight l₂ mRest) := by
                                                              intro _ _ heq; subst heq; rfl
                                                            exact hG hEqL
                                                          rw [hM1, cast_cast, ← hStepM (stmtTys ++ prefSpecs.map (·.ty)) mRest, cast_cast]
                                                        rw [hMemEq]; exact hM
                                                      obtain ⟨recV, hAV⟩ := hAlV stV hSlotRest
                                                        (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm => hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                                      exact ⟨recV, by rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]; exact hAV⟩
                                                    · intro v hv; dsimp only [src''] at hv; rw [patchSource_self] at hv; cases hv
                                                      exact ⟨hAllows, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                                    · intro at' τ' hNotIn
                                                      have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                                      dsimp only [src'']; rw [patchSource_ne M src' at_ e.τ coin hne τ']; exact hAgSrc' at' τ' hNotIn
                                            · -- Uncarried draw (dropped by both layouts)
                                              rw [ite_eq_right hCar] at hRemW' hV2'
                                              cases hRemW'; cases hV2'
                                              have hPrefWNext : ∃ prefP', collectCompactWire d.admitted layout unitTy prover verifier
                                                  declKey events 0 (pref ++ [e]) = .ok (prefSpecs, prefP') := by
                                                simpa using collectCompactWire_prefix_step (headSpecs := []) hEvSplit hCW hRemRec (by simpa using hSpecSplit)
                                              have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                                  declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                                ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                              obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                                hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                                ih coin (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                                  hPrefWNext hRemWNext _ _ st' buf source hSt'V hBufV
                                                  (hFolRest coin) (hPP' coin) (hPV' coin)
                                                  (hSP.2 coin hCoinV) (hSV.2 coin hCoinV)
                                                  (hShP.2 coin trivial) (hShV.2 coin trivial)
                                                  (hPShape.2 coin) (hUniq coin).2 hLP' hFed' hNoHalt'
                                              have hLayPAns : Clause.answer M fnTable rTable lPCl
                                                  (.give .message [verifier] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) buf =
                                                  .done ((), buf) := by
                                                rw [hpAllEq]
                                                rw [clause_answer_append_right M fnTable rTable _ buf prefP _
                                                  (hNoMatchPrefP_told (.give .message [verifier] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin)
                                                    hToldSiteEq.symm)]
                                                exact layoutDropClause_answer M fnTable rTable prover _ .message [verifier]
                                                  ⟨at_.path, drawToldKey events pref.length⟩ hToldSiteEq coin buf remPair.2
                                              have hStepP : (Stack.handler M fnTable rTable [conP0, layP0]).clause
                                                  (.hear (.coin law) verifier at_ e.τ) (.cons st (.cons buf .nil)) =
                                                  .done (coin, .cons st' (.cons buf .nil)) :=
                                                stack2_clause_step M fnTable rTable conP0 layP0 _ _ st st' buf buf
                                                  () coin _ (by simpa using hConPAns) hLayPAns rfl
                                              let src'' := patchSource M src' at_ e.τ coin
                                              have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                                fun at' τ' hne => (patchSource_ne M src' at_ e.τ coin hne τ').symm
                                              refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src'',
                                                Event.given (.coin law) verifier [prover] at_ e.τ coin :: evs',
                                                hTr, ?_, ?_, ?_, hpP, hpV, ?_, ?_,
                                                .given (patchSource_self M src' at_ e.τ coin) (grun_of_agree M hAgPatch hOccK hRun')⟩
                                              · unfold compactWireArgs
                                                rw [← hESite, ite_eq_right (fun hm => hCar hm.2.2)]
                                                exact hWArgs
                                              · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]; exact hAlP
                                              · intro stV hSlot hRecEv
                                                have hLayVAns : Clause.answer M fnTable rTable lVCl
                                                    (.give .message [prover] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin) stV =
                                                    .done ((), stV) := by
                                                  rw [hvAllEq]
                                                  rw [clause_answer_append_right M fnTable rTable _ stV v1' _
                                                    (hNoMatchPrefV_told (.give .message [prover] ⟨at_.path, drawToldKey events pref.length⟩ e.τ coin)
                                                      hToldSiteEq.symm)]
                                                  exact layoutDropClause_answer M fnTable rTable verifier _ .message [prover]
                                                    ⟨at_.path, drawToldKey events pref.length⟩ hToldSiteEq coin stV vRest
                                                have hStepV : (Stack.handler M fnTable rTable [conV0, layV0]).clause
                                                    (.own (.coin law) [prover] at_ [] .nil e.τ) (.cons st (.cons stV .nil)) =
                                                    .done (coin, .cons st' (.cons stV .nil)) :=
                                                  stack2_clause_step M fnTable rTable conV0 layV0 _ _ st st' stV stV
                                                    () coin _ (by simpa using hConVAns) hLayVAns rfl
                                                obtain ⟨recV, hAV⟩ := hAlV stV hSlot
                                                  (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm => hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                                exact ⟨recV, by rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]; exact hAV⟩
                                              · intro v hv; dsimp only [src''] at hv; rw [patchSource_self] at hv; cases hv
                                                exact ⟨hAllows, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                              · intro at' τ' hNotIn
                                                have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                                dsimp only [src'']; rw [patchSource_ne M src' at_ e.τ coin hne τ']; exact hAgSrc' at' τ' hNotIn
                          · -- Private coin (`hearers = []`)
                            subst hNil
                            obtain ⟨v, hSrcV, hFed'⟩ := hFed
                            have ⟨hAllowsV, hLP'⟩ := hLP v hSrcV
                            have hValV : M.Valid e.τ v := allows_valid M hAllowsV
                            have hNotHeard : at_.site ∉ d.entry.shape.heardCoins := by
                              intro hIn
                              unfold Shape.heardCoins at hIn
                              obtain ⟨e', hE', hF⟩ := List.mem_filterMap.mp hIn
                              cases hC' : e'.cls with
                              | flow _ _ _ => rw [hC'] at hF; cases hF
                              | given gk' _ hs' =>
                                  rw [hC'] at hF
                                  cases gk' with
                                  | request _ => cases hF
                                  | coin _ =>
                                      cases hs' with
                                      | nil => cases hF
                                      | cons _ _ =>
                                          have hS' : e'.site = at_.site := Option.some.inj hF
                                          have hEqE : e' = e := by
                                            obtain ⟨i1, hi1, hAt1⟩ := List.getElem_of_mem hE'
                                            obtain ⟨i2, hi2, hAt2⟩ := List.getElem_of_mem (show e ∈ d.entry.shape.events [] id from hEIn)
                                            have hi : i1 = i2 :=
                                              list_nodup_getElem_inj hNodup (by simpa using hi1) (by simpa using hi2)
                                                (by simp only [List.getElem_map]; rw [hAt1, hAt2, hS', hESite])
                                            subst hi; rw [← hAt1, hAt2]
                                          subst hEqE; rw [hECls] at hC'; cases hC'
                            have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                                (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                                ∀ e', GExec M source₁ (k v) e' → ∃ a, e' = .returned a := by
                              intro s₁ hL₁ hAg₁ e' ⟨evs', hRun'⟩
                              have hS1 : s₁ at_ e.τ = some v := (hAg₁ at_ e.τ hNotHeard).trans hSrcV
                              have hL2 : Lawful M s₁ (.call (.given (.coin law) owner [] at_ gIns payload e.τ) k) := by
                                intro w hw; rw [hS1] at hw; cases hw; exact ⟨hAllowsV, hL₁⟩
                              exact hNoHalt s₁ hL2 hAg₁ e' ⟨_, .given hS1 hRun'⟩
                            unfold collectCompactWire at hRemW'
                            cases hRemRec : collectCompactWire d.admitted layout unitTy prover verifier
                                declKey events (pref.length + 1) rest with
                            | error _ => rw [hRemRec] at hRemW'; cases hRemW'
                            | ok remPair =>
                                rw [hRemRec] at hRemW'; dsimp only [bind, Except.bind] at hRemW'
                                rw [hECls] at hRemW'; dsimp only at hRemW'
                                rw [ite_eq_right (fun hm => nomatch hm.2)] at hRemW'; cases hRemW'
                                have hPrefWNext : ∃ prefP', collectCompactWire d.admitted layout unitTy prover verifier
                                    declKey events 0 (pref ++ [e]) = .ok (prefSpecs, prefP') := by
                                  simpa using collectCompactWire_prefix_step (headSpecs := []) hEvSplit hCW hRemRec (by simpa using hSpecSplit)
                                have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                    declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                  ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                                cases hPP with
                                | begins _ => exact False.elim (hNotMP trivial)
                                | settles _ => exact False.elim (hNotMP trivial)
                                | heard _ hIn _ => cases hIn
                                | owned hPP' =>
                                    cases hPV with
                                    | begins _ => exact False.elim (hNotMV trivial)
                                    | settles _ => exact False.elim (hNotMV trivial)
                                    | owned _ => exact absurd rfl hNe
                                    | heard _ hIn _ => cases hIn
                                    | unheard _ _ hPV' =>
                                        obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                          hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                          ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                            hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                            (hFolRest v) (hPP' v) (hPV' v) (hSP.2 v hValV) hSV
                                            (hShP.2 v trivial) hShV (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                        refine ⟨a, outP, outV, finalSt, wireVals, chunks,
                                          .owned prover (.coin law) at_ e.τ v :: recP, src',
                                          Event.given (.coin law) prover [] at_ e.τ v :: evs',
                                          hTr, ?_, ?_, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                        · unfold compactWireArgs; rw [ite_eq_right (fun hm => nomatch hm.2.1)]; exact hWArgs
                                        · rw [stack_run_own M _ (.coin law) [] at_ gIns payload e.τ _ _ (hPassP _ _ _ trivial)]
                                          exact .own hSrcV hAlP
                                        · intro stV hSlot hRecEv
                                          exact hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                            hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                        · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩
                                | unheard _ _ hPP' =>
                                    cases hPV with
                                    | begins _ => exact False.elim (hNotMV trivial)
                                    | settles _ => exact False.elim (hNotMV trivial)
                                    | heard _ hIn _ => cases hIn
                                    | owned hPV' =>
                                        obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                          hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                          ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                            hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                            (hFolRest v) (hPP' v) (hPV' v) hSP (hSV.2 v hValV)
                                            hShP (hShV.2 v trivial) (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                        refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                          Event.given (.coin law) verifier [] at_ e.τ v :: evs',
                                          hTr, ?_, hAlP, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                        · unfold compactWireArgs; rw [ite_eq_right (fun hm => nomatch hm.2.1)]; exact hWArgs
                                        · intro stV hSlot hRecEv
                                          obtain ⟨recV, hAV⟩ := hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                            hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                          exact ⟨.owned verifier (.coin law) at_ e.τ v :: recV, by
                                            rw [stack_run_own M _ (.coin law) [] at_ gIns payload e.τ _ _ (hPassV _ _ _ trivial)]
                                            exact .own hSrcV hAV⟩
                                        · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩
                                    | unheard _ _ hPV' =>
                                        obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                          hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                          ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                            hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                            (hFolRest v) (hPP' v) (hPV' v) hSP hSV hShP hShV
                                            (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                        have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                        refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                          Event.given (.coin law) owner [] at_ e.τ v :: evs',
                                          hTr, ?_, hAlP, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                        · unfold compactWireArgs; rw [ite_eq_right (fun hm => nomatch hm.2.1)]; exact hWArgs
                                        · intro stV hSlot hRecEv
                                          exact hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                            hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                        · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩
                      | request svc =>
                          obtain ⟨hPReq, hVReq⟩ := hDisc
                          obtain ⟨v, hSrcV, hFed'⟩ := hFed
                          have ⟨hAllowsV, hLP'⟩ := hLP v hSrcV
                          have hValV : M.Valid e.τ v := allows_valid M hAllowsV
                          have hNotHeard : at_.site ∉ d.entry.shape.heardCoins := by
                            intro hIn
                            unfold Shape.heardCoins at hIn
                            obtain ⟨e', hE', hF⟩ := List.mem_filterMap.mp hIn
                            cases hC' : e'.cls with
                            | flow _ _ _ => rw [hC'] at hF; cases hF
                            | given gk' _ hs' =>
                                rw [hC'] at hF
                                cases gk' with
                                | request _ => cases hF
                                | coin _ =>
                                    cases hs' with
                                    | nil => cases hF
                                    | cons _ _ =>
                                        have hS' : e'.site = at_.site := Option.some.inj hF
                                        have hEqE : e' = e := by
                                          obtain ⟨i1, hi1, hAt1⟩ := List.getElem_of_mem hE'
                                          obtain ⟨i2, hi2, hAt2⟩ := List.getElem_of_mem (show e ∈ d.entry.shape.events [] id from hEIn)
                                          have hi : i1 = i2 :=
                                            list_nodup_getElem_inj hNodup (by simpa using hi1) (by simpa using hi2)
                                              (by simp only [List.getElem_map]; rw [hAt1, hAt2, hS', hESite])
                                          subst hi; rw [← hAt1, hAt2]
                                        subst hEqE; rw [hECls] at hC'; cases hC'
                          have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                              (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                              ∀ e', GExec M source₁ (k v) e' → ∃ a, e' = .returned a := by
                            intro s₁ hL₁ hAg₁ e' ⟨evs', hRun'⟩
                            have hS1 : s₁ at_ e.τ = some v := (hAg₁ at_ e.τ hNotHeard).trans hSrcV
                            have hL2 : Lawful M s₁ (.call (.given (.request svc) owner hearers at_ gIns payload e.τ) k) := by
                              intro w hw; rw [hS1] at hw; cases hw; exact ⟨hAllowsV, hL₁⟩
                            exact hNoHalt s₁ hL2 hAg₁ e' ⟨_, .given hS1 hRun'⟩
                          unfold collectCompactWire at hRemW'
                          cases hRemRec : collectCompactWire d.admitted layout unitTy prover verifier
                              declKey events (pref.length + 1) rest with
                          | error _ => rw [hRemRec] at hRemW'; cases hRemW'
                          | ok remPair =>
                              rw [hRemRec] at hRemW'; dsimp only [bind, Except.bind] at hRemW'
                              rw [hECls] at hRemW'; cases hRemW'
                              have hPrefWNext : ∃ prefP', collectCompactWire d.admitted layout unitTy prover verifier
                                  declKey events 0 (pref ++ [e]) = .ok (prefSpecs, prefP') := by
                                simpa using collectCompactWire_prefix_step (headSpecs := []) hEvSplit hCW hRemRec (by simpa using hSpecSplit)
                              have hRemWNext : ∃ remP', collectCompactWire d.admitted layout unitTy prover verifier
                                  declKey events (pref ++ [e]).length rest = .ok (remPair.1, remP') :=
                                ⟨remPair.2, by simpa [List.length_append] using hRemRec⟩
                              cases hPP with
                              | begins _ => exact False.elim (hNotMP trivial)
                              | settles _ => exact False.elim (hNotMP trivial)
                              | heard hNeO hPIn _ =>
                                  rcases hPReq with hEq | hOut
                                  · exact absurd hEq hNeO
                                  · exact absurd hPIn hOut
                              | owned hPP' =>
                                  cases hPV with
                                  | begins _ => exact False.elim (hNotMV trivial)
                                  | settles _ => exact False.elim (hNotMV trivial)
                                  | owned _ => exact absurd rfl hNe
                                  | heard hNeO hVIn _ =>
                                      rcases hVReq with hEq | hOut
                                      · exact absurd hEq hNeO
                                      · exact absurd hVIn hOut
                                  | unheard _ _ hPV' =>
                                      obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                        hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                        ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                          hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                          (hFolRest v) (hPP' v) (hPV' v) (hSP.2 v hValV) hSV
                                          (hShP.2 v trivial) hShV (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                      have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                      refine ⟨a, outP, outV, finalSt, wireVals, chunks,
                                        .owned prover (.request svc) at_ e.τ v :: recP, src',
                                        Event.given (.request svc) prover hearers at_ e.τ v :: evs',
                                        hTr, hWArgs, ?_, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                      · rw [stack_run_own M _ (.request svc) hearers at_ gIns payload e.τ _ _ (hPassP _ _ _ trivial)]
                                        exact .own hSrcV hAlP
                                      · intro stV hSlot hRecEv
                                        exact hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                          hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                      · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩
                              | unheard _ _ hPP' =>
                                  cases hPV with
                                  | begins _ => exact False.elim (hNotMV trivial)
                                  | settles _ => exact False.elim (hNotMV trivial)
                                  | heard hNeO hVIn _ =>
                                      rcases hVReq with hEq | hOut
                                      · exact absurd hEq hNeO
                                      · exact absurd hVIn hOut
                                  | owned hPV' =>
                                      obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                        hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                        ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                          hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                          (hFolRest v) (hPP' v) (hPV' v) hSP (hSV.2 v hValV)
                                          hShP (hShV.2 v trivial) (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                      have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                      refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                        Event.given (.request svc) verifier hearers at_ e.τ v :: evs',
                                        hTr, hWArgs, hAlP, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                      · intro stV hSlot hRecEv
                                        obtain ⟨recV, hAV⟩ := hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                          hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                        exact ⟨.owned verifier (.request svc) at_ e.τ v :: recV, by
                                          rw [stack_run_own M _ (.request svc) hearers at_ gIns payload e.τ _ _ (hPassV _ _ _ trivial)]
                                          exact .own hSrcV hAV⟩
                                      · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩
                                  | unheard _ _ hPV' =>
                                      obtain ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src', evs',
                                        hTr, hWArgs, hAlP, hAlV, hpP, hpV, hLSrc', hAgSrc', hRun'⟩ :=
                                        ih v (pref ++ [e]) rest hEvSplit' prefSpecs remPair.1 hSpecSplit
                                          hPrefWNext hRemWNext _ _ st buf source hStV hBufV
                                          (hFolRest v) (hPP' v) (hPV' v) hSP hSV hShP hShV
                                          (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                      have hS' : src' at_ e.τ = some v := (hAgSrc' at_ e.τ hNotHeard).trans hSrcV
                                      refine ⟨a, outP, outV, finalSt, wireVals, chunks, recP, src',
                                        Event.given (.request svc) owner hearers at_ e.τ v :: evs',
                                        hTr, hWArgs, hAlP, ?_, hpP, hpV, ?_, hAgSrc', .given hS' hRun'⟩
                                      · intro stV hSlot hRecEv
                                        exact hAlV stV hSlot (fun k0 gs0 at0 τ0 x0 rKey0 rRef0 hm =>
                                          hRecEv k0 gs0 at0 τ0 x0 rKey0 rRef0 (List.mem_cons_of_mem _ hm))
                                      · intro w hw; rw [hS'] at hw; cases hw; exact ⟨hAllowsV, hLSrc'⟩)
            (fun at_ kV h => by
              obtain ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
              exact ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3,
                fun stV hSlot hRec => by
                  obtain ⟨rV, hV⟩ := h4 stV hSlot hRec
                  exact ⟨.began verifier at_ :: rV,
                    by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hV⟩,
                h5, h6, h7, h8, h9⟩)
            (fun at_ kV h => by
              obtain ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
              exact ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3,
                fun stV hSlot hRec => by
                  obtain ⟨rV, hV⟩ := h4 stV hSlot hRec
                  exact ⟨.settled verifier at_ :: rV,
                    by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hV⟩,
                h5, h6, h7, h8, h9⟩)
            hPV hSV hShV)
        (fun at_ kP h => by
          obtain ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
          exact ⟨a, oP, oV, fSt, wV, ch, .began prover at_ :: rP, s', evs, h1, h2,
            by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin h3,
            h4, h5, h6, h7, h8, h9⟩)
        (fun at_ kP h => by
          obtain ⟨a, oP, oV, fSt, wV, ch, rP, s', evs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
          exact ⟨a, oP, oV, fSt, wV, ch, .settled prover at_ :: rP, s', evs, h1, h2,
            by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle h3,
            h4, h5, h6, h7, h8, h9⟩)
        hPP hSP hShP

/-! ## Top-level compact layout completeness theorem (`deploy_complete_compact`) -/

private theorem cast_ins_eq_cast_hdr {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (ls : List (Layer V hs r hdr₂.ins)) :
    (congrArg ProtocolHeader.ins h) ▸ ls = h ▸ ls := by
  subst h; rfl

/-- Completeness for `.derived` compact proof layouts (`layout.recover ≠ []`, with optional `carry`)
under `SuiteLawfulFor`, `LayoutLawful`, and `RecoveryLawful`. -/
theorem deploy_complete_compact (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    {suite : ModuleRef} {sessionTag : Option (List Nat)}
    (hCon : declaration.construction = .derived suite sessionTag)
    {layout : Layout} (hLay : declaration.layout = some layout)
    (hRecNonEmpty : layout.recover.isEmpty = false)
    (hNoRetry : declaration.retry = none)
    (hNoSamp : declaration.samples = none)
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (hSuiteLaw : d.SuiteLawfulFor enc M) (hLayLaw : d.LayoutLawful M) (hRecLaw : d.RecoveryLawful M)
    (hNoHalt : ∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) →
      ∀ e, GExec M source (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out)
    (source : Source M)
    (hLP : LawfulPrivate M source (protocolMeaning M d.admitted.program d.callee [] ins))
    (hFed : Fed M source (protocolMeaning M d.admitted.program d.callee [] ins)) :
    ∃ outP gives recordP outV givesV recordV,
      Alone M source prover
        (d.run M prover (hideAll M prover ins) (cast (congrArg (HList M.Val) first.symm) .nil))
        recordP (.returned (outP, gives)) ∧
      Alone M source verifier
        (d.run M verifier (hideAll M verifier ins) (cast (congrArg (HList M.Val) matched) gives))
        recordV (.returned (outV, givesV)) ∧
      ∃ source' out,
        Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins) (.returned out) ∧
        outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1 := by
  have hProjP := projection M d.admitted.program d.callee prover [] ins
  have hProjV := projection M d.admitted.program d.callee verifier [] ins
  have hInsP : (hideAll M prover ins).All (RV.Valid M prover) := hideAll_valid M prover ins hIns
  have hInsV : (hideAll M verifier ins).All (RV.Valid M verifier) := hideAll_valid M verifier ins hIns
  have hKeep := deploy_keeps enc a declaration d hDep
  have hSafeP : (roleMeaning M d.admitted.program d.callee prover [] (hideAll M prover ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee prover [] (hideAll M prover ins) hInsP
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hSafeV : (roleMeaning M d.admitted.program d.callee verifier [] (hideAll M verifier ins)).SafeWith
      M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) := by
    have hs := roleMeaning_safeWith_valid M (hKeep.1 ▸ hAdmit) d.callee verifier [] (hideAll M verifier ins) hInsV
    exact Process.safeWith_mono M (fun _ _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) hs
  have hShapeP := roleMeaning_matchesShape M d.admitted.program d.callee prover [] (hideAll M prover ins)
  have hShapeV := roleMeaning_matchesShape M d.admitted.program d.callee verifier [] (hideAll M verifier ins)
  have hPShape := protocolMeaning_matchesShape M d.admitted.program d.callee [] ins
  have hUniq := protocolMeaning_uniqueOccs M d.admitted.program d.callee [] ins
  have hNoHalt' : ∀ source₁, Lawful M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) →
      (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source₁ at_ τ = source at_ τ) →
      ∀ e, GExec M source₁ (protocolMeaning M d.admitted.program d.callee [] ins) e →
      ∃ out, e = .returned out := fun s₁ hL₁ _ e hEx => hNoHalt s₁ hL₁ e hEx
  cases deploy_ok_elim enc a declaration d hDep with
  | interactive w _ => rw [w.hCon] at hCon; cases hCon
  | authored w _ => rw [w.hCon] at hCon; cases hCon
  | derived w hEq =>
      subst hEq
      have hLayEq : w.layout = layout := Option.some.inj (w.hLayOpt.symm.trans hLay)
      subst hLayEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hSampNone : w.prep.sampLayer = none := by
        have hs := w.prep.hSamp
        unfold buildSamplesLayer at hs; rw [hNoSamp] at hs; exact (Except.ok.inj hs).symm
      cases buildLayoutLayers_ok_elim w.hLay with
      | streaming wL _ _ =>
          have hEmp := wL.hEmpty; rw [hRecNonEmpty] at hEmp; cases hEmp
      | compact wL hComp =>
          -- Extract straight-line + distinct-site guarantees from `checkLayoutSites`
          have hSites := wL.hSites
          unfold checkLayoutSites at hSites
          rw [hRecNonEmpty] at hSites
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hSites
          have hStraightF : w.foundPair.1.shape.isStraightLine = true := hSites.2.1
          have hNodupF : ((w.foundPair.1.shape.events [] id).map (·.site)).Nodup :=
            (listNodupBool_true_iff _).mp hSites.2.2
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          have hStraight : w.toDeployed.entry.shape.isStraightLine = true := by
            show (((a.program.findProtocol declaration.entry).get _).1).shape.isStraightLine = true
            rw [hEntryF]; exact hStraightF
          have hNodup : ((w.toDeployed.entry.shape.events [] id).map (·.site)).Nodup := by
            show ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id).map (·.site) |>.Nodup
            rw [hEntryF]; exact hNodupF
          have hFollows := protocolMeaning_followsEvents M a.program w.toDeployed.callee [] ins hStraight
          -- Unpack `buildCompactLayoutLayers`
          unfold buildCompactLayoutLayers at hComp
          cases hCW : collectCompactWire a w.layout wL.unitTy w.prover w.verifier declaration.key
              (w.foundPair.1.shape.events [] id) 0 (w.foundPair.1.shape.events [] id) with
          | error _ => rw [hCW] at hComp; cases hComp
          | ok cwPair =>
              rw [hCW] at hComp; dsimp only [bind, Except.bind] at hComp
              let vTys := .seq wL.unitTy none :: held w.verifier w.foundPair.1.ins
              let stmtPos := statementPositions w.verifier w.prover w.verifier (.inr rfl) w.foundPair.1.ins
              let stmtItems : List ((τ : V.Ty) × Var (Ctx.positional vTys) τ) :=
                stmtPos.map fun sp =>
                  ⟨sp.ty, posVar vTys (sp.heldIndex + 1) (by simpa [vTys] using sp.atHeld)⟩
              let stmtTys := stmtItems.map Sigma.fst
              let wireSpecs := cwPair.1
              let pClauses := cwPair.2
              let stateTys := tysOfList (stmtTys ++ wireSpecs.map (·.ty))
              split at hComp
              · rename_i htfree
                cases hCV : buildCompactVClauses a w.layout wL.unitTy w.prover w.verifier declaration.key
                    (w.foundPair.1.shape.events [] id) stmtTys wireSpecs htfree 0
                    (w.foundPair.1.shape.events [] id) with
                | error _ => rw [hCV] at hComp; cases hComp
                | ok vClauses =>
                    rw [hCV] at hComp
                    dsimp only [bind, Except.bind, pure, Except.pure] at hComp
                    have hLayEqPair : (_, _) = (w.layP, w.layV) := Except.ok.inj hComp
                    have hLPW : w.layP = {
                        line := .layout, state := .seq wL.unitTy none, takes := [], gives := [.seq wL.unitTy none],
                        clauses := pClauses, again := restoreAgain (.seq wL.unitTy none),
                        start := layoutPStart wL.unitTy, finish := identityFinish (.seq wL.unitTy none)
                      } := (Prod.mk.inj hLayEqPair).1.symm
                    let readers : List ((τ : V.Ty) × SafeFnRef V a.program.headers.fns [.seq wL.unitTy none, .nat] [τ, .nat]) :=
                      wireSpecs.map fun ws => ⟨ws.ty, ws.readRef⟩
                    have hMapReaders : readers.map Sigma.fst = wireSpecs.map (·.ty) := by simp [readers]
                    let startTerm : Term (localDialect V a.program.headers.fns)
                        (Ctx.positional (.seq wL.unitTy none :: held w.verifier w.foundPair.1.ins)) [.tuple stateTys] :=
                      cast (congrArg (fun ts => Term (localDialect V a.program.headers.fns)
                        (Ctx.positional (.seq wL.unitTy none :: held w.verifier w.foundPair.1.ins)) [.tuple (tysOfList ts)])
                        (show stmtItems.map Sigma.fst ++ readers.map Sigma.fst = stmtTys ++ wireSpecs.map (·.ty) by rw [hMapReaders]))
                        (compactLayoutVStart wL.unitTy wL.hfree (finishGuardKey (w.foundPair.1.shape.events [] id)) stmtItems readers)
                    have hLVW : w.layV = {
                        line := .layout, state := .tuple stateTys, takes := [.seq wL.unitTy none], gives := [],
                        clauses := vClauses, again := restoreAgain (.tuple stateTys),
                        start := startTerm, finish := emptyFinish (.tuple stateTys)
                      } := (Prod.mk.inj hLayEqPair).2.symm
                    let conPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
                      { line := .construction, state := w.stateTy, takes := [], gives := [],
                        clauses := w.cPClauses, again := restoreAgain w.stateTy,
                        start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
                        finish := emptyFinish w.stateTy }
                    let conVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
                      { line := .construction, state := w.stateTy, takes := [], gives := [],
                        clauses := w.cVClauses, again := restoreAgain w.stateTy,
                        start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
                        finish := emptyFinish w.stateTy }
                    let layPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
                      { line := .layout, state := .seq wL.unitTy none, takes := [], gives := [.seq wL.unitTy none],
                        clauses := pClauses, again := restoreAgain (.seq wL.unitTy none),
                        start := layoutPStart wL.unitTy, finish := identityFinish (.seq wL.unitTy none) }
                    let layVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
                      { line := .layout, state := .tuple stateTys, takes := [.seq wL.unitTy none], gives := [],
                        clauses := vClauses, again := restoreAgain (.tuple stateTys),
                        start := startTerm, finish := emptyFinish (.tuple stateTys) }
                    have hInsF := ins_cast_valid M hEntryF ins hIns
                    let insF : HList (LVal M) w.foundPair.1.ins :=
                      cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins
                    obtain ⟨st0, hSt0P, hSt0Valid⟩ := constructionStart_done M a
                      w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP
                      (heldValues M w.prover (hideAll M w.prover insF))
                      (heldValues_valid M w.prover _ (hideAll_valid M w.prover insF hInsF))
                    have hSt0V : conVL.start.denote (localSem M a.program.headers.fns
                        (Defs.fnTable M a.program.defs)) []
                        (Env.positional (heldValues M w.verifier (hideAll M w.verifier insF))) =
                        .done (.cons st0 .nil) :=
                      (constructionStart_agree M a w.suite w.prover w.verifier
                        w.foundPair.1.ins declaration.key w.sessBytes w.hSessBytes w.startRef w.absorbRef
                        w.stmtP w.stmtV w.hSP w.hSV insF).symm.trans hSt0P
                    let conP' : Layer V a.program.headers w.prover _ := hEntryF ▸ conPL
                    let conV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ conVL
                    let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layPL
                    let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layVL
                    have hCPSt : conP'.state = w.stateTy := layer_cast_state hEntryF conPL
                    have hCVSt : conV'.state = w.stateTy := layer_cast_state hEntryF conVL
                    have hLPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layPL
                    have hLVSt : layV'.state = .tuple stateTys := layer_cast_state hEntryF layVL
                    have hCPCl : hCPSt ▸ conP'.clauses = w.cPClauses := layer_cast_clauses hEntryF conPL
                    have hCVCl : hCVSt ▸ conV'.clauses = w.cVClauses := layer_cast_clauses hEntryF conVL
                    have hLPCl : hLPSt ▸ layP'.clauses = pClauses := layer_cast_clauses hEntryF layPL
                    have hLVCl : hLVSt ▸ layV'.clauses = vClauses := layer_cast_clauses hEntryF layVL
                    have hCC' : buildConstructionClauses.go enc a w.suite w.stateTy w.suiteUnitTy
                        w.absorbRef w.prover w.verifier declaration.key
                        (w.toDeployed.entry.shape.events [] id) 0
                        (w.toDeployed.entry.shape.eventsWithAbsorb w.prover w.verifier [] id false) =
                        .ok (w.cPClauses, w.cVClauses) := by
                      show buildConstructionClauses.go enc a w.suite w.stateTy w.suiteUnitTy
                        w.absorbRef w.prover w.verifier declaration.key
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id) 0
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.eventsWithAbsorb w.prover w.verifier [] id false) = _
                      rw [hEntryF]; exact w.hCC
                    have hCW' : collectCompactWire a w.layout wL.unitTy w.prover w.verifier declaration.key
                        (w.toDeployed.entry.shape.events [] id) 0 (w.toDeployed.entry.shape.events [] id) =
                        .ok (wireSpecs, pClauses) := by
                      show collectCompactWire a w.layout wL.unitTy w.prover w.verifier declaration.key
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id) 0
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id) = _
                      rw [hEntryF]; exact hCW
                    have hCV' : buildCompactVClauses a w.layout wL.unitTy w.prover w.verifier declaration.key
                        (w.toDeployed.entry.shape.events [] id) stmtTys wireSpecs htfree 0
                        (w.toDeployed.entry.shape.events [] id) = .ok vClauses := by
                      show buildCompactVClauses a w.layout wL.unitTy w.prover w.verifier declaration.key
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id) stmtTys wireSpecs htfree 0
                        ((((a.program.findProtocol declaration.entry).get _).1).shape.events [] id) = _
                      rw [hEntryF]; exact hCV
                    obtain ⟨out, outP, outV, finalSt, wireVals, chunks, recP, source', evs,
                      hTrace, hWArgs, hAlP, hAlVAll, hPostP, hPostV, hLSrc', hAgSrc', hRun'⟩ :=
                      simulate_compact_derived M w.hNe (d := w.toDeployed)
                        stmtTys wireSpecs htfree w.cPClauses w.cVClauses pClauses vClauses
                        conP' conV' layP' layV' hCPSt hCVSt hLPSt hLVSt hCPCl hCVCl hLPCl hLVCl
                        w.hCon w.hStart w.hLayOpt hSuiteLaw hLayLaw hNodup hCC' hCW' hCV'
                        (protocolMeaning M a.program w.toDeployed.callee [] ins)
                        [] (w.toDeployed.entry.shape.events [] id) rfl
                        [] wireSpecs rfl ⟨[], rfl⟩ ⟨pClauses, hCW'⟩
                        (roleMeaning M a.program w.toDeployed.callee w.prover [] (hideAll M w.prover ins))
                        (roleMeaning M a.program w.toDeployed.callee w.verifier [] (hideAll M w.verifier ins))
                        st0 [] source hSt0Valid (fun _ h => nomatch h) hFollows
                        hProjP hProjV hSafeP hSafeV hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
                    -- Construct the exact compact verifier state `stV` parsed by `startTerm` on `chunks.flatten`
                    have hStmtTys : stmtTys = (compactStmtArgs M w.prover w.verifier insF).map Sigma.fst :=
                      (evalVarList_map_fst M _ stmtItems).symm.trans
                        (congrArg (List.map Sigma.fst) (evalVarList_stmtPos_go M w.prover w.verifier wL.unitTy 0 insF chunks.flatten))
                    let stmtVals : HList M.Val stmtTys :=
                      cast (congrArg (HList M.Val) hStmtTys.symm) (HList.ofSigmaList (compactStmtArgs M w.prover w.verifier insF))
                    let stV : stateTys.Val M.toCarriers :=
                      Tys.ofHList M stateTys
                        (cast (congrArg (HList M.Val) (tysOfList_toList (stmtTys ++ wireSpecs.map (·.ty))).symm)
                          (HList.append stmtVals wireVals))
                    have hStartV : startTerm.denote (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                        (Env.positional (.cons (a := .seq wL.unitTy none) chunks.flatten
                          (heldValues M w.verifier (hideAll M w.verifier insF)))) = .done (.cons stV .nil) := by
                      have hReads := compactLayoutVStart_reads M w.hLayOpt hLayLaw w.prover w.verifier
                        wL.unitTy wL.hfree (finishGuardKey (w.foundPair.1.shape.events [] id)) insF hTrace
                      dsimp only [startTerm]
                      have hCastDen : ∀ {ts₁ ts₂ : List V.Ty} (heq : ts₁ = ts₂)
                          (t : Term (localDialect V a.program.headers.fns) (Ctx.positional vTys) [.tuple (tysOfList ts₁)])
                          (env : Env M.Val (Ctx.positional vTys))
                          (val : HList M.Val (tysOfList ts₁).toList),
                          t.denote (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) [] env =
                            .done (.cons (Tys.ofHList M (tysOfList ts₁) val) .nil) →
                          (cast (congrArg (fun ts => Term (localDialect V a.program.headers.fns) (Ctx.positional vTys) [.tuple (tysOfList ts)]) heq) t).denote
                            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) [] env =
                            .done (.cons (Tys.ofHList M (tysOfList ts₂)
                              (cast (congrArg (fun ts => HList M.Val (tysOfList ts).toList) heq) val)) .nil) := by
                        intro _ _ heq _ _ _ hD; subst heq; exact hD
                      have hD := hCastDen (show stmtItems.map Sigma.fst ++ readers.map Sigma.fst = stmtTys ++ wireSpecs.map (·.ty) by rw [hMapReaders])
                        _ _ _ hReads
                      refine hD.trans ?_
                      congr 1; congr 1; congr 1
                      exact cast_cast _ _ _
                    -- Verify slot agreement on `stV`
                    have hStVSlot : ∀ {τ} (mRem : Member (wireSpecs.map (·.ty)) τ),
                        Tys.getAt M stateTys
                          (cast (congrArg (fun l => Member l τ) (by rw [tysOfList_toList]; simp))
                            (memberAppendRight (stmtTys ++ ([] : List (WireSpec V a.program.headers.fns wL.unitTy)).map (·.ty)) mRem)) stV =
                          HList.getAtMember wireVals mRem := by
                      intro τ mRem
                      dsimp only [stV]
                      rw [tys_getAt_ofHList, hlist_getAtMember_cast (tysOfList_toList _).symm, cast_cast]
                      have hMemEq : ∀ {l₁ l₂ : List V.Ty} (heq : l₁ = l₂)
                          (xs : HList M.Val l₁) (ys : HList M.Val (wireSpecs.map (·.ty)))
                          (m : Member (wireSpecs.map (·.ty)) τ),
                          HList.getAtMember (HList.append xs ys)
                            (cast (congrArg (fun l => Member l τ) (by rw [heq])) (memberAppendRight l₂ m)) =
                            HList.getAtMember ys m := by
                        intro _ _ heq _ _ _; subst heq; exact hlist_getAtMember_append_right _ _ _
                      exact hMemEq (List.append_nil stmtTys).symm stmtVals wireVals mRem
                    -- Verify recovery functions agree on `stV` via `hRecLaw`
                    have hStVRec : ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (x : M.Val τ)
                        (recKey : Key) (recRef : SafeFnRef V a.program.headers.fns stateTys.toList [τ]),
                        Event.flow kind w.prover getters at_ τ x ∈ evs →
                        w.verifier ∈ getters →
                        w.layout.recover.lookup at_.site = some recKey →
                        findSafeFnRef a recKey stateTys.toList [τ] = some recRef →
                        recRef.eval M (Defs.fnTable M a.program.defs) (Tys.toHList M stateTys stV) = .done (.cons x .nil) := by
                      intro kind getters at_ τ x recKey recRef hEvIn hVin hLk hFindRec
                      have hStmtInsEq : compactStmtArgs M w.prover w.verifier ins =
                          compactStmtArgs M w.prover w.verifier insF := by
                        have hG : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂) (xs : HList (LVal M) hdr₁.ins),
                            compactStmtArgs M w.prover w.verifier xs =
                              compactStmtArgs M w.prover w.verifier (cast (congrArg (fun h0 => HList (LVal M) h0.ins) h) xs) := by
                          intro _ _ h _; subst h; rfl
                        exact hG hEntryF ins
                      let args := compactStmtArgs M w.prover w.verifier ins ++ compactWireArgs M w.prover w.verifier w.layout evs
                      have hArgsMap : args.map Sigma.fst = stateTys.toList := by
                        dsimp only [args]
                        rw [List.map_append, hStmtInsEq, ← hStmtTys, hWArgs, wireSigmaList_map_fst, tysOfList_toList]
                      have hToHList : Tys.toHList M stateTys stV =
                          cast (congrArg (HList M.Val) hArgsMap) (HList.ofSigmaList args) := by
                        dsimp only [stV]
                        rw [Tys.toHList_ofHList]
                        dsimp only [args]
                        rw [hlist_ofSigmaList_append, cast_cast]
                        have hEqW : HList.ofSigmaList (compactWireArgs M w.prover w.verifier w.layout evs) =
                            cast (congrArg (HList M.Val) (by rw [hWArgs, wireSigmaList_map_fst])) wireVals := by
                          have hGW : ∀ {l₁ l₂ : List ((τ : V.Ty) × M.Val τ)} (hl : l₁ = l₂)
                              (ht : l₂.map Sigma.fst = wireSpecs.map (·.ty))
                              (hEq : HList.ofSigmaList l₂ = cast (congrArg (HList M.Val) ht.symm) wireVals),
                              HList.ofSigmaList l₁ = cast (congrArg (HList M.Val) (Eq.symm (by rw [hl, ht]))) wireVals := by
                            intro _ _ hl _ hEq; subst hl; exact hEq
                          exact hGW hWArgs (wireSigmaList_map_fst M wireSpecs wireVals) (ofSigmaList_wireSigmaList M wireSpecs wireVals)
                        have hEqS : HList.ofSigmaList (compactStmtArgs M w.prover w.verifier ins) =
                            cast (congrArg (HList M.Val) (by rw [hStmtInsEq, ← hStmtTys])) stmtVals := by
                          dsimp only [stmtVals]
                          have hG : ∀ {l₁ l₂ : List ((τ : V.Ty) × M.Val τ)} (hl : l₁ = l₂)
                              (ht : l₂.map Sigma.fst = stmtTys),
                              HList.ofSigmaList l₁ = cast (congrArg (HList M.Val) (by rw [hl, ht]))
                                (cast (congrArg (HList M.Val) ht) (HList.ofSigmaList l₂)) := by
                            intro _ _ hl ht; subst hl; rw [cast_cast]; rfl
                          exact hG hStmtInsEq hStmtTys.symm
                        rw [hEqS, hEqW]
                        have hAppCast : ∀ {a1 a2 b1 b2 : List V.Ty} (ha : a1 = a2) (hb : b1 = b2)
                            (xs : HList M.Val a1) (ys : HList M.Val b1),
                            HList.append (cast (congrArg (HList M.Val) ha) xs) (cast (congrArg (HList M.Val) hb) ys) =
                              cast (congrArg (HList M.Val) (by rw [ha, hb])) (HList.append xs ys) := by
                          intro _ _ _ _ ha hb _ _; subst ha; subst hb; rfl
                        rw [hAppCast (by rw [hStmtInsEq, ← hStmtTys]) (by rw [hWArgs, wireSigmaList_map_fst]), cast_cast]
                      have hFindProg := findSafeFnRef_some hFindRec
                      have hRecFn := hRecLaw w.layout w.prover w.verifier w.hLayOpt hRoles ins hIns
                        source' evs out hLSrc' hRun' kind getters at_ τ x recKey hEvIn hVin hLk
                        recRef.hdr recRef.member hFindProg (recRef.insEq.trans hArgsMap.symm) recRef.outsEq
                      have hEvalEq := recRef.eval_eq_fnTable M (Defs.fnTable M a.program.defs) (Tys.toHList M stateTys stV)
                      rw [hEvalEq, hToHList]
                      rcases recRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _⟩
                      dsimp only at hIn hOut hRecFn ⊢
                      cases hIn; cases hOut
                      simp only [cast_eq] at hRecFn ⊢
                      exact hRecFn
                    obtain ⟨recV, hAlV0⟩ := hAlVAll stV hStVSlot hStVRec
                    -- Wrap prover & verifier `Alone` executions with `Stack.start` and `Stack.finish`
                    have hFinishComp : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
                        (callee : Member a.program.headers.protocols hdr)
                        (ins' : HList (LVal M) hdr.ins)
                        (hInsEq : cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins' = insF)
                        (first' : Stack.Takes (hE ▸ [conPL, layPL]) = [])
                        (matched' : Stack.Gives (hE ▸ [conPL, layPL]) = Stack.Takes (hE ▸ [conVL, layVL]))
                        (outP' : HList (RV M w.prover) hdr.outs)
                        (outV' : HList (RV M w.verifier) hdr.outs)
                        (recP' recV' : List (Happened M)),
                        Alone M source w.prover
                          ((Stack.handler M (Defs.fnTable M a.program.defs)
                            (Defs.rTable M a.program.defs) (hE ▸ [conPL, layPL])).run
                            (retryOf M none)
                            (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                            (cast (by subst hE; rfl) (HList.cons st0 (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil))))
                          recP' (.returned (outP', cast (by subst hE; rfl)
                            (HList.cons finalSt (HList.cons chunks.flatten HList.nil)))) →
                        Alone M source w.verifier
                          ((Stack.handler M (Defs.fnTable M a.program.defs)
                            (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                            (retryOf M none)
                            (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                            (cast (by subst hE; rfl) (HList.cons st0 (HList.cons stV HList.nil))))
                          recV' (.returned (outV', cast (by subst hE; rfl)
                            (HList.cons finalSt (HList.cons stV HList.nil)))) →
                        ∃ gives givesV,
                          Alone M source w.prover
                            (runStack a M callee none w.prover (hE ▸ [conPL, layPL])
                              (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                            recP' (.returned (outP', gives)) ∧
                          Alone M source w.verifier
                            (runStack a M callee none w.verifier (hE ▸ [conVL, layVL])
                              (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                            recV' (.returned (outV', givesV)) := by
                      intro hdr hE callee ins' hInsEq first' matched' outP' outV' recP' recV' hAP hAV
                      subst hE; simp only [cast_eq] at hInsEq; subst hInsEq
                      change Alone M source w.prover
                        ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conPL, layPL]).run
                          (retryOf M none) (roleMeaning M a.program callee w.prover [] (hideAll M w.prover insF))
                          (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)))
                        recP' (.returned (outP', .cons finalSt (.cons chunks.flatten .nil))) at hAP
                      change Alone M source w.verifier
                        ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                          (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier insF))
                          (.cons st0 (.cons stV .nil)))
                        recV' (.returned (outV', .cons finalSt (.cons stV .nil))) at hAV
                      refine ⟨.cons chunks.flatten .nil, .nil, ?_, ?_⟩
                      · unfold runStack
                        change Alone M source w.prover
                          ((Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                            (hideAll M w.prover insF) .nil).bind _) _ _
                        have hStP2 : Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                            (hideAll M w.prover insF) .nil =
                            .done (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)) := by
                          change ((liftLocal id (conPL.start.denote
                            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                            (Env.positional (heldValues M w.prover (hideAll M w.prover insF))))).bind fun f₁ =>
                              ((liftLocal id ((layoutPStart wL.unitTy).denote
                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                (Env.positional (heldValues M w.prover (hideAll M w.prover insF))))).bind fun f₂ =>
                                  (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map
                                fun others => HList.cons f₁.single others) = _
                          rw [hSt0P, liftLocal_done]; dsimp only [Process.bind, HList.single]
                          rw [layoutPStart_denote]; rfl
                        rw [hStP2]; dsimp only [Process.bind]
                        have hAP' := alone_mapHalt M (g := Prod.fst) hAP
                        rw [← List.append_nil recP']
                        refine alone_bind M hAP' ?_
                        have hFinP2 : Stack.finish M (Defs.fnTable M a.program.defs) [conPL, layPL]
                            (.cons finalSt (.cons chunks.flatten .nil)) = .done (.cons chunks.flatten .nil) := by
                          rw [stack_finish_two]; dsimp only [conPL, layPL]
                          rw [emptyFinish_denote]; dsimp only [liftLocal_done, Process.bind]
                          rw [identityFinish_denote]; rfl
                        rw [hFinP2]; exact .done
                      · unfold runStack
                        change Alone M source w.verifier
                          ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                            (hideAll M w.verifier insF) (.cons chunks.flatten .nil)).bind _) _ _
                        have hStV2 : Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                            (hideAll M w.verifier insF) (.cons chunks.flatten .nil) =
                            .done (.cons st0 (.cons stV .nil)) := by
                          change ((liftLocal id (conVL.start.denote
                            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                            (Env.positional (heldValues M w.verifier (hideAll M w.verifier insF))))).bind fun f₁ =>
                              ((liftLocal id (startTerm.denote
                                (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                                (Env.positional (.cons chunks.flatten (heldValues M w.verifier (hideAll M w.verifier insF)))))).bind fun f₂ =>
                                  (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map
                                fun others => HList.cons f₁.single others) = _
                          rw [hSt0V, liftLocal_done]; dsimp only [Process.bind, HList.single]
                          rw [hStartV, liftLocal_done]; rfl
                        rw [hStV2]; dsimp only [Process.bind]
                        have hAV' := alone_mapHalt M (g := Prod.fst) hAV
                        rw [← List.append_nil recV']
                        refine alone_bind M hAV' ?_
                        have hFinV2 : Stack.finish M (Defs.fnTable M a.program.defs) [conVL, layVL]
                            (.cons finalSt (.cons stV .nil)) = .done .nil := by
                          rw [stack_finish_two]; dsimp only [conVL, layVL]
                          rw [emptyFinish_denote]; dsimp only [liftLocal_done, Process.bind]
                          rw [emptyFinish_denote]; rfl
                        rw [hFinV2]; exact .done
                    have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [conPL, layPL] := by
                      dsimp only [DeployDerived.toDeployed, DeployDerived.prover, DeployDerived.layP,
                        DeployDerived.sampLayer] at hLPW hSampNone ⊢
                      rw [dite_eq_left rfl, hSampNone, hLPW]
                      exact cast_ins_eq_cast_hdr hEntryF _
                    have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [conVL, layVL] := by
                      dsimp only [DeployDerived.toDeployed, DeployDerived.prover, DeployDerived.verifier,
                        DeployDerived.layV] at hLVW ⊢
                      rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
                      exact cast_ins_eq_cast_hdr hEntryF _
                    have hFirst' : Stack.Takes (hEntryF ▸ [conPL, layPL]) = [] := by
                      rw [← hStackPEq]; exact first
                    have hMatched' : Stack.Gives (hEntryF ▸ [conPL, layPL]) = Stack.Takes (hEntryF ▸ [conVL, layVL]) := by
                      rw [← hStackPEq, ← hStackVEq]; exact matched
                    obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
                      hFinishComp _ hEntryF _ ins rfl hFirst' hMatched'
                        outP outV recP recV
                        (alone_cast_stack2 M hEntryF conPL layPL rfl rfl (by rw [List.nil_append] at hAlP; exact hAlP))
                        (alone_cast_stack2 M hEntryF conVL layVL rfl rfl hAlV0)
                    refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
                      recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
                      ?_, ?_, source', out, hLSrc', hAgSrc', ⟨evs, hRun'⟩, hPostP, hPostV⟩
                    · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
                        ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
                    · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
                        ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
                        (cast_heq _ _) hRunV
              · cases hComp

end CompactCompleteness

end Zkc.Core

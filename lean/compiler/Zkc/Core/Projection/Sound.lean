module

public import Zkc.Core.Program.Project
public import Zkc.Core.Projection.Proj

@[expose] public section

/-!
The projection theorem: the program of a role is a projection of the protocol.

For an enclosed term, under tables whose role programs are projections of their protocols
and in which a role at or above a callee's roles does nothing, the process of the role's
program on what the role holds is related by `Proj` to the process of the term, and where the
protocol returns, the role returns what it holds of the results.

A role that is none of `parts` does nothing while a region within `parts` runs (`quiet`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## Tables -/

/-- The programs of the roles of the callees are projections of the callees. -/
def TableSound {protocols : List (ProtocolHeader V)} (gTable : GTable M protocols)
    (rTable : RTable M protocols) : Prop :=
  ∀ hdr (callee : Var protocols hdr) (j : Role) (path : List Frame) (ins : HList (LVal M) hdr.ins),
    Proj M j (fun out rvs => rvs = hideAll M j out.1) (gTable hdr callee path ins)
      (rTable hdr callee j path (hideAll M j ins))

/-- A role at or above a callee's roles does nothing while the callee runs. -/
def TableQuiet {protocols : List (ProtocolHeader V)} (gTable : GTable M protocols) : Prop :=
  ∀ hdr (callee : Var protocols hdr) (j : Role) (path : List Frame) (ins : HList (LVal M) hdr.ins),
    hdr.roles ≤ j → Proj M j (fun _ (_ : Unit) => True) (gTable hdr callee path ins) (.done ())

/-! ## What a role holds of the values of a run -/

theorem restrict_apply (r : Role) {Γ : List (LTy V)} (env : Env (LVal M) Γ) (a : LTy V)
    (x : Var Γ a) : restrict M r env a x = hide M r a (env a x) := rfl

/-- What a role holds of the values that the iterations of a loop collected so far. -/
def hideLists (r : Role) {each : List (LTy V)} (s : HList (fun a => List (LVal M a)) each) :
    HList (fun a => List (RV M r a)) each :=
  s.map fun a vs => vs.map (hide M r a)

theorem hideLists_empties (r : Role) : ∀ (each : List (LTy V)),
    hideLists M r (HList.empties each) = HList.empties each
  | [] => rfl
  | _ :: rest => by
      show HList.cons [] (hideLists M r (HList.empties rest)) = _
      rw [hideLists_empties r rest]
      rfl

theorem hideLists_push (r : Role) : ∀ {each : List (LTy V)}
    (s : HList (fun a => List (LVal M a)) each) (vs : HList (LVal M) each),
    (hideLists M r s).push (hideAll M r vs) = hideLists M r (s.push vs)
  | [], .nil, .nil => rfl
  | a :: _, .cons xs rest, .cons v more => by
      show HList.cons (xs.map (hide M r a) ++ [hide M r a v]) ((hideLists M r rest).push (hideAll M r more)) =
        HList.cons ((xs ++ [v]).map (hide M r a)) (hideLists M r (rest.push more))
      rw [hideLists_push r rest more, List.map_append]
      rfl

theorem split_hideAll (r : Role) : ∀ (as : List (LTy V)) {bs : List (LTy V)}
    (vs : HList (LVal M) (as ++ bs)),
    HList.split as (hideAll M r vs) =
      (hideAll M r (HList.split as vs).1, hideAll M r (HList.split as vs).2)
  | [], _, _ => rfl
  | a :: as, _, .cons v rest => by
      have ih := split_hideAll r as rest
      show (HList.cons (hide M r a v) (HList.split as (hideAll M r rest)).1,
          (HList.split as (hideAll M r rest)).2) = _
      rw [ih]
      rfl

theorem hideAll_append (r : Role) : ∀ {as bs : List (LTy V)} (xs : HList (LVal M) as)
    (ys : HList (LVal M) bs), hideAll M r (xs.append ys) = (hideAll M r xs).append (hideAll M r ys)
  | [], _, .nil, _ => rfl
  | a :: _, _, .cons x rest, ys => by
      show HList.cons (hide M r a x) (hideAll M r (rest.append ys)) = _
      rw [hideAll_append r rest ys]
      rfl

/-! ## The alternative of a variant -/

def Pick.map {α : Type} {F G : α → Type} (f : ∀ a, F a → G a) :
    {items : List α} → Pick F items → Pick G items
  | _ :: _, .here v => .here (f _ v)
  | _ :: _, .there p => .there (Pick.map f p)

theorem Pick.map_cast {α : Type} {F G : α → Type} (f : ∀ a, F a → G a) {l1 l2 : List α}
    (e : l1 = l2) (p : Pick F l1) :
    Pick.map f (cast (congrArg (Pick F) e) p) = cast (congrArg (Pick G) e) (Pick.map f p) := by
  subst e
  rfl

theorem Tys.pickAt_map {W W' : LTy V → Type} (ps : Holders) (f : ∀ τ, M.Val τ → W ⟨τ, ps⟩)
    (g : ∀ a, W a → W' a) :
    ∀ (alternatives : Tys V.TypeKey) (v : alternatives.Choice M.toCarriers),
      Pick.map g (Tys.pickAt M ps f alternatives v) =
        Tys.pickAt M ps (fun τ u => g _ (f τ u)) alternatives v
  | .nil, v => nomatch v
  | .cons _ _, .inl _ => rfl
  | .cons _ rest, .inr v => by
      show Pick.there (Pick.map g (Tys.pickAt M ps f rest v)) = _
      rw [Tys.pickAt_map ps f g rest v]
      rfl

theorem locatedPick_map {W W' : LTy V → Type} (ps : Holders) (f : ∀ τ, M.Val τ → W ⟨τ, ps⟩)
    (g : ∀ a, W a → W' a) {τ : V.Ty} {payloads : List (LTy V)}
    (h : ∃ key alternatives, τ = .variant key alternatives ∧
      payloads = alternatives.toList.map fun τ => ⟨τ, ps⟩)
    (v : M.Val τ) :
    Pick.map g (locatedPick M ps f h v) = locatedPick M ps (fun τ u => g _ (f τ u)) h v := by
  unfold locatedPick
  rw [Pick.map_cast, Tys.pickAt_map]
  obtain ⟨_, _, e, p⟩ := h
  rw [Ty.alternatives_of e, p]

theorem rolePick_hide (r : Role) {ps : Holders} {t : LTy V} {payloads : List (LTy V)}
    (ok : ∃ key alternatives, t.ty = .variant key alternatives ∧
      payloads = alternatives.toList.map (fun τ => ⟨τ, ps⟩) ∧ r ∈ t.holders ∧ r ∈ ps)
    (h : ∃ key alternatives, t.ty = .variant key alternatives ∧
      payloads = alternatives.toList.map fun τ => ⟨τ, ps⟩)
    (v : LVal M t) :
    rolePick M r ok (hide M r t v) =
      Pick.map (fun a u => hide M r a u) (locatedPick M ps (W := LVal M) (fun _ u => u) h v) := by
  unfold rolePick
  rw [reveal_hide, locatedPick_map]

/-! ## Projection of one operation -/

theorem project_own {hs : Headers V} (r : Role) (key : Key) {Γ outs : List (LTy V)}
    {kind : GivenKind V} {hearers : List Role} {operands : List (LTy V)} {τ : V.Ty}
    {typed : kind.Typed (operands.map (·.ty)) τ} {held : ∀ a, a ∈ operands → r ∈ a.holders}
    {apart : r ∉ hearers} (args : HList (Var Γ) operands)
    (rest : Term (roleDialect V hs r) ([⟨τ, Holders.ofList (r :: hearers)⟩] ++ Γ) outs) :
    ProtocolOp.project r key (.given kind r hearers operands τ typed held apart) args rest =
      .op key (.own kind hearers operands τ typed held) args rest := by
  simp only [ProtocolOp.project, ↓reduceDIte]

section
variable {hs : Headers V} (fnTable : FnTable M hs.fns) (gTable : GTable M hs.protocols)

theorem hideAll_collected (r : Role) (rTable : RTable M hs.protocols) (size : Option Nat) :
    ∀ {each : List (LTy V)} (s : HList (fun a => List (LVal M a)) each),
      hideAll M r ((protocolSem M fnTable gTable).collected size s) =
        (roleSem M r fnTable rTable).collected size (hideLists M r s)
  | [], .nil => rfl
  | a :: _, .cons vs rest => by
      show HList.cons (hide M r (LTy.collected size a) vs)
          (hideAll M r ((protocolSem M fnTable gTable).collected size rest)) =
        HList.cons (collectRV M r size a (vs.map (hide M r a)))
          ((roleSem M r fnTable rTable).collected size (hideLists M r rest))
      rw [collectRV_hide, hideAll_collected r rTable size rest]

/-! ## A role that takes no part -/

theorem op_quiet {r : Role} {parts : List Role} (hr : r ∉ parts) (silent : TableQuiet M gTable)
    (key : Key) {ins res : List (LTy V)} (o : ProtocolOp V hs ins res) (path : List Frame)
    (vs : HList (LVal M) ins) (within : ProtocolOp.Within parts o) :
    Proj M r (fun _ (_ : Unit) => True) (protocolOp M fnTable gTable key o path vs) (.done ()) := by
  cases o with
  | compute R lo operands types held =>
      simp only [protocolOp]
      exact Proj.liftOut M (fun m => hr (within r m)) () (fun _ => trivial) _
  | flow kind giver getters holds apart =>
      cases vs with
      | cons v more =>
          cases more with
          | nil =>
              simp only [protocolOp]
              exact Proj.passed (fun e => hr (e ▸ within.1)) (fun m => hr (within.2 r m))
                (.done trivial)
  | given kind owner hearers operands τ typed held apart =>
      simp only [protocolOp]
      exact Proj.unheard (fun e => hr (e ▸ within.1)) (fun m => hr (within.2 r m))
        fun _ => .done trivial
  | narrow R among =>
      cases vs with
      | cons v more =>
          cases more with
          | nil => exact .done trivial
  | @apply hdr callee roles distinct covers operands fits =>
      simp only [protocolOp]
      have out : hdr.roles ≤ (RoleMap.ofList roles distinct).back r := by
        rw [← covers]
        exact RoleMap.ofList_back roles distinct fun m => hr (within r m)
      have inner := Proj.mapRoles M (RoleMap.ofList roles distinct).injective
        (silent _ callee ((RoleMap.ofList roles distinct).back r) (path ++ [.application key])
          (unmapAll M (RoleMap.ofList roles distinct).to (fitAll M fits vs)) out)
      rw [RoleMap.right] at inner
      exact Proj.map_left M inner fun _ _ _ => trivial

mutual
  /-- A role that is none of `parts` does nothing while a region within `parts` runs. -/
  theorem quiet {r : Role} {parts : List Role} (hr : r ∉ parts) (silent : TableQuiet M gTable) :
      ∀ {Γ outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame)
        (env : Env (LVal M) Γ), Within parts t →
        Proj M r (fun _ (_ : Unit) => True) (t.denote (protocolSem M fnTable gTable) path env)
          (.done ())
    | _, _, .ret _, _, _, _ => .done trivial
    | _, _, .op key o args rest, path, env, h => by
        simp only [Term.denote]
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ())
          (op_quiet M fnTable gTable hr silent key o path (env.all args) h.1)
          fun results _ _ => quiet hr silent rest path (Env.extend results env) h.2
    | _, _, .guard key ps c ok why rest, path, env, h => by
        simp only [Term.denote]
        cases asBool M ok.1 (env _ c)
        · exact .stopsElsewhere fun m => hr (h.1 _ m)
        · exact quiet hr silent rest path env h.2
    | _, _, .choose _ ps c ok _ onTrue onFalse rest, path, env, h => by
        simp only [Term.denote]
        have arm : Proj M r (fun _ (_ : Unit) => True)
            (bif asBool M ok.1 (env _ c) then onTrue.denote (protocolSem M fnTable gTable) path env
              else onFalse.denote (protocolSem M fnTable gTable) path env) (.done ()) := by
          cases asBool M ok.1 (env _ c)
          · exact quiet hr silent onFalse path env h.2.2.1
          · exact quiet hr silent onTrue path env h.2.1
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ()) arm fun mids _ _ =>
          quiet hr silent rest path _ h.2.2.2
    | _, _, .cases _ ps x ok _ arms rest, path, env, h => by
        simp only [Term.denote]
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ())
          (quietArms hr silent arms path env _ h.2.1) fun mids _ _ => quiet hr silent rest path _ h.2.2
    | _, _, .loop key ps times _ init body rest, path, env, h => by
        simp only [Term.denote]
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ())
          (Proj.iterate_quiet M (fun i state =>
            Proj.bind M (q := .done ()) (g := fun _ => .done ())
              (quiet hr silent body (path ++ [.iteration key i]) _ h.2.1) fun _ _ _ => .done trivial)
            _ 0 _)
          fun _ _ _ => quiet hr silent rest path _ h.2.2
    | _, _, .block key number body rest, path, env, h => by
        simp only [Term.denote]
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ())
          (quiet hr silent body (path ++ [.iteration key number]) env h.1)
          fun mids _ _ => quiet hr silent rest path _ h.2
    | _, _, .attempt key w owns body rest, path, env, h => by
        rw [attempt_denote]
        exact Proj.bind M (q := .done ()) (g := fun _ => .done ())
          (quiet hr silent body path _ h.2.1) fun mids _ _ => quiet hr silent rest path _ h.2.2
  theorem quietArms {r : Role} {parts : List Role} (hr : r ∉ parts) (silent : TableQuiet M gTable) :
      ∀ {Γ mid payloads : List (LTy V)} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
        WithinArms parts arms →
        Proj M r (fun _ (_ : Unit) => True) (arms.denote (protocolSem M fnTable gTable) path env p)
          (.done ())
    | _, _, _, .nil, _, _, p, _ => nomatch p
    | _, _, _, .cons arm _, path, _, .here _, h => quiet hr silent arm path _ h.1
    | _, _, _, .cons _ rest, path, env, .there p, h => quietArms hr silent rest path env p h.2
end

/-! ## The theorem -/

variable (r : Role) (rTable : RTable M hs.protocols)

/-- The role's part of one operation, then the rest. -/
theorem op_sound (tsound : TableSound M gTable rTable) (key : Key) {Γ outs ins res : List (LTy V)}
    (o : ProtocolOp V hs ins res) (args : HList (Var Γ) ins)
    (rest : Term (protocolDialect V hs) (res ++ Γ) outs) (path : List Frame)
    (env : Env (LVal M) Γ)
    (ih : ∀ results : HList (LVal M) res, Proj M r (fun vs rvs => rvs = hideAll M r vs)
      (rest.denote (protocolSem M fnTable gTable) path (Env.extend results env))
      ((project r rest).denote (roleSem M r fnTable rTable) path
        (Env.extend (hideAll M r results) (restrict M r env)))) :
    Proj M r (fun vs rvs => rvs = hideAll M r vs)
      ((Term.op key o args rest).denote (protocolSem M fnTable gTable) path env)
      ((ProtocolOp.project r key o args (project r rest)).denote (roleSem M r fnTable rTable) path
        (restrict M r env)) := by
  cases o with
  | compute R lo operands types held =>
      by_cases hR : r ∈ R
      · simp only [ProtocolOp.project, hR, ↓reduceDIte, Term.denote]
        refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
          fun results _ e => by subst e; exact ih results
        simp only [protocolOp, roleOp, restrict_all, revealAll_hideAll]
        exact Proj.liftIn M (post := fun vs rvs => rvs = hideAll M r vs) hR (fun _ => rfl) _
      · simp only [ProtocolOp.project, hR, ↓reduceDIte, Term.denote]
        refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
          fun results _ e => by subst e; exact ih results
        simp only [protocolOp, roleOp]
        exact Proj.liftOut M (post := fun vs rvs => rvs = hideAll M r vs) hR _
          (fun _ => (hideAll_nothings M _ _).symm) _
  | flow kind giver getters holds apart =>
      cases args with
      | cons x more =>
          cases more with
          | nil =>
              by_cases hg : r = giver
              · subst giver
                simp only [ProtocolOp.project, ↓reduceDIte, Term.denote]
                refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
                  fun results _ e => by subst e; exact ih results
                simp only [Env.all, protocolOp, roleOp, restrict_apply]
                rw [reveal_hide]
                exact Proj.gave (post := fun vs rvs => rvs = hideAll M r vs) apart (.done rfl)
              · by_cases hm : r ∈ getters
                · simp only [ProtocolOp.project, hg, ↓reduceDIte, hm, ↓reduceDIte, Term.denote]
                  refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
                    fun results _ e => by subst e; exact ih results
                  simp only [Env.all, protocolOp, roleOp]
                  exact Proj.got (post := fun vs rvs => rvs = hideAll M r vs) (Ne.symm hg) hm
                    (.done rfl)
                · simp only [ProtocolOp.project, hg, ↓reduceDIte, hm, ↓reduceDIte, Term.denote]
                  refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
                    fun results _ e => by subst e; exact ih results
                  simp only [Env.all, protocolOp, roleOp, restrict_apply, carry_hide]
                  exact Proj.passed (post := fun vs rvs => rvs = hideAll M r vs) (Ne.symm hg) hm
                    (.done rfl)
  | given kind owner hearers operands τ typed held apart =>
      by_cases ho : r = owner
      · subst owner
        rw [project_own]
        simp only [Term.denote]
        refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
          fun results _ e => by subst e; exact ih results
        simp only [protocolOp, roleOp]
        rw [restrict_all, revealAll_hideAll]
        exact Proj.owned (post := fun vs rvs => rvs = hideAll M r vs) fun _ => .done rfl
      · by_cases hh : r ∈ hearers
        · simp only [ProtocolOp.project, ho, ↓reduceDIte, hh, ↓reduceDIte, Term.denote]
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
            fun results _ e => by subst e; exact ih results
          simp only [protocolOp, roleOp]
          exact Proj.heard (post := fun vs rvs => rvs = hideAll M r vs) (Ne.symm ho) hh
            fun _ => .done rfl
        · simp only [ProtocolOp.project, ho, ↓reduceDIte, hh, ↓reduceDIte, Term.denote]
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
            fun results _ e => by subst e; exact ih results
          simp only [protocolOp, roleOp]
          exact Proj.unheard (post := fun vs rvs => rvs = hideAll M r vs) (Ne.symm ho) hh
            fun _ => .done (hideAll_nothings M _ _).symm
  | narrow R among =>
      cases args with
      | cons x more =>
          cases more with
          | nil =>
              by_cases hR : r ∈ R
              · simp only [ProtocolOp.project, hR, ↓reduceDIte, Term.denote]
                refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
                  fun results _ e => by subst e; exact ih results
                simp only [Env.all, protocolOp, roleOp, restrict_apply, carry_hide]
                exact .done rfl
              · simp only [ProtocolOp.project, hR, ↓reduceDIte, Term.denote]
                refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
                  fun results _ e => by subst e; exact ih results
                simp only [Env.all, protocolOp, roleOp]
                exact .done (hideAll_nothings M _ _).symm
  | apply callee roles distinct covers operands fits =>
      simp only [ProtocolOp.project, Term.denote]
      refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_
        fun results _ e => by subst e; exact ih results
      simp only [protocolOp, roleOp, restrict_all, fitAllRV_hide, enterAll_hide]
      have inner := Proj.mapRoles M (RoleMap.ofList roles distinct).injective
        (tsound _ callee ((RoleMap.ofList roles distinct).back r) (path ++ [.application key])
          (unmapAll M (RoleMap.ofList roles distinct).to (fitAll M fits (env.all args))))
      rw [RoleMap.right] at inner
      exact Proj.map M inner fun out _ e => by subst e; exact leaveAll_hide M _ r out.1

/-- A loop that the role performs: the role repeats the projection of the body as often as
the protocol repeats the body. -/
theorem loop_sound (key : Key) (ps : Holders) (hr : r ∈ ps) {Γ outs carried each : List (LTy V)}
    (times : Times (protocolDialect V hs) ps Γ)
    (gives : ∀ a, a ∈ carried ++ each → (protocolDialect V hs).Gives ps a)
    (init : HList (Var Γ) carried)
    (body : Term (protocolDialect V hs) (LTy.index ps :: (carried ++ Γ)) (carried ++ each))
    (rest : Term (protocolDialect V hs) ((carried ++ each.map (LTy.collected times.size)) ++ Γ) outs)
    (path : List Frame) (env : Env (LVal M) Γ)
    (hbody : ∀ (path : List Frame) (env : Env (LVal M) (LTy.index ps :: (carried ++ Γ))),
      Proj M r (fun vs rvs => rvs = hideAll M r vs) (body.denote (protocolSem M fnTable gTable) path env)
        ((project r body).denote (roleSem M r fnTable rTable) path (restrict M r env)))
    (hrest : ∀ env : Env (LVal M) ((carried ++ each.map (LTy.collected times.size)) ++ Γ),
      Proj M r (fun vs rvs => rvs = hideAll M r vs) (rest.denote (protocolSem M fnTable gTable) path env)
        ((project r rest).denote (roleSem M r fnTable rTable) path (restrict M r env))) :
    Proj M r (fun vs rvs => rvs = hideAll M r vs)
      ((Term.loop key ps times gives init body rest).denote (protocolSem M fnTable gTable) path env)
      ((projectLoop r key ps hr times init (project r body) (project r rest)).denote
        (roleSem M r fnTable rTable) path (restrict M r env)) := by
  cases times
  all_goals
    simp only [projectLoop, Term.denote, Semantics.times, restrict_apply, reveal_hide, restrict_all]
    refine Proj.bind M
      (post := fun (s : (protocolSem M fnTable gTable).LoopState carried each)
        (rs : (roleSem M r fnTable rTable).LoopState carried each) =>
        rs = (hideAll M r s.1, hideLists M r s.2)) ?_ fun state _ e => ?_
    · refine Proj.iterate M ?_ _ 0 _ _ ?_
      · intro i a b e
        subst e
        refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_ fun out _ e => ?_
        · have ih := hbody (path ++ [.iteration key i])
            (Env.cons (V := LVal M) (a := LTy.index ps) i (Env.extend a.1 env))
          rw [restrict_cons, restrict_extend] at ih
          exact ih
        · subst e
          refine .done ?_
          simp only [split_hideAll, hideLists_push]
      · rw [hideLists_empties]
    · subst e
      have ih := hrest (Env.extend (state.1.append
        ((protocolSem M fnTable gTable).collected _ state.2)) env)
      rw [restrict_extend, hideAll_append, hideAll_collected M fnTable gTable r rTable] at ih
      exact ih

mutual
  /-- The program of a role is a projection of the protocol: where the protocol returns, the
  role returns what it holds of the results. -/
  theorem project_sound (tsound : TableSound M gTable rTable) (tquiet : TableQuiet M gTable) :
      ∀ {Γ outs : List (LTy V)} (t : Term (protocolDialect V hs) Γ outs) (path : List Frame)
        (env : Env (LVal M) Γ), Enclosed t →
        Proj M r (fun vs rvs => rvs = hideAll M r vs) (t.denote (protocolSem M fnTable gTable) path env)
          ((project r t).denote (roleSem M r fnTable rTable) path (restrict M r env))
    | _, _, .ret xs, _, env, _ => .done (restrict_all M r env xs)
    | _, _, .op key o args rest, path, env, h =>
        op_sound M fnTable gTable r rTable tsound key o args rest path env fun results => by
          have ih := project_sound tsound tquiet rest path (Env.extend results env) h
          rwa [restrict_extend] at ih
    | _, _, .guard key ps c ok why rest, path, env, h => by
        have ih := project_sound tsound tquiet rest path env h
        by_cases hr : r ∈ ps
        · simp only [project, hr, ↓reduceDIte, Term.denote, restrict_apply, reveal_hide]
          cases asBool M ok.1 (env _ c)
          · exact .stopsHere hr
          · exact ih
        · simp only [project, hr, ↓reduceDIte, Term.denote]
          cases asBool M ok.1 (env _ c)
          · exact .stopsElsewhere hr
          · exact ih
    | _, _, .choose key ps c ok gives onTrue onFalse rest, path, env, h => by
        by_cases hr : r ∈ ps
        · simp only [project, hr, ↓reduceDIte, Term.denote, restrict_apply, reveal_hide]
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) ?_ fun mids _ e => ?_
          · cases asBool M ok.1 (env _ c)
            · exact project_sound tsound tquiet onFalse path env h.2.2.2.1
            · exact project_sound tsound tquiet onTrue path env h.2.2.1
          · subst e
            have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2.2.2.2
            rwa [restrict_extend] at ih
        · simp only [project, hr, ↓reduceDIte, Term.denote, roleOp, Process.bind]
          have arm : Proj M r (fun _ (_ : Unit) => True)
              (bif asBool M ok.1 (env _ c) then onTrue.denote (protocolSem M fnTable gTable) path env
                else onFalse.denote (protocolSem M fnTable gTable) path env) (.done ()) := by
            cases asBool M ok.1 (env _ c)
            · exact quiet M fnTable gTable hr tquiet onFalse path env h.2.1
            · exact quiet M fnTable gTable hr tquiet onTrue path env h.1
          refine Proj.bind M (q := .done ()) (g := fun _ => _) arm fun mids _ _ => ?_
          have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2.2.2.2
          rw [restrict_extend, hideAll_nothings M (fun a ha hr' => hr (gives a ha r hr'))] at ih
          exact ih
    | _, _, .cases key ps x ok gives arms rest, path, env, h => by
        by_cases hr : r ∈ ps
        · simp only [project, hr, ↓reduceDIte, Term.denote, restrict_apply]
          rw [rolePick_hide M r _
            (by obtain ⟨key, alternatives, e, p, _⟩ := ok; exact ⟨key, alternatives, e, p⟩)]
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs)
            (project_soundArms tsound tquiet arms path env _ h.2.1) fun mids _ e => ?_
          subst e
          have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2.2
          rwa [restrict_extend] at ih
        · simp only [project, hr, ↓reduceDIte, Term.denote, roleOp, Process.bind]
          refine Proj.bind M (q := .done ()) (g := fun _ => _)
            (quietArms M fnTable gTable hr tquiet arms path env _ h.1) fun mids _ _ => ?_
          have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2.2
          rw [restrict_extend, hideAll_nothings M (fun a ha hr' => hr (gives a ha r hr'))] at ih
          exact ih
    | _, _, .loop (carried := carried) (each := each) key ps times gives init body rest,
        path, env, h => by
        by_cases hr : r ∈ ps
        · simp only [project, hr, ↓reduceDIte]
          exact loop_sound M fnTable gTable r rTable key ps hr times gives init body rest path env
            (fun path env => project_sound tsound tquiet body path env h.2.1)
            (fun env => project_sound tsound tquiet rest path env h.2.2)
        · simp only [project, hr, ↓reduceDIte, Term.denote, roleOp, Process.bind]
          have out : ∀ a, a ∈ carried ++ each.map ((protocolDialect V hs).collected times.size) →
              r ∉ a.holders := fun a ha hr' => by
            rcases List.mem_append.mp ha with ha | ha
            · exact hr (gives a (List.mem_append.mpr (.inl ha)) r hr')
            · obtain ⟨b, hb, e⟩ := List.mem_map.mp ha
              subst e
              exact hr (gives b (List.mem_append.mpr (.inr hb)) r hr')
          refine Proj.bind M (q := .done ()) (g := fun _ => _)
            (Proj.iterate_quiet M (fun i state =>
              Proj.bind M (q := .done ()) (g := fun _ => .done ())
                (quiet M fnTable gTable hr tquiet body (path ++ [.iteration key i]) _ h.1)
                fun _ _ _ => .done trivial) _ 0 _) fun state _ _ => ?_
          have ih := project_sound tsound tquiet rest path
            (Env.extend (state.1.append
              ((protocolSem M fnTable gTable).collected times.size state.2)) env) h.2.2
          rw [restrict_extend, hideAll_nothings M out] at ih
          exact ih
    | _, _, .block key number body rest, path, env, h => by
        simp only [project, Term.denote]
        refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs)
          (project_sound tsound tquiet body (path ++ [.iteration key number]) env h.1)
          fun mids _ e => ?_
        subst e
        have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2
        rwa [restrict_extend] at ih
    | _, _, .attempt key w owns body rest, path, env, h => by
        simp only [project]
        rw [attempt_denote]
        simp only [Term.denote]
        have hbody := project_sound tsound tquiet body path
          (Env.cons (V := LVal M) (a := LTy.index w) (0 : Nat) env) h.1
        rw [restrict_cons] at hbody
        have hrest : ∀ mids, Proj M r (fun vs rvs => rvs = hideAll M r vs)
            (rest.denote (protocolSem M fnTable gTable) path (Env.extend mids env))
            ((project r rest).denote (roleSem M r fnTable rTable) path
              (Env.extend (hideAll M r mids) (restrict M r env))) := fun mids => by
          have ih := project_sound tsound tquiet rest path (Env.extend mids env) h.2
          rwa [restrict_extend] at ih
        by_cases hr : r ∈ w
        · simp only [hr, ↓reduceIte, Process.bind]
          refine Proj.begins ?_
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) hbody fun mids _ e => ?_
          subst e
          exact Proj.settles (hrest mids)
        · simp only [hr, ↓reduceIte, Process.bind]
          refine Proj.bind M (post := fun vs rvs => rvs = hideAll M r vs) hbody fun mids _ e => ?_
          subst e
          exact hrest mids
  theorem project_soundArms (tsound : TableSound M gTable rTable) (tquiet : TableQuiet M gTable) :
      ∀ {Γ mid payloads : List (LTy V)} (arms : Arms (protocolDialect V hs) Γ mid payloads)
        (path : List Frame) (env : Env (LVal M) Γ) (p : Pick (LVal M) payloads),
        EnclosedArms arms →
        Proj M r (fun vs rvs => rvs = hideAll M r vs)
          (arms.denote (protocolSem M fnTable gTable) path env p)
          ((projectArms r arms).denote (roleSem M r fnTable rTable) path (restrict M r env)
            (Pick.map (fun a u => hide M r a u) p))
    | _, _, _, .nil, _, _, p, _ => nomatch p
    | _, _, _, .cons arm _, path, env, .here v, h => by
        have ih := project_sound tsound tquiet arm path (Env.cons v env) h.1
        rw [restrict_cons] at ih
        exact ih
    | _, _, _, .cons _ rest, path, env, .there p, h =>
        project_soundArms tsound tquiet rest path env p h.2
end

end

end

end Zkc.Core

#print axioms Zkc.Core.quiet
#print axioms Zkc.Core.project_sound

module

public import Zkc.Core.Scheme.Safety

@[expose] public section

/-!
Streaming completeness (`deploy_complete`) and shared clause-stepping / lawfulness lemmas
for deployed schemes (supporting Chiesa-Orru trailing-message absorption elision in lockstep
on both prover and verifier).
-/

namespace Zkc.Core

open LayerBuild

section Completeness

variable {V : Vocabulary} (M : Model V)

/-! ### `Alone`, `patchSource`, and `Stack.handler` stepping lemmas -/

private theorem alone_bind {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {f : A → Process (RSig M) H B}
    {a : A} {rec₁ rec₂ : List (Happened M)} {e : Ending B H}
    (hp : Alone M source r p rec₁ (.returned a))
    (hf : Alone M source r (f a) rec₂ e) :
    Alone M source r (p.bind f) (rec₁ ++ rec₂) e := by
  generalize hEnd : Ending.returned a = end₁ at hp
  induction hp with
  | done => cases hEnd; exact hf
  | halt => cases hEnd
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

private theorem alone_map {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {f : A → B} {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.map f) rec (.returned (f a)) := by
  rw [Process.map_eq_bind, ← List.append_nil rec]
  exact alone_bind M hp .done

private theorem alone_mapHalt {source : Source M} {r : Role} {H H' A : Type}
    {p : Process (RSig M) H A} {g : H → H'} {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.mapHalt g) rec (.returned a) := by
  generalize hEnd : Ending.returned a = end₁ at hp
  induction hp with
  | done => cases hEnd; exact .done
  | halt => cases hEnd
  | waits => cases hEnd
  | give _ ih => exact .give (ih hEnd)
  | own hsrc _ ih => exact .own hsrc (ih hEnd)
  | hear hsrc _ ih => exact .hear hsrc (ih hEnd)
  | begin _ ih => exact .begin (ih hEnd)
  | settle _ ih => exact .settle (ih hEnd)

/-- Patch a `Source` at a single `(occurrence, type)` pair. -/
private def patchSource (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) : Source M :=
  fun at_ τ =>
    if h : at_ = target ∧ τ = τ₀ then some (cast (congrArg M.Val h.2.symm) v₀)
    else source at_ τ

private theorem patchSource_self (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) :
    patchSource M source target τ₀ v₀ target τ₀ = some v₀ := by
  unfold patchSource
  rw [dite_eq_left ⟨rfl, rfl⟩]
  rfl

private theorem patchSource_ne (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) {at_ : Occurrence} (hne : at_ ≠ target) (τ : V.Ty) :
    patchSource M source target τ₀ v₀ at_ τ = source at_ τ := by
  unfold patchSource
  rw [dite_eq_right (fun h => hne h.1)]

private theorem lawful_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
    (hAgree : ∀ at_ τ, P at_ → s₁ at_ τ = s₂ at_ τ) :
    ∀ {p : Protocol M A}, Protocol.OccsIn M P p → Lawful M s₁ p → Lawful M s₂ p
  | .done _, _, _ => trivial
  | .halt _, _, _ => trivial
  | .call (.flow ..) k, ⟨_, hk⟩, hL => lawful_of_agree hAgree (p := k ()) (hk ()) hL
  | .call (.given _ _ _ at_ _ _ τ) k, ⟨ho, hk⟩, hL => by
      intro v hv
      rw [← hAgree at_ τ ho] at hv
      have ⟨hA, hL'⟩ := hL v hv
      exact ⟨hA, lawful_of_agree hAgree (p := k v) (hk v) hL'⟩

private theorem grun_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
    (hAgree : ∀ at_ τ, P at_ → s₁ at_ τ = s₂ at_ τ)
    {p : Protocol M A} {evs : List (Event M)} {e : GEnd A}
    (hOcc : Protocol.OccsIn M P p) (hRun : GRun M s₁ p evs e) : GRun M s₂ p evs e := by
  induction hRun with
  | done => exact .done
  | halt => exact .halt
  | flow _ ih => exact .flow (ih (hOcc.2 ()))
  | given hsrc _ ih =>
      exact .given (by
        dsimp only [Protocol.OccsIn, GOp.occurrence] at hOcc
        rw [← hAgree _ _ hOcc.1]; exact hsrc) (ih (hOcc.2 _))

theorem stack1_clause_done {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (lay : Layer V hs r ins) (op : ROp M) (s s' : M.Val lay.state) (reply : (RSig M).Reply op)
    (hLay : Clause.answer M fnTable rTable lay.clauses op s = .done (reply, s')) :
    (Stack.handler M fnTable rTable [lay]).clause op (.cons s .nil) =
      .done (reply, .cons s' .nil) := by
  change ((((Layer.handler M fnTable rTable lay).over
      (Stack.handler M fnTable rTable [])).clause op (s, .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .done (reply, .cons s' .nil)
  dsimp only [Layer.handler, Handler.over]
  rw [hLay]; rfl

theorem stack1_clause_pass {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (lay : Layer V hs r ins) (op : ROp M) (s : M.Val lay.state)
    (hLay : Clause.answer M fnTable rTable lay.clauses op s = .call op fun reply => .done (reply, s)) :
    (Stack.handler M fnTable rTable [lay]).clause op (.cons s .nil) =
      .call op fun reply => .done (reply, .cons s .nil) := by
  change ((((Layer.handler M fnTable rTable lay).over
      (Stack.handler M fnTable rTable [])).clause op (s, .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .call op fun reply => .done (reply, .cons s .nil)
  dsimp only [Layer.handler, Handler.over]
  rw [hLay]; rfl

theorem stack2_clause_step {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (con lay : Layer V hs r ins) (op op₂ : ROp M)
    (st st' : M.Val con.state) (laySt laySt' : M.Val lay.state)
    (r₂ : (RSig M).Reply op₂) (reply : (RSig M).Reply op)
    (k₂ : (RSig M).Reply op₂ → Process (RSig M) (Stop × M.Val con.state) ((RSig M).Reply op × M.Val con.state))
    (hCon : Clause.answer M fnTable rTable con.clauses op st = .call op₂ k₂)
    (hLay : Clause.answer M fnTable rTable lay.clauses op₂ laySt = .done (r₂, laySt'))
    (hK : k₂ r₂ = .done (reply, st')) :
    (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons laySt .nil)) =
      .done (reply, .cons st' (.cons laySt' .nil)) := by
  change ((((Layer.handler M fnTable rTable con).over
      (Stack.handler M fnTable rTable [lay])).clause op (st, .cons laySt .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) = .done (reply, .cons st' (.cons laySt' .nil))
  dsimp only [Layer.handler, Handler.over]
  rw [hCon]
  dsimp only [Handler.answer]
  rw [stack1_clause_done M fnTable rTable lay op₂ laySt laySt' r₂ hLay]
  dsimp only [Process.mapHalt, Process.bind]
  rw [hK]; rfl

theorem stack2_clause_pass {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {ins : List (LTy V)}
    (con lay : Layer V hs r ins) (op : ROp M) (st : M.Val con.state) (laySt : M.Val lay.state)
    (hCon : Clause.answer M fnTable rTable con.clauses op st = .call op fun reply => .done (reply, st))
    (hLay : Clause.answer M fnTable rTable lay.clauses op laySt = .call op fun reply => .done (reply, laySt)) :
    (Stack.handler M fnTable rTable [con, lay]).clause op (.cons st (.cons laySt .nil)) =
      .call op fun reply => .done (reply, .cons st (.cons laySt .nil)) := by
  change ((((Layer.handler M fnTable rTable con).over
      (Stack.handler M fnTable rTable [lay])).clause op (st, .cons laySt .nil)).mapHalt
        (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))).map
        (fun out => (out.1, HList.cons out.2.1 out.2.2)) =
      .call op fun reply => .done (reply, .cons st (.cons laySt .nil))
  dsimp only [Layer.handler, Handler.over]
  rw [hCon]
  dsimp only [Handler.answer]
  rw [stack1_clause_pass M fnTable rTable lay op laySt hLay]
  rfl

/-! ### Exact `Clause.answer` behavior lemmas for streaming `deploy` -/

theorem clause_answer_unmatched_all {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty}
    (op : ROp M) (s : M.Val state) :
    ∀ (cs : List (Clause V hs r state)),
      (∀ c ∈ cs, ¬ ClauseMatches M c op) →
      Clause.answer M fnTable rTable cs op s = .call op fun reply => .done (reply, s)
  | [], _ => rfl
  | c :: cs, hNo => by
      unfold Clause.answer
      have hne := hNo c List.mem_cons_self
      unfold ClauseMatches at hne
      rw [dite_eq_right hne]
      exact clause_answer_unmatched_all fnTable rTable op s cs (fun c' hc' => hNo c' (List.mem_cons_of_mem _ hc'))

/-- Exact `Clause.answer` result of `proverAbsorbClause` on a matching `.give`. -/
private theorem proverAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (st : M.Val stateTy)
    (enc : List (M.Val unitTy)) (st' : M.Val stateTy)
    (hEnc : encRef.eval M fnTable (.cons msg .nil) = .done (.cons enc .nil))
    (hAbs : absRef.eval M fnTable (.cons st (.cons label (.cons enc .nil))) = .done (.cons st' .nil))
    (cs : List (Clause V hs prover stateTy)) :
    Clause.answer M fnTable rTable
        (proverAbsorbClause prover site kind getters label hlabel encRef absRef :: cs)
        (.give kind getters at_ τ msg) st =
      .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ => .done ((), st') := by
  unfold Clause.answer
  have hM : (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.site =
      (ROp.occurrence M (.give kind getters at_ τ msg)).site ∧
      some (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.part =
      ROp.part M (.give kind getters at_ τ msg) ∧
      (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.takes =
      ROp.takes M (.give kind getters at_ τ msg) ∧
      (proverAbsorbClause prover site kind getters label hlabel encRef absRef).site.gives =
      ROp.gives M (.give kind getters at_ τ msg) := ⟨hSite, rfl, rfl, rfl⟩
  rw [dite_eq_left hM]
  change (((proverAbsorbClause prover site kind getters label hlabel encRef absRef).code.denote
    (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons msg (.cons st .nil))))).mapHalt _).map _ = _
  have hStep : ((liftLocal (S := RSig M) id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
      (liftLocal (S := RSig M) id (absRef.eval M fnTable (.cons st (.cons label (.cons enc.single .nil))))).bind fun nextSt =>
        .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
          .done (aloneIn M prover nextSt)) =
      .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
        .done (aloneIn M prover (.cons st' .nil)) := by
    rw [hEnc, liftLocal_done]
    change ((liftLocal (S := RSig M) id
      (absRef.eval M fnTable (.cons st (.cons label (.cons enc .nil))))).bind fun nextSt =>
        .call (.give kind getters ⟨at_.path, site.key⟩ τ msg) fun _ =>
          .done (aloneIn M prover nextSt)) = _
    rw [hAbs, liftLocal_done]
    rfl
  rw [proverAbsorbClause_denote, hStep]
  dsimp only [Process.map, Process.mapHalt, proverAbsorbClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

/-- Exact `Clause.answer` result of `verifierAbsorbClause` on a matching `.get`. -/
private theorem verifierAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy unitTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (absRef : TypedFnRef V hs.fns [stateTy, bytesTy, .seq unitTy none] [stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (cs : List (Clause V hs verifier stateTy)) :
    Clause.answer M fnTable rTable
        (verifierAbsorbClause verifier prover site kind label hlabel encRef absRef :: cs)
        (.get kind prover at_ τ) st =
      .call (.get kind prover ⟨at_.path, site.key⟩ τ) fun msg =>
        (((liftLocal id (encRef.eval M fnTable (.cons msg .nil))).bind fun enc =>
          (liftLocal id (absRef.eval M fnTable (.cons st (.cons label (.cons enc.single .nil))))).map
            fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
          let values := HList.split [τ] (aloneOut M verifier out)
          (values.1.single, values.2.single) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((verifierAbsorbClause verifier prover site kind label hlabel encRef absRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
  rw [verifierAbsorbClause_denote]
  dsimp only [Process.mapHalt, Process.map, verifierAbsorbClause, Clause.site, ROp.reply]
  congr 1; funext msg; congr 1; funext out
  cases hsp : HList.split [τ] (aloneOut M verifier out) with
  | mk v1 v2 =>
      cases v1 with | cons a an => cases an; rfl

/-- Exact `Clause.answer` result of `deriveClause` (`drawIns = []`) on a matching `.hear`/`.own`. -/
private theorem deriveClause_answer_hear {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (prover verifier : Role) (site : Site) (law : V.LawKey)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (derRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (coin : M.Val τ) (st' : M.Val stateTy)
    (hDer : derRef.eval M fnTable (.cons st (.cons label .nil)) = .done (.cons coin (.cons st' .nil)))
    (cs : List (Clause V hs prover stateTy)) :
    Clause.answer M fnTable rTable
        (deriveClause prover verifier site (.hear (.coin law) verifier) [] toldKey label hlabel derRef :: cs)
        (.hear (.coin law) verifier at_ τ) st =
      .call (.give .message [verifier] ⟨at_.path, toldKey⟩ τ coin) fun _ => .done (coin, st') := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((deriveClause prover verifier site (.hear (.coin law) verifier) [] toldKey label hlabel
    derRef).code.denote (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons st .nil)))).mapHalt _).map _ = _
  rw [deriveClause_denote_nil, hDer, liftLocal_done]
  dsimp only [Process.bind, deriveClause, Clause.site, List.cons_append, List.nil_append]
  simp only [Process.map, Process.mapHalt, aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem deriveClause_answer_own {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (verifier prover : Role) (site : Site) (law : V.LawKey) (hearers : List Role)
    (toldKey : Key) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (derRef : TypedFnRef V hs.fns [stateTy, bytesTy] [τ, stateTy])
    (at_ : Occurrence) (hSite : site = at_.site) (st : M.Val stateTy)
    (coin : M.Val τ) (st' : M.Val stateTy)
    (hDer : derRef.eval M fnTable (.cons st (.cons label .nil)) = .done (.cons coin (.cons st' .nil)))
    (cs : List (Clause V hs verifier stateTy)) :
    Clause.answer M fnTable rTable
        (deriveClause verifier prover site (.own (.coin law) hearers) [] toldKey label hlabel derRef :: cs)
        (.own (.coin law) hearers at_ [] .nil τ) st =
      .call (.give .message [prover] ⟨at_.path, toldKey⟩ τ coin) fun _ => .done (coin, st') := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((deriveClause verifier prover site (.own (.coin law) hearers) [] toldKey label hlabel
    derRef).code.denote (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt _).map _ = _
  rw [deriveClause_denote_nil, hDer, liftLocal_done]
  dsimp only [Process.bind, deriveClause, Clause.site, List.cons_append, List.nil_append]
  simp only [Process.map, Process.mapHalt, aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem layoutPWriteClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (prover : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (wRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (buf chunk : List (M.Val unitTy))
    (hW : wRef.eval M fnTable (.cons msg .nil) = .done (.cons chunk .nil))
    (cs : List (Clause V hs prover (.seq unitTy none))) :
    Clause.answer M fnTable rTable
        (layoutPWriteClause prover site kind getters wRef :: cs)
        (.give kind getters at_ τ msg) buf =
      .done ((), buf ++ chunk) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutPWriteClause prover site kind getters wRef).code.denote
    (roleSem M prover fnTable rTable) at_.path
    (Env.positional (aloneIn M prover (.cons msg (.cons buf .nil))))).mapHalt _).map _ = _
  rw [layoutPWriteClause_denote, hW, liftLocal_done]
  dsimp only [Process.map, Process.mapHalt, HList.single, layoutPWriteClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, ROp.reply]

theorem layoutDropClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty}
    (r : Role) (site : Site) (kind : FlowKind) (getters : List Role)
    (at_ : Occurrence) (hSite : site = at_.site) (msg : M.Val τ) (s : M.Val stateTy)
    (cs : List (Clause V hs r stateTy)) :
    Clause.answer M fnTable rTable
        (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters :: cs)
        (.give kind getters at_ τ msg) s =
      .done ((), s) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutDropClause r site kind getters).code.denote
    (roleSem M r fnTable rTable) at_.path
    (Env.positional (aloneIn M r (.cons msg (.cons s .nil))))).mapHalt _).map _ = _
  rw [layoutDropClause_denote]
  dsimp only [Process.map, Process.mapHalt, layoutDropClause, Clause.site]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

private theorem layoutVReadClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (at_ : Occurrence) (hSite : site = at_.site) (buf : List (M.Val unitTy)) (off nextOff : Nat)
    (v : M.Val τ)
    (hR : rRef.eval M fnTable (.cons buf (.cons off .nil)) = .done (.cons v (.cons nextOff .nil)))
    (cs : List (Clause V hs verifier (streamStateTy unitTy))) :
    Clause.answer M fnTable rTable
        (layoutVReadClause hfree verifier prover site kind rRef :: cs)
        (.get kind prover at_ τ) (buf, (off, ())) =
      .done (v, (buf, (nextOff, ()))) := by
  unfold Clause.answer
  rw [dite_eq_left (⟨hSite, rfl, rfl, rfl⟩ : _)]
  change (((layoutVReadClause hfree verifier prover site kind rRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons (buf, (off, ())) .nil)))).mapHalt _).map _ = _
  rw [layoutVReadClause_denote, hR, liftLocal_done]
  dsimp only [Process.map, Process.mapHalt, layoutVReadClause, Clause.site,
    List.cons_append, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]
  rfl

private theorem layoutVCarryClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (rRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (at_ : Occurrence) (hSite : toldSite = at_.site)
    (coin : M.Val τ) (buf : List (M.Val unitTy)) (off nextOff : Nat)
    (hR : rRef.eval M fnTable (.cons buf (.cons off .nil)) = .done (.cons coin (.cons nextOff .nil)))
    (hEq : eqRef.eval M fnTable (.cons coin (.cons coin .nil)) = .done (.cons true .nil))
    (cs : List (Clause V hs verifier (streamStateTy unitTy))) :
    Clause.answer M fnTable rTable
        (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef :: cs)
        (.give .message [prover] at_ τ coin) (buf, (off, ())) =
      .done ((), (buf, (nextOff, ()))) := by
  unfold Clause.answer
  have hM : (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.site =
      (ROp.occurrence M (.give .message [prover] at_ τ coin)).site ∧
      some (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.part =
      ROp.part M (.give .message [prover] at_ τ coin) ∧
      (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.takes =
      ROp.takes M (.give .message [prover] at_ τ coin) ∧
      (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.gives =
      ROp.gives M (.give .message [prover] at_ τ coin) := ⟨hSite, rfl, rfl, rfl⟩
  rw [dite_eq_left hM]
  change (((layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).code.denote
    (roleSem M verifier fnTable rTable) at_.path
    (Env.positional (aloneIn M verifier (.cons coin (.cons (buf, (off, ())) .nil))))).mapHalt _).map _ = _
  rw [layoutVCarryClause_denote, hR, liftLocal_done]
  change ((((liftLocal (S := RSig M) id (eqRef.eval M fnTable (.cons coin (.cons coin .nil)))).bind fun eqRes =>
      bif eqRes.single then .done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))
      else .halt (.declared .reject ⟨at_.path, guardKey⟩)).mapHalt
        (fun why => (why, (buf, (off, ()))))).map
      (fun out =>
        let values := HList.split (layoutVCarryClause hfree verifier prover toldSite guardKey rRef eqRef).site.gives (aloneOut M verifier out)
        (ROp.reply M (.give .message [prover] at_ τ coin) (cast (congrArg (HList M.Val) hM.2.2.2) values.1), values.2.single))) = _
  rw [hEq, liftLocal_done]
  change ((Process.done (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (nextOff, ())) .nil))).mapHalt _).map _ = _
  dsimp only [Process.map, Process.mapHalt, layoutVCarryClause, Clause.site, List.nil_append]
  simp only [aloneOut_aloneIn, HList.split, HList.single, ROp.reply]

/-! ### Builder behavior lookups for `buildConstructionClauses` and `buildStreamingLayoutClauses` -/

private theorem construction_clauses_answer_prover_flow_abs {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
        (msg : M.Val τ) (st : M.Val stateTy),
        M.Valid τ msg → M.Valid stateTy st →
        (∃ e, (e, true) ∈ es ∧ e.site = at_.site ∧ e.τ = τ ∧ e.cls = .flow kind prover getters) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
          (enc : List (M.Val unitTy)) (st' : M.Val stateTy),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil) = .done (.cons enc .nil) ∧
          absRef.eval M (Defs.fnTable M a.program.defs)
            (.cons st (.cons (msgLabel at_.site) (.cons enc .nil))) = .done (.cons st' .nil) ∧
          M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cP (.give kind getters at_ τ msg) st =
            .call (.give kind getters ⟨at_.path, at_.site.key⟩ τ msg) fun _ => .done ((), st')
  | _, [], _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, cP, cV, cS, h, kind, getters, at_, τ, msg, st, hMsgV, hStV,
      ⟨e', he', hSite, hTy, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_prover_flow_abs (idx + 1) rest hRec
            kind getters at_ τ msg st hMsgV hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        by_cases hMatch :
                            (proverAbsorbClause prover e.site kind₀ getters₀ (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef absRef).site.site = at_.site ∧
                            some (proverAbsorbClause prover e.site kind₀ getters₀ (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef absRef).site.part = some (.give kind getters) ∧
                            [e.τ] = [τ] ∧ ([] : List V.Ty) = []
                        · have hSiteEq : e.site = at_.site := hMatch.1
                          have hPartEq : Part.give kind₀ getters₀ = .give kind getters := Option.some.inj hMatch.2.1
                          cases hPartEq
                          have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.1 |>.1
                          subst hTyEq
                          obtain ⟨encH, hEncD, hEncV⟩ := encRef.eval_done M a (.cons msg .nil) ⟨hMsgV, trivial⟩
                          cases encH with
                          | cons enc en =>
                              cases en
                              have hLblV : M.Valid bytesTy (msgLabel e.site) :=
                                ⟨msgLabel_bytes e.site, (fun _ h => nomatch h)⟩
                              obtain ⟨stH, hAbsD, hAbsV⟩ := absRef.eval_done M a
                                (.cons st (.cons (msgLabel e.site) (.cons enc .nil)))
                                ⟨hStV, hLblV, hEncV.1, trivial⟩
                              cases stH with
                              | cons st' sn =>
                                  cases sn
                                  refine ⟨encRef, enc, st', hEnc, hEncD, hSiteEq ▸ hAbsD, hAbsV.1, ?_⟩
                                  rw [← hSiteEq]
                                  exact proverAbsorbClause_answer M _ _ prover e.site kind getters
                                    (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef
                                    at_ hSiteEq msg st enc st' hEncD hAbsD triple.1
                        · rcases List.mem_cons.mp he' with hEqPair | hmem
                          · cases hEqPair
                            rw [hCls] at hECls; cases hECls
                            exact absurd ⟨hSite, rfl, by cases hTy; rfl, rfl⟩ hMatch
                          · obtain ⟨encR, enc, st', hE, hED, hAD, hSV, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                            refine ⟨encR, enc, st', hE, hED, hAD, hSV, ?_⟩
                            unfold Clause.answer
                            exact (dite_eq_right hMatch).trans hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
              · split at h
                · rename_i hOut
                  cases h
                  rcases List.mem_cons.mp he' with hEqPair | hmem
                  · cases hEqPair; rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                rcases List.mem_cons.mp he' with hEqPair | hmem
                                · cases hEqPair; rw [hCls] at hECls; cases hECls
                                · obtain ⟨encR, enc, st', hE, hED, hAD, hSV, hAns⟩ :=
                                    ih ⟨e', hmem, hSite, hTy, hECls⟩
                                  refine ⟨encR, enc, st', hE, hED, hAD, hSV, ?_⟩
                                  unfold Clause.answer
                                  rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                  exact hAns
                              · cases h
                        · cases h
                  · split at h
                    · rcases List.mem_cons.mp he' with hEqPair | hmem
                      · cases hEqPair; rw [hCls] at hECls; cases hECls
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                  · cases h

private theorem construction_clauses_answer_verifier_flow_abs {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        (∃ e, (e, true) ∈ es ∧ e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (encRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none]),
          findSuiteEncode a suite unitTy τ = some encRef ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.get kind prover at_ τ) st =
            .call (.get kind prover ⟨at_.path, at_.site.key⟩ τ) fun msg =>
              (((liftLocal id (encRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil))).bind fun enc =>
                (liftLocal id (absRef.eval M (Defs.fnTable M a.program.defs)
                  (.cons st (.cons (msgLabel at_.site) (.cons enc.single .nil))))).map
                  fun nextSt => aloneIn M verifier (.cons msg nextSt)).mapHalt fun why => (why, st)).map fun out =>
                let values := HList.split [τ] (aloneOut M verifier out)
                (values.1.single, values.2.single)
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, cP, cV, cS, h, kind, at_, τ, st,
      ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_verifier_flow_abs (idx + 1) rest hRec
            kind at_ τ st hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        by_cases hMatch :
                            (verifierAbsorbClause verifier prover e.site kind₀ (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef absRef).site.site = at_.site ∧
                            some (verifierAbsorbClause verifier prover e.site kind₀ (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef absRef).site.part = some (.get kind prover) ∧
                            ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                        · have hSiteEq : e.site = at_.site := hMatch.1
                          have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                          cases hPartEq
                          have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                          subst hTyEq
                          refine ⟨encRef, hEnc, ?_⟩
                          rw [← hSiteEq]
                          exact verifierAbsorbClause_answer M _ _ verifier prover e.site kind
                            (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef at_ hSiteEq st triple.2.1
                        · rcases List.mem_cons.mp he' with hEqPair | hmem
                          · cases hEqPair
                            rw [hCls] at hECls; cases hECls
                            exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                          · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                            refine ⟨encR, hE, ?_⟩
                            unfold Clause.answer
                            exact (dite_eq_right hMatch).trans hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
              · split at h
                · rename_i hOut
                  cases h
                  rcases List.mem_cons.mp he' with hEqPair | hmem
                  · cases hEqPair; rw [hCls] at hECls; cases hECls; exact absurd rfl hOut.1
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                rcases List.mem_cons.mp he' with hEqPair | hmem
                                · cases hEqPair; rw [hCls] at hECls; cases hECls
                                · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                                  refine ⟨encR, hE, ?_⟩
                                  unfold Clause.answer
                                  rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                  exact hAns
                              · cases h
                        · cases h
                  · split at h
                    · rcases List.mem_cons.mp he' with hEqPair | hmem
                      · cases hEqPair; rw [hCls] at hECls; cases hECls
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        · cases h; exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                  · cases h

/-- When no event at `(at_.site, kind, τ)` is marked for absorption (a trailing prover message),
neither `cP` nor `cV` matches the flow, so both layers pass the flow straight through in lockstep. -/
private theorem construction_clauses_unmatched_elided_flow {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (msg : M.Val τ),
        (∀ e b, (e, b) ∈ es → e.site = at_.site → e.τ = τ →
          (∃ gs, verifier ∈ gs ∧ e.cls = .flow kind prover gs) → b = false) →
        (∀ c ∈ cP, ¬ ClauseMatches M c (.give kind getters at_ τ msg)) ∧
        (∀ c ∈ cV, ¬ ClauseMatches M c (.get kind prover at_ τ))
  | _, [], _, _, _, h, _, _, _, _, _, _ => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, cS, h, kind, getters, at_, τ, msg, hNoAbs => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have hNoAbsRest : ∀ e' b', (e', b') ∈ rest → e'.site = at_.site → e'.τ = τ →
              (∃ gs, verifier ∈ gs ∧ e'.cls = .flow kind prover gs) → b' = false :=
            fun e' b' hmem => hNoAbs e' b' (List.mem_cons_of_mem _ hmem)
          obtain ⟨ihP, ihV⟩ := construction_clauses_unmatched_elided_flow (idx + 1) rest hRec
            kind getters at_ τ msg hNoAbsRest
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro hM
                            have hSite : e.site = at_.site := hM.1
                            have hKind : kind₀ = kind := by
                              have hp := Option.some.inj hM.2.1; cases hp; rfl
                            have hTy : e.τ = τ := (List.cons.inj hM.2.2.1).1
                            have hFalse := hNoAbs e true List.mem_cons_self hSite hTy
                              ⟨getters₀, hPV.2, hKind ▸ hPV.1 ▸ hCls⟩
                            cases hFalse
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro hM
                            have hSite : e.site = at_.site := hM.1
                            have hKind : kind₀ = kind := by
                              have hp := Option.some.inj hM.2.1; cases hp; rfl
                            have hTy : e.τ = τ := (List.cons.inj hM.2.2.2).1
                            have hFalse := hNoAbs e true List.mem_cons_self hSite hTy
                              ⟨getters₀, hPV.2, hKind ▸ hPV.1 ▸ hCls⟩
                            cases hFalse
                          · exact ihV c hm
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    cases h; exact ⟨ihP, ihV⟩
              · split at h
                · cases h; exact ⟨ihP, ihV⟩
                · cases h
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some _ =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hM; cases hM.2.1
                                  · exact ihP c hm
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hM; cases hM.2.1
                                  · exact ihV c hm
                              · cases h
                        · cases h
                  · split at h
                    · split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihP, ihV⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some _ => rw [hS] at h; cases h; exact ⟨ihP, ihV⟩
                      · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
                  · cases h

private theorem construction_clauses_answer_prover_coin {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)}
        {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (law : V.LawKey) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧
          ∃ hearers, prover ∈ hearers ∧ p.1.cls = .given (.coin law) verifier hearers) →
        ∃ (idxP : Nat) (eP : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxP]? = some eP ∧ eP.site = at_.site ∧ eP.τ = τ ∧
          (∃ hearersP, prover ∈ hearersP ∧ eP.cls = .given (.coin law) verifier hearersP) ∧
          findSuiteDerive a suite stateTy [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cP (.hear (.coin law) verifier at_ τ) st =
            .call (.give .message [verifier] ⟨at_.path, drawToldKey events idxP⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cP, cV, cS, h, law, at_, τ, st, hStV,
      ⟨p', hp', hSite, hTy, hs', hPin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k p'', rest[k]? = some p'' → events[(idx + 1) + k]? = some p''.1 := by
        intro k p'' hk
        have := hSuf (k + 1) p'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_prover_coin (idx + 1) rest hSufRest hRec
            law at_ τ st hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        rcases List.mem_cons.mp hp' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, hAns⟩ :=
                            ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                          refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
              · split at h
                · cases h
                  rcases List.mem_cons.mp hp' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law₀ =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law₀ with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                let derRefP : TypedFnRef V a.program.headers.fns [stateTy, bytesTy]
                                    [e.τ, stateTy] := hIns ▸ derRef
                                have hDerP : findSuiteDerive a suite stateTy [] e.τ = some derRefP := by
                                  cases sig with
                                  | mk sIns sOut =>
                                      dsimp only [derRefP] at hIns ⊢
                                      subst hIns; exact hDer
                                by_cases hMatch :
                                    e.site = at_.site ∧
                                    some (Part.hear (.coin law₀) verifier) = some (.hear (.coin law) verifier) ∧
                                    ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                · have hSiteEq : e.site = at_.site := hMatch.1
                                  have hLawEq : law₀ = law := by
                                    have hp := Option.some.inj hMatch.2.1
                                    cases hp; rfl
                                  have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                  subst hLawEq; subst hTyEq
                                  have hLblV : M.Valid bytesTy (drawLabel e.site) :=
                                    ⟨drawLabel_bytes e.site, (fun _ h => nomatch h)⟩
                                  obtain ⟨resH, hDerD, hResV⟩ := derRefP.eval_done M a
                                    (.cons st (.cons (drawLabel e.site) .nil)) ⟨hStV, hLblV, trivial⟩
                                  cases resH with
                                  | cons coin r1 =>
                                      cases r1 with
                                      | cons st' r2 =>
                                          cases r2
                                          refine ⟨idx, e, derRefP, coin, st', hIdx, hSiteEq, rfl,
                                            ⟨hearers, hCoin.2, hCoin.1 ▸ hCls⟩, hDerP,
                                            hSiteEq ▸ hDerD, hResV.1, hResV.2.1, ?_⟩
                                          exact deriveClause_answer_hear M _ _ prover verifier e.site law₀
                                            (drawToldKey events idx) (drawLabel e.site)
                                            (drawLabel_bytes e.site) derRefP at_ hSiteEq st coin st'
                                            hDerD triple.1
                                · rcases List.mem_cons.mp hp' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                    exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                  · obtain ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, hAns⟩ :=
                                      ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                                    refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                                    unfold Clause.answer
                                    exact (dite_eq_right hMatch).trans hAns
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                        · cases h; exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hs', hPin, hECls⟩
                  · cases h

private theorem construction_clauses_answer_verifier_coin {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)}
        {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧ prover ∈ hearers ∧
          p.1.cls = .given (.coin law) verifier hearers) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier hearers ∧
          V.law law = some ⟨[], τ⟩ ∧
          findSuiteDerive a suite stateTy [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) hearers at_ [] .nil τ) st =
            .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cP, cV, cS, h, law, hearers, at_, τ, st, hStV,
      ⟨p', hp', hSite, hTy, hPin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k p'', rest[k]? = some p'' → events[(idx + 1) + k]? = some p''.1 := by
        intro k p'' hk
        have := hSuf (k + 1) p'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => construction_clauses_answer_verifier_coin (idx + 1) rest hSufRest hRec
            law hearers at_ τ st hStV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        rcases List.mem_cons.mp hp' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, hAns⟩ :=
                            ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                          refine ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
              · split at h
                · cases h
                  rcases List.mem_cons.mp hp' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                · cases h
          | given gkind owner hearers₀ =>
              rw [hCls] at h
              cases gkind with
              | coin law₀ =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law₀ with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · rename_i hOutEq
                          cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                have hSigEq : sig = ⟨[], e.τ⟩ := by
                                    cases sig with
                                    | mk ins out =>
                                        dsimp only at hIns hOutEq
                                        subst hIns; subst hOutEq; rfl
                                subst hSigEq
                                by_cases hMatch :
                                    e.site = at_.site ∧
                                    some (Part.own (.coin law₀) hearers₀) = some (.own (.coin law) hearers) ∧
                                    ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                                · have hSiteEq : e.site = at_.site := hMatch.1
                                  have hPartEq : Part.own (.coin law₀) hearers₀ = .own (.coin law) hearers :=
                                    Option.some.inj hMatch.2.1
                                  cases hPartEq
                                  have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                                  subst hTyEq
                                  have hLblV : M.Valid bytesTy (drawLabel e.site) :=
                                    ⟨drawLabel_bytes e.site, (fun _ h => nomatch h)⟩
                                  obtain ⟨resH, hDerD, hResV⟩ := derRef.eval_done M a
                                    (.cons st (.cons (drawLabel e.site) .nil)) ⟨hStV, hLblV, trivial⟩
                                  cases resH with
                                  | cons coin r1 =>
                                      cases r1 with
                                      | cons st' r2 =>
                                          cases r2
                                          refine ⟨idx, e, derRef, coin, st', hIdx, hSiteEq, rfl,
                                            hCoin.1 ▸ hCls, hLaw, hDer, hSiteEq ▸ hDerD,
                                            hResV.1, hResV.2.1, ?_⟩
                                          exact deriveClause_answer_own M _ _ verifier prover e.site law
                                            hearers (drawToldKey events idx) (drawLabel e.site)
                                            (drawLabel_bytes e.site) derRef at_ hSiteEq st coin st'
                                            hDerD triple.2.1
                                · rcases List.mem_cons.mp hp' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                    exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                  · obtain ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, hAns⟩ :=
                                      ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                                    refine ⟨idxV, eV, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
                                    unfold Clause.answer
                                    exact (dite_eq_right hMatch).trans hAns
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; subst hNil; cases hPin
                      · split at h
                        · cases samplesKey with
                          | none => cases h; exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                          | some sKey =>
                              dsimp only at h
                              cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                              | none => rw [hS] at h; cases h
                              | some _ => rw [hS] at h; cases h; exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                        · cases h; exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
                  · cases h

/-- No clause in `cP` or `cV` matches a closed effect (`.own (.coin _) []`, `.own (.request _)`,
`.begin`, `.settle`). -/
private theorem construction_clauses_unmatched_closed {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {samplesKey : Option Key} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)}
      {cS : List (Clause V a.program.headers prover .nat)},
      buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier samplesKey
        declKey events idx es = .ok (cP, cV, cS) →
      ∀ op, ROp.IsClosed M op →
        (∀ c ∈ cP, ¬ ClauseMatches M c op) ∧ (∀ c ∈ cV, ¬ ClauseMatches M c op)
  | _, [], _, _, _, h, _, _ => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, cS, h, op, hCl => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go a suite stateTy unitTy absRef prover verifier
          samplesKey declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok triple =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := construction_clauses_unmatched_closed (idx + 1) rest hRec op hCl
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some _ =>
                        rw [hEnc] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, proverAbsorbClause] at hCl hm
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, verifierAbsorbClause] at hCl hm
                          · exact ihV c hm
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h; exact ⟨ihP, ihV⟩
              · split at h
                · cases h; exact ⟨ihP, ihV⟩
                · cases h
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · rename_i hCoin
                    cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hDer : findSuiteDerive a suite stateTy sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some _ =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hm; cases op <;> simp [ROp.IsClosed, ROp.part, ClauseMatches, deriveClause] at hCl hm
                                  · exact ihP c hm
                                · rcases List.mem_cons.mp hc with rfl | hm
                                  · intro hm
                                    cases op with
                                    | own gk hs' _ _ _ _ =>
                                        cases gk with
                                        | coin _ =>
                                            cases hs' with
                                            | nil =>
                                                have hp := Option.some.inj hm.2.1
                                                cases hp
                                                exact nomatch hCoin.2
                                            | cons _ _ => exact False.elim hCl
                                        | request _ =>
                                            have hp := Option.some.inj hm.2.1; cases hp
                                    | give | get | hear | «begin» | settle =>
                                        simp [ROp.IsClosed, ROp.part, ClauseMatches, deriveClause] at hCl hm
                                  · exact ihV c hm
                              · cases h
                        · cases h
                  · split at h
                    · split at h
                      · cases samplesKey with
                        | none => cases h; exact ⟨ihP, ihV⟩
                        | some sKey =>
                            dsimp only at h
                            cases hS : findTypedFnRef a sKey [.nat, .nat] [e.τ] with
                            | none => rw [hS] at h; cases h
                            | some _ => rw [hS] at h; cases h; exact ⟨ihP, ihV⟩
                      · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
                  · cases h

theorem streaming_layout_unmatched_closed {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ op, ROp.IsClosed M op →
        (∀ c ∈ pCs, ¬ ClauseMatches M c op) ∧ (∀ c ∈ vCs, ¬ ClauseMatches M c op)
  | _, [], _, _, h, _, _ => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, pCs, vCs, h, op, hCl => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihP, ihV⟩ := streaming_layout_unmatched_closed (idx + 1) rest hRec op hCl
          have hNotGive : ∀ k gs, some (Part.give k gs) ≠ ROp.part M op := by
            intro k gs hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          have hNotGet : ∀ k g, some (Part.get k g) ≠ ROp.part M op := by
            intro k g hm; cases op <;> simp [ROp.IsClosed, ROp.part] at hCl hm
          cases hCls : e.cls with
          | flow _ _ _ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · cases h
                  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact fun hM => hNotGive _ _ hM.2.1
                    · exact ihP c hm
                  · rcases List.mem_cons.mp hc with rfl | hm
                    · exact fun hM => hNotGet _ _ hM.2.1
                    · exact ihV c hm
              · cases h; exact ⟨ihP, ihV⟩
          | given gkind _ _ =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact fun hM => hNotGive _ _ hM.2.1
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact fun hM => hNotGive _ _ hM.2.1
                          · exact ihV c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact fun hM => hNotGive _ _ hM.2.1
                        · exact ihP c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact fun hM => hNotGive _ _ hM.2.1
                        · exact ihV c hm
                  · cases h; exact ⟨ihP, ihV⟩
              | request _ => cases h; exact ⟨ihP, ihV⟩

private theorem streaming_layout_answer_prover_flow {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty)
        (msg : M.Val τ) (buf : List (M.Val unitTy)),
        M.Valid τ msg →
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (wRef : TypedFnRef V a.program.headers.fns [τ] [.seq unitTy none])
          (chunk : List (M.Val unitTy)),
          findLayoutWrite a layout.module unitTy τ = some wRef ∧
          wRef.eval M (Defs.fnTable M a.program.defs) (.cons msg .nil) = .done (.cons chunk .nil) ∧
          (∀ u ∈ chunk, M.Valid unitTy u) ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            pCs (.give kind getters at_ τ msg) buf = .done ((), buf ++ chunk)
  | _, [], _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, hSub, pCs, vCs, h, kind, getters, at_, τ, msg, buf, hMsgV,
      ⟨e', he', hSite, hTy, hVin, hECls⟩ => by
      unfold buildStreamingLayoutClauses.go at h
      have hSubRest : ∀ e'' ∈ rest, e'' ∈ events := fun e'' he'' => hSub e'' (List.mem_cons_of_mem _ he'')
      have hAtInEvents : at_.site.key ∈ events.map (·.site.key) := by
        have hMemE' : e' ∈ events := hSub e' he'
        rw [← hSite]
        exact List.mem_map.mpr ⟨e', hMemE', rfl⟩
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => streaming_layout_answer_prover_flow (idx + 1) rest hSubRest hRec
            kind getters at_ τ msg buf hMsgV hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · rename_i hPV
                cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef
                  cases h
                  by_cases hMatch :
                      e.site = at_.site ∧
                      some (Part.give (V := V) kind₀ getters₀) = some (.give kind getters) ∧
                      [e.τ] = [τ] ∧ ([] : List V.Ty) = []
                  · have hSiteEq : e.site = at_.site := hMatch.1
                    have hPartEq : Part.give kind₀ getters₀ = .give kind getters := Option.some.inj hMatch.2.1
                    cases hPartEq
                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.1 |>.1
                    subst hTyEq
                    obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M a (.cons msg .nil) ⟨hMsgV, trivial⟩
                    cases chH with
                    | cons chunk cn =>
                        cases cn
                        refine ⟨wRef, chunk, hW, hWD, hChV.1.1, ?_⟩
                        exact layoutPWriteClause_answer M _ _ prover e.site kind getters wRef
                          at_ hSiteEq msg buf chunk hWD pair.1
                  · rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                      exact absurd ⟨hSite, rfl, by cases hTy; rfl, rfl⟩ hMatch
                    · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                      refine ⟨wR, ch, h1, h2, h3, ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans hAns
              · rename_i hNotPV
                cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              have hNoTold : ¬ (⟨e.site.through, drawToldKey events idx⟩ : Site) = at_.site := by
                intro heq
                have hk : drawToldKey events idx = at_.site.key := congrArg Site.key heq
                exact drawToldKey_fresh events idx (hk ▸ hAtInEvents)
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                          refine ⟨wR, ch, h1, h2, h3, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => hNoTold hm.1)]
                          exact hAns
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨wR, ch, h1, h2, h3, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
                        refine ⟨wR, ch, h1, h2, h3, ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => hNoTold hm.1)]
                        exact hAns
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hVin, hECls⟩

private theorem streaming_layout_answer_verifier_flow {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V))
      {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
      {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty)
        (buf : List (M.Val unitTy)) (off : Nat),
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧
          ∃ getters, verifier ∈ getters ∧ e.cls = .flow kind prover getters) →
        ∃ (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]),
          findLayoutRead a layout.module unitTy τ = some rRef ∧
          (∀ v nextOff,
            rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
              .done (.cons v (.cons nextOff .nil)) →
            Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.get kind prover at_ τ) (buf, (off, ())) = .done (v, (buf, (nextOff, ()))))
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, pCs, vCs, h, kind, at_, τ, buf, off,
      ⟨e', he', hSite, hTy, gs', hVin, hECls⟩ => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := fun hIn => streaming_layout_answer_verifier_flow (idx + 1) rest hRec
            kind at_ τ buf off hIn
          cases hCls : e.cls with
          | flow kind₀ giver₀ getters₀ =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                  simp only [hW, hR] at h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef
                  cases h
                  by_cases hMatch :
                      e.site = at_.site ∧
                      some (Part.get (V := V) kind₀ prover) = some (.get kind prover) ∧
                      ([] : List V.Ty) = [] ∧ [e.τ] = [τ]
                  · have hSiteEq : e.site = at_.site := hMatch.1
                    have hPartEq : Part.get kind₀ prover = .get kind prover := Option.some.inj hMatch.2.1
                    cases hPartEq
                    have hTyEq : e.τ = τ := List.cons.inj hMatch.2.2.2 |>.1
                    subst hTyEq
                    refine ⟨rRef, hR, fun v nextOff hRD => ?_⟩
                    exact layoutVReadClause_answer M _ _ hfree verifier prover e.site kind rRef
                      at_ hSiteEq buf off nextOff v hRD pair.2
                  · rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                      exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                    · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                      refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans (hAns v nextOff hRD)
              · rename_i hNotPV
                cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, hVin⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
          | given gkind owner hearers =>
              rw [hCls] at h
              cases gkind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                      cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      cases hE : findLayoutEqual a layout.module e.τ <;>
                        simp only [hW, hR, hE] at h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                      · cases h
                        rcases List.mem_cons.mp he' with rfl | hmem
                        · rw [hCls] at hECls; cases hECls
                        · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                          refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns v nextOff hRD
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
                        refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => by cases hm.2.1)]
                        exact hAns v nextOff hRD
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, gs', hVin, hECls⟩

private theorem streaming_layout_answer_told {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)),
      (∀ e ∈ es, e ∈ events) →
      ∀ {pCs : List (Clause V a.program.headers prover (.seq unitTy none))}
        {vCs : List (Clause V a.program.headers verifier (streamStateTy unitTy))},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      ∀ (k : Nat) (e₀ : ShapeEvent V), es[k]? = some e₀ →
        ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (coin : M.Val e₀.τ),
          e₀.cls = .given (.coin law) verifier hearers → prover ∈ hearers →
          at_.site = ⟨e₀.site.through, drawToldKey events (idx + k)⟩ →
          M.Valid e₀.τ coin →
          if e₀.site ∈ layout.carry then
            ∃ (wRef : TypedFnRef V a.program.headers.fns [e₀.τ] [.seq unitTy none])
              (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [e₀.τ, .nat])
              (eqRef : TypedFnRef V a.program.headers.fns [e₀.τ, e₀.τ] [.bool])
              (chunk : List (M.Val unitTy)),
              findLayoutWrite a layout.module unitTy e₀.τ = some wRef ∧
              findLayoutRead a layout.module unitTy e₀.τ = some rRef ∧
              findLayoutEqual a layout.module e₀.τ = some eqRef ∧
              wRef.eval M (Defs.fnTable M a.program.defs) (.cons coin .nil) = .done (.cons chunk .nil) ∧
              (∀ u ∈ chunk, M.Valid unitTy u) ∧
              (∀ buf, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                pCs (.give .message [verifier] at_ e₀.τ coin) buf = .done ((), buf ++ chunk)) ∧
              (∀ buf off nextOff,
                rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
                  .done (.cons coin (.cons nextOff .nil)) →
                eqRef.eval M (Defs.fnTable M a.program.defs) (.cons coin (.cons coin .nil)) =
                  .done (.cons true .nil) →
                Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                  vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) =
                  .done ((), (buf, (nextOff, ()))))
          else
            (∀ buf, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              pCs (.give .message [verifier] at_ e₀.τ coin) buf = .done ((), buf)) ∧
            (∀ buf off, Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.give .message [prover] at_ e₀.τ coin) (buf, (off, ())) = .done ((), (buf, (off, ()))))
  | _, [], _, _, _, _, _, _, hk, _, _, _, _, _, _, _, _ => by simp at hk
  | idx, e :: rest, hSub, pCs, vCs, h, k, e₀, hk, law, hearers, at_, coin, hE₀Cls, hPin, hAtSite, hCoinV => by
      unfold buildStreamingLayoutClauses.go at h
      have hSubRest : ∀ e'' ∈ rest, e'' ∈ events := fun e'' he'' => hSub e'' (List.mem_cons_of_mem _ he'')
      have hMemE : e ∈ events := hSub e List.mem_cons_self
      have hFlowNoMatch : e.site ≠ at_.site := by
        intro heq
        have hkEq : e.site.key = drawToldKey events (idx + k) := by
          have := congrArg Site.key heq; rw [hAtSite] at this; exact this
        exact drawToldKey_fresh events (idx + k) (hkEq ▸ List.mem_map.mpr ⟨e, hMemE, rfl⟩)
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          cases k with
          | zero =>
              simp at hk; subst hk
              rw [hE₀Cls] at h; dsimp only at h
              rw [ite_eq_left ⟨rfl, hPin⟩] at h
              have hSiteEq : ⟨e.site.through, drawToldKey events idx⟩ = at_.site := by
                simpa using hAtSite.symm
              by_cases hCar : e.site ∈ layout.carry
              · rw [ite_eq_left hCar] at h
                cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                cases hE : findLayoutEqual a layout.module e.τ <;>
                  simp only [hW, hR, hE] at h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · cases h
                · rename_i wRef rRef eqRef
                  cases h
                  rw [ite_eq_left hCar]
                  obtain ⟨chH, hWD, hChV⟩ := wRef.eval_done M a (.cons coin .nil) ⟨hCoinV, trivial⟩
                  cases chH with
                  | cons chunk cn =>
                      cases cn
                      refine ⟨wRef, rRef, eqRef, chunk, rfl, rfl, rfl, hWD, hChV.1.1, fun buf => ?_,
                        fun buf off nextOff hRD hEqD => ?_⟩
                      · exact layoutPWriteClause_answer M _ _ prover _ .message [verifier] wRef
                          at_ hSiteEq coin buf chunk hWD pair.1
                      · exact layoutVCarryClause_answer M _ _ hfree verifier prover _ _ rRef eqRef
                          at_ hSiteEq coin buf off nextOff hRD hEqD pair.2
              · rw [ite_eq_right hCar] at h; cases h
                rw [ite_eq_right hCar]
                exact ⟨fun buf => layoutDropClause_answer M _ _ prover _ .message [verifier] at_ hSiteEq coin buf pair.1,
                       fun buf off => layoutDropClause_answer M _ _ verifier _ .message [prover] at_ hSiteEq coin (buf, (off, ())) pair.2⟩
          | succ k' =>
              have hShiftSite : at_.site = ⟨e₀.site.through, drawToldKey events ((idx + 1) + k')⟩ := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAtSite
              have hToldNoMatch : (⟨e.site.through, drawToldKey events idx⟩ : Site) ≠ at_.site := by
                intro heq
                have hkEq : (drawToldKey events idx).number = (drawToldKey events (idx + (k' + 1))).number := by
                  have := congrArg (fun s : Site => s.key.number) heq
                  rw [hAtSite] at this; exact this
                simp only [drawToldKey] at hkEq; omega
              have ih := streaming_layout_answer_told (idx + 1) rest hSubRest hRec k' e₀ hk
                law hearers at_ coin hE₀Cls hPin hShiftSite hCoinV
              cases hCls : e.cls with
              | flow _ _ _ =>
                  rw [hCls] at h; dsimp only at h
                  split at h
                  · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                    cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                      simp only [hW, hR] at h
                    · cases h
                    · cases h
                    · cases h
                    · cases h
                      by_cases hCar : e₀.site ∈ layout.carry
                      · rw [ite_eq_left hCar] at ih ⊢
                        obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                        refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact hAnsP buf
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                      · rw [ite_eq_right hCar] at ih ⊢
                        refine ⟨fun buf => ?_, fun buf off => ?_⟩
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact ih.1 buf
                        · unfold Clause.answer; rw [dite_eq_right (fun hm => hFlowNoMatch hm.1)]; exact ih.2 buf off
                  · cases h; exact ih
              | given gkind _ _ =>
                  rw [hCls] at h
                  cases gkind with
                  | coin _ =>
                      dsimp only at h
                      split at h
                      · split at h
                        · cases hW : findLayoutWrite a layout.module unitTy e.τ <;>
                          cases hR : findLayoutRead a layout.module unitTy e.τ <;>
                          cases hE : findLayoutEqual a layout.module e.τ <;>
                            simp only [hW, hR, hE] at h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                          · cases h
                            by_cases hCar : e₀.site ∈ layout.carry
                            · rw [ite_eq_left hCar] at ih ⊢
                              obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                              refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsP buf
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                            · rw [ite_eq_right hCar] at ih ⊢
                              refine ⟨fun buf => ?_, fun buf off => ?_⟩
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.1 buf
                              · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.2 buf off
                        · cases h
                          by_cases hCar : e₀.site ∈ layout.carry
                          · rw [ite_eq_left hCar] at ih ⊢
                            obtain ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, hAnsP, hAnsV⟩ := ih
                            refine ⟨wR, rR, eqR, ch, h1, h2, h3, h4, h5, fun buf => ?_, fun buf off nO hRD hEqD => ?_⟩
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsP buf
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact hAnsV buf off nO hRD hEqD
                          · rw [ite_eq_right hCar] at ih ⊢
                            refine ⟨fun buf => ?_, fun buf off => ?_⟩
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.1 buf
                            · unfold Clause.answer; rw [dite_eq_right (fun hm => hToldNoMatch hm.1)]; exact ih.2 buf off
                      · cases h; exact ih
                  | request _ => cases h; exact ih

/-! ### Applying strengthened `SuiteLawful` and `LayoutLawful` to `TypedFnRef` / `SafeFnRef` -/

theorem suiteLawful_allows {d : Deployed V} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawful M)
    {stateTy τ : V.Ty} {derRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy] [τ, stateTy]}
    (hFind : findSuiteDerive d.admitted suite stateTy [] τ = some derRef)
    {e : ShapeEvent V} (hE : e ∈ d.entry.shape.events [] id)
    {law : V.LawKey} {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) (hTy : e.τ = τ)
    (hLaw : V.law law = some ⟨[], τ⟩)
    {st st' : M.Val stateTy} {label : List Nat} {coin : M.Val τ}
    (hStV : M.Valid stateTy st) (hLbl : ∀ b, b ∈ label → b < 256)
    (hEval : derRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil)) =
      .done (.cons coin (.cons st' .nil))) :
    Allows M (.coin law) [] .nil τ coin := by
  subst hTy
  unfold Deployed.SuiteLawful at hSuite
  rw [hCon] at hSuite
  obtain ⟨defKey, hInSuite, hProgFind⟩ := findSuiteDerive_some hFind
  have hFnEq : Defs.fnTable M d.admitted.program.defs derRef.hdr derRef.member
      (cast (congrArg (HList M.Val) derRef.insEq.symm) (.cons st (.cons label .nil))) =
      .done (cast (congrArg (HList M.Val) derRef.outsEq.symm) (.cons coin (.cons st' .nil))) := by
    have hEq := derRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil))
    rw [hEval] at hEq
    rcases derRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut
    cases hIn; cases hOut
    exact hEq.symm
  exact hSuite.1 defKey hInSuite derRef.hdr derRef.member hProgFind stateTy [] e law owner h0 hs
    hE hCls hLaw derRef.insEq derRef.outsEq st label .nil coin st' hStV hLbl trivial hFnEq

theorem suiteLawful_encode_injective {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawful M)
    {unitTy τ : V.Ty} {encRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    (hFind : findSuiteEncode d.admitted suite unitTy τ = some encRef)
    {v₁ v₂ : M.Val τ} {u : List (M.Val unitTy)}
    (hV₁ : M.Valid τ v₁) (hV₂ : M.Valid τ v₂)
    (hE₁ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₁ .nil) = .done (.cons u .nil))
    (hE₂ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₂ .nil) = .done (.cons u .nil)) :
    v₁ = v₂ := by
  unfold Deployed.SuiteLawful at hSuite
  rw [hCon] at hSuite
  obtain ⟨eKey, hInSuite, hProgFind⟩ := findSuiteEncode_some hFind
  have hFn₁ : Defs.fnTable M d.admitted.program.defs encRef.hdr encRef.member
      (cast (congrArg (HList M.Val) encRef.insEq.symm) (.cons v₁ .nil)) =
      .done (cast (congrArg (HList M.Val) encRef.outsEq.symm) (.cons u .nil)) := by
    have hEq := encRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v₁ .nil)
    rw [hE₁] at hEq
    rcases encRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut; cases hIn; cases hOut; exact hEq.symm
  have hFn₂ : Defs.fnTable M d.admitted.program.defs encRef.hdr encRef.member
      (cast (congrArg (HList M.Val) encRef.insEq.symm) (.cons v₂ .nil)) =
      .done (cast (congrArg (HList M.Val) encRef.outsEq.symm) (.cons u .nil)) := by
    have hEq := encRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v₂ .nil)
    rw [hE₂] at hEq
    rcases encRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut; cases hIn; cases hOut; exact hEq.symm
  exact hSuite.2 eKey hInSuite encRef.hdr encRef.member hProgFind unitTy τ
    encRef.insEq encRef.outsEq v₁ v₂ u hV₁ hV₂ hFn₁ hFn₂

theorem layoutLawful_roundTrip {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {unitTy τ : V.Ty}
    {wRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    {rRef : SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
    (hW : findLayoutWrite d.admitted layout.module unitTy τ = some wRef)
    (hR : findLayoutRead d.admitted layout.module unitTy τ = some rRef)
    {v : M.Val τ} {chunk pre post : List (M.Val unitTy)}
    (hV : M.Valid τ v) (hPre : ∀ u ∈ pre, M.Valid unitTy u) (hPost : ∀ u ∈ post, M.Valid unitTy u)
    (hWrite : wRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil) =
      .done (.cons chunk .nil)) :
    rRef.eval M (Defs.fnTable M d.admitted.program.defs)
      (.cons (pre ++ chunk ++ post) (.cons pre.length .nil)) =
      .done (.cons v (.cons (pre.length + chunk.length) .nil)) := by
  unfold Deployed.LayoutLawful at hLayLaw
  rw [hLayOpt] at hLayLaw
  obtain ⟨wKey, hInW, hFindW⟩ := findLayoutWrite_some hW
  obtain ⟨rKey, hInR, hFindR⟩ := findLayoutRead_some hR
  have hWF : Defs.fnTable M d.admitted.program.defs wRef.hdr wRef.member
      (cast (congrArg (HList M.Val) wRef.insEq.symm) (.cons v .nil)) =
      .done (cast (congrArg (HList M.Val) wRef.outsEq.symm) (.cons chunk .nil)) := by
    have hEq := wRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil)
    rw [hWrite] at hEq
    rcases wRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut
    cases hIn; cases hOut
    exact hEq.symm
  have hRF := hLayLaw.1 wKey rKey hInW hInR wRef.hdr rRef.hdr wRef.member rRef.member
    hFindW hFindR unitTy τ wRef.insEq wRef.outsEq rRef.insEq rRef.outsEq v chunk pre post
    hV hPre hPost hWF
  have hEqR := rRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs)
    (.cons (pre ++ chunk ++ post) (.cons pre.length .nil))
  rw [hEqR, hRF]
  rcases rRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _⟩
  dsimp only at hIn hOut
  cases hIn; cases hOut
  rfl

theorem layoutLawful_written {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {unitTy τ : V.Ty}
    {wRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    {rRef : SafeFnRef V d.admitted.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]}
    (hW : findLayoutWrite d.admitted layout.module unitTy τ = some wRef)
    (hR : findLayoutRead d.admitted layout.module unitTy τ = some rRef)
    {buf : List (M.Val unitTy)} {off : Nat} {v : M.Val τ} {nextOff : Nat}
    (hBuf : ∀ u ∈ buf, M.Valid unitTy u) (hOff : off ≤ buf.length)
    (hRead : rRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons buf (.cons off .nil)) =
      .done (.cons v (.cons nextOff .nil))) :
    M.Valid τ v ∧ off ≤ nextOff ∧ nextOff ≤ buf.length ∧
    ∃ chunk,
      wRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil) =
        .done (.cons chunk .nil) ∧
      buf = buf.take off ++ chunk ++ buf.drop nextOff := by
  unfold Deployed.LayoutLawful at hLayLaw
  rw [hLayOpt] at hLayLaw
  obtain ⟨wKey, hInW, hFindW⟩ := findLayoutWrite_some hW
  obtain ⟨rKey, hInR, hFindR⟩ := findLayoutRead_some hR
  have hRF : Defs.fnTable M d.admitted.program.defs rRef.hdr rRef.member
      (cast (congrArg (HList M.Val) rRef.insEq.symm) (.cons buf (.cons off .nil))) =
      .done (cast (congrArg (HList M.Val) rRef.outsEq.symm) (.cons v (.cons nextOff .nil))) := by
    have hEq := rRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons buf (.cons off .nil))
    rw [hRead] at hEq
    rcases rRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _⟩
    dsimp only at hIn hOut; cases hIn; cases hOut; exact hEq.symm
  obtain ⟨hV, hLe1, hLe2, chunk, hWF, hBufEq⟩ :=
    hLayLaw.2.1 wKey rKey hInW hInR wRef.hdr rRef.hdr wRef.member rRef.member
      hFindW hFindR unitTy τ wRef.insEq wRef.outsEq rRef.insEq rRef.outsEq
      buf off v nextOff hBuf hOff hRF
  refine ⟨hV, hLe1, hLe2, chunk, ?_, hBufEq⟩
  have hEqW := wRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v .nil)
  rw [hEqW, hWF]
  rcases wRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
  dsimp only at hIn hOut; cases hIn; cases hOut; rfl

theorem layoutLawful_equal_refl {d : Deployed V} {layout : Layout}
    (hLayOpt : d.declaration.layout = some layout) (hLayLaw : d.LayoutLawful M)
    {τ : V.Ty} {eqRef : TypedFnRef V d.admitted.program.headers.fns [τ, τ] [.bool]}
    (hE : findLayoutEqual d.admitted layout.module τ = some eqRef)
    {v : M.Val τ} (hV : M.Valid τ v) :
    eqRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v (.cons v .nil)) =
      .done (.cons true .nil) := by
  unfold Deployed.LayoutLawful at hLayLaw
  rw [hLayOpt] at hLayLaw
  obtain ⟨eqKey, hInE, hFindE⟩ := findLayoutEqual_some hE
  obtain ⟨resH, hDone, _⟩ := eqRef.eval_done M d.admitted (.cons v (.cons v .nil)) ⟨hV, hV, trivial⟩
  cases resH with
  | cons b bn =>
      cases bn
      have hFn : Defs.fnTable M d.admitted.program.defs eqRef.hdr eqRef.member
          (cast (congrArg (HList M.Val) eqRef.insEq.symm) (.cons v (.cons v .nil))) =
          .done (cast (congrArg (HList M.Val) eqRef.outsEq.symm) (.cons b .nil)) := by
        have hEq := eqRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons v (.cons v .nil))
        rw [hDone] at hEq
        rcases eqRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
        dsimp only at hIn hOut; cases hIn; cases hOut; exact hEq.symm
      have hIff := hLayLaw.2.2 eqKey hInE eqRef.hdr eqRef.member hFindE τ
        eqRef.insEq eqRef.outsEq v v b hV hV hFn
      have hb : b = true := hIff.mpr rfl
      subst hb
      exact hDone

/-! ### Mark-peeling helpers for `Proj.begins` and `Proj.settles` -/

private def isRoleMark {A : Type} : Program M A → Prop
  | .call (.begin _) _ => True
  | .call (.settle _) _ => True
  | _ => False

private theorem proj_peel_begin {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Nat → Program M B},
      Proj M r post p (.call (.begin at_) k) → Proj M r post p (k 0)
  | _, _, _, .begins h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_begin h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_begin (h v))

private theorem proj_peel_settle {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Unit → Program M B},
      Proj M r post p (.call (.settle at_) k) → Proj M r post p (k ())
  | _, _, _, .settles h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_settle h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_settle (h v))

private theorem peelMarks_alone {A B σ : Type} {r : Role}
    {h : Handler (RSig M) (RSig M) Stop σ}
    (hMarkPass : ∀ (op : ROp M) (s : σ), (op = .begin (ROp.occurrence M op) ∨ op = .settle (ROp.occurrence M op)) →
      h.clause op s = .call op fun reply => .done (reply, s))
    {post : A → B → Prop} {p : Protocol M A} {events : List (ShapeEvent V)}
    (Q : Program M B → Prop)
    (hBase : ∀ q, ¬ isRoleMark M q → Proj M r post p q →
      q.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      q.SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events) (fun _ => True) (fun _ => True) →
      Q q)
    (hStepBegin : ∀ at_ k, Q (k 0) → Q (.call (.begin at_) k))
    (hStepSettle : ∀ at_ k, Q (k ()) → Q (.call (.settle at_) k)) :
    ∀ {q : Program M B}, Proj M r post p q →
      q.SafeWith M (ValidReply M) (ROp.ValidPayload M) (fun _ => True) (· ≠ .undefined) →
      q.SafeWith M (fun _ _ => True) (ROp.MatchesShape M r events) (fun _ => True) (fun _ => True) →
      Q q
  | .call (.begin at_) k, hProj, hSafe, hShape =>
      hStepBegin at_ k
        (peelMarks_alone hMarkPass Q hBase hStepBegin hStepSettle (proj_peel_begin M hProj)
          (hSafe.2 0 trivial) (hShape.2 0 trivial))
  | .call (.settle at_) k, hProj, hSafe, hShape =>
      hStepSettle at_ k
        (peelMarks_alone hMarkPass Q hBase hStepBegin hStepSettle (proj_peel_settle M hProj)
          (hSafe.2 () trivial) (hShape.2 () trivial))
  | .done _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .halt _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.give ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.get ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.own ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape
  | .call (.hear ..) _, hProj, hSafe, hShape => hBase _ (fun h => h) hProj hSafe hShape

private theorem stack_run_begin {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Nat → Program M B) (s : σ)
    (hPass : h.clause (.begin at_) s = .call (.begin at_) fun n => .done (n, s)) :
    h.run (retryOf M none) (.call (.begin at_) k) s =
      .call (.begin at_) fun n => h.run (retryOf M none) (k n) s := by
  change (h.clause (.begin at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_settle {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Unit → Program M B) (s : σ)
    (hPass : h.clause (.settle at_) s = .call (.settle at_) fun u => .done (u, s)) :
    h.run (retryOf M none) (.call (.settle at_) k) s =
      .call (.settle at_) fun u => h.run (retryOf M none) (k u) s := by
  change (h.clause (.settle at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_own {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (gkind : GivenKind V) (hearers : List Role) (at_ : Occurrence)
    (gIns : List V.Ty) (payload : HList M.Val gIns) (τ : V.Ty)
    (k : M.Val τ → Program M B) (s : σ)
    (hPass : h.clause (.own gkind hearers at_ gIns payload τ) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w => .done (w, s)) :
    h.run (retryOf M none) (.call (.own gkind hearers at_ gIns payload τ) k) s =
      .call (.own gkind hearers at_ gIns payload τ) fun w => h.run (retryOf M none) (k w) s := by
  change (h.clause (.own gkind hearers at_ gIns payload τ) s).bind
    (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

private theorem stack_run_clause_done {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (op : ROp M) (k : (RSig M).Reply op → Program M B) (s s' : σ) (reply : (RSig M).Reply op)
    (hStep : h.clause op s = .done (reply, s')) :
    h.run (retryOf M none) (.call op k) s = h.run (retryOf M none) (k reply) s' := by
  change (h.clause op s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hStep]
  rfl

private theorem layer_cast_state {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) : (h ▸ l).state = l.state := by
  subst h; rfl

private theorem layer_cast_clauses {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) :
    (layer_cast_state h l) ▸ (h ▸ l).clauses = l.clauses := by
  subst h; rfl

private theorem ins_cast_valid {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (LVal M) hdr₁.ins) (hv : ins.All (fun a v => M.Valid a.ty v)) :
    (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) h) ins).All (fun a v => M.Valid a.ty v) := by
  subst h; exact hv

theorem insRV_cast_valid {r : Role} {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (RV M r) hdr₁.ins) (hv : ins.All (RV.Valid M r)) :
    (cast (congrArg (fun hdr => HList (RV M r) hdr.ins) h) ins).All (RV.Valid M r) := by
  subst h; exact hv

private theorem alone_cast_stack1 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (l : Layer V a.program.headers r hdr₂.ins)
    {st : V.Ty} (hSt : l.state = st) {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B} {s0 s1 : M.Val st}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [hE ▸ l]).run
        (retryOf M none) p (.cons ((layer_cast_state hE l).trans hSt ▸ s0) .nil))
      rec (.returned (out, .cons ((layer_cast_state hE l).trans hSt ▸ s1) .nil))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hE ▸ [l])).run
        (retryOf M none) p (cast (by subst hE; subst hSt; rfl) (HList.cons s0 HList.nil)))
      rec (.returned (out, cast (by subst hE; subst hSt; rfl) (HList.cons s1 HList.nil))) := by
  subst hE; subst hSt; exact hAl

private theorem alone_cast_stack2 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (hE : hdr₁ = hdr₂) (c l : Layer V a.program.headers r hdr₂.ins)
    {stC stL : V.Ty} (hStC : c.state = stC) (hStL : l.state = stL)
    {B : Type} {source : Source M} {p : Program M B}
    {rec : List (Happened M)} {out : B} {c0 c1 : M.Val stC} {l0 l1 : M.Val stL}
    (hAl : Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [hE ▸ c, hE ▸ l]).run
        (retryOf M none) p (.cons ((layer_cast_state hE c).trans hStC ▸ c0)
          (.cons ((layer_cast_state hE l).trans hStL ▸ l0) .nil)))
      rec (.returned (out, .cons ((layer_cast_state hE c).trans hStC ▸ c1)
        (.cons ((layer_cast_state hE l).trans hStL ▸ l1) .nil)))) :
    Alone M source r
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) (hE ▸ [c, l])).run
        (retryOf M none) p (cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c0 (HList.cons l0 HList.nil))))
      rec (.returned (out, cast (by subst hE; subst hStC; subst hStL; rfl) (HList.cons c1 (HList.cons l1 HList.nil)))) := by
  subst hE; subst hStC; subst hStL; exact hAl

theorem stack_finish_one {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l : Layer V hs r ins) (s : M.Val l.state) :
    Stack.finish M fnTable [l] (.cons s .nil) =
      (liftLocal id (l.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s .nil)))).bind
        fun mine => .done (mine.append .nil) := rfl

theorem stack_finish_two {hs : Headers V} (fnTable : FnTable M hs.fns)
    {r : Role} {ins : List (LTy V)} (l₁ l₂ : Layer V hs r ins)
    (s₁ : M.Val l₁.state) (s₂ : M.Val l₂.state) :
    Stack.finish M fnTable [l₁, l₂] (.cons s₁ (.cons s₂ .nil)) =
      (liftLocal id (l₁.finish.denote (localSem M hs.fns fnTable) [] (Env.positional (.cons s₁ .nil)))).bind
        fun m₁ =>
          ((liftLocal id (l₂.finish.denote (localSem M hs.fns fnTable) []
            (Env.positional (.cons s₂ .nil)))).bind fun m₂ => .done (m₂.append .nil)).map
            fun others => m₁.append others := rfl

private theorem alone_deployed_run_congr {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
    (hRet : d.retry = none) {r : Role} {s : List (Layer V a.program.headers r d.entry.ins)}
    (hSt : hA ▸ d.stack r = s)
    {source : Source M} {ins : HList (RV M r) d.entry.ins}
    {t₁ : HList M.Val (Stack.Takes (d.stack r))} {t₂ : HList M.Val (Stack.Takes s)}
    (hT : HEq t₁ t₂)
    {rec : List (Happened M)} {out : HList (RV M r) d.entry.outs}
    {g₁ : HList M.Val (Stack.Gives (d.stack r))} {g₂ : HList M.Val (Stack.Gives s)}
    (hG : HEq g₁ g₂)
    (hRun : Alone M source r (runStack a M (hA ▸ d.callee) none r s ins t₂) rec (.returned (out, g₂))) :
    Alone M source r (d.run M r ins t₁) rec (.returned (out, g₁)) := by
  cases d; dsimp only at hA; subst hA
  dsimp only [Deployed.run, runStack, Deployed.callee, Deployed.entry] at hSt hRun ⊢
  subst hSt; rw [hRet]; cases eq_of_heq hT; cases eq_of_heq hG; exact hRun

theorem ideal_deployed_run_congr {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
    (hRet : d.retry = none) {r : Role} {s : List (Layer V a.program.headers r d.entry.ins)}
    (hSt : hA ▸ d.stack r = s)
    {ins : HList (RV M r) d.entry.ins}
    {t₁ : HList M.Val (Stack.Takes (d.stack r))} {t₂ : HList M.Val (Stack.Takes s)}
    (hT : HEq t₁ t₂)
    {hG₁ : Stack.Gives (d.stack r) = []} {hG₂ : Stack.Gives s = []}
    (serviceKey : Key)
    (oracle : (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (M.Val τ)) :
    (Process.answerService serviceKey oracle (d.run M r ins t₁)).map
      (fun out => (out.1, cast (congrArg (HList M.Val) hG₁) out.2)) =
    (Process.answerService serviceKey oracle (runStack a M (hA ▸ d.callee) none r s ins t₂)).map
      (fun out => (out.1, cast (congrArg (HList M.Val) hG₂) out.2)) := by
  cases d; dsimp only at hA; subst hA
  dsimp only [Deployed.run, runStack, Deployed.callee, Deployed.entry] at hSt ⊢
  subst hSt; rw [hRet]; cases eq_of_heq hT; rfl

/-! ### Coupled prover-verifier-protocol simulation for streaming `.derived` and `.authored` -/

private theorem mem_heardCoins_of_event {s : Shape V} {e : ShapeEvent V}
    (hE : e ∈ s.events [] id) {law : V.LawKey} {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) :
    e.site ∈ s.heardCoins := by
  unfold Shape.heardCoins
  exact List.mem_filterMap.mpr ⟨e, hE, by simp [hCls]⟩

private theorem simulate_derived {d : Deployed V} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {layout : Layout} {stateTy suiteUnitTy unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {absRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy, .seq suiteUnitTy none] [stateTy]}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {conP : Layer V d.admitted.program.headers prover d.entry.ins}
    {conV : Layer V d.admitted.program.headers verifier d.entry.ins}
    {layP : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hConDecl : d.declaration.construction = .derived suite sessionTag)
    (hLayDecl : d.declaration.layout = some layout)
    (hSuiteLaw : d.SuiteLawful M) (hLayLaw : d.LayoutLawful M)
    (hConPState : conP.state = stateTy) (hConVState : conV.state = stateTy)
    (hLayPState : layP.state = .seq unitTy none) (hLayVState : layV.state = streamStateTy unitTy)
    {cS : List (Clause V d.admitted.program.headers prover .nat)}
    (hCC : buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy absRef prover verifier
      none declKey (d.entry.shape.events [] id) 0
      (d.entry.shape.eventsWithAbsorb prover verifier [] id false) =
      .ok (hConPState ▸ conP.clauses, hConVState ▸ conV.clauses, cS))
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLayPState ▸ layP.clauses, hLayVState ▸ layV.clauses)) :
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pP : Program M BP) (pV : Program M BV)
      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M),
      M.Valid stateTy st → (∀ u ∈ buf, M.Valid unitTy u) →
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
      ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy) (suffix : List (M.Val unitTy))
        (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
            (Defs.rTable M d.admitted.program.defs) [conP, layP]).run (retryOf M none) pP
              (.cons (hConPState.symm ▸ st) (.cons (hLayPState.symm ▸ buf) .nil)))
          recP (.returned (outP, .cons (hConPState.symm ▸ finalSt) (.cons (hLayPState.symm ▸ (buf ++ suffix)) .nil))) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [conV, layV]).run (retryOf M none) pV
                (.cons (hConVState.symm ▸ st) (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil)))
            recV (.returned (outV, .cons (hConVState.symm ▸ finalSt)
              (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil)))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' p (.returned a) := by
  cases conP with
  | mk cPLine cPSt cPTakes cPGives cPClauses cPAgain cPStart cPFin =>
      cases conV with
      | mk cVLine cVSt cVTakes cVGives cVClauses cVAgain cVStart cVFin =>
          cases layP with
          | mk lPLine lPSt lPTakes lPGives lPClauses lPAgain lPStart lPFin =>
              cases layV with
              | mk lVLine lVSt lVTakes lVGives lVClauses lVAgain lVStart lVFin =>
                  dsimp only at hConPState hConVState hLayPState hLayVState
                  subst cPSt; subst cVSt; subst lPSt; subst lVSt
                  dsimp only at hCC hSL
                  let conP' : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨cPLine, stateTy, cPTakes, cPGives, cPClauses, cPAgain, cPStart, cPFin⟩
                  let conV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨cVLine, stateTy, cVTakes, cVGives, cVClauses, cVAgain, cVStart, cVFin⟩
                  let layP' : Layer V d.admitted.program.headers prover d.entry.ins :=
                    ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPClauses, lPAgain, lPStart, lPFin⟩
                  let layV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
                    ⟨lVLine, streamStateTy unitTy, lVTakes, lVGives, lVClauses, lVAgain, lVStart, lVFin⟩
                  let fnTable := Defs.fnTable M d.admitted.program.defs
                  let rTable := Defs.rTable M d.admitted.program.defs
                  let events := d.entry.shape.events [] id
                  let eventsAbs := d.entry.shape.eventsWithAbsorb prover verifier [] id false
                  have hFst : eventsAbs.map Prod.fst = events :=
                    eventsWithAbsorb_fst prover verifier [] id false d.entry.shape
                  have hConUnm := fun op hCl =>
                    construction_clauses_unmatched_closed M 0 eventsAbs hCC op hCl
                  have hLayUnm := fun op hCl =>
                    streaming_layout_unmatched_closed M 0 events hSL op hCl
                  have hPassP : ∀ op (st : M.Val stateTy) (buf : List (M.Val unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conP', layP']).clause op (.cons st (.cons buf .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons buf .nil)) := fun op st buf hCl =>
                    stack2_clause_pass M fnTable rTable conP' layP' op st buf
                      (clause_answer_unmatched_all M fnTable rTable op st cPClauses (hConUnm op hCl).1)
                      (clause_answer_unmatched_all M fnTable rTable op buf lPClauses (hLayUnm op hCl).1)
                  have hPassV : ∀ op (st : M.Val stateTy) (lst : M.Val (streamStateTy unitTy)),
                      ROp.IsClosed M op →
                      (Stack.handler M fnTable rTable [conV', layV']).clause op (.cons st (.cons lst .nil)) =
                        .call op fun reply => .done (reply, .cons st (.cons lst .nil)) := fun op st lst hCl =>
                    stack2_clause_pass M fnTable rTable conV' layV' op st lst
                      (clause_answer_unmatched_all M fnTable rTable op st cVClauses (hConUnm op hCl).2)
                      (clause_answer_unmatched_all M fnTable rTable op lst lVClauses (hLayUnm op hCl).2)
                  have hEventDisc : ∀ e ∈ events,
                      (match e.cls with
                       | .flow _ giver getters =>
                           (giver = prover ∧ verifier ∈ getters) ∨
                           (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                       | .given (.coin law) owner hearers =>
                           (owner = verifier ∧ prover ∈ hearers ∧
                             ∃ sig, V.law law = some sig ∧ sig.out = e.τ ∧ sig.ins = []) ∨
                           hearers = []
                       | .given (.request _) owner hearers =>
                           (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers)) := by
                    have hGo : ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)) {cP' cV' cS'},
                        buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy absRef
                          prover verifier none declKey events idx es = .ok (cP', cV', cS') →
                        ∀ p ∈ es, match p.1.cls with
                          | .flow _ giver getters =>
                              (giver = prover ∧ verifier ∈ getters) ∨
                              (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                          | .given (.coin law) owner hearers =>
                              (owner = verifier ∧ prover ∈ hearers ∧
                                ∃ sig, V.law law = some sig ∧ sig.out = p.1.τ ∧ sig.ins = []) ∨
                              hearers = []
                          | .given (.request _) owner hearers =>
                              (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
                      intro idx es
                      induction es generalizing idx with
                      | nil => intro _ _ _ _ _ hp; cases hp
                      | cons p rest ih =>
                          intro cP' cV' cS' hGo' p' hp'
                          unfold buildConstructionClauses.go at hGo'
                          cases hRec : buildConstructionClauses.go d.admitted suite stateTy suiteUnitTy
                              absRef prover verifier none declKey events (idx + 1) rest with
                          | error _ => rw [hRec] at hGo'; cases hGo'
                          | ok tr =>
                              rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
                              rcases List.mem_cons.mp hp' with rfl | hmem
                              · cases hCls : p'.1.cls with
                                | flow _ giver getters =>
                                    rw [hCls] at hGo'; dsimp only at hGo'
                                    split at hGo'
                                    · exact .inl ‹_›
                                    · split at hGo'
                                      · exact .inr ‹_›
                                      · cases hGo'
                                | given gkind owner hearers =>
                                    rw [hCls] at hGo'
                                    cases gkind with
                                    | coin law =>
                                        dsimp only at hGo'
                                        split at hGo'
                                        · rename_i hC
                                          cases hLaw : V.law law with
                                          | none => rw [hLaw] at hGo'; cases hGo'
                                          | some sig =>
                                              rw [hLaw] at hGo'; dsimp only at hGo'
                                              split at hGo'
                                              · rename_i hOut
                                                cases hDer : findSuiteDerive d.admitted suite stateTy sig.ins p'.1.τ with
                                                | none => rw [hDer] at hGo'; cases hGo'
                                                | some _ =>
                                                    rw [hDer] at hGo'; dsimp only at hGo'
                                                    split at hGo'
                                                    · rename_i hIns; exact .inl ⟨hC.1, hC.2, sig, hLaw, hOut, hIns⟩
                                                    · cases hGo'
                                              · cases hGo'
                                        · split at hGo'
                                          · exact .inr ‹_›
                                          · cases hGo'
                                    | request _ =>
                                        dsimp only at hGo'
                                        split at hGo'
                                        · rename_i hReq; exact hReq
                                        · cases hGo'
                              · exact ih (idx + 1) hRec p' hmem
                    intro e he
                    rw [← hFst] at he
                    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
                    exact hGo 0 eventsAbs hCC p hp
                  intro A BP BV p
                  let SimGoal := fun (p0 : Protocol M A) (postP : A → BP → Prop) (postV : A → BV → Prop)
                      (st : M.Val stateTy) (buf : List (M.Val unitTy)) (source : Source M)
                      (qP : Program M BP) (qV : Program M BV) =>
                    ∃ (a : A) (outP : BP) (outV : BV) (finalSt : M.Val stateTy) (suffix : List (M.Val unitTy))
                      (recP : List (Happened M)) (source' : Source M),
                      (∀ u ∈ suffix, M.Valid unitTy u) ∧
                      Alone M source prover
                        ((Stack.handler M fnTable rTable [conP', layP']).run (retryOf M none) qP
                            (.cons st (.cons buf .nil)))
                        recP (.returned (outP, .cons finalSt (.cons (buf ++ suffix) .nil))) ∧
                      (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                        ∃ recV, Alone M source verifier
                          ((Stack.handler M fnTable rTable [conV', layV']).run (retryOf M none) qV
                              (.cons st (.cons (buf ++ suffix ++ post, (buf.length, ())) .nil)))
                          recV (.returned (outV, .cons finalSt
                            (.cons (buf ++ suffix ++ post, (buf.length + suffix.length, ())) .nil)))) ∧
                      postP a outP ∧ postV a outV ∧
                      Lawful M source' p0 ∧
                      (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
                      GExec M source' p0 (.returned a)
                  induction p with
                  | done a =>
                      intro postP postV pP pV st buf source hStV hBufV hProjP hProjV hSafeP hSafeV hShapeP hShapeV _ _ _ _ _
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conP', layP'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons buf' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ _ trivial)
                        (fun qP => SimGoal (.done a) postP postV st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, fSt, suf, .began prover at_ :: recP, src', h1,
                            by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a', outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1,
                            by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      cases hPP with
                      | done hPostP =>
                          refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV', layV'])
                            (fun op s hM => by
                              cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                            (fun qV => SimGoal (.done a) postP postV st buf source (.done _) qV)
                            (fun qV hNotMV hPV hSV hShV => ?_)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.began verifier at_ :: recV,
                                    by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            (fun at_ kV h => by
                              obtain ⟨a', outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                              exact ⟨a', outP, outV, fSt, suf, recP, src', h1, h2,
                                fun post hPost =>
                                  let ⟨recV, hAlV⟩ := h3 post hPost
                                  ⟨.settled verifier at_ :: recV,
                                    by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                                h4, h5, h6, h7, h8⟩)
                            hProjV hSafeV hShapeV
                          cases hPV with
                          | done hPostV =>
                              exact ⟨a, _, _, st, [], [], source, (fun _ h => nomatch h),
                                by simpa [Handler.run] using Alone.done,
                                fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                                hPostP, hPostV, trivial, fun _ _ _ => rfl, ⟨[], .done⟩⟩
                          | begins _ => exact False.elim (hNotMV trivial)
                          | settles _ => exact False.elim (hNotMV trivial)
                      | begins _ => exact False.elim (hNotMP trivial)
                      | settles _ => exact False.elim (hNotMP trivial)
                  | halt payload =>
                      intro _ _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ _ hNoHalt
                      obtain ⟨a, hContra⟩ := hNoHalt source trivial (fun _ _ _ => rfl)
                        (.stopped payload.1 payload.2) ⟨[], .halt⟩
                      cases hContra
                  | call op k ih =>
                      intro postP postV pP pV st buf source hStV hBufV hProjP hProjV hSafeP hSafeV
                        hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conP', layP'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons buf' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ _ trivial)
                        (fun qP => SimGoal (.call op k) postP postV st buf source qP pV)
                        (fun qP hNotMP hPP hSP hShP => ?_)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, .began prover at_ :: recP, src', h1,
                            by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .begin h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        (fun at_ kP h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, .settled prover at_ :: recP, src', h1,
                            by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ _ trivial)]; exact .settle h2,
                            h3, h4, h5, h6, h7, h8⟩)
                        hProjP hSafeP hShapeP
                      refine peelMarks_alone M (h := Stack.handler M fnTable rTable [conV', layV'])
                        (fun op s hM => by
                          cases s with | cons st' s1 => cases s1 with | cons lst' sn => cases sn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ _ trivial)
                        (fun qV => SimGoal (.call op k) postP postV st buf source qP qV)
                        (fun qV hNotMV hPV hSV hShV => ?_)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.began verifier at_ :: recV,
                                by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .begin hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        (fun at_ kV h => by
                          obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                          exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2,
                            fun post hPost =>
                              let ⟨recV, hAlV⟩ := h3 post hPost
                              ⟨.settled verifier at_ :: recV,
                                by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ _ trivial)]; exact .settle hAlV⟩,
                            h4, h5, h6, h7, h8⟩)
                        hProjV hSafeV hShapeV
                      cases op with
                      | flow kind giver getters at_ τ x =>
                          have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                              (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                              ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := by
                            intro source₁ hL₁ hAg e ⟨evs, hRun⟩
                            exact hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                          cases hPP with
                          | begins _ => exact False.elim (hNotMP trivial)
                          | settles _ => exact False.elim (hNotMP trivial)
                          | gave hNotIn hPP' =>
                              obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
                              have hDisc := hEventDisc eP hEP
                              rw [hClsP] at hDisc
                              have hVin : verifier ∈ getters := by
                                rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
                                · exact hV
                                · exact absurd rfl hNotP
                              have hMsgV : M.Valid τ x := hSP.1
                              cases hPV with
                              | begins _ => exact False.elim (hNotMV trivial)
                              | settles _ => exact False.elim (hNotMV trivial)
                              | gave _ _ => exact absurd rfl hNe
                              | passed _ hVOut _ => exact absurd hVin hVOut
                              | got _ _ hPV' =>
                                  have hEPInAbs : ∃ bP, (eP, bP) ∈ eventsAbs := by
                                    have hM : eP ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEP
                                    obtain ⟨⟨e₀, b₀⟩, hIn, hEq⟩ := List.mem_map.mp hM
                                    dsimp only at hEq; subst hEq
                                    exact ⟨b₀, hIn⟩
                                  obtain ⟨needP, hNeedP⟩ := hEPInAbs
                                  obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                                    streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                                      kind getters ⟨at_.path, at_.site.key⟩ τ x buf hMsgV
                                      ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                                  have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                                    intro u hu
                                    rcases List.mem_append.mp hu with h1 | h2
                                    · exact hBufV u h1
                                    · exact hChV u h2
                                  cases needP with
                                  | true =>
                                      obtain ⟨encP, enc, st', hEncFindP, hEncD, hAbsD, hSt'V, hConPAns⟩ :=
                                        construction_clauses_answer_prover_flow_abs M 0 eventsAbs hCC
                                          kind getters at_ τ x st hMsgV hStV ⟨eP, hNeedP, hSiteP, hTyP, hClsP⟩
                                      obtain ⟨encV, hEncFindV, hConVAns⟩ :=
                                        construction_clauses_answer_verifier_flow_abs M 0 eventsAbs hCC
                                          kind at_ τ st ⟨eP, hNeedP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                      have hEncEq : encP = encV := Option.some.inj (hEncFindP.symm.trans hEncFindV)
                                      subst hEncEq
                                      obtain ⟨rRef, hRFind, _⟩ :=
                                        streaming_layout_answer_verifier_flow M 0 events hSL
                                          kind ⟨at_.path, at_.site.key⟩ τ buf buf.length
                                          ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih () _ _ st' (buf ++ chunk) source hSt'V hBufChV hPP' hPV'
                                          (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                                          (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.give kind getters at_ τ x) (.cons st (.cons buf .nil)) =
                                          .done ((), .cons st' (.cons (buf ++ chunk) .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st st' buf (buf ++ chunk)
                                          () () _ hConPAns hLayPAns rfl
                                      refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src', ?_, ?_, ?_,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        simpa [List.append_assoc] using hAlP
                                      · intro post hPost
                                        have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                          intro u hu
                                          rcases List.mem_append.mp hu with h1 | h2
                                          · exact hSufV u h1
                                          · exact hPost u h2
                                        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                                          hMsgV hBufV hSufPostV hWD
                                        have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                                          simp [List.append_assoc]
                                        obtain ⟨rRef', hRFind', hLayVAns'⟩ :=
                                          streaming_layout_answer_verifier_flow M 0 events hSL
                                            kind ⟨at_.path, at_.site.key⟩ τ
                                            (buf ++ chunk ++ (suf' ++ post)) buf.length
                                            ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                        have hREq : rRef = rRef' := Option.some.inj (hRFind.symm.trans hRFind')
                                        subst hREq
                                        have hLayVDone := hLayVAns' x (buf.length + chunk.length) hRD
                                        have hKV :
                                            ((((liftLocal (S := RSig M) id (encP.eval M fnTable (.cons x .nil))).bind fun enc0 =>
                                              (liftLocal (S := RSig M) id (absRef.eval M fnTable
                                                (.cons st (.cons (msgLabel at_.site) (.cons enc0.single .nil))))).map
                                                fun nextSt => aloneIn M verifier (.cons x nextSt)).mapHalt
                                                  fun why => (why, st)).map fun out =>
                                              let values := HList.split [τ] (aloneOut M verifier out)
                                              (values.1.single, values.2.single)) =
                                            .done (x, st') := by
                                          rw [hEncD]
                                          simp only [liftLocal_done, Process.bind, HList.single]
                                          rw [hAbsD]
                                          simp only [liftLocal_done, Process.map, Process.mapHalt,
                                            aloneOut_aloneIn, HList.split]
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.get kind prover at_ τ)
                                            (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (x, .cons st' (.cons (buf ++ chunk ++ (suf' ++ post),
                                              (buf.length + chunk.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st st'
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ()))
                                            x x _ hConVAns hLayVDone hKV
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        rw [hBufEq]
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        have hLenEq : buf.length + (chunk ++ suf').length =
                                            (buf ++ chunk).length + suf'.length := by
                                          simp [List.length_append, Nat.add_assoc]
                                        have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                                          simp [List.append_assoc]
                                        rw [hLenEq, hBufEq2, ← List.length_append]
                                        exact hAlV'
                                  | false =>
                                      -- Trailing message elided in lockstep on both prover and verifier!
                                      have hNoAbs : ∀ e' b', (e', b') ∈ eventsAbs → e'.site = at_.site →
                                          e'.τ = τ → (∃ gs, verifier ∈ gs ∧ e'.cls = .flow kind prover gs) →
                                          b' = false := by
                                        intro e' b' hIn hS hT ⟨gs, hVg, hC⟩
                                        exact eventsWithAbsorb_flow_consistent prover verifier [] id false
                                          d.entry.shape hIn hNeedP (hS.trans hSiteP.symm)
                                          (hT.trans hTyP.symm) hC hVg hClsP hVin
                                      obtain ⟨hUnmP, hUnmV⟩ :=
                                        construction_clauses_unmatched_elided_flow M 0 eventsAbs hCC
                                          kind getters at_ τ x hNoAbs
                                      have hConPPass : Clause.answer M fnTable rTable cPClauses
                                          (.give kind getters at_ τ x) st =
                                          .call (.give kind getters at_ τ x) fun reply => .done (reply, st) :=
                                        clause_answer_unmatched_all M fnTable rTable _ st cPClauses hUnmP
                                      have hConVPass : Clause.answer M fnTable rTable cVClauses
                                          (.get kind prover at_ τ) st =
                                          .call (.get kind prover at_ τ) fun reply => .done (reply, st) :=
                                        clause_answer_unmatched_all M fnTable rTable _ st cVClauses hUnmV
                                      obtain ⟨wRef', chunk', hWFind', hWD', hChV', hLayPAns'⟩ :=
                                        streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                                          kind getters at_ τ x buf hMsgV
                                          ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                                      have hBufChV' : ∀ u ∈ buf ++ chunk', M.Valid unitTy u := by
                                        intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hBufV u h1
                                        · exact hChV' u h2
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih () _ _ st (buf ++ chunk') source hStV hBufChV' hPP' hPV'
                                          (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                                          (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.give kind getters at_ τ x) (.cons st (.cons buf .nil)) =
                                          .done ((), .cons st (.cons (buf ++ chunk') .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st st buf (buf ++ chunk')
                                          () () _ hConPPass hLayPAns' rfl
                                      refine ⟨a, outP, outV, fSt, chunk' ++ suf', recP, src', ?_, ?_, ?_,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV' u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        simpa [List.append_assoc] using hAlP
                                      · intro post hPost
                                        have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                          intro u hu
                                          rcases List.mem_append.mp hu with h1 | h2
                                          · exact hSufV u h1
                                          · exact hPost u h2
                                        obtain ⟨rRef', hRFind', hLayVAns'⟩ :=
                                          streaming_layout_answer_verifier_flow M 0 events hSL
                                            kind at_ τ (buf ++ chunk' ++ (suf' ++ post)) buf.length
                                            ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                                        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind' hRFind'
                                          hMsgV hBufV hSufPostV hWD'
                                        have hLayVDone := hLayVAns' x (buf.length + chunk'.length) hRD
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.get kind prover at_ τ)
                                            (.cons st (.cons (buf ++ chunk' ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (x, .cons st (.cons (buf ++ chunk' ++ (suf' ++ post),
                                              (buf.length + chunk'.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st st
                                            (buf ++ chunk' ++ (suf' ++ post), (buf.length, ()))
                                            (buf ++ chunk' ++ (suf' ++ post), (buf.length + chunk'.length, ()))
                                            x x _ hConVPass hLayVDone rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        have hBufEq : buf ++ (chunk' ++ suf') ++ post = buf ++ chunk' ++ (suf' ++ post) := by
                                          simp [List.append_assoc]
                                        rw [hBufEq]
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        have hLenEq : buf.length + (chunk' ++ suf').length =
                                            (buf ++ chunk').length + suf'.length := by
                                          simp [List.length_append, Nat.add_assoc]
                                        have hBufEq2 : buf ++ chunk' ++ (suf' ++ post) = (buf ++ chunk') ++ suf' ++ post := by
                                          simp [List.append_assoc]
                                        rw [hLenEq, hBufEq2, ← List.length_append]
                                        exact hAlV'
                          | got hGNeP hPIn _ =>
                              obtain ⟨eP, hEP, _, _, _, gs', hPin', hClsP⟩ := hShP.1
                              have hDisc := hEventDisc eP hEP
                              rw [hClsP] at hDisc
                              rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
                              · exact absurd hEqP hGNeP
                              · exact absurd hPin' hNotP
                          | passed hGNeP hPOut hPP' =>
                              cases hPV with
                              | begins _ => exact False.elim (hNotMV trivial)
                              | settles _ => exact False.elim (hNotMV trivial)
                              | gave _ _ =>
                                  obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
                                  have hDisc := hEventDisc eV hEV
                                  rw [hClsV] at hDisc
                                  rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                                  · exact absurd hEqP.symm hNe
                                  · exact absurd rfl hNotV
                              | got _ hVin _ =>
                                  obtain ⟨eV, hEV, _, _, _, gs', hVin', hClsV⟩ := hShV.1
                                  have hDisc := hEventDisc eV hEV
                                  rw [hClsV] at hDisc
                                  rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
                                  · exact absurd hEqP hGNeP
                                  · exact absurd hVin' hNotV
                              | passed _ _ hPV' =>
                                  obtain ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                                    ih () _ _ st buf source hStV hBufV hPP' hPV' hSP hSV hShP hShV
                                      (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                                  exact ⟨a, outP, outV, fSt, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
                      | given gkind owner hearers at_ gIns payload τ =>
                          have hCoinDec : Decidable (∃ law, gkind = .coin law) :=
                            match gkind with
                            | .coin law => isTrue ⟨law, rfl⟩
                            | .request _ => isFalse fun ⟨_, h⟩ => nomatch h
                          have hHeardDec : Decidable ((∃ law, gkind = .coin law) ∧ owner = verifier ∧ prover ∈ hearers) :=
                            @instDecidableAnd _ _ hCoinDec (@instDecidableAnd _ _ inferInstance inferInstance)
                          cases hHeardDec with
                          | isTrue hHeardCoin =>
                            obtain ⟨⟨law, rfl⟩, hOwV, hPin⟩ := hHeardCoin
                            subst owner
                            have hNonEmpty : ∃ h0 hs, hearers = h0 :: hs := by
                              cases hearers with
                              | nil => cases hPin
                              | cons h0 hs => exact ⟨h0, hs, rfl⟩
                            obtain ⟨h0, hs, hHCons⟩ := hNonEmpty
                            cases hPP with
                            | begins _ => exact False.elim (hNotMP trivial)
                            | settles _ => exact False.elim (hNotMP trivial)
                            | owned _ => exact absurd rfl hNe
                            | unheard _ hOut _ => exact absurd hPin hOut
                            | heard _ _ hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | heard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | unheard hNeSelf _ _ => exact absurd rfl hNeSelf
                                | owned hPV' =>
                                    obtain ⟨eV, hEV, hSiteV, hTyV, hClsV, hTypedV⟩ := hShV.1
                                    have hDisc := hEventDisc eV hEV
                                    rw [hClsV] at hDisc
                                    have hGInsNil : gIns = [] := by
                                      rcases hDisc with ⟨_, _, sig, hLaw, _, hSigIns⟩ | hNil
                                      · obtain ⟨s, hsLaw, hsIns, _⟩ := hTypedV
                                        rw [hLaw] at hsLaw; cases hsLaw
                                        rw [← hsIns, hSigIns]
                                      · subst hNil; cases hPin
                                    subst hGInsNil
                                    cases payload
                                    have hEVAbs : ∃ p ∈ eventsAbs, p.1 = eV := by
                                      have hM : eV ∈ eventsAbs.map Prod.fst := hFst.symm ▸ hEV
                                      obtain ⟨p, hp, hEq⟩ := List.mem_map.mp hM
                                      exact ⟨p, hp, hEq⟩
                                    obtain ⟨pV, hpV, hpVEq⟩ := hEVAbs
                                    have hSuf0 : ∀ k p, eventsAbs[k]? = some p → events[0 + k]? = some p.1 := by
                                      intro k p hk
                                      rw [Nat.zero_add, ← hFst, List.getElem?_map, hk]; rfl
                                    obtain ⟨idxP, ⟨ePSite, ePCls, ePτ⟩, derP, coinP, stP', hIdxP, hSiteP, hTyP,
                                      ⟨hsP, hPinP, hClsP⟩, hDerFindP, hDerDP, hCoinPV, hStP'V, hConPAns⟩ :=
                                      construction_clauses_answer_prover_coin M 0 eventsAbs hSuf0 hCC
                                        law at_ τ st hStV
                                        ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV,
                                          hearers, hPin, hpVEq.symm ▸ hClsV⟩
                                    obtain ⟨idxV, ⟨eV'Site, eV'Cls, eV'τ⟩, derV, coinV, stV', hIdxV, hSiteV', hTyV',
                                      hClsV', hLawV', hDerFindV, hDerDV, hCoinVV, hStV'V, hConVAns⟩ :=
                                      construction_clauses_answer_verifier_coin M 0 eventsAbs hSuf0 hCC
                                        law hearers at_ τ st hStV
                                        ⟨pV, hpV, hpVEq.symm ▸ hSiteV, hpVEq.symm ▸ hTyV,
                                          hPin, hpVEq.symm ▸ hClsV⟩
                                    dsimp only at hSiteP hTyP hClsP hSiteV' hTyV' hClsV'
                                    subst ePτ; subst eV'τ
                                    have hDerEq : derP = derV := Option.some.inj (hDerFindP.symm.trans hDerFindV)
                                    subst hDerEq
                                    have hEvalEq : Process.done (HList.cons coinP (HList.cons stP' HList.nil)) =
                                        .done (.cons coinV (.cons stV' .nil)) := hDerDP.symm.trans hDerDV
                                    cases hEvalEq
                                    have hAllowsCoin : Allows M (.coin law) [] .nil τ coinP :=
                                      suiteLawful_allows M hConDecl hSuiteLaw hDerFindV
                                        (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV') rfl hLawV'
                                        hStV (drawLabel_bytes at_.site) hDerDV
                                    have hAtHeard : at_.site ∈ d.entry.shape.heardCoins := by
                                      rw [← hSiteV']
                                      exact mem_heardCoins_of_event (List.mem_of_getElem? hIdxV) (hHCons ▸ hClsV')
                                    have hLP' : LawfulPrivate M source (k coinP) := by
                                      subst hHCons; exact hLP coinP hAllowsCoin
                                    have hFed' : Fed M source (k coinP) := by
                                      subst hHCons; exact hFed coinP hAllowsCoin
                                    have hOccK : Protocol.OccsIn M (· ≠ at_) (k coinP) := (hUniq coinP).1
                                    have hNoHalt' : ∀ source₁, Lawful M source₁ (k coinP) →
                                        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                          source₁ at' τ' = source at' τ') →
                                        ∀ e, GExec M source₁ (k coinP) e → ∃ a, e = .returned a := by
                                      intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                                      let source₂ := patchSource M source₁ at_ τ coinP
                                      have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M source₁ at_ τ coinP hne τ').symm
                                      have hL₂ : Lawful M source₂ (.call (.given (.coin law) verifier hearers at_ [] .nil τ) k) := by
                                        intro v hv
                                        dsimp only [source₂] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgree12 hOccK hL₁⟩
                                      have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                          source₂ at' τ' = source at' τ' := by
                                        intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [source₂]
                                        rw [patchSource_ne M source₁ at_ τ coinP hne τ']
                                        exact hAg₁ at' τ' hNotIn
                                      have hRun₂ : GRun M source₂
                                          (.call (.given (.coin law) verifier hearers at_ [] .nil τ) k) _ e :=
                                        .given (patchSource_self M source₁ at_ τ coinP)
                                          (grun_of_agree M hAgree12 hOccK hRun₁)
                                      exact hNoHalt source₂ hL₂ hAg₂ e ⟨_, hRun₂⟩
                                    have hToldSiteP : (⟨at_.path, drawToldKey events idxP⟩ : Occurrence).site =
                                        ⟨ePSite.through, drawToldKey events (0 + idxP)⟩ := by
                                      simpa using site_told_from_match hSiteP (k := drawToldKey events idxP)
                                    have hToldSiteV : (⟨at_.path, drawToldKey events idxV⟩ : Occurrence).site =
                                        ⟨eV'Site.through, drawToldKey events (0 + idxV)⟩ := by
                                      simpa using site_told_from_match hSiteV' (k := drawToldKey events idxV)
                                    have hCarryP := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
                                      idxP ⟨ePSite, ePCls, τ⟩ hIdxP law hsP ⟨at_.path, drawToldKey events idxP⟩
                                      coinP hClsP hPinP hToldSiteP hCoinPV
                                    have hCarryV := streaming_layout_answer_told M 0 events (fun _ h => h) hSL
                                      idxV ⟨eV'Site, eV'Cls, τ⟩ hIdxV law hearers ⟨at_.path, drawToldKey events idxV⟩
                                      coinP hClsV' hPin hToldSiteV hCoinPV
                                    by_cases hCar : at_.site ∈ layout.carry
                                    · have hCarP : ePSite ∈ layout.carry := hSiteP.symm ▸ hCar
                                      have hCarV : eV'Site ∈ layout.carry := hSiteV'.symm ▸ hCar
                                      rw [ite_eq_left hCarP] at hCarryP
                                      rw [ite_eq_left hCarV] at hCarryV
                                      obtain ⟨wRef, _, _, chunk, hWFind, _, _, hWD, hChV, hLayPAns, _⟩ := hCarryP
                                      obtain ⟨wRefV, rRef, eqRef, chunkV, hWFindV, hRFind, hEqFind, _, _, _, hLayVAns⟩ := hCarryV
                                      have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                                        intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hBufV u h1
                                        · exact hChV u h2
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ stP' (buf ++ chunk) source hStP'V hBufChV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons (buf ++ chunk) .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st stP' buf (buf ++ chunk)
                                          () coinP _ hConPAns (hLayPAns buf) rfl
                                      refine ⟨a, outP, outV, fSt, chunk ++ suf', recP, src'', ?_, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · intro u hu
                                        rcases List.mem_append.mp hu with h1 | h2
                                        · exact hChV u h1
                                        · exact hSufV u h2
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        simpa [List.append_assoc] using hAlP
                                      · intro post hPost
                                        have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                                          intro u hu
                                          rcases List.mem_append.mp hu with h1 | h2
                                          · exact hSufV u h1
                                          · exact hPost u h2
                                        have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                                          hCoinPV hBufV hSufPostV hWD
                                        have hEqD := layoutLawful_equal_refl M hLayDecl hLayLaw hEqFind hCoinPV
                                        have hLayVDone := hLayVAns (buf ++ chunk ++ (suf' ++ post))
                                          buf.length (buf.length + chunk.length) hRD hEqD
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ chunk ++ (suf' ++ post), (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ chunk ++ (suf' ++ post),
                                              (buf.length + chunk.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st stP'
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                                            (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ()))
                                            () coinP _ hConVAns hLayVDone rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                                          simp [List.append_assoc]
                                        rw [hBufEq]
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        have hLenEq : buf.length + (chunk ++ suf').length =
                                            (buf ++ chunk).length + suf'.length := by
                                          simp [List.length_append, Nat.add_assoc]
                                        have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                                          simp [List.append_assoc]
                                        rw [hLenEq, hBufEq2, ← List.length_append]
                                        exact hAlV'
                                      · intro v hv
                                        dsimp only [src''] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                      · intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                                    · have hCarP : ePSite ∉ layout.carry := hSiteP.symm ▸ hCar
                                      have hCarV : eV'Site ∉ layout.carry := hSiteV'.symm ▸ hCar
                                      rw [ite_eq_right hCarP] at hCarryP
                                      rw [ite_eq_right hCarV] at hCarryV
                                      obtain ⟨a, outP, outV, fSt, suf', recP, src', hSufV, hAlP, hAlV,
                                        hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                        ih coinP _ _ stP' buf source hStP'V hBufV
                                          (hPP' coinP) (hPV' coinP)
                                          (hSP.2 coinP hCoinPV) (hSV.2 coinP hCoinPV)
                                          (hShP.2 coinP trivial) (hShV.2 coinP trivial)
                                          (hPShape.2 coinP) (hUniq coinP).2 hLP' hFed' hNoHalt'
                                      let src'' := patchSource M src' at_ τ coinP
                                      have hAgPatch : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                        fun at' τ' hne => (patchSource_ne M src' at_ τ coinP hne τ').symm
                                      have hStepP : (Stack.handler M fnTable rTable [conP', layP']).clause
                                          (.hear (.coin law) verifier at_ τ) (.cons st (.cons buf .nil)) =
                                          .done (coinP, .cons stP' (.cons buf .nil)) :=
                                        stack2_clause_step M fnTable rTable conP' layP' _ _ st stP' buf buf
                                          () coinP _ hConPAns (hCarryP.1 buf) rfl
                                      refine ⟨a, outP, outV, fSt, suf', recP, src'', hSufV, ?_, ?_,
                                        hPostP, hPostV, ?_, ?_, ?_⟩
                                      · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                                        exact hAlP
                                      · intro post hPost
                                        have hStepV : (Stack.handler M fnTable rTable [conV', layV']).clause
                                            (.own (.coin law) hearers at_ [] .nil τ)
                                            (.cons st (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) =
                                            .done (coinP, .cons stP' (.cons (buf ++ suf' ++ post, (buf.length, ())) .nil)) :=
                                          stack2_clause_step M fnTable rTable conV' layV' _ _ st stP'
                                            (buf ++ suf' ++ post, (buf.length, ()))
                                            (buf ++ suf' ++ post, (buf.length, ()))
                                            () coinP _ hConVAns (hCarryV.2 (buf ++ suf' ++ post) buf.length) rfl
                                        obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                        refine ⟨recV, ?_⟩
                                        rw [stack_run_clause_done M _ _ _ _ _ _ hStepV]
                                        exact hAlV'
                                      · intro v hv
                                        dsimp only [src''] at hv
                                        rw [patchSource_self] at hv; cases hv
                                        exact ⟨hAllowsCoin, lawful_of_agree M hAgPatch hOccK hLSrc'⟩
                                      · intro at' τ' hNotIn
                                        have hne : at' ≠ at_ := fun heq => hNotIn (heq ▸ hAtHeard)
                                        dsimp only [src'']
                                        rw [patchSource_ne M src' at_ τ coinP hne τ']
                                        exact hAgSrc' at' τ' hNotIn
                                      · exact ⟨_, .given (patchSource_self M src' at_ τ coinP)
                                          (grun_of_agree M hAgPatch hOccK hRun')⟩
                          | isFalse hHeardCoin =>
                            obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
                            have hDisc := hEventDisc eG hEG
                            rw [hClsG] at hDisc
                            have hNotHeardCoin : (∃ law, gkind = .coin law ∧ hearers = []) ∨
                                (∃ svc, gkind = .request svc ∧
                                  (owner = prover ∨ prover ∉ hearers) ∧
                                  (owner = verifier ∨ verifier ∉ hearers)) := by
                              cases gkind with
                              | coin law =>
                                  rcases hDisc with ⟨hO, hP, _⟩ | hNil
                                  · exact absurd ⟨⟨law, rfl⟩, hO, hP⟩ hHeardCoin
                                  · exact .inl ⟨law, rfl, hNil⟩
                              | request svc =>
                                  exact .inr ⟨svc, rfl, hDisc⟩
                            have hSrcFed : ∃ v, source at_ τ = some v ∧ Fed M source (k v) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                              · exact hFed
                              · exact hFed
                            obtain ⟨v, hSrc, hFed'⟩ := hSrcFed
                            have hLPv : Allows M gkind gIns payload τ v ∧ LawfulPrivate M source (k v) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩
                              · exact hLP v hSrc
                              · exact hLP v hSrc
                            obtain ⟨hAllows, hLP'⟩ := hLPv
                            have hValV : M.Valid τ v := allows_valid M hAllows
                            have hIsClOwn : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ) := by
                              rcases hNotHeardCoin with ⟨law, rfl, rfl⟩ | ⟨svc, rfl, _⟩ <;> trivial
                            have hOccK : Protocol.OccsIn M (· ≠ at_) (k v) := (hUniq v).1
                            have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                                (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                  source₁ at' τ' = source at' τ') →
                                ∀ e, GExec M source₁ (k v) e → ∃ a, e = .returned a := by
                              intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                              let source₂ := patchSource M source₁ at_ τ v
                              have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                                fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
                              have hL₂ : Lawful M source₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
                                intro w hw
                                dsimp only [source₂] at hw
                                rw [patchSource_self] at hw; cases hw
                                exact ⟨hAllows, lawful_of_agree M hAgree12 hOccK hL₁⟩
                              have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                                  source₂ at' τ' = source at' τ' := by
                                intro at' τ' hNotIn
                                unfold source₂ patchSource
                                split
                                · rename_i heq
                                  cases heq.1; cases heq.2; exact hSrc.symm
                                · exact hAg₁ at' τ' hNotIn
                              exact hNoHalt source₂ hL₂ hAg₂ e
                                ⟨_, .given (patchSource_self M source₁ at_ τ v)
                                  (grun_of_agree M hAgree12 hOccK hRun₁)⟩
                            have hWrapSrc : ∀ (src' : Source M) {evs' a},
                                Lawful M src' (k v) →
                                (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src' at' τ' = source at' τ') →
                                GRun M src' (k v) evs' (.returned a) →
                                ∃ src'', Lawful M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) ∧
                                  (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src'' at' τ' = source at' τ') ∧
                                  GExec M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) (.returned a) := by
                              intro src' evs' a hL' hAg' hRun'
                              let src'' := patchSource M src' at_ τ v
                              have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                                fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                              refine ⟨src'', ?_, ?_, ?_⟩
                              · intro w hw
                                dsimp only [src''] at hw
                                rw [patchSource_self] at hw; cases hw
                                exact ⟨hAllows, lawful_of_agree M hAgP hOccK hL'⟩
                              · intro at' τ' hNotIn
                                unfold src'' patchSource
                                split
                                · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                                · exact hAg' at' τ' hNotIn
                              · exact ⟨_, .given (patchSource_self M src' at_ τ v)
                                  (grun_of_agree M hAgP hOccK hRun')⟩
                            cases hPP with
                            | begins _ => exact False.elim (hNotMP trivial)
                            | settles _ => exact False.elim (hNotMP trivial)
                            | heard hONeP hPin _ =>
                                rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, hPReq, _⟩
                                · cases hPin
                                · rcases hPReq with hEqO | hNotIn
                                  · exact absurd hEqO hONeP
                                  · exact absurd hPin hNotIn
                            | owned hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | owned _ => exact absurd rfl hNe
                                | heard _ hVin _ =>
                                    rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                                    · cases hVin
                                    · rcases hVReq with hEqO | hNotIn
                                      · exact absurd hEqO hNe
                                      · exact absurd hVin hNotIn
                                | unheard _ _ hPV' =>
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        (hSP.2 v hValV) hSV (hShP.2 v trivial) hShV
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    refine ⟨a, outP, outV, fSt, suf,
                                      .owned prover gkind at_ τ v :: recP, src'', hSufV, ?_, hAlV,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                    rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassP _ _ _ hIsClOwn)]
                                    exact .own hSrc hAlP
                            | unheard hONeP _ hPP' =>
                                cases hPV with
                                | begins _ => exact False.elim (hNotMV trivial)
                                | settles _ => exact False.elim (hNotMV trivial)
                                | heard hONeV hVin _ =>
                                    rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                                    · cases hVin
                                    · rcases hVReq with hEqO | hNotIn
                                      · exact absurd hEqO hONeV
                                      · exact absurd hVin hNotIn
                                | owned hPV' =>
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        hSP (hSV.2 v hValV) hShP (hShV.2 v trivial)
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    refine ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, ?_,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩
                                    intro post hPost
                                    obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                                    refine ⟨.owned verifier gkind at_ τ v :: recV, ?_⟩
                                    rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassV _ _ _ hIsClOwn)]
                                    exact .own hSrc hAlV'
                                | unheard _ _ hPV' =>
                                    obtain ⟨a, outP, outV, fSt, suf, recP, src', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                                      ih v _ _ st buf source hStV hBufV (hPP' v) (hPV' v)
                                        hSP hSV hShP hShV
                                        (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                                    obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                                    exact ⟨a, outP, outV, fSt, suf, recP, src'', hSufV, hAlP, hAlV,
                                      hPostP, hPostV, hL'', hAg'', hGEx''⟩

private theorem simulate_authored {d : Deployed V} {layout : Layout} {unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} (hNe : prover ≠ verifier) {declKey : Key}
    {layP : Layer V d.admitted.program.headers prover d.entry.ins}
    {layV : Layer V d.admitted.program.headers verifier d.entry.ins}
    (hLayDecl : d.declaration.layout = some layout)
    (hLayLaw : d.LayoutLawful M)
    (hLayPState : layP.state = .seq unitTy none) (hLayVState : layV.state = streamStateTy unitTy)
    {cS : List (Clause V d.admitted.program.headers prover .nat)}
    (hAuth : checkAuthoredEvents d.admitted prover verifier none declKey
      (d.entry.shape.events [] id) = .ok cS)
    (hSL : buildStreamingLayoutClauses.go d.admitted layout unitTy hfree prover verifier declKey
      (d.entry.shape.events [] id) 0 (d.entry.shape.events [] id) =
      .ok (hLayPState ▸ layP.clauses, hLayVState ▸ layV.clauses)) :
    ∀ {A BP BV : Type} (p : Protocol M A) {postP : A → BP → Prop} {postV : A → BV → Prop}
      (pP : Program M BP) (pV : Program M BV)
      (buf : List (M.Val unitTy)) (source : Source M),
      (∀ u ∈ buf, M.Valid unitTy u) →
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
      ∃ (a : A) (outP : BP) (outV : BV) (suffix : List (M.Val unitTy))
        (recP : List (Happened M)) (source' : Source M),
        (∀ u ∈ suffix, M.Valid unitTy u) ∧
        Alone M source prover
          ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
            (Defs.rTable M d.admitted.program.defs) [layP]).run (retryOf M none) pP
              (.cons (hLayPState.symm ▸ buf) .nil))
          recP (.returned (outP, .cons (hLayPState.symm ▸ (buf ++ suffix)) .nil)) ∧
        (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
          ∃ recV, Alone M source verifier
            ((Stack.handler M (Defs.fnTable M d.admitted.program.defs)
              (Defs.rTable M d.admitted.program.defs) [layV]).run (retryOf M none) pV
                (.cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length, ()))) .nil))
            recV (.returned (outV,
              .cons (hLayVState.symm ▸ (buf ++ suffix ++ post, (buf.length + suffix.length, ()))) .nil))) ∧
        postP a outP ∧ postV a outV ∧
        Lawful M source' p ∧
        (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
        GExec M source' p (.returned a) := by
  cases layP with
  | mk lPLine lPSt lPTakes lPGives lPClauses lPAgain lPStart lPFin =>
      cases layV with
      | mk lVLine lVSt lVTakes lVGives lVClauses lVAgain lVStart lVFin =>
          dsimp only at hLayPState hLayVState
          subst lPSt; subst lVSt
          dsimp only at hSL
          let layP' : Layer V d.admitted.program.headers prover d.entry.ins :=
            ⟨lPLine, .seq unitTy none, lPTakes, lPGives, lPClauses, lPAgain, lPStart, lPFin⟩
          let layV' : Layer V d.admitted.program.headers verifier d.entry.ins :=
            ⟨lVLine, streamStateTy unitTy, lVTakes, lVGives, lVClauses, lVAgain, lVStart, lVFin⟩
          let fnTable := Defs.fnTable M d.admitted.program.defs
          let rTable := Defs.rTable M d.admitted.program.defs
          let events := d.entry.shape.events [] id
          have hLayUnm := fun op hCl => streaming_layout_unmatched_closed M 0 events hSL op hCl
          have hPassP : ∀ op (buf : List (M.Val unitTy)), ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [layP']).clause op (.cons buf .nil) =
                .call op fun reply => .done (reply, .cons buf .nil) := fun op buf hCl =>
            stack1_clause_pass M fnTable rTable layP' op buf
              (clause_answer_unmatched_all M fnTable rTable op buf lPClauses (hLayUnm op hCl).1)
          have hPassV : ∀ op (lst : M.Val (streamStateTy unitTy)), ROp.IsClosed M op →
              (Stack.handler M fnTable rTable [layV']).clause op (.cons lst .nil) =
                .call op fun reply => .done (reply, .cons lst .nil) := fun op lst hCl =>
            stack1_clause_pass M fnTable rTable layV' op lst
              (clause_answer_unmatched_all M fnTable rTable op lst lVClauses (hLayUnm op hCl).2)
          have hEventDisc : ∀ e ∈ events,
              match e.cls with
              | .flow _ giver getters =>
                  (giver = prover ∧ verifier ∈ getters) ∨
                  (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
              | .given (.coin _) _ hearers => hearers = []
              | .given (.request _) owner hearers =>
                  (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
            have hGo : ∀ (es : List (ShapeEvent V)) {cS'},
                checkAuthoredEvents d.admitted prover verifier none declKey es = .ok cS' →
                ∀ e ∈ es, match e.cls with
                  | .flow _ giver getters =>
                      (giver = prover ∧ verifier ∈ getters) ∨
                      (giver ≠ prover ∧ giver ≠ verifier ∧ prover ∉ getters ∧ verifier ∉ getters)
                  | .given (.coin _) _ hearers => hearers = []
                  | .given (.request _) owner hearers =>
                      (owner = prover ∨ prover ∉ hearers) ∧ (owner = verifier ∨ verifier ∉ hearers) := by
              intro es
              induction es with
              | nil => intro _ _ _ he; cases he
              | cons e rest ih =>
                  intro cS' hGo' e' he'
                  unfold checkAuthoredEvents at hGo'
                  cases hRec : checkAuthoredEvents d.admitted prover verifier none declKey rest with
                  | error _ => rw [hRec] at hGo'; cases hGo'
                  | ok sRest =>
                      rw [hRec] at hGo'; dsimp only [bind, Except.bind] at hGo'
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · cases hCls : e'.cls with
                        | flow _ giver getters =>
                            rw [hCls] at hGo'; dsimp only at hGo'
                            split at hGo'
                            · rename_i hCond; exact hCond
                            · cases hGo'
                        | given gkind owner hearers =>
                            rw [hCls] at hGo'
                            cases gkind with
                            | coin _ =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hNil; exact hNil
                                · cases hGo'
                            | request _ =>
                                dsimp only at hGo'
                                split at hGo'
                                · rename_i hReq; exact hReq
                                · cases hGo'
                      · exact ih hRec e' hmem
            exact hGo events hAuth
          intro A BP BV p
          let SimGoal := fun (p0 : Protocol M A) (postP : A → BP → Prop) (postV : A → BV → Prop)
              (buf : List (M.Val unitTy)) (source : Source M)
              (qP : Program M BP) (qV : Program M BV) =>
            ∃ (a : A) (outP : BP) (outV : BV) (suffix : List (M.Val unitTy))
              (recP : List (Happened M)) (source' : Source M),
              (∀ u ∈ suffix, M.Valid unitTy u) ∧
              Alone M source prover
                ((Stack.handler M fnTable rTable [layP']).run (retryOf M none) qP (.cons buf .nil))
                recP (.returned (outP, .cons (buf ++ suffix) .nil)) ∧
              (∀ (post : List (M.Val unitTy)), (∀ u ∈ post, M.Valid unitTy u) →
                ∃ recV, Alone M source verifier
                  ((Stack.handler M fnTable rTable [layV']).run (retryOf M none) qV
                      (.cons (buf ++ suffix ++ post, (buf.length, ())) .nil))
                  recV (.returned (outV, .cons (buf ++ suffix ++ post, (buf.length + suffix.length, ())) .nil))) ∧
              postP a outP ∧ postV a outV ∧
              Lawful M source' p0 ∧
              (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
              GExec M source' p0 (.returned a)
          induction p with
          | done a =>
              intro postP postV pP pV buf source hBufV hProjP hProjV hSafeP hSafeV hShapeP hShapeV _ _ _ _ _
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layP'])
                (fun op s hM => by
                  cases s with | cons b bn => cases bn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ trivial)
                (fun qP => SimGoal (.done a) postP postV buf source qP pV)
                (fun qP hNotMP hPP hSP hShP => ?_)
                (fun at_ kP h => by
                  obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a', outP, outV, suf, .began prover at_ :: recP, src', h1,
                    by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ trivial)]; exact .begin h2,
                    h3, h4, h5, h6, h7, h8⟩)
                (fun at_ kP h => by
                  obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a', outP, outV, suf, .settled prover at_ :: recP, src', h1,
                    by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ trivial)]; exact .settle h2,
                    h3, h4, h5, h6, h7, h8⟩)
                hProjP hSafeP hShapeP
              cases hPP with
              | done hPostP =>
                  refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layV'])
                    (fun op s hM => by
                      cases s with | cons l ln => cases ln; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ trivial)
                    (fun qV => SimGoal (.done a) postP postV buf source (.done _) qV)
                    (fun qV hNotMV hPV hSV hShV => ?_)
                    (fun at_ kV h => by
                      obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                      exact ⟨a', outP, outV, suf, recP, src', h1, h2,
                        fun post hPost =>
                          let ⟨recV, hAlV⟩ := h3 post hPost
                          ⟨.began verifier at_ :: recV,
                            by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ trivial)]; exact .begin hAlV⟩,
                        h4, h5, h6, h7, h8⟩)
                    (fun at_ kV h => by
                      obtain ⟨a', outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                      exact ⟨a', outP, outV, suf, recP, src', h1, h2,
                        fun post hPost =>
                          let ⟨recV, hAlV⟩ := h3 post hPost
                          ⟨.settled verifier at_ :: recV,
                            by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ trivial)]; exact .settle hAlV⟩,
                        h4, h5, h6, h7, h8⟩)
                    hProjV hSafeV hShapeV
                  cases hPV with
                  | done hPostV =>
                      exact ⟨a, _, _, [], [], source, (fun _ h => nomatch h),
                        by simpa [Handler.run] using Alone.done,
                        fun post _ => ⟨[], by simpa [Handler.run] using Alone.done⟩,
                        hPostP, hPostV, trivial, fun _ _ _ => rfl, ⟨[], .done⟩⟩
                  | begins _ => exact False.elim (hNotMV trivial)
                  | settles _ => exact False.elim (hNotMV trivial)
              | begins _ => exact False.elim (hNotMP trivial)
              | settles _ => exact False.elim (hNotMP trivial)
          | halt payload =>
              intro _ _ _ _ _ source _ _ _ _ _ _ _ _ _ _ _ hNoHalt
              obtain ⟨a, hContra⟩ := hNoHalt source trivial (fun _ _ _ => rfl)
                (.stopped payload.1 payload.2) ⟨[], .halt⟩
              cases hContra
          | call op k ih =>
              intro postP postV pP pV buf source hBufV hProjP hProjV hSafeP hSafeV
                hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layP'])
                (fun op s hM => by
                  cases s with | cons b bn => cases bn; rcases hM with hM | hM <;> rw [hM] <;> exact hPassP _ _ trivial)
                (fun qP => SimGoal (.call op k) postP postV buf source qP pV)
                (fun qP hNotMP hPP hSP hShP => ?_)
                (fun at_ kP h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, .began prover at_ :: recP, src', h1,
                    by rw [stack_run_begin M _ at_ kP _ (hPassP _ _ trivial)]; exact .begin h2,
                    h3, h4, h5, h6, h7, h8⟩)
                (fun at_ kP h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, .settled prover at_ :: recP, src', h1,
                    by rw [stack_run_settle M _ at_ kP _ (hPassP _ _ trivial)]; exact .settle h2,
                    h3, h4, h5, h6, h7, h8⟩)
                hProjP hSafeP hShapeP
              refine peelMarks_alone M (h := Stack.handler M fnTable rTable [layV'])
                (fun op s hM => by
                  cases s with | cons l ln => cases ln; rcases hM with hM | hM <;> rw [hM] <;> exact hPassV _ _ trivial)
                (fun qV => SimGoal (.call op k) postP postV buf source qP qV)
                (fun qV hNotMV hPV hSV hShV => ?_)
                (fun at_ kV h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, recP, src', h1, h2,
                    fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.began verifier at_ :: recV,
                        by rw [stack_run_begin M _ at_ kV _ (hPassV _ _ trivial)]; exact .begin hAlV⟩,
                    h4, h5, h6, h7, h8⟩)
                (fun at_ kV h => by
                  obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
                  exact ⟨a, outP, outV, suf, recP, src', h1, h2,
                    fun post hPost =>
                      let ⟨recV, hAlV⟩ := h3 post hPost
                      ⟨.settled verifier at_ :: recV,
                        by rw [stack_run_settle M _ at_ kV _ (hPassV _ _ trivial)]; exact .settle hAlV⟩,
                    h4, h5, h6, h7, h8⟩)
                hProjV hSafeV hShapeV
              cases op with
              | flow kind giver getters at_ τ x =>
                  have hNoHalt' : ∀ source₁, Lawful M source₁ (k ()) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                      ∀ e, GExec M source₁ (k ()) e → ∃ a, e = .returned a := fun source₁ hL₁ hAg e ⟨evs, hRun⟩ =>
                    hNoHalt source₁ hL₁ hAg e ⟨_, .flow hRun⟩
                  cases hPP with
                  | begins _ => exact False.elim (hNotMP trivial)
                  | settles _ => exact False.elim (hNotMP trivial)
                  | gave _ hPP' =>
                      obtain ⟨eP, hEP, hSiteP, hTyP, hClsP⟩ := hShP.1
                      have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
                      have hVin : verifier ∈ getters := by
                        rcases hDisc with ⟨_, hV⟩ | ⟨hNotP, _, _, _⟩
                        · exact hV
                        · exact absurd rfl hNotP
                      have hMsgV : M.Valid τ x := hSP.1
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | gave _ _ => exact absurd rfl hNe
                      | passed _ hVOut _ => exact absurd hVin hVOut
                      | got _ _ hPV' =>
                          obtain ⟨wRef, chunk, hWFind, hWD, hChV, hLayPAns⟩ :=
                            streaming_layout_answer_prover_flow M 0 events (fun _ h => h) hSL
                              kind getters at_ τ x buf hMsgV ⟨eP, hEP, hSiteP, hTyP, hVin, hClsP⟩
                          have hBufChV : ∀ u ∈ buf ++ chunk, M.Valid unitTy u := by
                            intro u hu; rcases List.mem_append.mp hu with h1 | h2
                            · exact hBufV u h1
                            · exact hChV u h2
                          obtain ⟨a, outP, outV, suf', recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ (buf ++ chunk) source hBufChV hPP' hPV'
                              (hSP.2 () trivial) (hSV.2 x hMsgV) (hShP.2 () trivial) (hShV.2 x trivial)
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          have hStepP := stack1_clause_done M fnTable rTable layP'
                            (.give kind getters at_ τ x) buf (buf ++ chunk) () hLayPAns
                          refine ⟨a, outP, outV, chunk ++ suf', recP, src', ?_, ?_, ?_,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨_, .flow hRun'⟩⟩
                          · intro u hu; rcases List.mem_append.mp hu with h1 | h2
                            · exact hChV u h1
                            · exact hSufV u h2
                          · rw [stack_run_clause_done M _ _ _ _ _ _ hStepP]
                            simpa [List.append_assoc] using hAlP
                          · intro post hPost
                            have hSufPostV : ∀ u ∈ suf' ++ post, M.Valid unitTy u := by
                              intro u hu; rcases List.mem_append.mp hu with h1 | h2
                              · exact hSufV u h1
                              · exact hPost u h2
                            obtain ⟨rRef, hRFind, hLayVAns⟩ :=
                              streaming_layout_answer_verifier_flow M 0 events hSL
                                kind at_ τ (buf ++ chunk ++ (suf' ++ post)) buf.length
                                ⟨eP, hEP, hSiteP, hTyP, getters, hVin, hClsP⟩
                            have hRD := layoutLawful_roundTrip M hLayDecl hLayLaw hWFind hRFind
                              hMsgV hBufV hSufPostV hWD
                            have hStepV := stack1_clause_done M fnTable rTable layV'
                              (.get kind prover at_ τ)
                              (buf ++ chunk ++ (suf' ++ post), (buf.length, ()))
                              (buf ++ chunk ++ (suf' ++ post), (buf.length + chunk.length, ())) x
                              (hLayVAns x (buf.length + chunk.length) hRD)
                            obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                            refine ⟨recV, ?_⟩
                            have hBufEq : buf ++ (chunk ++ suf') ++ post = buf ++ chunk ++ (suf' ++ post) := by
                              simp [List.append_assoc]
                            rw [hBufEq, stack_run_clause_done M _ _ _ _ _ _ hStepV]
                            have hLenEq : buf.length + (chunk ++ suf').length =
                                (buf ++ chunk).length + suf'.length := by
                              simp [List.length_append, Nat.add_assoc]
                            have hBufEq2 : buf ++ chunk ++ (suf' ++ post) = (buf ++ chunk) ++ suf' ++ post := by
                              simp [List.append_assoc]
                            rw [hLenEq, hBufEq2, ← List.length_append]
                            exact hAlV'
                  | got hGNeP _ _ =>
                      obtain ⟨eP, hEP, _, _, _, gs', hPin', hClsP⟩ := hShP.1
                      have hDisc := hEventDisc eP hEP; rw [hClsP] at hDisc
                      rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, hNotP, _⟩
                      · exact absurd hEqP hGNeP
                      · exact absurd hPin' hNotP
                  | passed hGNeP _ hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | gave _ _ =>
                          obtain ⟨eV, hEV, _, _, hClsV⟩ := hShV.1
                          have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
                          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, hNotV, _, _⟩
                          · exact absurd hEqP.symm hNe
                          · exact absurd rfl hNotV
                      | got _ _ _ =>
                          obtain ⟨eV, hEV, _, _, _, gs', hVin', hClsV⟩ := hShV.1
                          have hDisc := hEventDisc eV hEV; rw [hClsV] at hDisc
                          rcases hDisc with ⟨hEqP, _⟩ | ⟨_, _, _, hNotV⟩
                          · exact absurd hEqP hGNeP
                          · exact absurd hVin' hNotV
                      | passed _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨evs', hRun'⟩⟩ :=
                            ih () _ _ buf source hBufV hPP' hPV' hSP hSV hShP hShV
                              (hPShape.2 ()) (hUniq ()).2 hLP hFed hNoHalt'
                          exact ⟨a, outP, outV, suf, recP, src', h1, h2, h3, h4, h5, h6, h7, ⟨_, .flow hRun'⟩⟩
              | given gkind owner hearers at_ gIns payload τ =>
                  obtain ⟨eG, hEG, _, _, hClsG⟩ := hPShape.1
                  have hDisc := hEventDisc eG hEG; rw [hClsG] at hDisc
                  have hNotHeardCoin : (∃ law, gkind = .coin law ∧ hearers = []) ∨
                      (∃ svc, gkind = .request svc ∧
                        (owner = prover ∨ prover ∉ hearers) ∧
                        (owner = verifier ∨ verifier ∉ hearers)) := by
                    cases gkind with
                    | coin law => exact .inl ⟨law, rfl, hDisc⟩
                    | request svc => exact .inr ⟨svc, rfl, hDisc⟩
                  have hSrcFed : ∃ v, source at_ τ = some v ∧ Fed M source (k v) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> exact hFed
                  obtain ⟨v, hSrc, hFed'⟩ := hSrcFed
                  have hLPv : Allows M gkind gIns payload τ v ∧ LawfulPrivate M source (k v) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> exact hLP v hSrc
                  obtain ⟨hAllows, hLP'⟩ := hLPv
                  have hValV : M.Valid τ v := allows_valid M hAllows
                  have hIsClOwn : ROp.IsClosed M (.own gkind hearers at_ gIns payload τ) := by
                    rcases hNotHeardCoin with ⟨_, rfl, rfl⟩ | ⟨_, rfl, _⟩ <;> trivial
                  have hOccK : Protocol.OccsIn M (· ≠ at_) (k v) := (hUniq v).1
                  have hNoHalt' : ∀ source₁, Lawful M source₁ (k v) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → source₁ at' τ' = source at' τ') →
                      ∀ e, GExec M source₁ (k v) e → ∃ a, e = .returned a := by
                    intro source₁ hL₁ hAg₁ e ⟨evs₁, hRun₁⟩
                    let source₂ := patchSource M source₁ at_ τ v
                    have hAgree12 : ∀ at' τ', at' ≠ at_ → source₁ at' τ' = source₂ at' τ' :=
                      fun at' τ' hne => (patchSource_ne M source₁ at_ τ v hne τ').symm
                    have hL₂ : Lawful M source₂ (.call (.given gkind owner hearers at_ gIns payload τ) k) := by
                      intro w hw; dsimp only [source₂] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAllows, lawful_of_agree M hAgree12 hOccK hL₁⟩
                    have hAg₂ : ∀ at' τ', at'.site ∉ d.entry.shape.heardCoins →
                        source₂ at' τ' = source at' τ' := by
                      intro at' τ' hNotIn
                      unfold source₂ patchSource; split
                      · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                      · exact hAg₁ at' τ' hNotIn
                    exact hNoHalt source₂ hL₂ hAg₂ e
                      ⟨_, .given (patchSource_self M source₁ at_ τ v)
                        (grun_of_agree M hAgree12 hOccK hRun₁)⟩
                  have hWrapSrc : ∀ (src' : Source M) {evs' a},
                      Lawful M src' (k v) →
                      (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src' at' τ' = source at' τ') →
                      GRun M src' (k v) evs' (.returned a) →
                      ∃ src'', Lawful M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) ∧
                        (∀ at' τ', at'.site ∉ d.entry.shape.heardCoins → src'' at' τ' = source at' τ') ∧
                        GExec M src'' (.call (.given gkind owner hearers at_ gIns payload τ) k) (.returned a) := by
                    intro src' evs' a hL' hAg' hRun'
                    let src'' := patchSource M src' at_ τ v
                    have hAgP : ∀ at' τ', at' ≠ at_ → src' at' τ' = src'' at' τ' :=
                      fun at' τ' hne => (patchSource_ne M src' at_ τ v hne τ').symm
                    refine ⟨src'', ?_, ?_, ?_⟩
                    · intro w hw; dsimp only [src''] at hw; rw [patchSource_self] at hw; cases hw
                      exact ⟨hAllows, lawful_of_agree M hAgP hOccK hL'⟩
                    · intro at' τ' hNotIn
                      unfold src'' patchSource; split
                      · rename_i heq; cases heq.1; cases heq.2; exact hSrc.symm
                      · exact hAg' at' τ' hNotIn
                    · exact ⟨_, .given (patchSource_self M src' at_ τ v)
                        (grun_of_agree M hAgP hOccK hRun')⟩
                  cases hPP with
                  | begins _ => exact False.elim (hNotMP trivial)
                  | settles _ => exact False.elim (hNotMP trivial)
                  | heard hONeP hPin _ =>
                      rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, hPReq, _⟩
                      · cases hPin
                      · rcases hPReq with hEqO | hNotIn
                        · exact absurd hEqO hONeP
                        · exact absurd hPin hNotIn
                  | owned hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | owned _ => exact absurd rfl hNe
                      | heard _ hVin _ =>
                          rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                          · cases hVin
                          · rcases hVReq with hEqO | hNotIn
                            · exact absurd hEqO hNe
                            · exact absurd hVin hNotIn
                      | unheard _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              (hSP.2 v hValV) hSV (hShP.2 v trivial) hShV
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          refine ⟨a, outP, outV, suf, .owned prover gkind at_ τ v :: recP, src'',
                            hSufV, ?_, hAlV, hPostP, hPostV, hL'', hAg'', hGEx''⟩
                          rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassP _ _ hIsClOwn)]
                          exact .own hSrc hAlP
                  | unheard hONeP _ hPP' =>
                      cases hPV with
                      | begins _ => exact False.elim (hNotMV trivial)
                      | settles _ => exact False.elim (hNotMV trivial)
                      | heard hONeV hVin _ =>
                          rcases hNotHeardCoin with ⟨_, _, rfl⟩ | ⟨_, _, _, hVReq⟩
                          · cases hVin
                          · rcases hVReq with hEqO | hNotIn
                            · exact absurd hEqO hONeV
                            · exact absurd hVin hNotIn
                      | owned hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              hSP (hSV.2 v hValV) hShP (hShV.2 v trivial)
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          refine ⟨a, outP, outV, suf, recP, src'', hSufV, hAlP, ?_,
                            hPostP, hPostV, hL'', hAg'', hGEx''⟩
                          intro post hPost
                          obtain ⟨recV, hAlV'⟩ := hAlV post hPost
                          refine ⟨.owned verifier gkind at_ τ v :: recV, ?_⟩
                          rw [stack_run_own M _ gkind hearers at_ gIns payload τ _ _ (hPassV _ _ hIsClOwn)]
                          exact .own hSrc hAlV'
                      | unheard _ _ hPV' =>
                          obtain ⟨a, outP, outV, suf, recP, src', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hLSrc', hAgSrc', ⟨evs', hRun'⟩⟩ :=
                            ih v _ _ buf source hBufV (hPP' v) (hPV' v)
                              hSP hSV hShP hShV
                              (hPShape.2 v) (hUniq v).2 hLP' hFed' hNoHalt'
                          obtain ⟨src'', hL'', hAg'', hGEx''⟩ := hWrapSrc src' hLSrc' hAgSrc' hRun'
                          exact ⟨a, outP, outV, suf, recP, src'', hSufV, hAlP, hAlV,
                            hPostP, hPostV, hL'', hAg'', hGEx''⟩

/-- Top-level streaming completeness (`Statements.complete`) for `deploy`. -/
theorem deploy_complete (enc : VocabEncoder V) {named : NamedProgram V} {assoc : Association}
    {a : Admitted V} (hAdmit : admit named assoc = .ok a)
    {declaration : Declaration} {d : Deployed V} (hDep : deploy enc a declaration = .ok d)
    (hNonInt : declaration.interactive = false) (hNoRetry : declaration.retry = none)
    (hNoSamp : declaration.samples = none)
    (hNoRec : ∀ l, declaration.layout = some l → l.recover = [])
    (prover verifier : Role) (hRoles : d.roles = some (prover, verifier))
    (first : Stack.Takes (d.stack prover) = [])
    (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
    (ins : HList (LVal M) d.entry.ins) (hIns : ins.All (fun a v => M.Valid a.ty v))
    (hSuiteLaw : d.SuiteLawful M) (hLayLaw : d.LayoutLawful M)
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
  | interactive w _ => simp [Declaration.interactive, w.hCon] at hNonInt
  | authored w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      cases buildLayoutLayers_ok_elim w.hLay with
      | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
      | streaming wL hLPW hLVW =>
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          let layP0 : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
          let layV0 : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
          let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layP0
          let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layV0
          have hAuth' : checkAuthoredEvents a w.prover w.verifier none declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) = .ok w.sClauses := by
            rw [hEntryF, ← hNoSamp]; exact w.hAuth
          have hLayPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layP0
          have hLayVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layV0
          have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy wL.hfree
              w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) =
              .ok (hLayPSt ▸ layP'.clauses, hLayVSt ▸ layV'.clauses) := by
            rw [layer_cast_clauses hEntryF layP0, layer_cast_clauses hEntryF layV0, hEntryF]
            exact wL.hStr
          obtain ⟨out, outP, outV, suffix, recP, source', hSufV, hAlP, hAlV,
            hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
            simulate_authored M w.hNe (d := w.toDeployed)
              w.hLayOpt hLayLaw hLayPSt hLayVSt hAuth' hSL'
              (protocolMeaning M a.program _ [] ins)
              (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
              (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
              [] source (fun _ h => nomatch h) hProjP hProjV hSafeP hSafeV
              hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
          have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
              (callee : Member a.program.headers.protocols hdr)
              (ins' : HList (LVal M) hdr.ins)
              (first' : Stack.Takes (hE ▸ [layP0]) = [])
              (matched' : Stack.Gives (hE ▸ [layP0]) = Stack.Takes (hE ▸ [layV0]))
              (outP' : HList (RV M w.prover) hdr.outs)
              (outV' : HList (RV M w.verifier) hdr.outs)
              (recP' recV' : List (Happened M)),
              Alone M source w.prover
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [layP0])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                  (cast (by subst hE; rfl) (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil)))
                recP' (.returned (outP', cast (by subst hE; rfl) (HList.cons suffix HList.nil))) →
              Alone M source w.verifier
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [layV0])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                  (cast (by subst hE; rfl) (HList.cons (suffix, ((0 : Nat), ())) HList.nil)))
                recV' (.returned (outV', cast (by subst hE; rfl) (HList.cons (suffix, (suffix.length, ())) HList.nil))) →
              ∃ gives givesV,
                Alone M source w.prover
                  (runStack a M callee none w.prover (hE ▸ [layP0])
                    (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                  recP' (.returned (outP', gives)) ∧
                Alone M source w.verifier
                  (runStack a M callee none w.verifier (hE ▸ [layV0])
                    (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                  recV' (.returned (outV', givesV)) := by
            intro hdr hE callee ins' first' matched' outP' outV' recP' recV' hAP hAV
            subst hE
            change Alone M source w.prover
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layP0]).run
                (retryOf M none) (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                (.cons ([] : List (M.Val wL.unitTy)) .nil))
              recP' (.returned (outP', .cons suffix .nil)) at hAP
            change Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layV0]).run
                (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                (.cons (suffix, ((0 : Nat), ())) .nil))
              recV' (.returned (outV', .cons (suffix, (suffix.length, ())) .nil)) at hAV
            refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
            · unfold runStack
              change Alone M source w.prover
                ((Stack.start M (Defs.fnTable M a.program.defs) [layP0]
                  (hideAll M w.prover ins') .nil).bind _) _ _
              have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                  [layP0] (hideAll M w.prover ins') .nil =
                  .done (.cons ([] : List (M.Val wL.unitTy)) .nil) := by
                change ((liftLocal id ((layoutPStart wL.unitTy).denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun first =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                rw [layoutPStart_denote]; rfl
              rw [hStP]; dsimp only [Process.bind]
              have hAP' := alone_mapHalt M (g := Prod.fst) hAP
              rw [← List.append_nil recP']
              refine alone_bind M hAP' ?_
              have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                  [layP0] (.cons suffix .nil) = .done (.cons suffix .nil) := by
                rw [stack_finish_one]; dsimp only [layP0, BuildLayoutStreaming.layP]
                rw [identityFinish_denote]; rfl
              rw [hFinP]; exact .done
            · unfold runStack
              change Alone M source w.verifier
                ((Stack.start M (Defs.fnTable M a.program.defs) [layV0]
                  (hideAll M w.verifier ins') (.cons suffix .nil)).bind _) _ _
              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                  [layV0] (hideAll M w.verifier ins') (.cons suffix .nil) =
                  .done (.cons (suffix, ((0 : Nat), ())) .nil) := by
                change ((liftLocal id ((layoutVStart wL.unitTy).denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier ins')))))).bind fun first =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first.single others) = _
                rw [layoutVStart_denote]; rfl
              rw [hStV]; dsimp only [Process.bind]
              have hAV' := alone_mapHalt M (g := Prod.fst) hAV
              rw [← List.append_nil recV']
              refine alone_bind M hAV' ?_
              have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                  [layV0] (.cons (suffix, (suffix.length, ())) .nil) = .done .nil := by
                rw [stack_finish_one]; dsimp only [layV0, BuildLayoutStreaming.layV]
                rw [layoutVFinish_denote]
                simp only [Nat.beq_refl, Bool.cond_true]; rfl
              rw [hFinV]; exact .done
          obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
          simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
          have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [layP0] := by
            dsimp only [DeployAuthored.toDeployed]
            rw [dite_eq_left rfl, hNoSamp, hLPW]
          have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [layV0] := by
            dsimp only [DeployAuthored.toDeployed]
            rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
          have hFirst' : Stack.Takes (hEntryF ▸ [layP0]) = [] := by
            rw [← hStackPEq]; exact first
          have hMatched' : Stack.Gives (hEntryF ▸ [layP0]) = Stack.Takes (hEntryF ▸ [layV0]) := by
            rw [← hStackPEq, ← hStackVEq]; exact matched
          obtain ⟨gives, givesV, hRunP, hRunV⟩ := hFinish _ hEntryF _ ins hFirst' hMatched'
            outP outV recP recV
            (alone_cast_stack1 M hEntryF layP0 rfl hAlP)
            (alone_cast_stack1 M hEntryF layV0 rfl hAlV0)
          refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
            recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
            ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
              ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
              ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
              (cast_heq _ _) hRunV
  | derived w hEq =>
      subst hEq
      have hRolesEq : proverAndVerifier w.foundPair.1 declaration = some (prover, verifier) := by
        simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
      rw [w.hPV] at hRolesEq; cases hRolesEq
      have hRecNil : w.layout.recover = [] := hNoRec w.layout w.hLayOpt
      cases buildLayoutLayers_ok_elim w.hLay with
      | compact wL _ => have hne := wL.hNonEmpty; simp [hRecNil] at hne
      | streaming wL hLPW hLVW =>
          have hEntryF : ((a.program.findProtocol declaration.entry).get
              (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
          let conPL : Layer V a.program.headers w.prover w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cPClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP,
              finish := emptyFinish w.stateTy }
          let conVL : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
            { line := .construction, state := w.stateTy, takes := [],
              gives := [], clauses := w.cVClauses, again := restoreAgain w.stateTy,
              start := constructionStart w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtV,
              finish := emptyFinish w.stateTy }
          let layPL : Layer V a.program.headers w.prover w.foundPair.1.ins := wL.layP
          let layVL : Layer V a.program.headers w.verifier w.foundPair.1.ins := wL.layV
          have hStartEq : ∀ (ins' : HList (LVal M) w.foundPair.1.ins),
              ins'.All (fun a v => M.Valid a.ty v) →
              ∃ st0,
                conPL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))) =
                  .done (.cons st0 .nil) ∧
                conVL.start.denote (localSem M a.program.headers.fns
                  (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))) =
                  .done (.cons st0 .nil) ∧
                M.Valid w.stateTy st0 := by
            intro ins' hIns'
            obtain ⟨st0, hDoneP, hSt0V⟩ := constructionStart_done M a
              w.sessBytes w.hSessBytes w.startRef w.absorbRef w.stmtP
              (heldValues M w.prover (hideAll M w.prover ins'))
              (heldValues_valid M w.prover _ (hideAll_valid M w.prover ins' hIns'))
            have hAgree := constructionStart_agree M a w.suite w.prover w.verifier
              w.foundPair.1.ins declaration.key w.sessBytes w.hSessBytes w.startRef w.absorbRef
              w.stmtP w.stmtV w.hSP w.hSV ins'
            exact ⟨st0, hDoneP, hAgree.symm.trans hDoneP, hSt0V⟩
          have hInsF := ins_cast_valid M hEntryF ins hIns
          obtain ⟨st0, hSt0P, hSt0V, hSt0Valid⟩ :=
            hStartEq (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) hEntryF) ins) hInsF
          let conP' : Layer V a.program.headers w.prover _ := hEntryF ▸ conPL
          let conV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ conVL
          let layP' : Layer V a.program.headers w.prover _ := hEntryF ▸ layPL
          let layV' : Layer V a.program.headers w.verifier _ := hEntryF ▸ layVL
          have hCPSt : conP'.state = w.stateTy := layer_cast_state hEntryF conPL
          have hCVSt : conV'.state = w.stateTy := layer_cast_state hEntryF conVL
          have hLPSt : layP'.state = .seq wL.unitTy none := layer_cast_state hEntryF layPL
          have hLVSt : layV'.state = streamStateTy wL.unitTy := layer_cast_state hEntryF layVL
          have hCC' : buildConstructionClauses.go a w.suite w.stateTy w.suiteUnitTy
              w.absorbRef w.prover w.verifier none declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.eventsWithAbsorb w.prover w.verifier [] id false) =
              .ok (hCPSt ▸ conP'.clauses, hCVSt ▸ conV'.clauses, w.sClauses) := by
            rw [layer_cast_clauses hEntryF conPL, layer_cast_clauses hEntryF conVL, hEntryF, ← hNoSamp]
            exact w.hCC
          have hSL' : buildStreamingLayoutClauses.go a w.layout wL.unitTy
              wL.hfree w.prover w.verifier declaration.key
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) 0
              ((((a.program.findProtocol declaration.entry).get
                (by rw [w.hFound]; rfl)).1).shape.events [] id) =
              .ok (hLPSt ▸ layP'.clauses, hLVSt ▸ layV'.clauses) := by
            rw [layer_cast_clauses hEntryF layPL, layer_cast_clauses hEntryF layVL, hEntryF]
            exact wL.hStr
          obtain ⟨out, outP, outV, finalSt, suffix, recP, source',
            hSufV, hAlP, hAlV, hPostP, hPostV, hLSrc', hAgSrc', hGEx'⟩ :=
            simulate_derived M w.hNe (d := w.toDeployed)
              w.hCon w.hLayOpt hSuiteLaw hLayLaw hCPSt hCVSt hLPSt hLVSt hCC' hSL'
              (protocolMeaning M a.program _ [] ins)
              (roleMeaning M a.program _ w.prover [] (hideAll M w.prover ins))
              (roleMeaning M a.program _ w.verifier [] (hideAll M w.verifier ins))
              st0 [] source hSt0Valid (fun _ h => nomatch h)
              hProjP hProjV hSafeP hSafeV hShapeP hShapeV hPShape hUniq hLP hFed hNoHalt'
          obtain ⟨recV, hAlV0⟩ := hAlV [] (fun _ h => nomatch h)
          have hFinish : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
              (callee : Member a.program.headers.protocols hdr)
              (ins' : HList (LVal M) hdr.ins)
              (hStartP' : conPL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.prover (hideAll M w.prover (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
              (hStartV' : conVL.start.denote (localSem M a.program.headers.fns
                (Defs.fnTable M a.program.defs)) []
                (Env.positional (heldValues M w.verifier (hideAll M w.verifier (cast (congrArg (fun h => HList (LVal M) h.ins) hE) ins')))) =
                .done (.cons st0 .nil))
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
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons ([] : List (M.Val wL.unitTy)) HList.nil))))
                recP' (.returned (outP', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons suffix HList.nil)))) →
              Alone M source w.verifier
                ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs) (hE ▸ [conVL, layVL])).run
                  (retryOf M none)
                  (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                  (cast (by subst hE; rfl)
                    (HList.cons st0 (HList.cons (suffix, ((0 : Nat), ())) HList.nil))))
                recV' (.returned (outV', cast (by subst hE; rfl)
                  (HList.cons finalSt (HList.cons (suffix, (suffix.length, ())) HList.nil)))) →
              ∃ gives givesV,
                Alone M source w.prover
                  (runStack a M callee none w.prover (hE ▸ [conPL, layPL])
                    (hideAll M w.prover ins') (cast (congrArg (HList M.Val) first'.symm) .nil))
                  recP' (.returned (outP', gives)) ∧
                Alone M source w.verifier
                  (runStack a M callee none w.verifier (hE ▸ [conVL, layVL])
                    (hideAll M w.verifier ins') (cast (congrArg (HList M.Val) matched') gives))
                  recV' (.returned (outV', givesV)) := by
            intro hdr hE callee ins' hSP' hSV' first' matched' outP' outV' recP' recV' hAP hAV
            subst hE
            dsimp only at hSP' hSV'
            simp only [cast_eq] at hSP' hSV'
            change Alone M source w.prover
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conPL, layPL]).run
                (retryOf M none) (roleMeaning M a.program callee w.prover [] (hideAll M w.prover ins'))
                (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)))
              recP' (.returned (outP', .cons finalSt (.cons suffix .nil))) at hAP
            change Alone M source w.verifier
              ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [conVL, layVL]).run
                (retryOf M none) (roleMeaning M a.program callee w.verifier [] (hideAll M w.verifier ins'))
                (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)))
              recV' (.returned (outV', .cons finalSt (.cons (suffix, (suffix.length, ())) .nil))) at hAV
            refine ⟨.cons suffix .nil, .nil, ?_, ?_⟩
            · unfold runStack
              change Alone M source w.prover
                ((Stack.start M (Defs.fnTable M a.program.defs) [conPL, layPL]
                  (hideAll M w.prover ins') .nil).bind _) _ _
              have hStP : Stack.start M (Defs.fnTable M a.program.defs)
                  [conPL, layPL] (hideAll M w.prover ins') .nil =
                  .done (.cons st0 (.cons ([] : List (M.Val wL.unitTy)) .nil)) := by
                change ((liftLocal id (conPL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutPStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (heldValues M w.prover (hideAll M w.prover ins'))))).bind fun f₂ =>
                        (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                          HList.cons f₁.single others) = _
                rw [hSP', liftLocal_done]
                dsimp only [Process.bind, HList.single]
                rw [layoutPStart_denote]; rfl
              rw [hStP]; dsimp only [Process.bind]
              have hAP' := alone_mapHalt M (g := Prod.fst) hAP
              rw [← List.append_nil recP']
              refine alone_bind M hAP' ?_
              have hFinP : Stack.finish M (Defs.fnTable M a.program.defs)
                  [conPL, layPL] (.cons finalSt (.cons suffix .nil)) =
                  .done (.cons suffix .nil) := by
                rw [stack_finish_two]; dsimp only [conPL, layPL, BuildLayoutStreaming.layP]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [identityFinish_denote]; rfl
              rw [hFinP]; exact .done
            · unfold runStack
              change Alone M source w.verifier
                ((Stack.start M (Defs.fnTable M a.program.defs) [conVL, layVL]
                  (hideAll M w.verifier ins') (.cons suffix .nil)).bind _) _ _
              have hStV : Stack.start M (Defs.fnTable M a.program.defs)
                  [conVL, layVL] (hideAll M w.verifier ins') (.cons suffix .nil) =
                  .done (.cons st0 (.cons (suffix, ((0 : Nat), ())) .nil)) := by
                change ((liftLocal id (conVL.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional (heldValues M w.verifier (hideAll M w.verifier ins'))))).bind fun f₁ =>
                    ((liftLocal id ((layoutVStart wL.unitTy).denote
                      (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                      (Env.positional (.cons suffix (heldValues M w.verifier (hideAll M w.verifier ins')))))).bind fun f₂ =>
                        (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons f₂.single others).map fun others =>
                          HList.cons f₁.single others) = _
                rw [hSV', liftLocal_done]
                dsimp only [Process.bind, HList.single]
                rw [layoutVStart_denote]; rfl
              rw [hStV]; dsimp only [Process.bind]
              have hAV' := alone_mapHalt M (g := Prod.fst) hAV
              rw [← List.append_nil recV']
              refine alone_bind M hAV' ?_
              have hFinV : Stack.finish M (Defs.fnTable M a.program.defs)
                  [conVL, layVL] (.cons finalSt (.cons (suffix, (suffix.length, ())) .nil)) =
                  .done .nil := by
                rw [stack_finish_two]; dsimp only [conVL, layVL, BuildLayoutStreaming.layV]
                rw [emptyFinish_denote]
                dsimp only [liftLocal_done, Process.bind]
                rw [layoutVFinish_denote]
                simp only [Nat.beq_refl, Bool.cond_true]; rfl
              rw [hFinV]; exact .done
          simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hAlV0
          have hStackPEq : w.toDeployed.stack w.prover = hEntryF ▸ [conPL, layPL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_left rfl, hNoSamp, hLPW]
          have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [conVL, layVL] := by
            dsimp only [DeployDerived.toDeployed]
            rw [dite_eq_right (Ne.symm w.hNe), dite_eq_left rfl, hLVW]
          have hFirst' : Stack.Takes (hEntryF ▸ [conPL, layPL]) = [] := by
            rw [← hStackPEq]; exact first
          have hMatched' : Stack.Gives (hEntryF ▸ [conPL, layPL]) = Stack.Takes (hEntryF ▸ [conVL, layVL]) := by
            rw [← hStackPEq, ← hStackVEq]; exact matched
          obtain ⟨gives, givesV, hRunP, hRunV⟩ :=
            hFinish _ hEntryF _ ins hSt0P hSt0V hFirst' hMatched'
              outP outV recP recV
              (alone_cast_stack2 M hEntryF conPL layPL rfl rfl hAlP)
              (alone_cast_stack2 M hEntryF conVL layVL rfl rfl hAlV0)
          refine ⟨outP, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackPEq.symm) gives,
            recP, outV, cast (congrArg (fun s => HList M.Val (Stack.Gives s)) hStackVEq.symm) givesV, recV,
            ?_, ?_, source', out, hLSrc', hAgSrc', hGEx', hPostP, hPostV⟩
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackPEq
              ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _) hRunP
          · exact alone_deployed_run_congr M (d := w.toDeployed) rfl hNoRetry hStackVEq
              ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
              (cast_heq _ _) hRunV

end Completeness

end Zkc.Core

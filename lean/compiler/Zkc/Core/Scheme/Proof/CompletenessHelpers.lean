module

public import Zkc.Core.Scheme.Proof.Coverage
public import Zkc.Core.Scheme.Proof.UniqueOccs

@[expose] public section

/-!
Shared completeness helpers: `Alone` / `GRun` / `Stack.handler` stepping lemmas, builder clause
lookup lemmas, `SuiteLawfulFor` / `LayoutLawful` / `SamplesLawful` evaluation wrappers, and
source-patching helpers for completeness and ideal random-oracle proofs.
-/

namespace Zkc.Core

open LayerBuild

open LayerBuild

section Completeness

variable {V : Vocabulary} (M : Model V)

/-! ### `Alone`, `patchSource`, and `Stack.handler` stepping lemmas -/

theorem alone_bind {source : Source M} {r : Role} {H A B : Type}
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

theorem alone_map {source : Source M} {r : Role} {H A B : Type}
    {p : Process (RSig M) H A} {f : A → B} {a : A} {rec : List (Happened M)}
    (hp : Alone M source r p rec (.returned a)) :
    Alone M source r (p.map f) rec (.returned (f a)) := by
  rw [Process.map_eq_bind, ← List.append_nil rec]
  exact alone_bind M hp .done

theorem alone_mapHalt {source : Source M} {r : Role} {H H' A : Type}
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
def patchSource (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) : Source M :=
  fun at_ τ =>
    if h : at_ = target ∧ τ = τ₀ then some (cast (congrArg M.Val h.2.symm) v₀)
    else source at_ τ

theorem patchSource_self (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) :
    patchSource M source target τ₀ v₀ target τ₀ = some v₀ := by
  unfold patchSource
  rw [dite_eq_left ⟨rfl, rfl⟩]
  rfl

theorem patchSource_ne (source : Source M) (target : Occurrence) (τ₀ : V.Ty)
    (v₀ : M.Val τ₀) {at_ : Occurrence} (hne : at_ ≠ target) (τ : V.Ty) :
    patchSource M source target τ₀ v₀ at_ τ = source at_ τ := by
  unfold patchSource
  rw [dite_eq_right (fun h => hne h.1)]

theorem lawful_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
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

theorem grun_of_agree {A : Type} {P : Occurrence → Prop} {s₁ s₂ : Source M}
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
theorem proverAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
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
theorem verifierAbsorbClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
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
theorem deriveClause_answer_hear {hs : Headers V} (fnTable : FnTable M hs.fns)
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

theorem deriveClause_answer_own {hs : Headers V} (fnTable : FnTable M hs.fns)
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

theorem layoutPWriteClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
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

theorem layoutVReadClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
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

theorem layoutVCarryClause_answer {hs : Headers V} (fnTable : FnTable M hs.fns)
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

theorem construction_clauses_answer_prover_flow_abs {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
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
  | _, [], _, _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, cP, cV, h, kind, getters, at_, τ, msg, st, hMsgV, hStV,
      ⟨e', he', hSite, hTy, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
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
                                    at_ hSiteEq msg st enc st' hEncD hAbsD pair.1
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
                        · cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
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
                    · cases h
                      rcases List.mem_cons.mp he' with hEqPair | hmem
                      · cases hEqPair; rw [hCls] at hECls; cases hECls
                      · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                  · cases h

theorem construction_clauses_answer_verifier_flow_abs {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      ∀ (kind : FlowKind) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        (∃ e, (e, true) ∈ es ∧ e.site = at_.site ∧ e.τ = τ ∧
          e.cls = .flow kind prover [verifier]) →
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
  | _, [], _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, cP, cV, h, kind, at_, τ, st,
      ⟨e', he', hSite, hTy, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
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
                            (msgLabel e.site) (msgLabel_bytes e.site) encRef absRef at_ hSiteEq st pair.2
                        · rcases List.mem_cons.mp he' with hEqPair | hmem
                          · cases hEqPair
                            rw [hCls] at hECls; cases hECls
                            exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                          · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                            refine ⟨encR, hE, ?_⟩
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
                        · cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · cases h
                                rcases List.mem_cons.mp he' with hEqPair | hmem
                                · cases hEqPair; rw [hCls] at hECls; cases hECls
                                · obtain ⟨encR, hE, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                                  refine ⟨encR, hE, ?_⟩
                                  unfold Clause.answer
                                  rw [dite_eq_right (fun hm => by cases hm.2.1)]
                                  exact hAns
                              · cases h
                        · cases h
                  · split at h
                    · cases h
                      rcases List.mem_cons.mp he' with hEqPair | hmem
                      · cases hEqPair; rw [hCls] at hECls; cases hECls
                      · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp he' with hEqPair | hmem
                    · cases hEqPair; rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
                  · cases h

/-- When no event at `(at_.site, kind, τ)` is marked for absorption (a trailing prover message),
neither `cP` nor `cV` matches the flow, so both layers pass the flow straight through in lockstep. -/
theorem construction_clauses_unmatched_elided_flow {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      ∀ (kind : FlowKind) (getters : List Role) (at_ : Occurrence) (τ : V.Ty) (msg : M.Val τ),
        (∀ e b, (e, b) ∈ es → e.site = at_.site → e.τ = τ →
          e.cls = .flow kind prover [verifier] → b = false) →
        (∀ c ∈ cP, ¬ ClauseMatches M c (.give kind getters at_ τ msg)) ∧
        (∀ c ∈ cV, ¬ ClauseMatches M c (.get kind prover at_ τ))
  | _, [], _, _, h, _, _, _, _, _, _ => by
      cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, h, kind, getters, at_, τ, msg, hNoAbs => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have hNoAbsRest : ∀ e' b', (e', b') ∈ rest → e'.site = at_.site → e'.τ = τ →
              e'.cls = .flow kind prover [verifier] → b' = false :=
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
                              (hPV.2 ▸ hKind ▸ hPV.1 ▸ hCls)
                            cases hFalse
                          · exact ihP c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro hM
                            have hSite : e.site = at_.site := hM.1
                            have hKind : kind₀ = kind := by
                              have hp := Option.some.inj hM.2.1; cases hp; rfl
                            have hTy : e.τ = τ := (List.cons.inj hM.2.2.2).1
                            have hFalse := hNoAbs e true List.mem_cons_self hSite hTy
                              (hPV.2 ▸ hKind ▸ hPV.1 ▸ hCls)
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
                        · cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
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
                    · cases h; exact ⟨ihP, ihV⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ⟨ihP, ihV⟩
                  · cases h

theorem construction_clauses_answer_prover_coin {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      ∀ (law : V.LawKey) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧
          p.1.cls = .given (.coin law) verifier [prover]) →
        ∃ (idxP : Nat) (eP : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxP]? = some eP ∧ eP.site = at_.site ∧ eP.τ = τ ∧
          eP.cls = .given (.coin law) verifier [prover] ∧
          findSuiteDerive enc a suite stateTy law [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cP (.hear (.coin law) verifier at_ τ) st =
            .call (.give .message [verifier] ⟨at_.path, drawToldKey events idxP⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cP, cV, h, law, at_, τ, st, hStV,
      ⟨p', hp', hSite, hTy, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k p'', rest[k]? = some p'' → events[(idx + 1) + k]? = some p''.1 := by
        intro k p'' hk
        have := hSuf (k + 1) p'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
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
                            ih ⟨p', hmem, hSite, hTy, hECls⟩
                          refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
              · split at h
                · cases h
                  rcases List.mem_cons.mp hp' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
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
                        · cases hDer : findSuiteDerive enc a suite stateTy law₀ sig.ins e.τ with
                          | none => rw [hDer] at h; cases h
                          | some derRef =>
                              rw [hDer] at h; dsimp only at h
                              split at h
                              · rename_i hIns
                                cases h
                                let derRefP : TypedFnRef V a.program.headers.fns [stateTy, bytesTy]
                                    [e.τ, stateTy] := hIns ▸ derRef
                                have hDerP : findSuiteDerive enc a suite stateTy law₀ [] e.τ = some derRefP := by
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
                                            hCoin.2 ▸ hCoin.1 ▸ hCls, hDerP,
                                            hSiteEq ▸ hDerD, hResV.1, hResV.2.1, ?_⟩
                                          exact deriveClause_answer_hear M _ _ prover verifier e.site law₀
                                            (drawToldKey events idx) (drawLabel e.site)
                                            (drawLabel_bytes e.site) derRefP at_ hSiteEq st coin st'
                                            hDerD pair.1
                                · rcases List.mem_cons.mp hp' with rfl | hmem
                                  · rw [hCls] at hECls; cases hECls
                                    exact absurd ⟨hSite, rfl, rfl, by cases hTy; rfl⟩ hMatch
                                  · obtain ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, hAns⟩ :=
                                      ih ⟨p', hmem, hSite, hTy, hECls⟩
                                    refine ⟨idxP, eP, derR, coin, st', h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
                                    unfold Clause.answer
                                    exact (dite_eq_right hMatch).trans hAns
                              · cases h
                        · cases h
                  · split at h
                    · rename_i hNil
                      cases h
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; cases hNil
                      · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h
                    rcases List.mem_cons.mp hp' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨p', hmem, hSite, hTy, hECls⟩
                  · cases h

theorem construction_clauses_answer_verifier_coin {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)),
      (∀ k p, es[k]? = some p → events[idx + k]? = some p.1) →
      ∀ {cP : List (Clause V a.program.headers prover stateTy)}
        {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      ∀ (law : V.LawKey) (hearers : List Role) (at_ : Occurrence) (τ : V.Ty) (st : M.Val stateTy),
        M.Valid stateTy st →
        (∃ p ∈ es, p.1.site = at_.site ∧ p.1.τ = τ ∧ hearers = [prover] ∧
          p.1.cls = .given (.coin law) verifier hearers) →
        ∃ (idxV : Nat) (eV : ShapeEvent V)
          (derRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy] [τ, stateTy])
          (coin : M.Val τ) (st' : M.Val stateTy),
          events[idxV]? = some eV ∧ eV.site = at_.site ∧ eV.τ = τ ∧
          eV.cls = .given (.coin law) verifier hearers ∧
          V.law law = some ⟨[], τ⟩ ∧
          findSuiteDerive enc a suite stateTy law [] τ = some derRef ∧
          derRef.eval M (Defs.fnTable M a.program.defs) (.cons st (.cons (drawLabel at_.site) .nil)) =
            .done (.cons coin (.cons st' .nil)) ∧
          M.Valid τ coin ∧ M.Valid stateTy st' ∧
          Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
            cV (.own (.coin law) hearers at_ [] .nil τ) st =
            .call (.give .message [prover] ⟨at_.path, drawToldKey events idxV⟩ τ coin)
              fun _ => .done (coin, st')
  | _, [], _, _, _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, (e, needAbs) :: rest, hSuf, cP, cV, h, law, hearers, at_, τ, st, hStV,
      ⟨p', hp', hSite, hTy, hPin, hECls⟩ => by
      unfold buildConstructionClauses.go at h
      have hSufRest : ∀ k p'', rest[k]? = some p'' → events[(idx + 1) + k]? = some p''.1 := by
        intro k p'' hk
        have := hSuf (k + 1) p'' hk
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hIdx : events[idx]? = some e := by simpa using hSuf 0 (e, needAbs) rfl
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
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
                          cases hDer : findSuiteDerive enc a suite stateTy law₀ sig.ins e.τ with
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
                                            hDerD pair.2
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
                      cases h
                      rcases List.mem_cons.mp hp' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls; rw [hPin] at hNil; cases hNil
                      · exact ih ⟨p', hmem, hSite, hTy, hPin, hECls⟩
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
theorem construction_clauses_unmatched_closed {enc : VocabEncoder V} {a : Admitted V} {suite : ModuleRef}
    {stateTy unitTy : V.Ty}
    {absRef : TypedFnRef V a.program.headers.fns [stateTy, bytesTy, .seq unitTy none] [stateTy]}
    {prover verifier : Role} {declKey : Key}
    {events : List (ShapeEvent V)} :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool))
      {cP : List (Clause V a.program.headers prover stateTy)}
      {cV : List (Clause V a.program.headers verifier stateTy)},
      buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
        declKey events idx es = .ok (cP, cV) →
      ∀ op, ROp.IsClosed M op →
        (∀ c ∈ cP, ¬ ClauseMatches M c op) ∧ (∀ c ∈ cV, ¬ ClauseMatches M c op)
  | _, [], _, _, h, _, _ => by cases h; exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, (e, needAbs) :: rest, cP, cV, h, op, hCl => by
      unfold buildConstructionClauses.go at h
      cases hRec : buildConstructionClauses.go enc a suite stateTy unitTy absRef prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
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
                        · cases hDer : findSuiteDerive enc a suite stateTy law sig.ins e.τ with
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
                                                cases hCoin.2
                                            | cons _ _ => exact False.elim hCl
                                        | request _ =>
                                            have hp := Option.some.inj hm.2.1; cases hp
                                    | give | get | hear | «begin» | settle =>
                                        simp [ROp.IsClosed, ROp.part, ClauseMatches, deriveClause] at hCl hm
                                  · exact ihV c hm
                              · cases h
                        · cases h
                  · split at h
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

theorem streaming_layout_answer_prover_flow {a : Admitted V} {layout : Layout}
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
        (∃ e ∈ es, e.site = at_.site ∧ e.τ = τ ∧ getters = [verifier] ∧ e.cls = .flow kind prover getters) →
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

theorem streaming_layout_answer_verifier_flow {a : Admitted V} {layout : Layout}
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
          e.cls = .flow kind prover [verifier]) →
        ∃ (rRef : SafeFnRef V a.program.headers.fns [.seq unitTy none, .nat] [τ, .nat]),
          findLayoutRead a layout.module unitTy τ = some rRef ∧
          (∀ v nextOff,
            rRef.eval M (Defs.fnTable M a.program.defs) (.cons buf (.cons off .nil)) =
              .done (.cons v (.cons nextOff .nil)) →
            Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              vCs (.get kind prover at_ τ) (buf, (off, ())) = .done (v, (buf, (nextOff, ()))))
  | _, [], _, _, _, _, _, _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | idx, e :: rest, pCs, vCs, h, kind, at_, τ, buf, off,
      ⟨e', he', hSite, hTy, hECls⟩ => by
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
                    · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                      refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                      unfold Clause.answer
                      exact (dite_eq_right hMatch).trans (hAns v nextOff hRD)
              · rename_i hNotPV
                cases h
                rcases List.mem_cons.mp he' with rfl | hmem
                · rw [hCls] at hECls; cases hECls; exact absurd ⟨rfl, rfl⟩ hNotPV
                · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
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
                        · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                          refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                          unfold Clause.answer
                          rw [dite_eq_right (fun hm => by cases hm.2.1)]
                          exact hAns v nextOff hRD
                    · cases h
                      rcases List.mem_cons.mp he' with rfl | hmem
                      · rw [hCls] at hECls; cases hECls
                      · obtain ⟨rR, h1, hAns⟩ := ih ⟨e', hmem, hSite, hTy, hECls⟩
                        refine ⟨rR, h1, fun v nextOff hRD => ?_⟩
                        unfold Clause.answer
                        rw [dite_eq_right (fun hm => by cases hm.2.1)]
                        exact hAns v nextOff hRD
                  · cases h
                    rcases List.mem_cons.mp he' with rfl | hmem
                    · rw [hCls] at hECls; cases hECls
                    · exact ih ⟨e', hmem, hSite, hTy, hECls⟩
              | request _ =>
                  cases h
                  rcases List.mem_cons.mp he' with rfl | hmem
                  · rw [hCls] at hECls; cases hECls
                  · exact ih ⟨e', hmem, hSite, hTy, hECls⟩

theorem streaming_layout_answer_told {a : Admitted V} {layout : Layout}
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
          e₀.cls = .given (.coin law) verifier hearers → hearers = [prover] →
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

theorem suiteLawful_allows {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawfulFor enc M)
    {stateTy τ : V.Ty} {law : V.LawKey}
    {startRef : TypedFnRef V d.admitted.program.headers.fns [bytesTy] [stateTy]}
    (hStart : findSuiteStart d.admitted suite = some ⟨stateTy, startRef⟩)
    {derRef : TypedFnRef V d.admitted.program.headers.fns [stateTy, bytesTy] [τ, stateTy]}
    (hFind : findSuiteDerive enc d.admitted suite stateTy law [] τ = some derRef)
    {e : ShapeEvent V} (hE : e ∈ d.entry.shape.events [] id)
    {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) (hTy : e.τ = τ)
    (hLaw : V.law law = some ⟨[], τ⟩)
    {st st' : M.Val stateTy} {label : List Nat} {coin : M.Val τ}
    (hStV : M.Valid stateTy st) (hLbl : ∀ b, b ∈ label → b < 256)
    (hEval : derRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil)) =
      .done (.cons coin (.cons st' .nil))) :
    Allows M (.coin law) [] .nil τ coin := by
  subst hTy
  have hSuite' := hSuite suite sessionTag hCon
  have hFnEq : Defs.fnTable M d.admitted.program.defs derRef.hdr derRef.member
      (cast (congrArg (HList M.Val) derRef.insEq.symm) (.cons st (.cons label .nil))) =
      .done (cast (congrArg (HList M.Val) derRef.outsEq.symm) (.cons coin (.cons st' .nil))) := by
    have hEq := derRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs) (.cons st (.cons label .nil))
    rw [hEval] at hEq
    rcases derRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut
    cases hIn; cases hOut
    exact hEq.symm
  exact hSuite'.1 e law owner h0 hs [] stateTy startRef derRef hStart hE hCls hLaw hFind
    st label .nil coin st' hStV hLbl trivial hFnEq

theorem suiteLawfulFor_encode_injective {enc : VocabEncoder V} {d : Deployed V} {suite : ModuleRef}
    {sessionTag : Option (List Nat)}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawfulFor enc M)
    {unitTy τ : V.Ty} {encRef : TypedFnRef V d.admitted.program.headers.fns [τ] [.seq unitTy none]}
    (hFind : findSuiteEncode d.admitted suite unitTy τ = some encRef)
    {v₁ v₂ : M.Val τ} {u : List (M.Val unitTy)}
    (hV₁ : M.Valid τ v₁) (hV₂ : M.Valid τ v₂)
    (hE₁ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₁ .nil) = .done (.cons u .nil))
    (hE₂ : encRef.eval M (Defs.fnTable M d.admitted.program.defs) (.cons v₂ .nil) = .done (.cons u .nil)) :
    v₁ = v₂ := by
  have hSuite' := hSuite suite sessionTag hCon
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
  exact hSuite'.2 eKey hInSuite encRef.hdr encRef.member hProgFind unitTy τ
    encRef.insEq encRef.outsEq v₁ v₂ u hV₁ hV₂ hFn₁ hFn₂

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
  have hSuite' := hSuite suite sessionTag hCon
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
  exact hSuite'.2 eKey hInSuite encRef.hdr encRef.member hProgFind unitTy τ
    encRef.insEq encRef.outsEq v₁ v₂ u hV₁ hV₂ hFn₁ hFn₂

theorem samplesLawful_allows {enc : VocabEncoder V} {d : Deployed V} {sKey : Key}
    {prover verifier : Role} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {sessBytes : List Nat} {hSess : ∀ b, b ∈ sessBytes → b < 256}
    (hSamp : d.declaration.samples = some sKey)
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hRoles : d.roles = some (prover, verifier))
    (hRes : resolveSessionBytes enc d.admitted d.declaration sessionTag = .ok ⟨sessBytes, hSess⟩)
    (hSampLaw : d.SamplesLawfulFor enc M)
    {τ : V.Ty} {sRef : TypedFnRef V d.admitted.program.headers.fns
      (held prover d.entry.ins ++ [bytesTy, bytesTy, .nat, .nat]) [τ]}
    (hFind : findTypedFnRef d.admitted sKey
      (held prover d.entry.ins ++ [bytesTy, bytesTy, .nat, .nat]) [τ] = some sRef)
    {e : ShapeEvent V} (hE : e ∈ d.entry.shape.events [] id)
    {law : V.LawKey}
    (hCls : e.cls = .given (.coin law) prover []) (hTy : e.τ = τ)
    (hLaw : V.law law = some ⟨[], τ⟩)
    {heldVals : HList M.Val (held prover d.entry.ins)}
    {attemptNum callSeq : Nat} {coin : M.Val τ}
    (hHeldV : heldVals.All M.Valid)
    (hEval : sRef.eval M (Defs.fnTable M d.admitted.program.defs)
      (HList.append heldVals (.cons sessBytes (.cons (encodeSite e.site) (.cons (a := Ty.nat) attemptNum (.cons (a := Ty.nat) callSeq .nil))))) =
      .done (.cons coin .nil)) :
    Allows M (.coin law) [] .nil τ coin := by
  subst hTy
  have hProgFind := findTypedFnRef_some hFind
  have hFnEq : Defs.fnTable M d.admitted.program.defs sRef.hdr sRef.member
      (cast (congrArg (HList M.Val) sRef.insEq.symm)
        (HList.append heldVals (.cons sessBytes (.cons (encodeSite e.site) (.cons (a := Ty.nat) attemptNum (.cons (a := Ty.nat) callSeq .nil)))))) =
      .done (cast (congrArg (HList M.Val) sRef.outsEq.symm) (.cons coin .nil)) := by
    have hEq := sRef.eval_eq_fnTable M (Defs.fnTable M d.admitted.program.defs)
      (HList.append heldVals (.cons sessBytes (.cons (encodeSite e.site) (.cons (a := Ty.nat) attemptNum (.cons (a := Ty.nat) callSeq .nil)))))
    rw [hEval] at hEq
    rcases sRef with ⟨⟨_, _, _, _, _⟩, member, hIn, hOut, _, _⟩
    dsimp only at hIn hOut; cases hIn; cases hOut; exact hEq.symm
  exact hSampLaw sKey prover verifier suite sessionTag sessBytes hSess hSamp hCon hRoles hRes
    sRef.hdr sRef.member hProgFind e law hE hCls hLaw sRef.insEq sRef.outsEq heldVals
    attemptNum callSeq coin hHeldV hFnEq

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
  have hLay' := hLayLaw layout hLayOpt
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
  have hRF := hLay'.1 wKey rKey hInW hInR wRef.hdr rRef.hdr wRef.member rRef.member
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
  have hLay' := hLayLaw layout hLayOpt
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
    hLay'.2.1 wKey rKey hInW hInR wRef.hdr rRef.hdr wRef.member rRef.member
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
  have hLay' := hLayLaw layout hLayOpt
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
      have hIff := hLay'.2.2 eqKey hInE eqRef.hdr eqRef.member hFindE τ
        eqRef.insEq eqRef.outsEq v v b hV hV hFn
      have hb : b = true := hIff.mpr rfl
      subst hb
      exact hDone

/-! ### Mark-peeling helpers for `Proj.begins` and `Proj.settles` -/

def isRoleMark {A : Type} : Program M A → Prop
  | .call (.begin _) _ => True
  | .call (.settle _) _ => True
  | _ => False

theorem proj_peel_begin {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Nat → Program M B},
      Proj M r post p (.call (.begin at_) k) → Proj M r post p (k 0)
  | _, _, _, .begins h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_begin h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_begin (h v))

theorem proj_peel_settle {A B : Type} {r : Role} {post : A → B → Prop} :
    ∀ {p : Protocol M A} {at_ : Occurrence} {k : Unit → Program M B},
      Proj M r post p (.call (.settle at_) k) → Proj M r post p (k ())
  | _, _, _, .settles h => h
  | _, _, _, .stopsElsewhere h => .stopsElsewhere h
  | _, _, _, .passed h1 h2 h => .passed h1 h2 (proj_peel_settle h)
  | _, _, _, .unheard h1 h2 h => .unheard h1 h2 (fun v => proj_peel_settle (h v))

theorem peelMarks_alone {A B σ : Type} {r : Role}
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

theorem stack_run_begin {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Nat → Program M B) (s : σ)
    (hPass : h.clause (.begin at_) s = .call (.begin at_) fun n => .done (n, s)) :
    h.run (retryOf M none) (.call (.begin at_) k) s =
      .call (.begin at_) fun n => h.run (retryOf M none) (k n) s := by
  change (h.clause (.begin at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

theorem stack_run_settle {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (at_ : Occurrence) (k : Unit → Program M B) (s : σ)
    (hPass : h.clause (.settle at_) s = .call (.settle at_) fun u => .done (u, s)) :
    h.run (retryOf M none) (.call (.settle at_) k) s =
      .call (.settle at_) fun u => h.run (retryOf M none) (k u) s := by
  change (h.clause (.settle at_) s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hPass]
  rfl

theorem stack_run_own {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
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

theorem stack_run_clause_done {σ B : Type} (h : Handler (RSig M) (RSig M) Stop σ)
    (op : ROp M) (k : (RSig M).Reply op → Program M B) (s s' : σ) (reply : (RSig M).Reply op)
    (hStep : h.clause op s = .done (reply, s')) :
    h.run (retryOf M none) (.call op k) s = h.run (retryOf M none) (k reply) s' := by
  change (h.clause op s).bind (fun out => h.run (retryOf M none) (k out.1) out.2) = _
  rw [hStep]
  rfl

theorem layer_cast_state {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) : (h ▸ l).state = l.state := by
  subst h; rfl

theorem layer_cast_clauses {hs : Headers V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
    (h : hdr₁ = hdr₂) (l : Layer V hs r hdr₂.ins) :
    (layer_cast_state h l) ▸ (h ▸ l).clauses = l.clauses := by
  subst h; rfl

theorem ins_cast_valid {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (LVal M) hdr₁.ins) (hv : ins.All (fun a v => M.Valid a.ty v)) :
    (cast (congrArg (fun hdr => HList (LVal M) hdr.ins) h) ins).All (fun a v => M.Valid a.ty v) := by
  subst h; exact hv

theorem insRV_cast_valid {r : Role} {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
    (ins : HList (RV M r) hdr₁.ins) (hv : ins.All (RV.Valid M r)) :
    (cast (congrArg (fun hdr => HList (RV M r) hdr.ins) h) ins).All (RV.Valid M r) := by
  subst h; exact hv

theorem alone_cast_stack1 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
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

theorem alone_cast_stack2 {a : Admitted V} {r : Role} {hdr₁ hdr₂ : ProtocolHeader V}
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

theorem alone_deployed_run_congr {a : Admitted V} {d : Deployed V} (hA : d.admitted = a)
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

theorem mem_heardCoins_of_event {s : Shape V} {e : ShapeEvent V}
    (hE : e ∈ s.events [] id) {law : V.LawKey} {owner h0 : Role} {hs : List Role}
    (hCls : e.cls = .given (.coin law) owner (h0 :: hs)) :
    e.site ∈ s.heardCoins := by
  unfold Shape.heardCoins
  exact List.mem_filterMap.mpr ⟨e, hE, by simp [hCls]⟩


end Completeness

end Zkc.Core

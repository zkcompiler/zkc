module

public import Zkc.Core.Scheme.Proof.IdealLink
public import Zkc.Core.Scheme.Deploy.Structural

@[expose] public section

/-!
Random-oracle query uniqueness and cross-session / cross-statement domain separation for ideal
random-oracle deployments (`deployIdeal`).

Every draw clause in `deployIdeal` appends its labeled coin onto the pure transcript path
`(metaLog, dataLog)` after querying `serviceKey`, and every message absorption appends its labeled
encoded message onto `(metaLog, dataLog)`. Consequently:
1. Within any single execution path of `dIdeal.run M verifier ins taken` (even on arbitrary
   malicious proofs or inside runtime loops), every `serviceKey` query `(st, label)` extends the
   canonical initial path `st0` and has strictly increasing `st.1.length`, so the emitted query
   sequence is strictly duplicate-free (`qs.Nodup`, `deployIdeal_queries_nodup`).
2. Across any two deployments whose `(sessionTag, declaration, erased closure)` differ, `st0.1[0]?`
   commits `0 :: sessBytes`, so by `resolveSessionBytes_injective` no query from one deployment can
   ever collide with any query from the other (`deployIdeal_cross_session_disjoint`).
3. Across any two valid verifier inputs `ins₁, ins₂` of one deployment that differ on a statement
   input (under injective `SuiteSlot.encode`), `st0₁` and `st0₂` have equal length and distinct
   encoded data entries, so no query from `ins₁` can ever collide with any query from `ins₂`
   (`deployIdeal_cross_statement_disjoint`).
-/

namespace Zkc.Core

open LayerBuild

section QuerySeparation

variable {V : Vocabulary} (M : Model V)

/-! ## Local `Process.mapHalt` algebraic laws -/

private theorem mapHalt_id' {S : Sig} {H A : Type} :
    ∀ (p : Process S H A), p.mapHalt id = p
  | .done _ => rfl
  | .halt _ => rfl
  | .call _ k => by simp only [Process.mapHalt]; congr 1; funext r; exact mapHalt_id' (k r)

private theorem mapHalt_mapHalt {S : Sig} {H₁ H₂ H₃ A : Type} (f : H₁ → H₂) (g : H₂ → H₃) :
    ∀ (p : Process S H₁ A), (p.mapHalt f).mapHalt g = p.mapHalt (fun h => g (f h))
  | .done _ => rfl
  | .halt _ => rfl
  | .call _ k => by simp only [Process.mapHalt]; congr 1; funext r; exact mapHalt_mapHalt f g (k r)

private theorem mapHalt_map {S : Sig} {H₁ H₂ A B : Type} (f : A → B) (g : H₁ → H₂) :
    ∀ (p : Process S H₁ A), (p.map f).mapHalt g = (p.mapHalt g).map f
  | .done _ => rfl
  | .halt _ => rfl
  | .call _ k => by simp only [Process.map, Process.mapHalt]; congr 1; funext r; exact mapHalt_map f g (k r)

private theorem mapHalt_bind {S : Sig} {H₁ H₂ A B : Type} (g : H₁ → H₂) (k : A → Process S H₁ B) :
    ∀ (p : Process S H₁ A), (p.bind k).mapHalt g = (p.mapHalt g).bind fun a => (k a).mapHalt g
  | .done _ => rfl
  | .halt _ => rfl
  | .call _ k' => by simp only [Process.bind, Process.mapHalt]; congr 1; funext r; exact mapHalt_bind g k (k' r)

/-! ## Universal path-growing invariant and extracted service-query traces -/

/-- The dedicated ideal random-oracle service key does not collide with any application service
request declared by the protocol shape. -/
def ServiceKeyFresh (shape : Shape V) (serviceKey : Key) : Prop :=
  ∀ e ∈ shape.events [] id, ∀ svc owner hearers,
    e.cls = .given (.request svc) owner hearers → svc ≠ serviceKey

/-- Whether an `ROp` is NOT a request to `serviceKey`. -/
def ROp.NotService (serviceKey : Key) : ROp M → Prop
  | .own (.request svc) _ _ _ _ _ => svc ≠ serviceKey
  | _ => True

/-- Every path through `p` emits `serviceKey` ideal-oracle queries `(st, label)` whose transcript
path `st` extends `(prefixMeta, prefixData)` and has strictly increasing length starting from at
least `minLen`. -/
def Process.QueriesGrowing (unitTy : V.Ty) (serviceKey : Key)
    (prefixMeta : List (List Nat)) (prefixData : List (List (M.Val unitTy)))
    (minLen : Nat) {H A : Type} : Process (RSig M) H A → Prop
  | .done _ => True
  | .halt _ => True
  | .call (.own (.request svc) _ _ ins payload _) k =>
      if svc = serviceKey then
        ∃ (h : ins = [idealQueryTy unitTy]),
          let q : M.Val (idealQueryTy unitTy) :=
            (cast (congrArg (HList M.Val) h) payload).single
          prefixMeta <+: q.1.1 ∧ prefixData <+: q.1.2.1 ∧ minLen ≤ q.1.1.length ∧
          ∀ reply, Process.QueriesGrowing unitTy serviceKey prefixMeta prefixData
            (q.1.1.length + 1) (k reply)
      else
        ∀ reply, Process.QueriesGrowing unitTy serviceKey prefixMeta prefixData minLen (k reply)
  | .call _ k =>
      ∀ reply, Process.QueriesGrowing unitTy serviceKey prefixMeta prefixData minLen (k reply)

/-- A process never emits any `serviceKey` request along any path. -/
def Process.NoService (serviceKey : Key) {H A : Type} : Process (RSig M) H A → Prop
  | .done _ => True
  | .halt _ => True
  | .call op k => ROp.NotService M serviceKey op ∧ ∀ reply, Process.NoService serviceKey (k reply)

/-- Exact sequence of `serviceKey` ideal-oracle queries emitted along an execution path of `p`. -/
inductive Process.ServiceQueries (unitTy : V.Ty) (serviceKey : Key) {H A : Type} :
    Process (RSig M) H A → List (M.Val (idealQueryTy unitTy)) → Prop where
  | done {a} : ServiceQueries unitTy serviceKey (.done a) []
  | halt {why} : ServiceQueries unitTy serviceKey (.halt why) []
  | query {hearers at_ payload τ reply k qs} :
      ServiceQueries unitTy serviceKey (k reply) qs →
      ServiceQueries unitTy serviceKey
        (.call (.own (.request serviceKey) hearers at_ [idealQueryTy unitTy] payload τ) k)
        (payload.single :: qs)
  | other {op k reply qs} :
      ROp.NotService M serviceKey op →
      ServiceQueries unitTy serviceKey (k reply) qs →
      ServiceQueries unitTy serviceKey (.call op k) qs

theorem Process.queriesGrowing_mono {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {H A : Type}
    {m₁ m₂ : Nat} (hle : m₁ ≤ m₂) :
    ∀ {p : Process (RSig M) H A},
      p.QueriesGrowing M unitTy serviceKey pMeta pData m₂ →
      p.QueriesGrowing M unitTy serviceKey pMeta pData m₁
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give ..) _, h => fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.get ..) _, h => fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.own (.coin _) ..) _, h => fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.own (.request svc) ..) _, h => by
      dsimp only [Process.QueriesGrowing] at h ⊢
      split at h
      · next hEq =>
          rw [ite_eq_left hEq]
          obtain ⟨hIns, hPM, hPD, hLen, hCont⟩ := h
          exact ⟨hIns, hPM, hPD, Nat.le_trans hle hLen, hCont⟩
      · next hNe =>
          rw [ite_eq_right hNe]
          exact fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.hear ..) _, h => fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.begin _) _, h => fun r => Process.queriesGrowing_mono hle (h r)
  | .call (.settle _) _, h => fun r => Process.queriesGrowing_mono hle (h r)

theorem Process.queriesGrowing_map {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {minLen : Nat}
    {H A B : Type} (f : A → B) :
    ∀ {p : Process (RSig M) H A},
      p.QueriesGrowing M unitTy serviceKey pMeta pData minLen →
      (p.map f).QueriesGrowing M unitTy serviceKey pMeta pData minLen
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give ..) _, h => fun r => Process.queriesGrowing_map f (h r)
  | .call (.get ..) _, h => fun r => Process.queriesGrowing_map f (h r)
  | .call (.own (.coin _) ..) _, h => fun r => Process.queriesGrowing_map f (h r)
  | .call (.own (.request svc) ..) _, h => by
      dsimp only [Process.map, Process.QueriesGrowing] at h ⊢
      split at h
      · next hEq =>
          rw [ite_eq_left hEq]
          obtain ⟨hIns, hPM, hPD, hLen, hCont⟩ := h
          exact ⟨hIns, hPM, hPD, hLen, fun r => Process.queriesGrowing_map f (hCont r)⟩
      · next hNe =>
          rw [ite_eq_right hNe]
          exact fun r => Process.queriesGrowing_map f (h r)
  | .call (.hear ..) _, h => fun r => Process.queriesGrowing_map f (h r)
  | .call (.begin _) _, h => fun r => Process.queriesGrowing_map f (h r)
  | .call (.settle _) _, h => fun r => Process.queriesGrowing_map f (h r)

theorem Process.queriesGrowing_mapHalt {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {minLen : Nat}
    {H₁ H₂ A : Type} (f : H₁ → H₂) :
    ∀ {p : Process (RSig M) H₁ A},
      p.QueriesGrowing M unitTy serviceKey pMeta pData minLen →
      (p.mapHalt f).QueriesGrowing M unitTy serviceKey pMeta pData minLen
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call (.give ..) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.get ..) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.own (.coin _) ..) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.own (.request svc) ..) _, h => by
      dsimp only [Process.mapHalt, Process.QueriesGrowing] at h ⊢
      split at h
      · next hEq =>
          rw [ite_eq_left hEq]
          obtain ⟨hIns, hPM, hPD, hLen, hCont⟩ := h
          exact ⟨hIns, hPM, hPD, hLen, fun r => Process.queriesGrowing_mapHalt f (hCont r)⟩
      · next hNe =>
          rw [ite_eq_right hNe]
          exact fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.hear ..) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.begin _) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)
  | .call (.settle _) _, h => fun r => Process.queriesGrowing_mapHalt f (h r)

theorem Process.queriesGrowing_bind_noService {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {minLen : Nat}
    {H A B : Type} {k : A → Process (RSig M) H B} :
    ∀ {p : Process (RSig M) H A},
      p.NoService M serviceKey →
      (∀ a, (k a).QueriesGrowing M unitTy serviceKey pMeta pData minLen) →
      (p.bind k).QueriesGrowing M unitTy serviceKey pMeta pData minLen
  | .done a, _, hk => hk a
  | .halt _, _, _ => trivial
  | .call (.give ..) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.get ..) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.own (.coin _) ..) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.own (.request svc) ..) _, ⟨hNe, hns⟩, hk => by
      dsimp only [Process.bind, Process.QueriesGrowing]
      rw [ite_eq_right hNe]
      exact fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.hear ..) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.begin _) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk
  | .call (.settle _) _, ⟨_, hns⟩, hk => fun r => Process.queriesGrowing_bind_noService (hns r) hk

theorem Process.queriesGrowing_bind_liftLocal {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {minLen : Nat}
    {H A B : Type} (f : Stop → H) (p : Local A) (k : A → Process (RSig M) H B)
    (hk : ∀ a, (k a).QueriesGrowing M unitTy serviceKey pMeta pData minLen) :
    ((liftLocal (S := RSig M) f p).bind k).QueriesGrowing M unitTy serviceKey pMeta pData minLen := by
  cases p with
  | done a => exact hk a
  | halt _ => trivial
  | call op _ => cases op

theorem Process.queriesGrowing_bind_after_noService {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {minLen : Nat}
    {H A B : Type} {k : A → Process (RSig M) H B}
    (hk : ∀ a, (k a).NoService M serviceKey) :
    ∀ {p : Process (RSig M) H A},
      p.QueriesGrowing M unitTy serviceKey pMeta pData minLen →
      (p.bind k).QueriesGrowing M unitTy serviceKey pMeta pData minLen
  | .done a, _ =>
      let rec go {m : Nat} : ∀ {q : Process (RSig M) H B},
          q.NoService M serviceKey → q.QueriesGrowing M unitTy serviceKey pMeta pData m
        | .done _, _ => trivial
        | .halt _, _ => trivial
        | .call (.give ..) _, ⟨_, h⟩ => fun r => go (h r)
        | .call (.get ..) _, ⟨_, h⟩ => fun r => go (h r)
        | .call (.own (.coin _) ..) _, ⟨_, h⟩ => fun r => go (h r)
        | .call (.own (.request svc) ..) _, ⟨hNe, h⟩ => by
            dsimp only [Process.QueriesGrowing]; rw [ite_eq_right hNe]; exact fun r => go (h r)
        | .call (.hear ..) _, ⟨_, h⟩ => fun r => go (h r)
        | .call (.begin _) _, ⟨_, h⟩ => fun r => go (h r)
        | .call (.settle _) _, ⟨_, h⟩ => fun r => go (h r)
      go (hk a)
  | .halt _, _ => trivial
  | .call (.give ..) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.get ..) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.own (.coin _) ..) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.own (.request svc) ..) _, h => by
      dsimp only [Process.bind, Process.QueriesGrowing] at h ⊢
      split at h
      · next hEq =>
          rw [ite_eq_left hEq]
          obtain ⟨hIns, hPM, hPD, hLen, hCont⟩ := h
          exact ⟨hIns, hPM, hPD, hLen, fun r => Process.queriesGrowing_bind_after_noService hk (hCont r)⟩
      · next hNe =>
          rw [ite_eq_right hNe]
          exact fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.hear ..) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.begin _) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)
  | .call (.settle _) _, h => fun r => Process.queriesGrowing_bind_after_noService hk (h r)

theorem Process.noService_map {serviceKey : Key} {H A B : Type} (f : A → B) :
    ∀ {p : Process (RSig M) H A}, p.NoService M serviceKey → (p.map f).NoService M serviceKey
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ _, ⟨hOp, hk⟩ => ⟨hOp, fun r => Process.noService_map f (hk r)⟩

theorem Process.noService_mapHalt {serviceKey : Key} {H₁ H₂ A : Type} (f : H₁ → H₂) :
    ∀ {p : Process (RSig M) H₁ A}, p.NoService M serviceKey → (p.mapHalt f).NoService M serviceKey
  | .done _, _ => trivial
  | .halt _, _ => trivial
  | .call _ _, ⟨hOp, hk⟩ => ⟨hOp, fun r => Process.noService_mapHalt f (hk r)⟩

theorem Process.noService_bind {serviceKey : Key} {H A B : Type} {k : A → Process (RSig M) H B} :
    ∀ {p : Process (RSig M) H A},
      p.NoService M serviceKey → (∀ a, (k a).NoService M serviceKey) →
      (p.bind k).NoService M serviceKey
  | .done a, _, hk => hk a
  | .halt _, _, _ => trivial
  | .call _ _, ⟨hOp, hp⟩, hk => ⟨hOp, fun r => Process.noService_bind (hp r) hk⟩

theorem Process.noService_liftLocal {serviceKey : Key} {H A : Type} (f : Stop → H) (p : Local A) :
    (liftLocal (S := RSig M) f p).NoService M serviceKey := by
  cases p with
  | done _ => trivial
  | halt _ => trivial
  | call op _ => cases op

theorem Stack.finish_noService {hs : Headers V} (fnTable : FnTable M hs.fns) {r : Role}
    {ins : List (LTy V)} (serviceKey : Key) :
    ∀ (layers : List (Layer V hs r ins)) (states : HList M.Val (Stack.States layers)),
      (Stack.finish M fnTable layers states).NoService M serviceKey
  | [], .nil => trivial
  | _ :: rest, .cons _ states =>
      Process.noService_bind M (Process.noService_liftLocal M _ _) fun _ =>
        Process.noService_map M _ (Stack.finish_noService fnTable serviceKey rest states)

/-- Core extraction lemma: every query sequence `qs` emitted by a `QueriesGrowing` process is
strictly duplicate-free (`qs.Nodup`), every query extends `(pMeta, pData)`, and every query's
transcript path length is at least `minLen`. -/
theorem Process.queriesGrowing_nodup {unitTy : V.Ty} {serviceKey : Key}
    {pMeta : List (List Nat)} {pData : List (List (M.Val unitTy))} {H A : Type}
    {minLen : Nat} {p : Process (RSig M) H A} {qs : List (M.Val (idealQueryTy unitTy))}
    (hG : p.QueriesGrowing M unitTy serviceKey pMeta pData minLen)
    (hSQ : p.ServiceQueries M unitTy serviceKey qs) :
    qs.Nodup ∧ ∀ q ∈ qs, pMeta <+: q.1.1 ∧ pData <+: q.1.2.1 ∧ minLen ≤ q.1.1.length := by
  induction hSQ generalizing minLen with
  | done => exact ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | halt => exact ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | @query _ _ payload _ reply _ _ _ ih =>
      dsimp only [Process.QueriesGrowing] at hG
      rw [ite_eq_left rfl] at hG
      obtain ⟨_, hPM, hPD, hLen, hCont⟩ := hG
      simp only [cast_eq] at hPM hPD hLen hCont
      obtain ⟨hNodup, hAll⟩ := ih (hCont reply)
      refine ⟨List.nodup_cons.mpr ⟨?_, hNodup⟩, ?_⟩
      · intro hMem
        have hGe := (hAll payload.single hMem).2.2
        omega
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hMem
        · exact ⟨hPM, hPD, hLen⟩
        · obtain ⟨h1, h2, h3⟩ := hAll q hMem
          exact ⟨h1, h2, Nat.le_trans hLen (Nat.le_of_succ_le h3)⟩
  | @other op _ reply _ hNot _ ih =>
      cases op with
      | give | get | «begin» | settle | hear =>
          exact ih (hG reply)
      | own kind =>
          cases kind with
          | coin _ => exact ih (hG reply)
          | request svc =>
              dsimp only [ROp.NotService] at hNot
              dsimp only [Process.QueriesGrowing] at hG
              rw [ite_eq_right hNot] at hG
              exact ih (hG reply)

/-! ## Clause and 2-layer stack preservation for ideal random-oracle verifiers -/

/-- A layout clause never emits a `serviceKey` request on any matching effect. -/
private def LayoutClauseNoService {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty} (serviceKey : Key)
    (c : Clause V hs r state) : Prop :=
  ∀ (op : ROp M) (hMatch : ClauseMatches M c op) (s : M.Val state),
    (c.code.denote (roleSem M r fnTable rTable) (ROp.occurrence M op).path
      (Env.positional (aloneIn M r (HList.append
        (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op))
        (.cons s .nil))))).NoService M serviceKey

private theorem clause_answer_noService {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {r : Role} {state : V.Ty} {serviceKey : Key} :
    ∀ {cs : List (Clause V hs r state)},
      (∀ c ∈ cs, LayoutClauseNoService M fnTable rTable serviceKey c) →
      ∀ (op : ROp M) (s : M.Val state),
        ROp.NotService M serviceKey op →
        (Clause.answer M fnTable rTable cs op s).NoService M serviceKey
  | [], _, _, _, hNot => ⟨hNot, fun _ => trivial⟩
  | c :: cs, hAll, op, s, hNot => by
      unfold Clause.answer
      by_cases hM : c.site.site = (ROp.occurrence M op).site ∧ some c.site.part = ROp.part M op ∧
          c.site.takes = ROp.takes M op ∧ c.site.gives = ROp.gives M op
      · rw [dite_eq_left hM]
        exact Process.noService_map M _ (Process.noService_mapHalt M _
          (hAll c List.mem_cons_self op hM s))
      · rw [dite_eq_right hM]
        exact clause_answer_noService fnTable rTable
          (fun c' hc' => hAll c' (List.mem_cons_of_mem _ hc')) op s hNot

private theorem handler_answer_noService {τ X E : Type}
    (h : Handler (RSig M) (RSig M) Stop τ) (serviceKey : Key)
    (hCl : ∀ op t, ROp.NotService M serviceKey op → (h.clause op t).NoService M serviceKey) :
    ∀ {p : Process (RSig M) (Stop × E) X} (u : E) (t : τ),
      p.NoService M serviceKey → (h.answer p u t).NoService M serviceKey
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call op k, u, t, ⟨hNot, hk⟩ => by
      unfold Handler.answer
      exact Process.noService_bind M
        (Process.noService_mapHalt M _ (hCl op t hNot))
        (fun out => handler_answer_noService h serviceKey hCl u out.2 (hk out.1))

private theorem handler_answer_queriesGrowing {unitTy : V.Ty} {τ X E : Type}
    (h : Handler (RSig M) (RSig M) Stop τ) (serviceKey : Key)
    (pMeta : List (List Nat)) (pData : List (List (M.Val unitTy)))
    (hCl : ∀ op t, ROp.NotService M serviceKey op → (h.clause op t).NoService M serviceKey)
    (hPassSvc : ∀ hearers at_ ins payload τOut t,
      h.clause (.own (.request serviceKey) hearers at_ ins payload τOut) t =
        .call (.own (.request serviceKey) hearers at_ ins payload τOut) fun reply => .done (reply, t)) :
    ∀ {minLen : Nat} {p : Process (RSig M) (Stop × E) X} (u : E) (t : τ),
      p.QueriesGrowing M unitTy serviceKey pMeta pData minLen →
      (h.answer p u t).QueriesGrowing M unitTy serviceKey pMeta pData minLen
  | _, .done _, _, _, _ => trivial
  | _, .halt _, _, _, _ => trivial
  | minLen, .call (.give ..) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.get ..) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.hear ..) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.begin _) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.settle _) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.own (.coin _) ..) k, u, t, hG => by
      unfold Handler.answer
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hCl _ t trivial))
        (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))
  | minLen, .call (.own (.request svc) hearers at_ ins payload τOut) k, u, t, hG => by
      unfold Handler.answer
      by_cases hSvc : svc = serviceKey
      · subst hSvc
        dsimp only [Process.QueriesGrowing] at hG
        rw [ite_eq_left rfl] at hG
        obtain ⟨hIns, hPM, hPD, hLen, hCont⟩ := hG
        rw [hPassSvc]
        dsimp only [Process.mapHalt, Process.bind, Process.QueriesGrowing]
        rw [ite_eq_left rfl]
        exact ⟨hIns, hPM, hPD, hLen, fun reply =>
          handler_answer_queriesGrowing h svc pMeta pData hCl hPassSvc u t (hCont reply)⟩
      · dsimp only [Process.QueriesGrowing] at hG
        rw [ite_eq_right hSvc] at hG
        exact Process.queriesGrowing_bind_noService M
          (Process.noService_mapHalt M _ (hCl _ t hSvc))
          (fun out => handler_answer_queriesGrowing h serviceKey pMeta pData hCl hPassSvc u out.2 (hG out.1))

private theorem layoutClause_noService_drop {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTy τ : V.Ty} (r : Role) (site : Site)
    (kind : FlowKind) (getters : List Role) (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters) := by
  intro op hMatch s
  cases op with
  | give _ _ at_ _ x =>
      have hT : [τ] = _ := hMatch.2.2.1
      cases hT
      change ((layoutDropClause (hs := hs) (stateTy := stateTy) (τ := τ) r site kind getters).code.denote
        (roleSem M r fnTable rTable) at_.path
        (Env.positional (aloneIn M r (.cons x (.cons s .nil))))).NoService M serviceKey
      rw [layoutDropClause_denote]
      trivial
  | get | own | hear | «begin» | settle =>
      have hP := hMatch.2.1; cases hP

private theorem layoutClause_noService_vRead {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty} (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat]) (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (layoutVReadClause hfree verifier prover site kind readRef) := by
  intro op hMatch s
  rcases s with ⟨buf, off, ⟨⟩⟩
  cases op with
  | get _ _ at_ _ =>
      have hT := hMatch.2.2.1; cases hT
      have hG := hMatch.2.2.2; cases hG
      change ((layoutVReadClause hfree verifier prover site kind readRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil)))).NoService M serviceKey
      rw [layoutVReadClause_denote]
      exact Process.noService_map M _ (Process.noService_liftLocal M _ _)
  | give | own | hear | «begin» | settle => cases hMatch.2.1

private theorem layoutClause_noService_vCarry {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty} (hfree : Ty.isLinear V unitTy = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (readRef : SafeFnRef V hs.fns [.seq unitTy none, .nat] [τ, .nat])
    (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool]) (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef) := by
  intro op hMatch s
  rcases s with ⟨buf, off, ⟨⟩⟩
  cases op with
  | give _ _ at_ _ x =>
      have hT := hMatch.2.2.1; cases hT
      change ((layoutVCarryClause hfree verifier prover toldSite guardKey readRef eqRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons x (.cons (a := streamStateTy unitTy) (buf, (off, ())) .nil))))).NoService M serviceKey
      rw [layoutVCarryClause_denote]
      refine Process.noService_bind M (Process.noService_liftLocal M _ _) ?_
      intro vs
      cases vs with
      | cons _ r1 =>
          cases r1 with
          | cons _ r2 =>
              cases r2
              refine Process.noService_bind M (Process.noService_liftLocal M _ _) ?_
              intro eqv
              cases eqv.single <;> trivial
  | get | own | hear | «begin» | settle => cases hMatch.2.1

private theorem layoutClause_noService_compactRecover {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (recRef : SafeFnRef V hs.fns stateTys.toList [τ]) (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (compactRecoverClause verifier prover site kind recRef) := by
  intro op hMatch s
  cases op with
  | get _ _ at_ _ =>
      have hT := hMatch.2.2.1; cases hT
      have hG := hMatch.2.2.2; cases hG
      change ((compactRecoverClause verifier prover site kind recRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) s .nil)))).NoService M serviceKey
      rw [compactRecoverClause_denote]
      exact Process.noService_map M _ (Process.noService_liftLocal M _ _)
  | give | own | hear | «begin» | settle => cases hMatch.2.1

private theorem layoutClause_noService_compactReadSlot {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (site : Site) (kind : FlowKind)
    (pos : Member stateTys.toList τ) (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (compactReadSlotClause htfree verifier prover site kind pos) := by
  intro op hMatch s
  cases op with
  | get _ _ at_ _ =>
      have hT := hMatch.2.2.1; cases hT
      have hG := hMatch.2.2.2; cases hG
      change ((compactReadSlotClause htfree verifier prover site kind pos).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons (a := Ty.tuple stateTys) s .nil)))).NoService M serviceKey
      rw [compactReadSlotClause_denote]
      trivial
  | give | own | hear | «begin» | settle => cases hMatch.2.1

private theorem layoutClause_noService_compactCompare {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {stateTys : Tys V.TypeKey} {τ : V.Ty}
    (htfree : Tys.anyLinear V stateTys = false)
    (verifier prover : Role) (toldSite : Site) (guardKey : Key)
    (pos : Member stateTys.toList τ) (eqRef : TypedFnRef V hs.fns [τ, τ] [.bool])
    (serviceKey : Key) :
    LayoutClauseNoService M fnTable rTable serviceKey
      (compactCompareClause htfree verifier prover toldSite guardKey pos eqRef) := by
  intro op hMatch s
  cases op with
  | give _ _ at_ _ x =>
      have hT := hMatch.2.2.1; cases hT
      change ((compactCompareClause htfree verifier prover toldSite guardKey pos eqRef).code.denote
        (roleSem M verifier fnTable rTable) at_.path
        (Env.positional (aloneIn M verifier (.cons x (.cons (a := Ty.tuple stateTys) s .nil))))).NoService M serviceKey
      rw [compactCompareClause_denote]
      exact Process.noService_bind M (Process.noService_liftLocal M _ _) fun eqv => by
        cases eqv.single <;> trivial
  | get | own | hear | «begin» | settle => cases hMatch.2.1

private theorem buildStreamingLayoutClauses_v_noService {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {hfree : Ty.isLinear V unitTy = false}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)} {serviceKey : Key} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {pCs vCs},
      buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey events idx es =
        .ok (pCs, vCs) →
      (∀ c ∈ vCs, LayoutClauseNoService M (Defs.fnTable M a.program.defs)
        (Defs.rTable M a.program.defs) serviceKey c) ∧
      (∀ c ∈ vCs, ∀ hearers at_ ins payload τOut,
        ¬ ClauseMatches M c (.own (.request serviceKey) hearers at_ ins payload τOut))
  | _, [], _, _, h => by
      cases h
      exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, pCs, vCs, h => by
      unfold buildStreamingLayoutClauses.go at h
      cases hRec : buildStreamingLayoutClauses.go a layout unitTy hfree prover verifier declKey
          events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok pair =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihNS, ihNM⟩ := buildStreamingLayoutClauses_v_noService (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hW : findLayoutWrite a layout.module unitTy e.τ with
                | none => rw [hW] at h; cases h
                | some wRef =>
                    rw [hW] at h
                    cases hR : findLayoutRead a layout.module unitTy e.τ with
                    | none => rw [hR] at h; cases h
                    | some rRef =>
                        rw [hR] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact layoutClause_noService_vRead M _ _ hfree verifier prover e.site kind rRef serviceKey
                          · exact ihNS c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro _ _ _ _ _ hM; cases hM.2.1
                          · exact ihNM c hm
              · cases h; exact ⟨ihNS, ihNM⟩
          | given kind owner hearers =>
              rw [hCls] at h
              cases kind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hW : findLayoutWrite a layout.module unitTy e.τ with
                      | none => rw [hW] at h; cases h
                      | some wRef =>
                          rw [hW] at h
                          cases hR : findLayoutRead a layout.module unitTy e.τ with
                          | none => rw [hR] at h; cases h
                          | some rRef =>
                              rw [hR] at h
                              cases hE : findLayoutEqual a layout.module e.τ with
                              | none => rw [hE] at h; cases h
                              | some eqRef =>
                                  rw [hE] at h; cases h
                                  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                                  · rcases List.mem_cons.mp hc with rfl | hm
                                    · exact layoutClause_noService_vCarry M _ _ hfree verifier prover _ _ rRef eqRef serviceKey
                                    · exact ihNS c hm
                                  · rcases List.mem_cons.mp hc with rfl | hm
                                    · intro _ _ _ _ _ hM; cases hM.2.1
                                    · exact ihNM c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact layoutClause_noService_drop M _ _ verifier _ .message [prover] serviceKey
                        · exact ihNS c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · intro _ _ _ _ _ hM; cases hM.2.1
                        · exact ihNM c hm
                  · cases h; exact ⟨ihNS, ihNM⟩
              | request _ => cases h; exact ⟨ihNS, ihNM⟩

private theorem buildCompactVClauses_noService {a : Admitted V} {layout : Layout}
    {unitTy : V.Ty} {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {stmtTys : List V.Ty} {wireSpecs : List (WireSpec V a.program.headers.fns unitTy)}
    {htfree : Tys.anyLinear V (tysOfList (stmtTys ++ wireSpecs.map (·.ty))) = false}
    {serviceKey : Key} :
    ∀ (idx : Nat) (es : List (ShapeEvent V)) {vCs},
      buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys wireSpecs htfree
        idx es = .ok vCs →
      (∀ c ∈ vCs, LayoutClauseNoService M (Defs.fnTable M a.program.defs)
        (Defs.rTable M a.program.defs) serviceKey c) ∧
      (∀ c ∈ vCs, ∀ hearers at_ ins payload τOut,
        ¬ ClauseMatches M c (.own (.request serviceKey) hearers at_ ins payload τOut))
  | _, [], _, h => by
      cases h
      exact ⟨(fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  | idx, e :: rest, vCs, h => by
      unfold buildCompactVClauses at h
      cases hRec : buildCompactVClauses a layout unitTy prover verifier declKey events stmtTys
          wireSpecs htfree (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          obtain ⟨ihNS, ihNM⟩ := buildCompactVClauses_noService (idx + 1) rest hRec
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases hLk : layout.recover.lookup e.site with
                | some recKey =>
                    rw [hLk] at h; dsimp only at h
                    cases hRef : findSafeFnRef a recKey
                        (tysOfList (stmtTys ++ wireSpecs.map (·.ty))).toList [e.τ] with
                    | none => rw [hRef] at h; cases h
                    | some recRef =>
                        rw [hRef] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact layoutClause_noService_compactRecover M _ _ verifier prover e.site kind recRef serviceKey
                          · exact ihNS c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro _ _ _ _ _ hM; cases hM.2.1
                          · exact ihNM c hm
                | none =>
                    rw [hLk] at h; dsimp only at h
                    cases hMem : findWireMember e.site e.τ wireSpecs with
                    | none => rw [hMem] at h; cases h
                    | some mWire =>
                        rw [hMem] at h; cases h
                        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · exact layoutClause_noService_compactReadSlot M _ _ htfree verifier prover e.site kind _ serviceKey
                          · exact ihNS c hm
                        · rcases List.mem_cons.mp hc with rfl | hm
                          · intro _ _ _ _ _ hM; cases hM.2.1
                          · exact ihNM c hm
              · cases h; exact ⟨ihNS, ihNM⟩
          | given kind owner hearers =>
              rw [hCls] at h
              cases kind with
              | coin _ =>
                  dsimp only at h
                  split at h
                  · split at h
                    · cases hMem : findWireMember ⟨e.site.through, drawToldKey events idx⟩ e.τ wireSpecs with
                      | none => rw [hMem] at h; cases h
                      | some mWire =>
                          rw [hMem] at h
                          cases hEq : findLayoutEqual a layout.module e.τ with
                          | none => rw [hEq] at h; cases h
                          | some eqRef =>
                              rw [hEq] at h; cases h
                              refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                              · rcases List.mem_cons.mp hc with rfl | hm
                                · exact layoutClause_noService_compactCompare M _ _ htfree verifier prover _ _ _ eqRef serviceKey
                                · exact ihNS c hm
                              · rcases List.mem_cons.mp hc with rfl | hm
                                · intro _ _ _ _ _ hM; cases hM.2.1
                                · exact ihNM c hm
                    · cases h
                      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · exact layoutClause_noService_drop M _ _ verifier _ .message [prover] serviceKey
                        · exact ihNS c hm
                      · rcases List.mem_cons.mp hc with rfl | hm
                        · intro _ _ _ _ _ hM; cases hM.2.1
                        · exact ihNM c hm
                  · cases h; exact ⟨ihNS, ihNM⟩
              | request _ => cases h; exact ⟨ihNS, ihNM⟩

private theorem buildLayoutLayers_v_noService {a : Admitted V} {entry : ProtocolHeader V}
    {layout : Layout} {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {layP : Layer V a.program.headers prover entry.ins}
    {layV : Layer V a.program.headers verifier entry.ins} {serviceKey : Key}
    (hLay : buildLayoutLayers a entry layout prover verifier declKey events = .ok (layP, layV)) :
    (∀ c ∈ layV.clauses, LayoutClauseNoService M (Defs.fnTable M a.program.defs)
      (Defs.rTable M a.program.defs) serviceKey c) ∧
    (∀ c ∈ layV.clauses, ∀ hearers at_ ins payload τOut,
      ¬ ClauseMatches M c (.own (.request serviceKey) hearers at_ ins payload τOut)) := by
  cases buildLayoutLayers_ok_elim hLay with
  | streaming w _ hLV =>
      subst hLV
      exact buildStreamingLayoutClauses_v_noService M 0 events w.hStr
  | compact w hComp =>
      unfold buildCompactLayoutLayers at hComp
      cases hCol : collectCompactWire a layout w.unitTy prover verifier declKey events 0 events with
      | error _ => rw [hCol] at hComp; cases hComp
      | ok pair =>
          rw [hCol] at hComp
          dsimp only [bind, Except.bind] at hComp
          split at hComp
          · rename_i htfree
            cases hVC : buildCompactVClauses a layout w.unitTy prover verifier declKey events _ pair.1 htfree 0 events with
            | error _ => rw [hVC] at hComp; cases hComp
            | ok vCs =>
                rw [hVC] at hComp
                dsimp only [bind, Except.bind, pure, Except.pure] at hComp
                cases hComp
                exact buildCompactVClauses_noService M 0 events hVC
          · cases hComp

private theorem idealAbsorbClause_step_growing {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false) (verifier prover : Role) (site : Site)
    (kind : FlowKind) (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none]) (serviceKey : Key)
    {τLay : Type} (layH : Handler (RSig M) (RSig M) Stop τLay)
    (hLayNS : ∀ op t, ROp.NotService M serviceKey op → (layH.clause op t).NoService M serviceKey)
    (pMeta : List (List Nat)) (pData : List (List (M.Val unitTy)))
    (op : ROp M) (hMatch : ClauseMatches M
      (idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef) op)
    (st : M.Val (idealPathTy unitTy)) (t : τLay)
    (hPM : pMeta <+: st.1) (hPD : pData <+: st.2.1)
    {B : Type}
    (k : (RSig M).Reply op × (M.Val (idealPathTy unitTy) × τLay) → Process (RSig M) (Stop × M.Val (idealPathTy unitTy) × τLay) B)
    (hk : ∀ reply st' t', pMeta <+: st'.1 → pData <+: st'.2.1 → st.1.length ≤ st'.1.length →
      (k (reply, st', t')).QueriesGrowing M unitTy serviceKey pMeta pData st'.1.length) :
    (((layH.answer
        ((((idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code.denote
            (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
            (Env.positional (aloneIn M verifier (HList.append
              (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op))
              (.cons st .nil))))).mapHalt fun why => (why, st)).map fun out =>
            let values := HList.split [τ] (aloneOut M verifier out)
            (ROp.reply M op (cast (congrArg (HList M.Val) hMatch.2.2.2) values.1), values.2.single))
        st t).mapHalt fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
          k (out.1.1, (out.1.2, out.2))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length := by
  cases op with
  | get k' g' at_ τ' =>
      have hT := hMatch.2.2.1; cases hT
      have hG := hMatch.2.2.2; cases hG
      have hCode := idealAbsorbClause_denote M fnTable rTable hfree verifier prover site kind
        label hlabel encodeRef at_.path st
      have hArg : HList.append
          (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M (.get k' g' at_ τ)))
          (.cons st .nil) = .cons st .nil := rfl
      rw [hArg]
      change (((layH.answer
        ((((idealAbsorbClause hfree verifier prover site kind label hlabel encodeRef).code.denote
            (roleSem M verifier fnTable rTable) at_.path
            (Env.positional (aloneIn M verifier (.cons st .nil)))).mapHalt fun why => (why, st)).map fun out =>
            let values := HList.split [τ] (aloneOut M verifier out)
            (ROp.reply M (.get k' g' at_ τ) (cast (congrArg (HList M.Val) hMatch.2.2.2) values.1), values.2.single))
        st t).mapHalt fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
          k (out.1.1, (out.1.2, out.2))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length
      rw [hCode]
      dsimp only [Process.mapHalt, Process.map, Handler.answer, Process.bind]
      rw [mapHalt_bind, mapHalt_mapHalt, Process.bind_assoc]
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hLayNS _ t trivial))
        fun out1 => by
          cases hEnc : encodeRef.eval M fnTable (.cons out1.1 .nil) with
          | halt _ => trivial
          | call op' _ => cases op'
          | done encVs =>
              cases encVs with
              | cons enc rest =>
                  cases rest
                  dsimp only [liftLocal, Process.bind, Process.mapHalt, Process.map, Handler.answer]
                  have hPM' : pMeta <+: (idealPathPush M st (2 :: label) enc).1 :=
                    hPM.trans (List.prefix_append st.1 [2 :: label])
                  have hPD' : pData <+: (idealPathPush M st (2 :: label) enc).2.1 :=
                    hPD.trans (List.prefix_append st.2.1 [enc])
                  have hLen' : st.1.length ≤ (idealPathPush M st (2 :: label) enc).1.length := by
                    simp [idealPathPush]
                  have hNextSt :
                      (HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                        (HList.cons out1.1 (HList.cons (idealPathPush M st (2 :: label)
                          (HList.cons enc HList.nil).single) HList.nil))))).2.single =
                      idealPathPush M st (2 :: label) enc := by
                    rw [aloneOut_aloneIn]; rfl
                  have hHk := Process.queriesGrowing_mono M hLen'
                    (hk (ROp.reply M (.get k' g' at_ τ) (cast (congrArg (HList M.Val) hMatch.2.2.2)
                      (HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                        (HList.cons out1.1 (HList.cons (idealPathPush M st (2 :: label)
                          (HList.cons enc HList.nil).single) HList.nil))))).1))
                      (idealPathPush M st (2 :: label) enc) out1.2 hPM' hPD' hLen')
                  exact hNextSt.symm ▸ hHk
  | give | own | hear | «begin» | settle => cases hMatch.2.1

private theorem idealDeriveClause_step_growing {hs : Headers V} (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) {unitTy τ : V.Ty}
    (hfree : Ty.isLinear V unitTy = false) (verifier prover : Role) (site : Site)
    (part : Part V) (serviceKey reqKey toldKey : Key)
    (label : List Nat) (hlabel : ∀ b, b ∈ label → b < 256)
    (encodeRef : TypedFnRef V hs.fns [τ] [.seq unitTy none])
    {τLay : Type} (layH : Handler (RSig M) (RSig M) Stop τLay)
    (hLayNS : ∀ op t, ROp.NotService M serviceKey op → (layH.clause op t).NoService M serviceKey)
    (hLayPassSvc : ∀ hearers at_ ins payload τOut t,
      layH.clause (.own (.request serviceKey) hearers at_ ins payload τOut) t =
        .call (.own (.request serviceKey) hearers at_ ins payload τOut) fun reply => .done (reply, t))
    (pMeta : List (List Nat)) (pData : List (List (M.Val unitTy)))
    (op : ROp M) (hMatch : ClauseMatches M
      (idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey label hlabel encodeRef) op)
    (st : M.Val (idealPathTy unitTy)) (t : τLay)
    (hPM : pMeta <+: st.1) (hPD : pData <+: st.2.1)
    {B : Type}
    (k : (RSig M).Reply op × (M.Val (idealPathTy unitTy) × τLay) → Process (RSig M) (Stop × M.Val (idealPathTy unitTy) × τLay) B)
    (hk : ∀ reply st' t', pMeta <+: st'.1 → pData <+: st'.2.1 → st.1.length ≤ st'.1.length →
      (k (reply, st', t')).QueriesGrowing M unitTy serviceKey pMeta pData st'.1.length) :
    (((layH.answer
        ((((idealDeriveClause hfree verifier prover site part [] serviceKey reqKey toldKey label hlabel encodeRef).code.denote
            (roleSem M verifier fnTable rTable) (ROp.occurrence M op).path
            (Env.positional (aloneIn M verifier (HList.append
              (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op))
              (.cons st .nil))))).mapHalt fun why => (why, st)).map fun out =>
            let values := HList.split [τ] (aloneOut M verifier out)
            (ROp.reply M op (cast (congrArg (HList M.Val) hMatch.2.2.2) values.1), values.2.single))
        st t).mapHalt fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
          k (out.1.1, (out.1.2, out.2))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length := by
  have hPayNil : cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) =
      (HList.nil : HList M.Val []) := by
    generalize cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op) = v
    cases v; rfl
  have hCode := idealDeriveClause_denote_nil M fnTable rTable hfree verifier prover site part
    serviceKey reqKey toldKey label hlabel encodeRef (ROp.occurrence M op).path st
  have hArg : HList.append
      (cast (congrArg (HList M.Val) hMatch.2.2.1.symm) (ROp.payload M op)) (.cons st .nil) =
      .cons st .nil := by rw [hPayNil]; rfl
  rw [hArg, hCode]
  dsimp only [Process.mapHalt, Process.map, Handler.answer, Process.bind]
  rw [hLayPassSvc]
  dsimp only [Process.mapHalt, Process.bind, Process.QueriesGrowing]
  rw [ite_eq_left rfl]
  refine ⟨rfl, hPM, hPD, Nat.le_refl _, fun coin => ?_⟩
  rw [mapHalt_bind, mapHalt_mapHalt, Process.bind_assoc]
  exact Process.queriesGrowing_bind_noService M
    (Process.noService_mapHalt M _ (hLayNS _ t trivial))
    fun outTold => by
      cases hEnc : encodeRef.eval M fnTable (.cons coin .nil) with
      | halt _ => trivial
      | call op' _ => cases op'
      | done encVs =>
          cases encVs with
          | cons enc rest =>
              cases rest
              dsimp only [liftLocal, Process.bind, Process.mapHalt, Process.map, Handler.answer]
              have hPM' : pMeta <+: (idealPathPush M st (3 :: label) enc).1 :=
                hPM.trans (List.prefix_append st.1 [3 :: label])
              have hPD' : pData <+: (idealPathPush M st (3 :: label) enc).2.1 :=
                hPD.trans (List.prefix_append st.2.1 [enc])
              have hLenEq : (idealPathPush M st (3 :: label) enc).1.length = st.1.length + 1 := by
                simp [idealPathPush]
              have hLenGe : st.1.length ≤ (idealPathPush M st (3 :: label) enc).1.length := by
                omega
              have hNextSt :
                  (HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                    (HList.cons coin (HList.cons (idealPathPush M st (3 :: label)
                      (HList.cons enc HList.nil).single) HList.nil))))).2.single =
                  idealPathPush M st (3 :: label) enc := by
                rw [aloneOut_aloneIn]; rfl
              have hHk := hk
                (ROp.reply M op (cast (congrArg (HList M.Val) hMatch.2.2.2)
                  (HList.split [τ] (aloneOut M verifier (aloneIn M verifier
                    (HList.cons coin (HList.cons (idealPathPush M st (3 :: label)
                      (HList.cons enc HList.nil).single) HList.nil))))).1))
                (idealPathPush M st (3 :: label) enc) outTold.2 hPM' hPD' hLenGe
              have hLenGoal : (cast (congrArg (HList M.Val) rfl)
                  (HList.cons (a := idealQueryTy unitTy) (st, (label, ())) HList.nil)).single.1.1.length + 1 =
                  (idealPathPush M st (3 :: label) enc).1.length := by
                simpa [cast_eq, HList.single] using hLenEq.symm
              exact hNextSt.symm ▸ hLenGoal.symm ▸ hHk

private theorem ideal_clauses_step_growing {a : Admitted V} {suite : ModuleRef} {unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false} {serviceKey : Key}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {τLay : Type} (layH : Handler (RSig M) (RSig M) Stop τLay)
    (hLayNS : ∀ op t, ROp.NotService M serviceKey op → (layH.clause op t).NoService M serviceKey)
    (hLayPassSvc : ∀ hearers at_ ins payload τOut t,
      layH.clause (.own (.request serviceKey) hearers at_ ins payload τOut) t =
        .call (.own (.request serviceKey) hearers at_ ins payload τOut) fun reply => .done (reply, t))
    (pMeta : List (List Nat)) (pData : List (List (M.Val unitTy))) :
    ∀ (idx : Nat) (es : List (ShapeEvent V × Bool)) {vCs},
      buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier declKey
        events idx es = .ok vCs →
      ∀ (op : ROp M) (st : M.Val (idealPathTy unitTy)) (t : τLay),
        ROp.NotService M serviceKey op →
        pMeta <+: st.1 → pData <+: st.2.1 →
        ∀ {B : Type}
          (k : (RSig M).Reply op × (M.Val (idealPathTy unitTy) × τLay) →
            Process (RSig M) (Stop × M.Val (idealPathTy unitTy) × τLay) B),
          (∀ reply st' t', pMeta <+: st'.1 → pData <+: st'.2.1 → st.1.length ≤ st'.1.length →
            (k (reply, st', t')).QueriesGrowing M unitTy serviceKey pMeta pData st'.1.length) →
          (((layH.answer
              (Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) vCs op st)
              st t).mapHalt fun stop => (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
                k (out.1.1, (out.1.2, out.2))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length
  | _, [], _, h, op, st, t, hNot, hPM, hPD, _, k, hk => by
      cases h
      dsimp only [Clause.answer, Handler.answer, Process.mapHalt, Process.bind]
      rw [mapHalt_bind, mapHalt_mapHalt, Process.bind_assoc]
      exact Process.queriesGrowing_bind_noService M
        (Process.noService_mapHalt M _ (hLayNS op t hNot))
        fun out => by
          dsimp only [Handler.answer, Process.mapHalt, Process.bind]
          exact hk out.1 st out.2 hPM hPD (Nat.le_refl _)
  | idx, (e, needAbs) :: rest, vCs, h, op, st, t, hNot, hPM, hPD, _, k, hk => by
      unfold buildIdealVerifierClauses.go at h
      cases hRec : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier
          declKey events (idx + 1) rest with
      | error _ => rw [hRec] at h; cases h
      | ok vRest =>
          rw [hRec] at h; dsimp only [bind, Except.bind] at h
          have ih := ideal_clauses_step_growing layH hLayNS hLayPassSvc pMeta pData (idx + 1) rest
            hRec op st t hNot hPM hPD k hk
          cases hCls : e.cls with
          | flow kind giver getters =>
              rw [hCls] at h; dsimp only at h
              split at h
              · cases needAbs with
                | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; cases h; exact ih
                | true =>
                    simp only [↓reduceIte] at h
                    cases hEnc : findSuiteEncode a suite unitTy e.τ with
                    | none => rw [hEnc] at h; cases h
                    | some encRef =>
                        rw [hEnc] at h; cases h
                        unfold Clause.answer
                        by_cases hM :
                            (idealAbsorbClause hfree verifier prover e.site kind (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef).site.site = (ROp.occurrence M op).site ∧
                            some (idealAbsorbClause hfree verifier prover e.site kind (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef).site.part = ROp.part M op ∧
                            (idealAbsorbClause hfree verifier prover e.site kind (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef).site.takes = ROp.takes M op ∧
                            (idealAbsorbClause hfree verifier prover e.site kind (msgLabel e.site)
                              (msgLabel_bytes e.site) encRef).site.gives = ROp.gives M op
                        · rw [dite_eq_left hM]
                          exact idealAbsorbClause_step_growing M _ _ hfree verifier prover e.site
                            kind (msgLabel e.site) (msgLabel_bytes e.site) encRef serviceKey layH
                            hLayNS pMeta pData op hM st t hPM hPD k hk
                        · rw [dite_eq_right hM]; exact ih
              · split at h
                · cases h; exact ih
                · cases h
          | given kind owner hearers =>
              rw [hCls] at h
              cases kind with
              | coin law =>
                  dsimp only at h
                  split at h
                  · cases hLaw : V.law law with
                    | none => rw [hLaw] at h; cases h
                    | some sig =>
                        rw [hLaw] at h; dsimp only at h
                        split at h
                        · cases hIns : sig.ins with
                          | cons _ _ => rw [hIns] at h; cases h
                          | nil =>
                              rw [hIns] at h; dsimp only at h
                              cases hEnc : findSuiteEncode a suite unitTy e.τ with
                              | none => rw [hEnc] at h; cases h
                              | some encRef =>
                                  rw [hEnc] at h; cases h
                                  unfold Clause.answer
                                  by_cases hM :
                                      (idealDeriveClause hfree verifier prover e.site
                                        (.own (.coin law) hearers) [] serviceKey
                                        (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef).site.site =
                                        (ROp.occurrence M op).site ∧
                                      some (idealDeriveClause hfree verifier prover e.site
                                        (.own (.coin law) hearers) [] serviceKey
                                        (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef).site.part =
                                        ROp.part M op ∧
                                      (idealDeriveClause hfree verifier prover e.site
                                        (.own (.coin law) hearers) [] serviceKey
                                        (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef).site.takes =
                                        ROp.takes M op ∧
                                      (idealDeriveClause hfree verifier prover e.site
                                        (.own (.coin law) hearers) [] serviceKey
                                        (idealReqKey events idx) (drawToldKey events idx)
                                        (drawLabel e.site) (drawLabel_bytes e.site) encRef).site.gives =
                                        ROp.gives M op
                                  · rw [dite_eq_left hM]
                                    exact idealDeriveClause_step_growing M _ _ hfree verifier prover
                                      e.site (.own (.coin law) hearers) serviceKey
                                      (idealReqKey events idx) (drawToldKey events idx)
                                      (drawLabel e.site) (drawLabel_bytes e.site) encRef layH
                                      hLayNS hLayPassSvc pMeta pData op hM st t hPM hPD k hk
                                  · rw [dite_eq_right hM]; exact ih
                        · cases h
                  · split at h
                    · cases h; exact ih
                    · cases h
              | request _ =>
                  dsimp only at h
                  split at h
                  · cases h; exact ih
                  · cases h

private theorem stack2_ideal_run_queriesGrowing {a : Admitted V} {suite : ModuleRef} {unitTy : V.Ty}
    {hfree : Ty.isLinear V unitTy = false} {serviceKey : Key}
    {prover verifier : Role} {declKey : Key} {events : List (ShapeEvent V)}
    {eventsAbs : List (ShapeEvent V × Bool)} {entryIns : List (LTy V)}
    (idealConV layV : Layer V a.program.headers verifier entryIns)
    (hConSt : idealConV.state = idealPathTy unitTy)
    (hIV : buildIdealVerifierClauses.go a suite unitTy hfree serviceKey prover verifier declKey
      events 0 eventsAbs = .ok (hConSt ▸ idealConV.clauses))
    (hLayNS : ∀ c ∈ layV.clauses, LayoutClauseNoService M (Defs.fnTable M a.program.defs)
      (Defs.rTable M a.program.defs) serviceKey c)
    (hLayNM : ∀ c ∈ layV.clauses, ∀ hearers at_ ins payload τOut,
      ¬ ClauseMatches M c (.own (.request serviceKey) hearers at_ ins payload τOut))
    (pMeta : List (List Nat)) (pData : List (List (M.Val unitTy))) :
    ∀ {A : Type} (p : Program M A)
      (st : M.Val (idealPathTy unitTy)) (t : M.Val layV.state),
      p.NoService M serviceKey →
      pMeta <+: st.1 → pData <+: st.2.1 →
      ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
          [idealConV, layV]).run (retryOf M none) p
            (.cons (hConSt.symm ▸ st) (.cons t .nil))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length := by
  cases idealConV with
  | mk cLine cSt cTakes cGives cClauses cAgain cStart cFin =>
      dsimp only at hConSt
      subst cSt
      dsimp only at hIV ⊢
      have hLayCl : ∀ op t, ROp.NotService M serviceKey op →
          ((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).clause op t).NoService M serviceKey :=
        fun op t hNot => clause_answer_noService M _ _ hLayNS op t hNot
      have hLayPassSvc : ∀ hearers at_ ins payload τOut t,
          (layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).clause
              (.own (.request serviceKey) hearers at_ ins payload τOut) t =
            .call (.own (.request serviceKey) hearers at_ ins payload τOut) fun reply => .done (reply, t) := by
        intro hearers at_ ins payload τOut t
        exact clause_answer_unmatched_all M _ _ _ t layV.clauses
          (fun c hc => hLayNM c hc hearers at_ ins payload τOut)
      have hOver : ∀ {A : Type} (p : Program M A)
          (st : M.Val (idealPathTy unitTy)) (t : M.Val layV.state),
          p.NoService M serviceKey → pMeta <+: st.1 → pData <+: st.2.1 →
          ((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).run
              (retryOf M none) p (.cons st (.cons t .nil))).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length := by
        intro A p
        induction p with
        | done _ => intro _ _ _ _ _; trivial
        | halt _ => intro _ _ _ _ _; trivial
        | call op k ih =>
            intro st t ⟨hNot, hkNS⟩ hPM hPD
            change (((Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
              [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).clause
                op (.cons st (.cons t .nil))).bind fun out =>
              (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).run
                (retryOf M none) (k out.1) out.2).QueriesGrowing M unitTy serviceKey pMeta pData st.1.length
            have hStack2 :
                (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                  [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).clause
                  op (.cons st (.cons t .nil)) =
                (((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).answer
                    (Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) cClauses op st)
                    st t).mapHalt fun stop => (stop.1, .cons stop.2.1 (.cons stop.2.2 .nil))).map
                  fun out => (out.1.1, .cons out.1.2 (.cons out.2 .nil)) := by
              have hLay1 : ∀ op' s',
                  (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layV]).clause
                    op' (.cons s' .nil) =
                  (((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).clause op' s').mapHalt
                    fun stop => (stop.1, .cons stop.2 .nil)).map fun out => (out.1, .cons out.2 .nil) := by
                intro op' s'
                have hAnsNil : ∀ {X E : Type} (q : Process (RSig M) (Stop × E) (X × E)) (u : E),
                    ((Handler.answer (Stack.handler M (Defs.fnTable M a.program.defs)
                        (Defs.rTable M a.program.defs) (r := verifier) (ins := entryIns) [])
                        q u HList.nil).mapHalt
                      fun stop => (stop.1, (stop.2.1, stop.2.2))).bind
                      (fun out => Process.done (out.1.1, (out.1.2, out.2))) =
                    (q.mapHalt fun stop => (stop.1, (stop.2, HList.nil))).map fun out => (out.1, (out.2, HList.nil)) := by
                  intro X E q u
                  induction q with
                  | done x => rfl
                  | halt stop => rfl
                  | call op'' k'' ih'' =>
                      simp only [Stack.handler, Handler.answer, Process.mapHalt, Process.bind, Process.map]
                      congr 1; funext r; exact ih'' r
                change ((((Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layV).over
                  (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [])).clause
                    op' (s', HList.nil)).mapHalt fun stop => (stop.1, HList.cons stop.2.1 stop.2.2)).map
                  (fun out => (out.1, HList.cons out.2.1 out.2.2)) = _
                dsimp only [Handler.over]
                rw [hAnsNil]
                have hSimp1 : ∀ {H₁ H₂ H₃ A B C : Type}
                    (q : Process (RSig M) H₁ A) (f₁ : A → B) (f₂ : B → C)
                    (g₁ : H₁ → H₂) (g₂ : H₂ → H₃),
                    (((q.mapHalt g₁).map f₁).mapHalt g₂).map f₂ =
                    (q.mapHalt (fun h => g₂ (g₁ h))).map (fun a => f₂ (f₁ a)) := by
                  intro H₁ H₂ H₃ A B C q f₁ f₂ g₁ g₂
                  rw [mapHalt_map, mapHalt_mapHalt, Process.map_map]
                exact hSimp1 ((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).clause op' s')
                  (fun out => (out.1, (out.2, HList.nil)))
                  (fun out => (out.1, HList.cons out.2.1 out.2.2))
                  (fun stop => (stop.1, (stop.2, HList.nil)))
                  (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
              have hAnsCons : ∀ {X E : Type} (q : Process (RSig M) (Stop × E) X) (u : E) (s' : M.Val layV.state),
                  (Handler.answer (Stack.handler M (Defs.fnTable M a.program.defs)
                    (Defs.rTable M a.program.defs) [layV]) q u (.cons s' .nil)) =
                  ((Handler.answer (layV.handler M (Defs.fnTable M a.program.defs)
                    (Defs.rTable M a.program.defs)) q u s').mapHalt
                    fun stop => (stop.1, stop.2.1, HList.cons stop.2.2 .nil)).map
                    fun out => (out.1, HList.cons out.2 .nil) := by
                intro X E q u s'
                induction q generalizing s' with
                | done x => rfl
                | halt stop => rfl
                | call op'' k'' ih'' =>
                    simp only [Handler.answer, hLay1]
                    rw [mapHalt_map, mapHalt_mapHalt, Process.bind_map, mapHalt_bind,
                        mapHalt_mapHalt, Process.map_bind]
                    congr 1; funext out
                    exact ih'' out.1 out.2
              change ((((Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)
                ⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩).over
                (Stack.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) [layV])).clause
                  op (st, .cons t .nil)).mapHalt fun stop => (stop.1, HList.cons stop.2.1 stop.2.2)).map
                (fun out => (out.1, HList.cons out.2.1 out.2.2)) = _
              dsimp only [Handler.over, Layer.handler]
              rw [hAnsCons]
              have hSimp : ∀ {H₁ H₂ H₃ H₄ A B C D : Type}
                  (q : Process (RSig M) H₁ A) (f₁ : A → B) (f₂ : B → C) (f₃ : C → D)
                  (g₁ : H₁ → H₂) (g₂ : H₂ → H₃) (g₃ : H₃ → H₄),
                  (((((q.mapHalt g₁).map f₁).mapHalt g₂).bind (fun b => .done (f₂ b))).mapHalt g₃).map f₃ =
                  (q.mapHalt (fun h => g₃ (g₂ (g₁ h)))).map (fun a => f₃ (f₂ (f₁ a))) := by
                intro H₁ H₂ H₃ H₄ A B C D q f₁ f₂ f₃ g₁ g₂ g₃
                rw [mapHalt_map, mapHalt_mapHalt, Process.bind_map, ← Process.map_eq_bind,
                    mapHalt_map, mapHalt_mapHalt, Process.map_map]
              exact hSimp
                ((Layer.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) layV).answer
                  (Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) cClauses op st) st t)
                (fun out => (out.1, HList.cons out.2 HList.nil))
                (fun out => (out.1.1, (out.1.2, out.2)))
                (fun out => (out.1, HList.cons out.2.1 out.2.2))
                (fun stop => (stop.1, stop.2.1, HList.cons stop.2.2 HList.nil))
                (fun stop => (stop.1, (stop.2.1, stop.2.2)))
                (fun stop => (stop.1, HList.cons stop.2.1 stop.2.2))
            rw [hStack2, Process.bind_map]
            dsimp only
            have hHaltEq :
                (((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).answer
                    (Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) cClauses op st)
                    st t).mapHalt fun stop => (stop.1, HList.cons stop.2.1 (HList.cons stop.2.2 HList.nil))).bind
                  (fun out => (Stack.handler M (Defs.fnTable M a.program.defs)
                    (Defs.rTable M a.program.defs)
                    [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).run
                    (retryOf M none) (k out.1.1) (.cons out.1.2 (.cons out.2 .nil))) =
                ((((layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs)).answer
                    (Clause.answer M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs) cClauses op st)
                    st t).mapHalt fun stop => (stop.1, (stop.2.1, stop.2.2))).bind
                  (fun out => ((Stack.handler M (Defs.fnTable M a.program.defs)
                    (Defs.rTable M a.program.defs)
                    [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).run
                    (retryOf M none) (k out.1.1) (.cons out.1.2 (.cons out.2 .nil))).mapHalt
                    fun stop => (stop.1, match stop.2 with | .cons a (.cons b .nil) => (a, b)))).mapHalt
                  fun stop => (stop.1, .cons stop.2.1 (.cons stop.2.2 .nil)) := by
              rw [mapHalt_bind, mapHalt_mapHalt]
              congr 1
              funext out
              rw [mapHalt_mapHalt]
              dsimp only
              have hId : ∀ {X : Type} (q : Process (RSig M)
                  (Stop × HList M.Val (Stack.States
                    [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV])) X),
                  q = q.mapHalt (fun h => (h.1, HList.cons (match h.2 with | .cons a (.cons b .nil) => (a, b)).1
                    (HList.cons (match h.2 with | .cons a (.cons b .nil) => (a, b)).2 .nil))) := by
                intro X q
                induction q with
                | done _ => rfl
                | halt h =>
                    rcases h with ⟨s, hs⟩
                    cases hs with | cons a r1 => cases r1 with | cons b r2 => cases r2; rfl
                | call _ _ ih => simp only [Process.mapHalt]; congr 1; funext r; exact ih r
              exact hId _
            refine Eq.mp (congrArg (Process.QueriesGrowing M unitTy serviceKey pMeta pData st.1.length) hHaltEq.symm) ?_
            exact Process.queriesGrowing_mapHalt M _
              (ideal_clauses_step_growing M
                (layV.handler M (Defs.fnTable M a.program.defs) (Defs.rTable M a.program.defs))
                hLayCl hLayPassSvc pMeta pData 0 _ hIV op st t hNot hPM hPD
                (fun out => ((Stack.handler M (Defs.fnTable M a.program.defs)
                  (Defs.rTable M a.program.defs)
                  [⟨cLine, idealPathTy unitTy, cTakes, cGives, cClauses, cAgain, cStart, cFin⟩, layV]).run
                  (retryOf M none) (k out.1) (.cons out.2.1 (.cons out.2.2 .nil))).mapHalt
                  fun stop => (stop.1, match stop.2 with | .cons a (.cons b .nil) => (a, b)))
                (fun reply st' t' hPM' hPD' _ =>
                  Process.queriesGrowing_mapHalt M _ (ih reply st' t' (hkNS reply) hPM' hPD')))
      exact @hOver

private theorem roleMeaning_noService {p : Typed V} {hdr : ProtocolHeader V}
    (callee : Member p.headers.protocols hdr) (r : Role) (ins : HList (RV M r) hdr.ins)
    {serviceKey : Key} (hFresh : ServiceKeyFresh hdr.shape serviceKey) :
    (roleMeaning M p callee r [] ins).NoService M serviceKey := by
  have hShape := roleMeaning_matchesShape M p callee r [] ins
  have hGo : ∀ {A : Type} {q : Program M A},
      q.SafeWith M (fun _ _ => True) (ROp.MatchesShape M r (hdr.shape.events [] id))
        (fun _ => True) (fun _ => True) →
      q.NoService M serviceKey := by
    intro A q
    induction q with
    | done _ => intro _; trivial
    | halt _ => intro _; trivial
    | call op k ih =>
        intro ⟨hOp, hk⟩
        refine ⟨?_, fun reply => ih reply (hk reply trivial)⟩
        cases op with
        | give | get | hear | «begin» | settle => trivial
        | own kind =>
            cases kind with
            | coin _ => trivial
            | request svc =>
                obtain ⟨e, he, _, _, hEqCls, _⟩ := hOp
                exact hFresh e he svc r _ hEqCls
  exact hGo hShape

/-! ## Top-level query uniqueness and domain-separation theorems -/

/-- `idealInitialPath` always starts its metadata log with `0 :: sessBytes`. -/
theorem idealInitialPath_head {a : Admitted V} {suite : ModuleRef} {suiteUnitTy : V.Ty}
    {prover verifier : Role} {ins : List (LTy V)}
    {sessBytes : List Nat} {vals : HList (RV M verifier) ins}
    {st0 : M.Val (idealPathTy suiteUnitTy)}
    (hInit : idealInitialPath M a suite suiteUnitTy prover verifier sessBytes vals = some st0) :
    st0.1[0]? = some (0 :: sessBytes) := by
  unfold idealInitialPath at hInit
  have hGo : ∀ (sps : List (StmtPos V verifier ins))
      (st st' : M.Val (idealPathTy suiteUnitTy)),
      st.1[0]? = some (0 :: sessBytes) →
      idealInitialPath.go M a suite suiteUnitTy verifier vals st sps = some st' →
      st'.1[0]? = some (0 :: sessBytes) := by
    intro sps
    induction sps with
    | nil => intro st st' h0 hF; cases hF; exact h0
    | cons sp rest ih =>
        intro st st' h0 hF
        unfold idealInitialPath.go at hF
        cases hEnc : findSuiteEncode a suite suiteUnitTy sp.ty with
        | none => rw [hEnc] at hF; cases hF
        | some encRef =>
            rw [hEnc] at hF; dsimp only at hF
            cases hEv : encRef.eval M (Defs.fnTable M a.program.defs)
                (.cons ((Env.positional (heldValues M verifier vals)).get
                  (posVar (held verifier ins) sp.heldIndex sp.atHeld)) .nil) with
            | halt _ => rw [hEv] at hF; cases hF
            | call op _ => cases op
            | done vs =>
                rw [hEv] at hF; dsimp only at hF
                apply ih _ st' _ hF
                dsimp only [idealPathPush]
                cases hM : st.1 with
                | nil => rw [hM] at h0; cases h0
                | cons m0 ms => rw [hM] at h0; exact h0
  exact hGo _ (idealPathInit M suiteUnitTy sessBytes) st0 rfl hInit

/-- `idealInitialPath` produces metadata and data logs of equal length `1 + stmtCount`, and is
injective on statement inputs whenever `SuiteSlot.encode` is injective (`SuiteLawfulFor`). -/
theorem idealInitialPath_stmt_injective {enc : VocabEncoder V} {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {suiteUnitTy : V.Ty}
    {prover verifier : Role} {sessBytes : List Nat}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawfulFor enc M)
    {ins₁ ins₂ : HList (RV M verifier) d.entry.ins}
    (hV₁ : ins₁.All (RV.Valid M verifier)) (hV₂ : ins₂.All (RV.Valid M verifier))
    {st₁ st₂ : M.Val (idealPathTy suiteUnitTy)}
    (hI₁ : idealInitialPath M d.admitted suite suiteUnitTy prover verifier sessBytes ins₁ = some st₁)
    (hI₂ : idealInitialPath M d.admitted suite suiteUnitTy prover verifier sessBytes ins₂ = some st₂) :
    st₁.1.length = st₂.1.length ∧ st₁.2.1.length = st₂.2.1.length ∧
    (st₁.2.1 = st₂.2.1 →
      ∀ sp ∈ statementPositions verifier prover verifier (.inr rfl) d.entry.ins,
        HList.getAt (heldValues M verifier ins₁) sp.heldIndex sp.atHeld =
        HList.getAt (heldValues M verifier ins₂) sp.heldIndex sp.atHeld) := by
  unfold idealInitialPath at hI₁ hI₂
  have hHV₁ := heldValues_valid M verifier ins₁ hV₁
  have hHV₂ := heldValues_valid M verifier ins₂ hV₂
  have hGo : ∀ (sps : List (StmtPos V verifier d.entry.ins))
      (a₁ a₂ b₁ b₂ : M.Val (idealPathTy suiteUnitTy)),
      a₁.1.length = a₂.1.length → a₁.2.1.length = a₂.2.1.length →
      idealInitialPath.go M d.admitted suite suiteUnitTy verifier ins₁ a₁ sps = some b₁ →
      idealInitialPath.go M d.admitted suite suiteUnitTy verifier ins₂ a₂ sps = some b₂ →
      b₁.1.length = b₂.1.length ∧ b₁.2.1.length = b₂.2.1.length ∧
      (b₁.2.1 = b₂.2.1 →
        a₁.2.1 = a₂.2.1 ∧
        ∀ sp ∈ sps,
          HList.getAt (heldValues M verifier ins₁) sp.heldIndex sp.atHeld =
          HList.getAt (heldValues M verifier ins₂) sp.heldIndex sp.atHeld) := by
    intro sps
    induction sps with
    | nil =>
        intro a₁ a₂ b₁ b₂ hL1 hL2 hF1 hF2
        cases hF1; cases hF2
        exact ⟨hL1, hL2, fun hEq => ⟨hEq, fun _ h => nomatch h⟩⟩
    | cons sp rest ih =>
        intro a₁ a₂ b₁ b₂ hL1 hL2 hF1 hF2
        unfold idealInitialPath.go at hF1 hF2
        cases hEnc : findSuiteEncode d.admitted suite suiteUnitTy sp.ty with
        | none => rw [hEnc] at hF1; cases hF1
        | some encRef =>
            rw [hEnc] at hF1 hF2; dsimp only at hF1 hF2
            have hGet₁ : (Env.positional (heldValues M verifier ins₁)).get
                (posVar (held verifier d.entry.ins) sp.heldIndex sp.atHeld) =
                HList.getAt (heldValues M verifier ins₁) sp.heldIndex sp.atHeld :=
              env_get_positional (heldValues M verifier ins₁) sp.heldIndex sp.atHeld
            have hGet₂ : (Env.positional (heldValues M verifier ins₂)).get
                (posVar (held verifier d.entry.ins) sp.heldIndex sp.atHeld) =
                HList.getAt (heldValues M verifier ins₂) sp.heldIndex sp.atHeld :=
              env_get_positional (heldValues M verifier ins₂) sp.heldIndex sp.atHeld
            rw [hGet₁] at hF1
            rw [hGet₂] at hF2
            cases hEv₁ : encRef.eval M (Defs.fnTable M d.admitted.program.defs)
                (.cons (HList.getAt (heldValues M verifier ins₁) sp.heldIndex sp.atHeld) .nil) with
            | halt _ => rw [hEv₁] at hF1; cases hF1
            | call op _ => cases op
            | done vs₁ =>
                cases vs₁ with
                | cons e₁ r1 =>
                    cases r1
                    rw [hEv₁] at hF1; dsimp only [HList.single] at hF1
                    cases hEv₂ : encRef.eval M (Defs.fnTable M d.admitted.program.defs)
                        (.cons (HList.getAt (heldValues M verifier ins₂) sp.heldIndex sp.atHeld) .nil) with
                    | halt _ => rw [hEv₂] at hF2; cases hF2
                    | call op _ => cases op
                    | done vs₂ =>
                        cases vs₂ with
                        | cons e₂ r2 =>
                            cases r2
                            rw [hEv₂] at hF2; dsimp only [HList.single] at hF2
                            have hL1' : (idealPathPush M a₁ (1 :: stmtLabel sp.stmtIndex) e₁).1.length =
                                (idealPathPush M a₂ (1 :: stmtLabel sp.stmtIndex) e₂).1.length := by
                              simp [idealPathPush, hL1]
                            have hL2' : (idealPathPush M a₁ (1 :: stmtLabel sp.stmtIndex) e₁).2.1.length =
                                (idealPathPush M a₂ (1 :: stmtLabel sp.stmtIndex) e₂).2.1.length := by
                              simp [idealPathPush, hL2]
                            obtain ⟨hBL1, hBL2, hRec⟩ := ih _ _ b₁ b₂ hL1' hL2' hF1 hF2
                            refine ⟨hBL1, hBL2, fun hBEq => ?_⟩
                            obtain ⟨hPushEq, hRestEq⟩ := hRec hBEq
                            dsimp only [idealPathPush] at hPushEq
                            have hApp := List.append_inj hPushEq hL2
                            have hE12 : e₁ = e₂ := (List.cons.inj hApp.2).1
                            subst hE12
                            have hValEq := suiteLawfulFor_encode_injective M hCon hSuite hEnc
                              (HList.getAt_valid _ _ _ hHV₁) (HList.getAt_valid _ _ _ hHV₂) hEv₁ hEv₂
                            refine ⟨hApp.1, fun sp' hMem => ?_⟩
                            rcases List.mem_cons.mp hMem with rfl | hm
                            · exact hValEq
                            · exact hRestEq sp' hm
  obtain ⟨hL1, hL2, hImp⟩ := hGo _ (idealPathInit M suiteUnitTy sessBytes)
    (idealPathInit M suiteUnitTy sessBytes) st₁ st₂ rfl rfl hI₁ hI₂
  exact ⟨hL1, hL2, fun hEq => (hImp hEq).2⟩

/-- Main ideal random-oracle query-separation theorem: for ANY non-retried ideal deployment
(streaming OR compact, carry OR non-carry) whose `serviceKey` is fresh from the protocol's own
service requests, every execution path of `dIdeal.run M verifier ins taken` emits strictly growing
`serviceKey` queries extending the canonical initial transcript path `st0`. -/
theorem deployIdeal_queries_growing (enc : VocabEncoder V) (serviceKey : Key)
    {a : Admitted V} {decl : Declaration} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {dIdeal : Deployed V}
    (hDep : deployIdeal enc serviceKey a decl = .ok dIdeal)
    (hCon : decl.construction = .derived suite sessionTag)
    (hNoRetry : decl.retry = none)
    {prover verifier : Role} (hRoles : dIdeal.roles = some (prover, verifier))
    (hFresh : ServiceKeyFresh dIdeal.entry.shape serviceKey)
    (ins : HList (RV M verifier) dIdeal.entry.ins) (hIns : ins.All (RV.Valid M verifier)) :
    ∃ (suiteUnitTy : V.Ty) (hSuiteFree : Ty.isLinear V suiteUnitTy = false)
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st0 : M.Val (idealPathTy suiteUnitTy)),
      findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ ∧
      resolveSessionBytes enc a decl sessionTag = .ok ⟨sessBytes, hSess⟩ ∧
      idealInitialPath M a suite suiteUnitTy prover verifier sessBytes ins = some st0 ∧
      ∀ (taken : HList M.Val (Stack.Takes (dIdeal.stack verifier))),
        (dIdeal.run M verifier ins taken).QueriesGrowing M suiteUnitTy serviceKey
          st0.1 st0.2.1 st0.1.length := by
  let ⟨w, hEqD⟩ := deployIdeal_ok_elim enc serviceKey a decl dIdeal hDep
  subst hEqD
  have hConEq : Construction.derived w.suite w.sessionTag = .derived suite sessionTag :=
    w.hCon.symm.trans hCon
  have hSuiteEq : w.suite = suite := (Construction.derived.inj hConEq).1
  have hTagEq : w.sessionTag = sessionTag := (Construction.derived.inj hConEq).2
  have hRolesEq : proverAndVerifier w.foundPair.1 decl = some (prover, verifier) := by
    simpa [Deployed.roles, Deployed.entry, w.hFound] using hRoles
  rw [w.hPV] at hRolesEq; cases hRolesEq
  have hEntryF : ((a.program.findProtocol decl.entry).get
      (by rw [w.hFound]; rfl)).1 = w.foundPair.1 := by simp [w.hFound]
  have hInsF := insRV_cast_valid M hEntryF ins hIns
  obtain ⟨st0, hSt0Done, hInitF, _⟩ := idealInitialPath_eq_idealStart M a w.suite w.hSuiteFree
    w.prover w.verifier decl.key w.sessBytes w.hSessBytes w.stmtV w.hSV
    (cast (congrArg (fun hdr => HList (RV M w.verifier) hdr.ins) hEntryF) ins) hInsF
  have hInit : idealInitialPath M a suite w.suiteUnitTy w.prover w.verifier w.sessBytes ins = some st0 := by
    have hCast : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
        (xs : HList (RV M w.verifier) hdr₁.ins),
        idealInitialPath M a w.suite w.suiteUnitTy w.prover w.verifier w.sessBytes xs =
          idealInitialPath M a w.suite w.suiteUnitTy w.prover w.verifier w.sessBytes
            (cast (congrArg (fun hdr => HList (RV M w.verifier) hdr.ins) h) xs) := by
      intro _ _ h _; subst h; rfl
    rw [← hSuiteEq]
    erw [hCast hEntryF ins]
    exact hInitF
  let idealConV0 : Layer V a.program.headers w.verifier w.foundPair.1.ins :=
    { line := .construction, state := idealPathTy w.suiteUnitTy,
      takes := [], gives := [], clauses := w.idealVClauses,
      again := restoreAgain (idealPathTy w.suiteUnitTy),
      start := idealStart w.hSuiteFree w.sessBytes w.hSessBytes w.stmtV,
      finish := emptyFinish (idealPathTy w.suiteUnitTy) }
  obtain ⟨hLayNS, hLayNM⟩ := buildLayoutLayers_v_noService M (serviceKey := serviceKey) w.hLay
  refine ⟨w.suiteUnitTy, w.hSuiteFree, w.sessBytes, w.hSessBytes, st0,
    hSuiteEq ▸ w.hUnit, hTagEq ▸ w.hSess, hInit, ?_⟩
  have hStackVEq : w.toDeployed.stack w.verifier = hEntryF ▸ [idealConV0, w.layV] := by
    dsimp only [DeployIdealWitness.toDeployed]
    rw [dite_eq_left rfl]
    have hC : ∀ {hdr₁ hdr₂ : ProtocolHeader V} (h : hdr₁ = hdr₂)
        (ls : List (Layer V a.program.headers w.verifier hdr₂.ins)),
        (congrArg ProtocolHeader.ins h) ▸ ls = h ▸ ls := by intro _ _ h _; subst h; rfl
    exact hC hEntryF _
  have hBridge : ∀ (hdr : ProtocolHeader V) (hE : hdr = w.foundPair.1)
      (callee : Member a.program.headers.protocols hdr)
      (ins' : HList (RV M w.verifier) hdr.ins)
      (hFresh' : ServiceKeyFresh hdr.shape serviceKey)
      (hStart' : idealConV0.start.denote
        (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
        (Env.positional (heldValues M w.verifier
          (cast (congrArg (fun h => HList (RV M w.verifier) h.ins) hE) ins'))) =
        .done (.cons st0 .nil))
      (taken' : HList M.Val (Stack.Takes (hE ▸ [idealConV0, w.layV]))),
      (runStack a M callee none w.verifier (hE ▸ [idealConV0, w.layV]) ins' taken').QueriesGrowing
        M w.suiteUnitTy serviceKey st0.1 st0.2.1 st0.1.length := by
    intro hdr hE callee ins' hFresh' hStart' taken'
    subst hE
    dsimp only at hStart'
    simp only [cast_eq] at hStart'
    unfold runStack
    cases hLaySt : w.layV.start.denote (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs))
        [] (Env.positional ((HList.split w.layV.takes (HList.split idealConV0.takes taken').2).1.append
          (heldValues M w.verifier ins'))) with
    | call op _ => cases op
    | halt why =>
        have hStartHalt : Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, w.layV] ins' taken' =
            .halt why := by
          change ((liftLocal id (idealConV0.start.denote
            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
            (Env.positional ((HList.split idealConV0.takes taken').1.append (heldValues M w.verifier ins'))))).bind
              fun first =>
                ((liftLocal id (w.layV.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional ((HList.split w.layV.takes (HList.split idealConV0.takes taken').2).1.append
                    (heldValues M w.verifier ins'))))).bind fun first₂ =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first₂.single others).map
                  fun others => HList.cons first.single others) = _
          rw [show (HList.split idealConV0.takes taken').1 = .nil from rfl, HList.append, hStart', liftLocal_done]
          dsimp only [Process.bind]
          rw [hLaySt]
          rfl
        rw [hStartHalt]; trivial
    | done layVs =>
        have hStartDone : Stack.start M (Defs.fnTable M a.program.defs) [idealConV0, w.layV] ins' taken' =
            .done (.cons st0 (.cons layVs.single .nil)) := by
          change ((liftLocal id (idealConV0.start.denote
            (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
            (Env.positional ((HList.split idealConV0.takes taken').1.append (heldValues M w.verifier ins'))))).bind
              fun first =>
                ((liftLocal id (w.layV.start.denote
                  (localSem M a.program.headers.fns (Defs.fnTable M a.program.defs)) []
                  (Env.positional ((HList.split w.layV.takes (HList.split idealConV0.takes taken').2).1.append
                    (heldValues M w.verifier ins'))))).bind fun first₂ =>
                    (Process.done (HList.nil : HList M.Val [])).map fun others => HList.cons first₂.single others).map
                  fun others => HList.cons first.single others) = _
          rw [show (HList.split idealConV0.takes taken').1 = .nil from rfl, HList.append, hStart', liftLocal_done]
          dsimp only [Process.bind]
          rw [hLaySt, liftLocal_done]
          rfl
        rw [hStartDone]
        dsimp only [Process.bind]
        refine Process.queriesGrowing_bind_after_noService M
          (fun (out : HList (RV M w.verifier) w.foundPair.1.outs × HList M.Val (Stack.States [idealConV0, w.layV])) =>
            Process.noService_map M _ (Stack.finish_noService M _ serviceKey [idealConV0, w.layV] out.2)) ?_
        exact Process.queriesGrowing_mapHalt M Prod.fst
          (stack2_ideal_run_queriesGrowing M idealConV0 w.layV rfl w.hIV hLayNS hLayNM
            st0.1 st0.2.1
            (roleMeaning M a.program callee w.verifier [] ins')
            st0 layVs.single
            (roleMeaning_noService M callee w.verifier ins' hFresh')
            (List.prefix_refl _) (List.prefix_refl _))
  intro taken
  have hCongr : ∀ (ret : Option (Nat × Site)) (hRet : ret = none)
      (stk₁ stk₂ : List (Layer V a.program.headers w.verifier w.toDeployed.entry.ins))
      (hStk : stk₁ = stk₂)
      (t₁ : HList M.Val (Stack.Takes stk₁)) (t₂ : HList M.Val (Stack.Takes stk₂))
      (hT : HEq t₁ t₂),
      (runStack a M w.toDeployed.callee none w.verifier stk₂ ins t₂).QueriesGrowing
        M w.suiteUnitTy serviceKey st0.1 st0.2.1 st0.1.length →
      (runStack a M w.toDeployed.callee ret w.verifier stk₁ ins t₁).QueriesGrowing
        M w.suiteUnitTy serviceKey st0.1 st0.2.1 st0.1.length := by
    intro ret hRet stk₁ stk₂ hStk t₁ t₂ hT hG
    subst hRet; subst hStk; cases eq_of_heq hT; exact hG
  exact hCongr w.toDeployed.retry hNoRetry (w.toDeployed.stack w.verifier)
    _ hStackVEq taken
    (cast (congrArg (fun ls => HList M.Val (Stack.Takes ls)) hStackVEq) taken)
    (cast_heq _ _).symm
    (hBridge _ hEntryF w.toDeployed.callee ins hFresh hSt0Done _)

/-- Corollary: along EVERY execution path of a non-retried ideal random-oracle verifier, the
sequence `qs` of emitted `serviceKey` queries is strictly duplicate-free (`qs.Nodup`), and every
query extends the canonical initial transcript path `st0`. -/
theorem deployIdeal_queries_nodup (enc : VocabEncoder V) (serviceKey : Key)
    {a : Admitted V} {decl : Declaration} {suite : ModuleRef} {sessionTag : Option (List Nat)}
    {dIdeal : Deployed V}
    (hDep : deployIdeal enc serviceKey a decl = .ok dIdeal)
    (hCon : decl.construction = .derived suite sessionTag)
    (hNoRetry : decl.retry = none)
    {prover verifier : Role} (hRoles : dIdeal.roles = some (prover, verifier))
    (hFresh : ServiceKeyFresh dIdeal.entry.shape serviceKey)
    (ins : HList (RV M verifier) dIdeal.entry.ins) (hIns : ins.All (RV.Valid M verifier)) :
    ∃ (suiteUnitTy : V.Ty) (hSuiteFree : Ty.isLinear V suiteUnitTy = false)
      (sessBytes : List Nat) (hSess : ∀ b, b ∈ sessBytes → b < 256)
      (st0 : M.Val (idealPathTy suiteUnitTy)),
      findSuiteUnit a suite = some ⟨suiteUnitTy, ⟨hSuiteFree⟩⟩ ∧
      resolveSessionBytes enc a decl sessionTag = .ok ⟨sessBytes, hSess⟩ ∧
      idealInitialPath M a suite suiteUnitTy prover verifier sessBytes ins = some st0 ∧
      ∀ (taken : HList M.Val (Stack.Takes (dIdeal.stack verifier)))
        (qs : List (M.Val (idealQueryTy suiteUnitTy))),
        (dIdeal.run M verifier ins taken).ServiceQueries M suiteUnitTy serviceKey qs →
        qs.Nodup ∧ ∀ q ∈ qs, st0.1 <+: q.1.1 ∧ st0.2.1 <+: q.1.2.1 := by
  obtain ⟨u, hU, s, hS, st0, hFU, hRS, hI, hGrow⟩ :=
    deployIdeal_queries_growing M enc serviceKey hDep hCon hNoRetry hRoles hFresh ins hIns
  refine ⟨u, hU, s, hS, st0, hFU, hRS, hI, fun taken qs hSQ => ?_⟩
  obtain ⟨hNd, hAll⟩ := Process.queriesGrowing_nodup M (hGrow taken) hSQ
  exact ⟨hNd, fun q hq => ⟨(hAll q hq).1, (hAll q hq).2.1⟩⟩

/-- Cross-scheme / cross-session / cross-application domain separation: if two ideal deployments
(under an injective `VocabEncoder`) share ANY random-oracle query `q` on ANY proofs, inputs, or
rounds, then they MUST have the exact same `sessionTag`, `declaration` (including `application`
and `lawMembers`), and reachable erased definitions. -/
theorem deployIdeal_cross_session_disjoint (enc : VocabEncoder V) (hEnc : enc.Injective)
    {a₁ a₂ : Admitted V} {decl₁ decl₂ : Declaration}
    {suite₁ suite₂ : ModuleRef} {tag₁ tag₂ : Option (List Nat)}
    {unitTy : V.Ty} {prover₁ verifier₁ prover₂ verifier₂ : Role}
    {sess₁ sess₂ : List Nat} {hS₁ : ∀ b, b ∈ sess₁ → b < 256} {hS₂ : ∀ b, b ∈ sess₂ → b < 256}
    {ins₁ : List (LTy V)} {ins₂ : List (LTy V)}
    {vals₁ : HList (RV M verifier₁) ins₁} {vals₂ : HList (RV M verifier₂) ins₂}
    {st₁ st₂ : M.Val (idealPathTy unitTy)}
    (hRes₁ : resolveSessionBytes enc a₁ decl₁ tag₁ = .ok ⟨sess₁, hS₁⟩)
    (hRes₂ : resolveSessionBytes enc a₂ decl₂ tag₂ = .ok ⟨sess₂, hS₂⟩)
    (hInit₁ : idealInitialPath M a₁ suite₁ unitTy prover₁ verifier₁ sess₁ vals₁ = some st₁)
    (hInit₂ : idealInitialPath M a₂ suite₂ unitTy prover₂ verifier₂ sess₂ vals₂ = some st₂)
    {q : M.Val (idealQueryTy unitTy)}
    (hP₁ : st₁.1 <+: q.1.1) (hP₂ : st₂.1 <+: q.1.1) :
    tag₁ = tag₂ ∧ decl₁ = decl₂ ∧
      ((erase a₁.program).definitions.filter fun d =>
        decide (d.key ∈ (decl₁.entry :: decl₁.definitions).flatMap a₁.program.defs.closureOf)) =
      ((erase a₂.program).definitions.filter fun d =>
        decide (d.key ∈ (decl₂.entry :: decl₂.definitions).flatMap a₂.program.defs.closureOf)) := by
  have hHead₁ := idealInitialPath_head M hInit₁
  have hHead₂ := idealInitialPath_head M hInit₂
  obtain ⟨t₁, ht₁⟩ := hP₁
  obtain ⟨t₂, ht₂⟩ := hP₂
  have hQ₁ : q.1.1[0]? = some (0 :: sess₁) := by
    rw [← ht₁]
    cases hSt : st₁.1 with
    | nil => rw [hSt] at hHead₁; cases hHead₁
    | cons x xs => rw [hSt] at hHead₁; exact hHead₁
  have hQ₂ : q.1.1[0]? = some (0 :: sess₂) := by
    rw [← ht₂]
    cases hSt : st₂.1 with
    | nil => rw [hSt] at hHead₂; cases hHead₂
    | cons x xs => rw [hSt] at hHead₂; exact hHead₂
  have hSessEq : sess₁ = sess₂ := (List.cons.inj (Option.some.inj (hQ₁.symm.trans hQ₂))).2
  subst hSessEq
  exact resolveSessionBytes_injective enc hEnc hRes₁ hRes₂

/-- Cross-statement domain separation: on one ideal deployment with injective `SuiteSlot.encode`
(`SuiteLawfulFor`), if two valid verifier inputs `ins₁, ins₂` share ANY random-oracle query `q`
extending both `st₁` and `st₂`, then `ins₁` and `ins₂` agree on every statement input port. -/
theorem deployIdeal_cross_statement_disjoint (enc : VocabEncoder V) {d : Deployed V}
    {suite : ModuleRef} {sessionTag : Option (List Nat)} {unitTy : V.Ty}
    {prover verifier : Role} {sessBytes : List Nat}
    (hCon : d.declaration.construction = .derived suite sessionTag)
    (hSuite : d.SuiteLawfulFor enc M)
    {ins₁ ins₂ : HList (RV M verifier) d.entry.ins}
    (hV₁ : ins₁.All (RV.Valid M verifier)) (hV₂ : ins₂.All (RV.Valid M verifier))
    {st₁ st₂ : M.Val (idealPathTy unitTy)}
    (hI₁ : idealInitialPath M d.admitted suite unitTy prover verifier sessBytes ins₁ = some st₁)
    (hI₂ : idealInitialPath M d.admitted suite unitTy prover verifier sessBytes ins₂ = some st₂)
    {q : M.Val (idealQueryTy unitTy)}
    (hD₁ : st₁.2.1 <+: q.1.2.1) (hD₂ : st₂.2.1 <+: q.1.2.1) :
    ∀ sp ∈ statementPositions verifier prover verifier (.inr rfl) d.entry.ins,
      HList.getAt (heldValues M verifier ins₁) sp.heldIndex sp.atHeld =
      HList.getAt (heldValues M verifier ins₂) sp.heldIndex sp.atHeld := by
  obtain ⟨_, hLenEq, hInj⟩ := idealInitialPath_stmt_injective M hCon hSuite hV₁ hV₂ hI₁ hI₂
  obtain ⟨t₁, ht₁⟩ := hD₁
  obtain ⟨t₂, ht₂⟩ := hD₂
  have hDataEq : st₁.2.1 = st₂.2.1 := (List.append_inj (ht₁.trans ht₂.symm) hLenEq).1
  exact hInj hDataEq

end QuerySeparation

end Zkc.Core

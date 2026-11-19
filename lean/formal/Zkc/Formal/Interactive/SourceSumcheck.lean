module

public import Zkc.Formal.Interactive.TableVerifier

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.TableVerifier
open Core ReductionRound
open TableHalves (table)
variable {V : Vocabulary} (rows : ScalarRows V) (vectors : (d : Nat) → TableRestriction.Rows rows.scalarTy d)

structure Certified (p : Core.Typed V) (rootKey red eval : Key) (n : Nat) (events : Events rows.scalarTy) where
  shape : Shape V
  root : Member p.headers.protocols (header rows.scalarTy n rootKey shape)
  entry : ProtocolEntry p.defs root
  linked : Linked (earlier entry) red (table rows.scalarTy n) rows.scalarTy (table rows.scalarTy 0) 0 n events
  roundLaws : linked.rounds.AllMembers (fun ops => PairLaws rows linked.entry.definitions ops)
  evaluate : Member entry.earlier.fns (TableEvaluation.header rows.scalarTy eval n (0+n))
  tableLaw : TableEvaluation.Law vectors eval n (0+n) (fun M => Defs.fnTable M entry.definitions _ evaluate)
  meaning : ∀ M path inputs, roleMeaning M p root 1 path inputs =
    (witness events linked.ref evaluate rootKey shape).meaning entry.definitions 1 M path inputs

def certify (p : Core.Typed V) (rootKey red eval : Key) (n : Nat) (events : Events rows.scalarTy)
    (roundProof : ∀ key, FunctionReadback _ (rows.EvaluationLaw key)) :
    Option (Certified rows vectors p rootKey red eval n events) := do
  let t := rows.scalarTy
  let ⟨shape,root⟩ ← ProtocolEntry.locatePorts p.headers rootKey 2 [shared (table t n),shared t] []
  let entry := p.defs.protocolEntry p.distinct (show Member _ (header t n rootKey shape) from root)
  let linked ← link (earlier entry) red (table t n) t (table t 0) 0 n events
  let ⟨members⟩ ← checkPairSequence rows linked.entry.definitions (List.nodup_append.mp linked.entry.distinct).1 roundProof linked.rounds
  let ⟨evaluate,tableLaw⟩ ← TableEvaluation.check (V := V) (t := rows.scalarTy) rows.free vectors entry.definitions (List.nodup_append.mp entry.distinct).1 eval n (0+n)
  let target := witness events linked.ref evaluate rootKey shape
  let ⟨meaning⟩ ← entry.recognize 1 target (fun run => ∀ M path inputs, run M path inputs = target.meaning entry.definitions 1 M path inputs)
    (fun _ _ _ => rfl)
  return ⟨shape,root,entry,linked,members,evaluate,tableLaw,meaning⟩

private theorem evaluate_of_length {F : Type} (q : Claims F) (n : Nat) (x : q.State n) (rs : List F)
    (length : rs.length = n) : ∃ v, q.evaluate n x rs = some v := by
  induction n generalizing rs with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero length
    exact ⟨_,rfl⟩
  | succ n ih =>
    cases rs with
    | nil => contradiction
    | cons r rs => exact ih (q.restrict n x r) rs (Nat.succ.inj length)

variable {p : Core.Typed V} {rootKey red eval : Key} {n : Nat} {events : Events rows.scalarTy}

abbrev Certified.FreshFrom (cert : Certified rows vectors p rootKey red eval n events) (M : Model V)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (positive : 0 < points.length)
    (path : List Frame) (s : σ) (claim : rows.F M) : Prop :=
  let t := rows.scalarTy
  let hidden := nothing M (r := 1) (a := ⟨table t n,[0]⟩) (by simp)
  let env := Env.empty.extend (initialNames (table t n) t 0) (publicArgs M hidden [] claim)
  cert.linked.rounds.FreshFrom M (Defs.fnTable M cert.linked.entry.definitions) (Defs.rTable M cert.linked.entry.definitions)
    (K.renamePeers peerMap.to) points positive (path ++ [Frame.application ⟨1⟩]) env s

/-- Acceptance of the actual source verifier on an incorrect sum over its public Boolean-cube table. -/
theorem Certified.soundFrom (cert : Certified rows vectors p rootKey red eval n events) (M : Model V)
    [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (vectorMath : ∀ d, d < n → TableRestriction.Arithmetic (vectors d) M)
    (equality : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (path : List Frame) (s : σ) (x : Cube (rows.F M) n) (claim : rows.F M) (wrong : claim ≠ Cube.sum n x)
    (fresh : cert.FreshFrom rows vectors M K points positive path s claim) :
    K.probability (roleMeaning M p cert.root 1 path (args M (Cube.flatten n x) claim)) s (fun _ _ => true) ≤
      (n : Mass) * roundCost 1 points := by
  let t := rows.scalarTy
  let inner := path ++ [Frame.application ⟨1⟩]
  let hidden := nothing M (r := 1) (a := ⟨table t n,[0]⟩) (by simp)
  let env := Env.empty.extend (initialNames (table t n) t 0) (publicArgs M hidden [] claim)
  have relation := cert.linked.process M inner hidden [] claim
  change Defs.rTable M cert.entry.definitions _ cert.linked.ref 1 inner (publicArgs M hidden [] claim) = _ at relation
  rw [cert.meaning,callerProcess]
  unfold Experiment.probability
  rw [Experiment.expect_bind,Experiment.expect_mapR]
  rw [relation]
  simp only [Process.map_eq_bind,Experiment.expect_bind,Experiment.expect_done]
  have bounds := cert.linked.rounds.boundsFromMembers _ cert.roundLaws M _ _ Cube.claims points positive 1
    (fun _ law => (PairLaws.interpret rows law M math points distinct).reindex Fin.val) equality (K.renamePeers peerMap.to) inner env s x fresh
  have bounded := cert.linked.rounds.soundFrom M _ _ (K.renamePeers peerMap.to) Cube.claims (roundCost 1 points) inner
    (Mass.mul_nonneg Mass.natCast_nonneg (Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive)))) env s x bounds wrong
  apply Mass.le_trans _ bounded
  apply (K.renamePeers peerMap.to).expect_mono
  intro (last,rs,v) after reached
  have length := cert.linked.rounds.trace_length M _ _ inner env _ reached
  obtain ⟨answer,good⟩ := evaluate_of_length Cube.claims n x rs length
  have evaluated := cert.tableLaw M vectorMath x rs answer good
  have guard := guardValue events cert.evaluate M cert.entry.definitions path (Cube.flatten n x) claim rs v answer equality evaluated
  change K.expect _ (onReturn events cert.evaluate M cert.entry.definitions path (Cube.flatten n x) claim (leaveAll M peerMap 1 (PointReturn.values M rows.scalarTy (table rows.scalarTy 0) (0+n) rs v))) after ≤ _
  rw [guard]
  by_cases equal : v = answer
  · simp [equal,good]
  · simp [equal,Ne.symm equal,good]

/-- Public boundary for a Core-valid flat table and a false claim about its sum. -/
theorem Certified.soundValid (cert : Certified rows vectors p rootKey red eval n events) (M : Model V)
    [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (vectorMath : ∀ d, d < n → TableRestriction.Arithmetic (vectors d) M)
    (equality : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (path : List Frame) (s : σ) (xs : List (rows.F M)) (claim : rows.F M)
    (valid : M.Valid (table rows.scalarTy n) xs) (wrong : claim ≠ xs.sum)
    (fresh : cert.FreshFrom rows vectors M K points positive path s claim) :
    K.probability (roleMeaning M p cert.root 1 path (args M xs claim)) s (fun _ _ => true) ≤
      (n : Mass) * roundCost 1 points := by
  obtain ⟨x,rfl⟩ := Cube.exists_flatten_of_length n xs (valid.2 _ rfl)
  rw [Cube.sum_flatten] at wrong
  exact cert.soundFrom rows vectors M math vectorMath equality K points distinct positive path s x claim wrong fresh

/-- Acceptance of the actual source verifier on an incorrect sum over its public Boolean-cube table. -/
theorem Certified.sound (cert : Certified rows vectors p rootKey red eval n events) (M : Model V)
    [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (vectorMath : ∀ d, TableRestriction.Arithmetic (vectors d) M)
    (equality : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (fresh : ∀ path coin s, Fresh (K.renamePeers peerMap.to) points positive (challenge M events path coin) s)
    (path : List Frame) (s : σ) (x : Cube (rows.F M) n) (claim : rows.F M) (wrong : claim ≠ Cube.sum n x) :
    K.probability (roleMeaning M p cert.root 1 path (args M (Cube.flatten n x) claim)) s (fun _ _ => true) ≤
      (n : Mass) * roundCost 1 points := by
  apply cert.soundFrom rows vectors M math (fun d _ => vectorMath d) equality K points distinct positive path s x claim wrong
  exact cert.linked.rounds.freshFromService M _ _ _ points positive fresh _ _ _

#print axioms certify
#print axioms Certified.soundValid
#print axioms Certified.soundFrom
#print axioms Certified.sound
end Zkc.Formal.Interactive.Sumcheck.TableVerifier

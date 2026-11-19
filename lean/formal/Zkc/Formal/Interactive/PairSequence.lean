module

public import Zkc.Formal.Interactive.PairRound
public import Zkc.Formal.Interactive.RoundFamily
public import Zkc.Formal.Interactive.Multilinear

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary} (rows : ScalarRows V) {hs : Headers V} {ds : Defs V hs}
variable {msg state residual : V.Ty} {ops : Members hs rows.scalarTy msg state residual}

def PairLaws.interpret (laws : PairLaws rows ds ops) (M : Model V) [Lean.Grind.Field (rows.F M)]
    [DecidableEq (rows.F M)] (math : rows.Arithmetic M) (points : List (rows.F M)) (distinct : points.Nodup)
    (collisions : CollisionBound (fun a : rows.F M × rows.F M => a.1 + a.2) line 1 := lineCollisions) :
    RoundInterpretation M (Defs.fnTable M ds) Cube.claims points 1 ops where
  boundary m := (endpoints rows M laws.aligned m).1 + (endpoints rows M laws.aligned m).2
  evaluate m := line (endpoints rows M laws.aligned m)
  ends := laws.boundary M math
  atPoint := laws.evaluate M math
  roots := by
    intro n table m wrong
    change points.countP (fun r => decide (line (endpoints rows M laws.aligned m) r = Cube.sum n (Cube.interpolate r n table.1 table.2))) ≤ 1
    simpa only [Cube.sum_interpolate] using
      collisions (endpoints rows M laws.aligned m) (Cube.sum n table.1, Cube.sum n table.2) wrong points distinct

variable {Γ : Ctx (LTy V)} {events : Events rows.scalarTy} {running : Var Γ (shared rows.scalarTy)}
variable {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

def checkPairSequence (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k))
    (rounds : Sequence hs events state running term count)
    (alternatives : List (∀ k, FunctionReadback _ (rows.EvaluationLaw k)) := []) :=
  rounds.checkMembers (fun op => PairLaws rows defs op) fun op => certifyPairs rows defs unique op evaluation alternatives

theorem pairs_sound (rounds : Sequence hs events state running term count)
    (checked : rounds.AllMembers (fun ops => PairLaws rows ds ops))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)] (math : rows.Arithmetic M)
    (equalLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    {σ : Type} (K : Experiment (RSig M) σ) (points : List (rows.F M)) (distinct : points.Nodup) (positive : 0 < points.length)
    (fresh : ∀ path key s, Fresh K points positive (challenge M events path key) s) (path : List Frame)
    (env : Env (RV M 1) Γ) (s : σ) (table : Cube (rows.F M) count)
    (wrong : Sequence.scalar M env running ≠ Cube.sum count table) :
    K.probability (rounds.collect M (Defs.fnTable M ds) (Defs.rTable M ds) path env) s
      (fun (_,rs,value) _ => decide (Cube.evaluate count table rs = some value)) ≤ (count : Mass) * roundCost 1 points := by
  apply rounds.sound M _ _ K Cube.claims _ path _ _ env s table wrong
  · exact Mass.mul_nonneg Mass.natCast_nonneg (Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive)))
  · exact rounds.boundsOfMembers _ checked M _ _ _ points positive 1
      (fun _ laws => (PairLaws.interpret rows laws M math points distinct).reindex Fin.val) equalLaw K fresh path

#print axioms pairs_sound
end Zkc.Formal.Interactive.Sumcheck.ReductionRound

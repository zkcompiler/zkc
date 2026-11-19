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

/-- The table and restriction stay public throughout. Only the scalar representation
of an intermediate partial sum varies with the remaining number of coordinates. -/
def encodedClaims {F : Type} [Lean.Grind.CommRing F] (shifted : Nat → Bool) : Claims F :=
  ⟨Cube F, fun n x => ScalarRows.encode (shifted n) (Cube.sum n x), Cube.restrict⟩

theorem evaluate_encoded {F : Type} [Lean.Grind.CommRing F] (shifted : Nat → Bool) (terminal : shifted 0 = false)
    (n : Nat) (x : Cube F n) (rs : List F) :
    (encodedClaims shifted).evaluate n x rs = Cube.evaluate n x rs := by
  induction n generalizing rs with
  | zero => cases rs <;> simp [Cube.evaluate, Claims.evaluate, encodedClaims, Cube.claims, terminal, ScalarRows.encode]
  | succ n ih => cases rs with
    | nil => rfl
    | cons r rs => exact ih (Cube.restrict n x r) rs

def PairLaws.interpretAt (shifted : Nat → Bool) (d : Nat)
    (laws : PairLaws rows ds ops (shifted (d+1)) (shifted d))
    (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : rows.Arithmetic M) (points : List (rows.F M)) (distinct : points.Nodup)
    (collisions : CollisionBound (fun a : rows.F M × rows.F M => a.1 + a.2) line 1) :
    RoundInterpretationOn M (Defs.fnTable M ds) (encodedClaims shifted) points 1 ops (fun _ : Unit => d) where
  boundary m := ScalarRows.encode (shifted (d+1)) ((endpoints rows M laws.aligned m).1 + (endpoints rows M laws.aligned m).2)
  evaluate m r := ScalarRows.encode (shifted d) (line (endpoints rows M laws.aligned m) r)
  ends := laws.boundary M math
  atPoint := laws.evaluate M math
  roots := by
    intro _ x m wrong
    simpa only [encodedClaims, Cube.restrict, Cube.sum_interpolate, ScalarRows.encode_inj] using
      collisions (endpoints rows M laws.aligned m) (Cube.sum d x.1, Cube.sum d x.2)
        (fun eq => wrong (congrArg (ScalarRows.encode (shifted (d+1))) eq)) points distinct

variable {Γ : Ctx (LTy V)} {events : Events rows.scalarTy} {running : Var Γ (shared rows.scalarTy)}
variable {outs : List (LTy V)} {term : Term (protocolDialect V hs) Γ outs} {count : Nat}

def checkPairSequence (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k))
    (rounds : Sequence hs events state running term count)
    (alternatives : List (∀ k, FunctionReadback _ (rows.EvaluationLaw k)) := []) :=
  rounds.checkMembers (fun op => PairLaws rows defs op) fun op => certifyPairs rows defs unique op evaluation alternatives

/-- Only interior claims may change representation. Read each candidate offset from
the boundary callee that consumes it. The subsequent check proves both adjacent equations. -/
def intermediateOffsets (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (rounds : Sequence hs events state running term count) : Nat → Bool :=
  let offsets := (rounds.instances.drop 1).reverse.map fun occurrence => Id.run do
    let .call key := occurrence.checked.members.boundary.print | return false
    return ((rows.boundaryReadback key true).locate defs unique).isSome
  fun d => match d with
    | 0 => false
    | i+1 => offsets[i]?.getD false

def checkEncodedSequence (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (rounds : Sequence hs events state running term count) (shifted : Nat → Bool)
    (evaluation : ∀ k, FunctionReadback _ (rows.EvaluationLaw k))
    (alternatives : List (∀ k, FunctionReadback _ (rows.EvaluationLaw k))) :=
  rounds.checkMembersAt (fun d {_ _ _} ops => PairLaws rows defs ops (shifted (d+1)) (shifted d))
    fun d _ _ {_ _ _} ops => by
      cases out : shifted d with
      | false => exact certifyEncodedPairs rows defs unique ops _ false evaluation alternatives
      | true =>
        exact certifyEncodedPairs rows defs unique ops _ true
          (rows.encodedAffineReadback false true) [rows.encodedAffineReadback true true]

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
  · intro env s x
    let cert := rounds.interpretMembersAt _ checked M _ Cube.claims points 1 (fun d {_ _ _} _ law =>
      (PairLaws.interpret rows law M math points distinct).reindex (fun _ : Unit => d.val))
    exact rounds.boundsAtDepth M _ _ Cube.claims points positive 1 cert equalLaw K path env s x
      (rounds.freshFromService M _ _ K points positive fresh path env s)

#print axioms pairs_sound
end Zkc.Formal.Interactive.Sumcheck.ReductionRound

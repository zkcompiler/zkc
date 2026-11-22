module

public import ZkcFormal.Interactive.HonestMembers
public import ZkcFormal.Interactive.JointEntry
public import ZkcFormal.Interactive.LinkedReduction

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.HonestPairs
open Zkc.Core ReductionRound JointEntry
open TableHalves (table)
variable {V : Vocabulary} {hs : Headers V} {n : Nat} (rows : ScalarRows V)
variable {sr : SumRow rows n} {vec : TableRestriction.Rows rows.scalarTy n} {ds : Defs V hs}
variable {ops : Ops (hs := hs) (n := n) rows} (members : Members rows sr vec ds ops)
variable (events : Events rows.scalarTy)

def result (M : Model V) [Lean.Grind.Field (rows.F M)] (x : Cube (rows.F M) (n+1)) (r : rows.F M) :
    HList (LVal M) (outputs (table rows.scalarTy n) rows.scalarTy) :=
  let y := Cube.restrict n x r
  .cons (Cube.flatten n y) (.cons (Cube.sum n y) (.cons r .nil))

include members
set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
theorem roundReturns (M : Model V) [Lean.Grind.Field (rows.F M)] [DecidableEq (rows.F M)]
    (math : rows.Arithmetic M) (sums : sr.Arithmetic rows M) (vector : TableRestriction.Arithmetic vec M)
    (eqLaw : ScalarEquality.Law rows.scalarTy events.equal events.equalType M)
    (path : List Frame) (sites : Nat → Key) (x : Cube (rows.F M) (n+1)) :
    Returns ((body ops events (emptyPoint rows.scalarTy) sites).denote
      (protocolSem M (Defs.fnTable M ds) (Defs.gTable M ds)) path
      (Env.empty.extend names (.cons (Cube.flatten (n+1) x) (.cons [] (.cons (Cube.sum (n+1) x) .nil)))))
      (fun vs => ∃ r, vs = result rows M x r) := by
  let f := Defs.fnTable M ds
  let m : M.Val rows.pair := (Cube.sum n x.1,Cube.sum n x.2,())
  have sent : localOp M f ops.sendValue (.cons (Cube.flatten (n+1) x) .nil) = .done (.cons m .nil) :=
    members.message M sums x
  have ends : localOp M f ops.boundary (.cons m .nil) = .done (.cons (Cube.sum (n+1) x) .nil) :=
    members.pair.boundary M math m
  have eqRow : localOp M f (.row events.equal _ events.equalType)
      (.cons (Cube.sum (n+1) x) (.cons (Cube.sum (n+1) x) .nil)) = .done (.cons true .nil) := by
    simp [localOp,eqLaw (Cube.sum (n+1) x) (Cube.sum (n+1) x)]
  change Returns (((liftLocal _ (localOp M f ops.sendValue (.cons (Cube.flatten (n+1) x) .nil))).map _).bind _) _
  rw [sent]
  intro _ _
  change Returns (((liftLocal _ (localOp M f ops.boundary (.cons m .nil))).map _).bind _) _
  rw [ends]
  change Returns (((liftLocal _ (localOp M f (.row events.equal _ events.equalType)
    (.cons (Cube.sum (n+1) x) (.cons (Cube.sum (n+1) x) .nil)))).map _).bind _) _
  rw [eqRow]
  intro r _
  have bound := members.bound M vector x r
  dsimp only at bound
  change Returns (((liftLocal _ (localOp M f ops.bindState (.cons (Cube.flatten (n+1) x) (.cons r .nil)))).map _).bind _) _
  rw [bound]
  have eval : localOp M f ops.evaluate (.cons m (.cons r .nil)) =
      .done (.cons (Cube.sum n (Cube.restrict n x r)) .nil) := by
    rw [show Cube.sum n (Cube.restrict n x r) = line (Cube.sum n x.1,Cube.sum n x.2) r
      from Cube.sum_interpolate r n x.1 x.2]
    exact members.pair.evaluate M math m r
  change Returns (((liftLocal _ (localOp M f ops.evaluate (.cons m (.cons r .nil)))).map _).bind _) _
  rw [eval]
  exact ⟨r,rfl⟩

#print axioms roundReturns
end ZkcFormal.Interactive.Sumcheck.HonestPairs

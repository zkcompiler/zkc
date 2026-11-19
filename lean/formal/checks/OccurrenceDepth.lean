import Zkc.Core.Program.DefinitionChecks
import Zkc.Formal.Interactive.RoundFamily
import Zkc.Formal.Written.FiniteModel
open Zkc.Core Zkc.Formal.Written Zkc.Formal.Written.FiniteModel
open Zkc.Formal.Interactive.Sumcheck Zkc.Formal.Interactive.Sumcheck.ReductionRound
namespace OccurrenceDepth

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def claims : Claims Nat := ⟨fun _ => Unit, fun d _ => d, fun _ _ _ => ()⟩
def constant (key n : Nat) (two : Bool) : Definition Standard :=
  .fn ⟨key⟩ (if two then [.nat,.nat] else [.nat]) [.nat] false none Summary.empty
    (.mk (if two then [0,1] else [0]) [.op ⟨1⟩ [2] (.literal .nat [n]) []] [2])
def stored : NamedProgram Standard := ⟨[constant 5 3 false, constant 6 0 true, constant 7 1 true]⟩
abbrev h5 : FnHeader Standard := ⟨⟨5⟩, [.nat], [.nat], false, none, Summary.empty⟩
abbrev ns5 : Names h5.ins := .cons 0 (.nil)
def body5 : Fn Standard [] h5 ns5 :=
  .op ⟨1⟩ (.literal .nat [3] rfl) .nil (.cons 2 .nil) (.ret (.cons ⟨2,rfl⟩ .nil))
theorem ok5 : FnConditions body5 := FnConditions.of_checks (by decide +kernel)
abbrev h6 : FnHeader Standard := ⟨⟨6⟩, [.nat,.nat], [.nat], false, none, Summary.empty⟩
abbrev ns6 : Names h6.ins := .cons 0 (.cons 1 (.nil))
def body6 : Fn Standard [h5] h6 ns6 :=
  .op ⟨1⟩ (.literal .nat [0] rfl) .nil (.cons 2 .nil) (.ret (.cons ⟨2,rfl⟩ .nil))
theorem ok6 : FnConditions body6 := FnConditions.of_checks (by decide +kernel)
abbrev h7 : FnHeader Standard := ⟨⟨7⟩, [.nat,.nat], [.nat], false, none, Summary.empty⟩
abbrev ns7 : Names h7.ins := .cons 0 (.cons 1 (.nil))
def body7 : Fn Standard [h6,h5] h7 ns7 :=
  .op ⟨1⟩ (.literal .nat [1] rfl) .nil (.cons 2 .nil) (.ret (.cons ⟨2,rfl⟩ .nil))
theorem ok7 : FnConditions body7 := FnConditions.of_checks (by decide +kernel)
abbrev hs : Headers Standard := ⟨[h7,h6,h5],[]⟩
def installed : Typed Standard :=
  ⟨hs,.fn h7 ns7 body7 ok7 (.fn h6 ns6 body6 ok6 (.fn h5 ns5 body5 ok5 .nil)),by decide⟩
theorem succeeds : (admit stored ⟨[],[],[],[],[]⟩).isOk := by decide +kernel
theorem readback (a : Admitted Standard) (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a) :
    a.program = installed := admitted_eq_of_readback h (by rfl)
abbrev fns := Defs.fnTable model installed.defs
local instance : DecidableEq (model.Val (.nat : Standard.Ty)) := inferInstanceAs (DecidableEq Nat)
def boundOp : LocalOp Standard hs.fns [.nat] [.nat] := .call (.tail (.tail .head))
def evalZero : LocalOp Standard hs.fns [.nat,.nat] [.nat] := .call (.tail .head)
def evalOne : LocalOp Standard hs.fns [.nat,.nat] [.nat] := .call .head
def members (e : LocalOp Standard hs.fns [.nat,.nat] [.nat]) :
    Members hs .nat .nat .nat .nat := ⟨boundOp,e,boundOp,e⟩

abbrev Law (e : LocalOp Standard hs.fns [.nat,.nat] [.nat]) {ι : Type} (depth : ι → Nat) :=
  RoundInterpretationOn (t := .nat) model fns claims [0,1] 1 (members e) depth

def atOne : Law evalZero (fun _ : Unit => 1) where
  boundary := fun _ => 3
  evaluate := fun _ _ => 0
  ends := fun _ => rfl
  atPoint := fun _ _ => rfl
  roots := by intros; change 0 ≤ 1; decide

def atZero : Law evalOne (fun _ : Unit => 0) where
  boundary := fun _ => 3
  evaluate := fun _ _ => 1
  ends := fun _ => rfl
  atPoint := fun _ _ => rfl
  roots := by intros; change 0 ≤ 1; decide

def result (p : Local (HList model.Val [.nat])) : Nat :=
  (functionResult (t := .nat) (M := model) p).getD 99

theorem firstFailsCross (l : Law evalZero (Fin.val (n := 2))) : False := by
  have b : 3 = l.boundary 0 := congrArg result (l.ends 0)
  have ev (r : Nat) : 0 = l.evaluate 0 r := congrArg result (l.atPoint 0 r)
  have bad := l.roots (0 : Fin 2) () 0 (by rw [← b]; decide)
  change [0,1].countP (fun r : Nat => decide (l.evaluate 0 r = 0)) ≤ 1 at bad
  simp [← ev] at bad

theorem secondFailsCross (l : Law evalOne (Fin.val (n := 2))) : False := by
  have b : 3 = l.boundary 0 := congrArg result (l.ends 0)
  have ev (r : Nat) : 1 = l.evaluate 0 r := congrArg result (l.atPoint 0 r)
  have bad := l.roots (1 : Fin 2) () 0 (by rw [← b]; decide)
  change [0,1].countP (fun r : Nat => decide (l.evaluate 0 r = 1)) ≤ 1 at bad
  simp [← ev] at bad

end OccurrenceDepth

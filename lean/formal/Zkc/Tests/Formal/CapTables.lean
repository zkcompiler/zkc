import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project
import Zkc.Formal.Walk
import Zkc.Formal.Written.SiteCaps
import Zkc.Formal.Written.WalkFees
import Zkc.Formal.Written.LawSamplers
import Zkc.Formal.Written.PortSamplers
import Zkc.Formal.Written.StandardModel
import Zkc.Tests.Formal.WalkLoop

/-!
Tables of caps, against stored programs.

A table lists the uses that a root reaches: a definition at the proof arguments of one of its
applications, with the caps of its charged draws and with its calls. Four stored programs of
unlike shapes are read here.

- **How often a draw can occur** (`NamedProgram.occurrences`, the view by paths): a draw in a
  kept loop of three; a draw two kept loops deep; a callee applied once and three times in a
  kept loop, beside a draw of the caller; a stepped loop, whose three blocks each have a draw
  with a key of its own.
- **The counts of a table are the program's** (`CapTable.counted`, decided by the kernel), and
  are not for a table with another count, with a cap at an instruction that is no coin, with a
  call that the definition does not make, with a call left out, or whose last use is not of the
  root; and, on three levels of definitions, with a call that names the use of another
  definition, or a use that stands later than the caller's, each with nothing else wrong.
- **What a table adds up to and allows**: the total of the caller is its own draw and four
  times the callee's; two calls of one definition at different proof arguments are two uses,
  and exchanging them exchanges what each call is allowed; the list of sites of a table is the
  program's occurrences at the charged draws.
- **A draw two loops deep is paid at its site** (`charged_pay_at`): the verifier of the nested
  program, on a false claim, is judged never to return within the budget of its table, six
  times one eighth, each fee within the cap of the draw. The occurrence of the draw is read
  from the effect, and its cap from the table by the kernel.
-/

open Zkc.Core Zkc.Formal Zkc.Formal.ProbabilisticProcess Zkc.Formal.Written OracleComp ProbComp
open Zkc.Frontend.Written (CapTable UseCaps DrawCap CallCap)
open scoped NNRat ENNReal

namespace Zkc.Tests.Formal.CapTables

abbrev V : Vocabulary := WalkLoop.V

/-- The guessing protocol of three rounds: a message and a draw in a kept loop. -/
def guess : NamedProgram V := ⟨[WalkLoop.stored]⟩

/-- The same rounds in two kept loops, of two and of three. -/
def nested : Definition V :=
  .protocol ⟨1⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] []
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.compute [0, 1] (.literal .bool [0])) [],
      .op ⟨1⟩ [3] (.narrow [0, 1]) [2],
      .loop ⟨12⟩ [0, 1] (.fixed 2) [3] [18] (.mk [4, 5] [
        .op ⟨2⟩ [6] (.narrow [0, 1]) [5],
        .loop ⟨10⟩ [0, 1] (.fixed 3) [6] [16] (.mk [7, 8] [
          .op ⟨3⟩ [9] (.event (.flow .message 0 [1]) (.fin 8)) [1],
          .op ⟨4⟩ [10] (.event (.given (.coin (.uniform (.fin 8))) 1 [0]) (.fin 8)) [],
          .op ⟨5⟩ [11] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [10],
          .op ⟨6⟩ [12] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [9],
          .op ⟨7⟩ [13] (.compute [0, 1] (.owned OwnedName.natEqual [] [])) [11, 12],
          .op ⟨8⟩ [14] (.compute [0, 1] (.owned OwnedName.boolOr [] [])) [8, 13],
          .op ⟨9⟩ [15] (.narrow [0, 1]) [14]] [15]),
        .op ⟨11⟩ [17] (.narrow [0, 1]) [16]] [17]),
      .op ⟨13⟩ [19] (.compute [1] (.owned OwnedName.boolOr [] [])) [0, 18],
      .guard ⟨14⟩ [1] 19 .reject] [])


/-- A callee with one draw, and a caller that applies it once, then three times in a kept loop,
and draws once itself. -/
def once : Definition V :=
  .protocol ⟨1⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] [⟨.bool, [0, 1]⟩]
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.event (.flow .message 0 [1]) (.fin 8)) [1],
      .op ⟨1⟩ [3] (.event (.given (.coin (.uniform (.fin 8))) 1 [0]) (.fin 8)) [],
      .op ⟨2⟩ [4] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [3],
      .op ⟨3⟩ [5] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [2],
      .op ⟨4⟩ [6] (.compute [0, 1] (.owned OwnedName.natEqual [] [])) [4, 5],
      .op ⟨5⟩ [7] (.narrow [0, 1]) [6]] [7])

def caller : Definition V :=
  .protocol ⟨2⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] []
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.apply ⟨1⟩ [0, 1]) [0, 1],
      .op ⟨1⟩ [3] (.narrow [0, 1]) [2],
      .loop ⟨5⟩ [0, 1] (.fixed 3) [3] [9] (.mk [4, 5] [
        .op ⟨2⟩ [6] (.apply ⟨1⟩ [0, 1]) [0, 1],
        .op ⟨3⟩ [7] (.compute [0, 1] (.owned OwnedName.boolOr [] [])) [5, 6],
        .op ⟨4⟩ [8] (.narrow [0, 1]) [7]] [8]),
      .op ⟨6⟩ [10] (.event (.given (.coin (.uniform (.fin 4))) 1 [0]) (.fin 4)) [],
      .op ⟨7⟩ [11] (.compute [1] (.owned OwnedName.boolOr [] [])) [0, 9],
      .guard ⟨8⟩ [1] 11 .reject] [])

def calls : NamedProgram V := ⟨[once, caller]⟩

/-- A second callee with the body of the first under another key, and a definition that applies
the caller: three levels, for the conditions on which use a call names. -/
def other : Definition V :=
  .protocol ⟨3⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] [⟨.bool, [0, 1]⟩]
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.event (.flow .message 0 [1]) (.fin 8)) [1],
      .op ⟨1⟩ [3] (.event (.given (.coin (.uniform (.fin 8))) 1 [0]) (.fin 8)) [],
      .op ⟨2⟩ [4] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [3],
      .op ⟨3⟩ [5] (.compute [0, 1] (.owned OwnedName.finToNat [.fin 8] [])) [2],
      .op ⟨4⟩ [6] (.compute [0, 1] (.owned OwnedName.natEqual [] [])) [4, 5],
      .op ⟨5⟩ [7] (.narrow [0, 1]) [6]] [7])

def top : Definition V :=
  .protocol ⟨4⟩ 2 [⟨.bool, [0, 1]⟩, ⟨.fin 8, [0]⟩] []
    (.mk [0, 1] [.op ⟨0⟩ [] (.apply ⟨2⟩ [0, 1]) [0, 1]] [])

def levels : NamedProgram V := ⟨[other, once, caller, top]⟩

/-- A stepped loop of three: each block and each draw has a key of its own. -/
def stepped : NamedProgram V := ⟨[
  .protocol ⟨1⟩ 2 [⟨.bool, [0, 1]⟩] []
    (.mk [0] [
      .block ⟨1⟩ 0 [] (.mk [] [
        .op ⟨0⟩ [1] (.event (.given (.coin (.uniform (.fin 2))) 1 [0]) (.fin 2)) []] []),
      .block ⟨3⟩ 1 [] (.mk [] [
        .op ⟨2⟩ [2] (.event (.given (.coin (.uniform (.fin 3))) 1 [0]) (.fin 3)) []] []),
      .block ⟨5⟩ 2 [] (.mk [] [
        .op ⟨4⟩ [3] (.event (.given (.coin (.uniform (.fin 4))) 1 [0]) (.fin 4)) []] []),
      .guard ⟨6⟩ [1] 0 .reject] [])]⟩

/-! ## How often a draw can occur -/

example : guess.occurrences ⟨0⟩ = [(⟨[], ⟨3⟩⟩, some 3)] := by decide +kernel
example : (⟨[nested]⟩ : NamedProgram V).occurrences ⟨1⟩ = [(⟨[], ⟨4⟩⟩, some 6)] := by decide +kernel
example : calls.occurrences ⟨2⟩ =
    [(⟨[⟨0⟩], ⟨1⟩⟩, some 1), (⟨[⟨2⟩], ⟨1⟩⟩, some 3), (⟨[], ⟨6⟩⟩, some 1)] := by decide +kernel
example : stepped.occurrences ⟨1⟩ =
    [(⟨[], ⟨0⟩⟩, some 1), (⟨[], ⟨2⟩⟩, some 1), (⟨[], ⟨4⟩⟩, some 1)] := by decide +kernel

/-! ## The counts of a table -/

/-- The table of the guessing protocol: the draw at key 3, one eighth, three times. -/
def guessCaps : CapTable := ⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 3⟩], []⟩]⟩

/-- The table of the nested rounds: the draw at key 4, one eighth, six times. -/
def nestedCaps : CapTable := ⟨[⟨⟨1⟩, [⟨⟨4⟩, 1, 8, 6⟩], []⟩]⟩

/-- The table of the caller: the callee's use with its draw at one eighth, and the caller's use
with its own draw at one quarter and its two calls, once and three times. -/
def callsCaps : CapTable :=
  ⟨[⟨⟨1⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩, ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, 0⟩, ⟨⟨2⟩, 3, 0⟩]⟩]⟩

/-- The same caller with the callee at two proof arguments: the first call's use has the cap
three eighths, the second's one quarter. -/
def twoUses (first second : Nat) : CapTable :=
  ⟨[⟨⟨1⟩, [⟨⟨1⟩, 3, 8, 1⟩], []⟩, ⟨⟨1⟩, [⟨⟨1⟩, 1, 4, 1⟩], []⟩,
    ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, first⟩, ⟨⟨2⟩, 3, second⟩]⟩]⟩

def steppedCaps : CapTable :=
  ⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 2, 1⟩, ⟨⟨2⟩, 1, 2, 1⟩, ⟨⟨4⟩, 1, 2, 1⟩], []⟩]⟩

example : guessCaps.counted guess ⟨0⟩ = true := by decide +kernel
example : nestedCaps.counted ⟨[nested]⟩ ⟨1⟩ = true := by decide +kernel
example : callsCaps.counted calls ⟨2⟩ = true := by decide +kernel
example : (twoUses 0 1).counted calls ⟨2⟩ = true := by decide +kernel
example : (twoUses 1 0).counted calls ⟨2⟩ = true := by decide +kernel
example : steppedCaps.counted stepped ⟨1⟩ = true := by decide +kernel

-- another count
example : (⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 2⟩], []⟩]⟩ : CapTable).counted guess ⟨0⟩ = false := by decide +kernel
example : (⟨[⟨⟨1⟩, [⟨⟨4⟩, 1, 8, 5⟩], []⟩]⟩ : CapTable).counted ⟨[nested]⟩ ⟨1⟩ = false := by
  decide +kernel
-- a cap at the message, and at the guard
example : (⟨[⟨⟨0⟩, [⟨⟨2⟩, 1, 8, 3⟩], []⟩]⟩ : CapTable).counted guess ⟨0⟩ = false := by decide +kernel
example : (⟨[⟨⟨0⟩, [⟨⟨11⟩, 1, 8, 1⟩], []⟩]⟩ : CapTable).counted guess ⟨0⟩ = false := by decide +kernel
-- a draw listed twice
example : (⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 3⟩, ⟨⟨3⟩, 1, 8, 3⟩], []⟩]⟩ : CapTable).counted guess ⟨0⟩ = false := by
  decide +kernel
-- a call that the definition does not make, and a call left out
example : (⟨[⟨⟨0⟩, [], []⟩, ⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 3⟩], [⟨⟨1⟩, 1, 0⟩]⟩]⟩ : CapTable).counted guess ⟨0⟩ = false := by
  decide +kernel
example : (⟨[⟨⟨1⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩, ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, 0⟩]⟩]⟩ : CapTable).counted
    calls ⟨2⟩ = false := by decide +kernel
-- the count of a call, the use of another definition as its callee, a callee that stands later
example : (⟨[⟨⟨1⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩, ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, 0⟩, ⟨⟨2⟩, 2, 0⟩]⟩]⟩ :
    CapTable).counted calls ⟨2⟩ = false := by decide +kernel
example : (⟨[⟨⟨1⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩, ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, 1⟩, ⟨⟨2⟩, 3, 0⟩]⟩]⟩ :
    CapTable).counted calls ⟨2⟩ = false := by decide +kernel
-- the last use is not of the root
example : callsCaps.counted calls ⟨1⟩ = false := by decide +kernel

/-- The uses of the three levels: the second callee, the first, the caller, and the top. The
caller's two calls name the uses at the places `first` and `second`; with `callerFirst` the
caller's use stands before the uses of its callees. -/
def levelsCaps (first second : Nat) (callerFirst : Bool) : CapTable :=
  let otherUse : UseCaps := ⟨⟨3⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩
  let onceUse : UseCaps := ⟨⟨1⟩, [⟨⟨1⟩, 1, 8, 1⟩], []⟩
  let callerUse : UseCaps := ⟨⟨2⟩, [⟨⟨6⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, first⟩, ⟨⟨2⟩, 3, second⟩]⟩
  if callerFirst then ⟨[callerUse, otherUse, onceUse, ⟨⟨4⟩, [], [⟨⟨0⟩, 1, 0⟩]⟩]⟩
  else ⟨[otherUse, onceUse, callerUse, ⟨⟨4⟩, [], [⟨⟨0⟩, 1, 2⟩]⟩]⟩

-- each call names a use of the definition that it applies, which stands earlier
example : (levelsCaps 1 1 false).counted levels ⟨4⟩ = true := by decide +kernel
-- the use of another definition as the callee, and nothing else wrong: it stands earlier
example : (levelsCaps 0 1 false).counted levels ⟨4⟩ = false := by decide +kernel
-- the callee's use stands later than the caller's, and nothing else wrong: it is a use of the
-- applied definition, and the last use is of the root
example : (levelsCaps 2 2 true).counted levels ⟨4⟩ = false := by decide +kernel

/-! ## What a table adds up to and allows -/

example : guessCaps.budget = 3 / 8 := by decide +kernel
example : nestedCaps.budget = 6 / 8 := by decide +kernel
example : callsCaps.totals = [1 / 8, 3 / 4] := by decide +kernel
example : steppedCaps.budget = 3 / 2 := by decide +kernel

-- the caps of the caller: its own draw, the callee's draw below each call, and nothing elsewhere
example : callsCaps.cap ⟨[], ⟨6⟩⟩ = 1 / 4 := by decide +kernel
example : callsCaps.cap ⟨[⟨0⟩], ⟨1⟩⟩ = 1 / 8 := by decide +kernel
example : callsCaps.cap ⟨[⟨2⟩], ⟨1⟩⟩ = 1 / 8 := by decide +kernel
example : callsCaps.cap ⟨[], ⟨1⟩⟩ = 0 := by decide +kernel
example : callsCaps.cap ⟨[⟨7⟩], ⟨1⟩⟩ = 0 := by decide +kernel
example : callsCaps.cap ⟨[⟨0⟩, ⟨0⟩], ⟨1⟩⟩ = 0 := by decide +kernel

-- two uses of one definition: each call is allowed the cap of its own use, and exchanging the
-- uses exchanges the two, with the counts of the calls as they were
example : ((twoUses 0 1).cap ⟨[⟨0⟩], ⟨1⟩⟩, (twoUses 0 1).cap ⟨[⟨2⟩], ⟨1⟩⟩) = (3 / 8, 1 / 4) := by
  decide +kernel
example : ((twoUses 1 0).cap ⟨[⟨0⟩], ⟨1⟩⟩, (twoUses 1 0).cap ⟨[⟨2⟩], ⟨1⟩⟩) = (1 / 4, 3 / 8) := by
  decide +kernel
example : ((twoUses 0 1).budget, (twoUses 1 0).budget) = (11 / 8, 13 / 8) := by decide +kernel

-- the sites of a table are the program's occurrences at the charged draws
example : callsCaps.sites =
    [(⟨[], ⟨6⟩⟩, 1, 4, 1), (⟨[⟨0⟩], ⟨1⟩⟩, 1, 8, 1), (⟨[⟨2⟩], ⟨1⟩⟩, 1, 8, 3)] := by decide +kernel
example : (callsCaps.sites.all fun (site, _, _, count) =>
    (calls.occurrences ⟨2⟩).lookup site == some (some count)) = true := by decide +kernel
example : (nestedCaps.sites.all fun (site, _, _, count) =>
    ((⟨[nested]⟩ : NamedProgram V).occurrences ⟨1⟩).lookup site == some (some count)) = true := by
  decide +kernel

-- a ceiling: the budget of a table against a ratio of naturals, by the kernel
example : callsCaps.total ≤ ((3 : ℕ) : ℝ≥0∞) / (4 : ℕ) :=
  callsCaps.total_le_div 3 4 (by decide) (by decide +kernel)

/-! ## A draw that the role does not own -/

/-- The samplers of the laws give a sampler at a coin that the role owns and none at an effect
that it hears or gets: a cap at such a draw is part of a total, and pays for nothing in that
role's judgment. -/
example {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]
    (owner : Role) (at_ : Occurrence) :
    lawSamplers (StandardModel.model D) (StandardModel.draws D)
      (.hear (.coin (.uniform (.fin 8))) owner at_ (.fin 8)) = none := rfl

example {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]
    (giver : Role) (at_ : Occurrence) :
    lawSamplers (StandardModel.model D) (StandardModel.draws D)
      (.get .message giver at_ (.fin 8)) = none := rfl

/-! ## A draw two loops deep, paid at its site -/

noncomputable section

kernel_ok elaborated with header names body : Elaborated V Typed.empty.headers :=
  elaborateDefinition Typed.empty.headers nested

def installed : Typed V := Typed.empty.add elaborated

abbrev verifier : Role := 1

kernel_normal verifierProgram :
    Term (roleDialect V Typed.empty.headers verifier) (Ctx.empty.extend names) header.outs :=
  project verifier body

theorem verifier_meaning (M : Model V) (path : List Frame)
    (inputs : HList (RV M verifier) header.ins) :
    roleMeaning M installed Member.head verifier path inputs =
      (verifierProgram.denote (roleSem M verifier (Defs.fnTable M Typed.empty.defs)
        (Defs.rTable M Typed.empty.defs)) path (Env.empty.extend names inputs)).sealed := by
  kernel_rfl

variable {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]

abbrev model : Model V := StandardModel.model D

def inputs (claim : Bool) : HList (RV (model D) verifier) header.ins := .cons claim (.cons () .nil)

abbrev samplers : Samplers (RSig (model D)) := lawSamplers (model D) (StandardModel.draws D)

/-- A draw two kept loops deep is paid at every iteration of both, by the tactics of a text:
the walk stops at each effect, the message is met for free, and the draw pays one eighth for
the position that was sent. The occurrence of the draw, with the frames of both loops, the
sampler of its law and its cap in the table are read from the goal; the kernel decides the
cap. -/
theorem judged (path : List Frame) :
    (roleMeaning (model D) installed Member.head verifier path (inputs D false)).interpret
      (.charged (Permitted (model D)) (paysWithin (samplers D) (nestedCaps.allowance (model D) path)))
      (fun _ _ => False) (fun _ _ => True) nestedCaps.budget := by
  rw [verifier_meaning]
  walk
  walk_loop fun i (hit : Bool) budget => hit = false ∧ ((2 - i : ℕ) : ℚ≥0) * (3 / 8) ≤ budget
  case first =>
    refine ⟨rfl, le_of_eq ?_⟩
    have total : nestedCaps.budget = 6 / 8 := by decide +kernel
    rw [total]
    norm_num
  case step =>
    obtain ⟨rfl, enough⟩ := invariant_i
    have split : (2 - i : ℕ) = (2 - (i + 1)) + 1 := by omega
    rw [split, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at enough
    walk
    walk_loop fun j (hit : Bool) budget =>
      hit = false ∧ ((2 - (i + 1) : ℕ) : ℚ≥0) * (3 / 8) + ((3 - j : ℕ) : ℚ≥0) * (1 / 8) ≤ budget
    case first =>
      refine ⟨rfl, le_trans (le_of_eq ?_) enough⟩
      norm_num
    case step =>
      obtain ⟨rfl, left⟩ := invariant_j
      have inner : (3 - j : ℕ) = (3 - (j + 1)) + 1 := by omega
      rw [inner, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc] at left
      walk
      walk_free as got
      walk
      walk_pay (1 / 8) excluding (fun drawn : ℕ => drawn = got) as drawn differs
      case weight => simpa using prEvent_drawPosition_eq_le 7 got
      case within => exact le_trans le_add_self left
      walk
      refine ⟨?_, le_tsub_of_add_le_right left⟩
      exact Bool.eq_false_iff.mpr fun same => differs (Nat.eq_of_beq_eq_true same)
    case after =>
      obtain ⟨rfl, left⟩ := invariant_j
      walk
      exact ⟨rfl, by simpa using left⟩
  case after =>
    obtain ⟨rfl, _⟩ := invariant_i
    walk

end

/--
info: 'Zkc.Tests.Formal.CapTables.judged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms judged

/-! `kernel_rfl` is checked by the kernel also where a file turns the check of its
declarations off, and the words of the walk's tactics stay names. -/

/-- error: kernel_rfl: the kernel does not find the two sides definitionally equal -/
#guard_msgs in
set_option debug.skipKernelTC true in
example : (0 : Nat) = 1 := by kernel_rfl

example (n : Nat) : n + 0 = n := by kernel_rfl

example (late excluding : Nat) : late + excluding = excluding + late := Nat.add_comm late excluding

end Zkc.Tests.Formal.CapTables

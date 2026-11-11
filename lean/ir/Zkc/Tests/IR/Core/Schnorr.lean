import Zkc.Tools.IR.Core.Import
import Zkc.IR.Core.Laws

/-! The Schnorr proof of knowledge of the package chapter, as a `zkc.core/0` package.

The embedded package is the fixture `fixtures/core/schnorr.json`; the importer
compares the two as JSON values. Its side meanings for one and two roles are stated
as explicit processes over the effect signature and hold by definitional
unfolding, for every model. The model's operations and laws are named through the
row constants that the importer derives from the catalogue identities, and the
agreements of the signature say which input copies an honest execution starts with
equal. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

import_core schnorr from r#"["zkc.core/0",
 [["original",
   [["field", [["domain", "scalar"]]], ["group", [["domain", "curve"]]]],
   [],
   [["law.uniform", [["type", ["nominal", 0]]], "sampling", [], [["nominal", 0]]],
    ["curve.scale", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 0]], [["nominal", 1]]],
    ["curve.add", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 1]], [["nominal", 1]]],
    ["curve.equal", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 1]], ["bool"]],
    ["field.mul", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]],
    ["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
   [["protocol", 0, 2,
     [[["nominal", 1], 0], [["nominal", 1], 0], [["nominal", 0], 0],
      [["nominal", 1], 1], [["nominal", 1], 1]],
     [["bool", 1]],
     [[0, [0, 3]], [0, [1, 4]]],
     [[["sample", 0, 0, 0, []],
       ["at", 0, ["op", 1, [0, 5]]],
       ["exchange", 0, 1, 1, 6],
       ["draw", 1, [0], 2, 0, []],
       ["at", 0, ["op", 4, [9, 2]]],
       ["at", 0, ["op", 5, [5, 10]]],
       ["exchange", 0, 1, 3, 11],
       ["at", 1, ["op", 1, [3, 12]]],
       ["at", 1, ["op", 1, [4, 8]]],
       ["at", 1, ["op", 2, [7, 14]]],
       ["at", 1, ["op", 3, [13, 15]]]],
      [16]]]]]],
 [], [], [],
 [["schnorr"], [["prover", "verifier"]], [["nonce", "commitment", "challenge", "response"]]]]"# fixture "fixtures/core/schnorr.json"

namespace Zkc.Tests.Core.Schnorr

-- The definitions below name imported rows and programs, which are not compiled.
noncomputable section

abbrev scalar : Ty := .nominal 0
abbrev point : Ty := .nominal 1

/-- The uniform law over the scalar field. -/
abbrev uniform : SamplingRow := .of schnorr.row.«law.uniform(type field(domain scalar))»

abbrev prover : Side := Side.ofMask 0b01
abbrev verifier : Side := Side.ofMask 0b10
abbrev both : Side := Side.ofMask 0b11

variable (M : Model)

/-! The model's operations, by the catalogue identity of their rows. -/

def scale (p : M.Value point) (s : M.Value scalar) : M.Value point :=
  (M.pure (.of schnorr.row.«curve.scale(domain curve)») (.cons p (.cons s .nil))).get .here

def add (p q : M.Value point) : M.Value point :=
  (M.pure (.of schnorr.row.«curve.add(domain curve)») (.cons p (.cons q .nil))).get .here

def equal (p q : M.Value point) : Bool :=
  (M.pure (.of schnorr.row.«curve.equal(domain curve)») (.cons p (.cons q .nil))).get .here

def mul (a b : M.Value scalar) : M.Value scalar :=
  (M.pure (.of schnorr.row.«field.mul(domain scalar)») (.cons a (.cons b .nil))).get .here

def fieldAdd (a b : M.Value scalar) : M.Value scalar :=
  (M.pure (.of schnorr.row.«field.add(domain scalar)») (.cons a (.cons b .nil))).get .here

/-- The catalogue identities are data in the environment, by position. -/
example : schnorr.catalogue.operations.length = schnorr.operations.length := rfl

/-- The verifier receives the commitment, draws the challenge, receives the response,
and decides with the model's operations on its own copies of `g` and `y`. -/
theorem verifier_side (g y : M.Value point) :
    schnorr.schnorr.meaning M verifier
        (.cons () (.cons () (.cons () (.cons g (.cons y .nil))))) =
      .call (.receive ⟨0, 1⟩ point) fun commitment =>
      .call (.draw ⟨0, 2⟩ uniform .nil) fun challenge =>
      .call (.receive ⟨0, 3⟩ scalar) fun response =>
      .done (.cons (equal M (scale M g response) (add M commitment (scale M y challenge))) .nil) :=
  rfl

/-- The prover samples its nonce, sends the commitment, receives the challenge and
sends the response. It holds no output. -/
theorem prover_side (g y : M.Value point) (x : M.Value scalar) :
    schnorr.schnorr.meaning M prover
        (.cons g (.cons y (.cons x (.cons () (.cons () .nil))))) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun nonce =>
      .call (.send ⟨0, 1⟩ point (scale M g nonce)) fun _ =>
      .call (.receive ⟨0, 2⟩ scalar) fun challenge =>
      .call (.send ⟨0, 3⟩ scalar (fieldAdd M nonce (mul M challenge x))) fun _ =>
      .done (.cons () .nil) :=
  rfl

/-- The prover's side again, walked one operation at a time: the challenge is a draw
of the verifier, outside the side, announced to the prover alone. -/
theorem prover_side_stepwise (g y : M.Value point) (x : M.Value scalar) :
    schnorr.schnorr.meaning M prover
        (.cons g (.cons y (.cons x (.cons () (.cons () .nil))))) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun nonce =>
      .call (.send ⟨0, 1⟩ point (scale M g nonce)) fun _ =>
      .call (.receive ⟨0, 2⟩ scalar) fun challenge =>
      .call (.send ⟨0, 3⟩ scalar (fieldAdd M nonce (mul M challenge x))) fun _ =>
      .done (.cons () .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_call (sample_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun nonce => ?_)
  refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_send rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun _ => ?_)
  refine (sideMeaning_step_call (draw_received rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun challenge => ?_)
  iterate 2 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_send rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun _ => ?_)
  iterate 4 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  exact sideMeaning_ret

/-- Both roles together: the nonce and the challenge are the only effects. The
verifier's copies `g'` and `y'` of the agreed inputs stay separate values. -/
theorem honest_side (g y : M.Value point) (x : M.Value scalar) (g' y' : M.Value point) :
    schnorr.schnorr.meaning M both
        (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil))))) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun nonce =>
      .call (.draw ⟨0, 2⟩ uniform .nil) fun challenge =>
      .done (.cons (equal M (scale M g' (fieldAdd M nonce (mul M challenge x)))
        (add M (scale M g nonce) (scale M y' challenge))) .nil) :=
  rfl

theorem honest_side_randomness (g y : M.Value point) (x : M.Value scalar) (g' y' : M.Value point) :
    OnlyEffects Effect.random (schnorr.schnorr.meaning M both
      (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil)))))) := by
  rw [honest_side]
  exact ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩

/-! ## Agreements

The signature records two agreements over the inputs: the copies of `g` (inputs 0
and 3) and the copies of `y` (inputs 1 and 4). -/

/-- For both roles, the input agreements say that the two copies of `g` are equal and
the two copies of `y` are equal. -/
theorem agreements_both (g y : M.Value point) (x : M.Value scalar) (g' y' : M.Value point) :
    schnorr.schnorr.agreements.InputsHold M both
        (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil))))) ↔ g = g' ∧ y = y' := by
  constructor
  · intro holds
    exact ⟨holds _ (.head _) ⟨0, .here⟩ (.head _) ⟨1, .there (.there (.there .here))⟩
        (.tail _ (.head _)) rfl rfl,
      holds _ (.tail _ (.head _)) ⟨0, .there .here⟩ (.head _)
        ⟨1, .there (.there (.there (.there .here)))⟩ (.tail _ (.head _)) rfl rfl⟩
  · rintro ⟨rfl, rfl⟩ agreement member first firstCopy second secondCopy firstMember secondMember
    simp only [Program.agreements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at firstCopy secondCopy <;>
      rcases firstCopy with rfl | rfl <;> rcases secondCopy with rfl | rfl <;> rfl

/-- The verifier alone holds one copy of each agreed input: nothing is required. -/
theorem agreements_verifier (g y : M.Value point) :
    schnorr.schnorr.agreements.InputsHold M verifier
        (.cons () (.cons () (.cons () (.cons g (.cons y .nil))))) := by
  intro agreement member first firstCopy second secondCopy firstMember secondMember
  simp only [Program.agreements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at firstCopy secondCopy <;>
    rcases firstCopy with rfl | rfl <;> rcases secondCopy with rfl | rfl <;>
    first | rfl | exact Bool.noConfusion firstMember | exact Bool.noConfusion secondMember

/-- Completeness of the honest execution. The inputs satisfy the agreements of the
signature and the statement `y = x·g`; the model satisfies two laws, stated on the
named rows: scaling distributes over the scalar sum, and equality is reflexive. -/
theorem honest_accepts (g y : M.Value point) (x : M.Value scalar) (g' y' : M.Value point)
    (agree : schnorr.schnorr.agreements.InputsHold M both
      (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil))))))
    (statement : y = scale M g x)
    (distributes : ∀ (p : M.Value point) (a b c : M.Value scalar),
      scale M p (fieldAdd M a (mul M b c)) = add M (scale M p a) (scale M (scale M p c) b))
    (reflexive : ∀ p : M.Value point, equal M p p = true) :
    schnorr.schnorr.meaning M both
        (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil))))) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun _ =>
      .call (.draw ⟨0, 2⟩ uniform .nil) fun _ =>
      .done (.cons true .nil) := by
  obtain ⟨rfl, rfl⟩ := (agreements_both M g y x g' y').mp agree
  subst statement
  rw [honest_side]
  congr 1; funext nonce; congr 1; funext challenge
  rw [distributes, reflexive]

end

end Zkc.Tests.Core.Schnorr

/-- info: 'Zkc.Tests.Core.Schnorr.verifier_side' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Schnorr.verifier_side

/-- info: 'Zkc.Tests.Core.Schnorr.honest_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Schnorr.honest_accepts

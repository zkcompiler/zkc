import Zkc.Tools.IR.Core.Import
import Zkc.IR.Core.Laws

/-! A polynomial opening with a setup role, as a `zkc.core/0` package.

Role 0 samples the secret and computes the reference string for role 1 and the
verification key for role 2; role 1 commits to its polynomial, role 2 draws the
evaluation point, role 1 opens, and role 2 checks with a pairing. Every catalogue
operation keeps an uninterpreted meaning: the statements below hold for every
model. The embedded package is the fixture `fixtures/core/opening.json`.

Each side is walked one operation at a time with the equations of
`Zkc.IR.Core.Laws`: 31 instructions, without a raised recursion limit. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

import_core opening from r#"["zkc.core/0",
 [["original",
   [["field", [["domain", "scalar"]]],
    ["group", [["domain", "g1"]]],
    ["group", [["domain", "g2"]]],
    ["polynomial", [["domain", "scalar"]]],
    ["groups", [["domain", "g1"]]],
    ["vector", [["domain", "scalar"]]]],
   [],
   [["law.uniform", [["type", ["nominal", 0]]], "sampling", [], [["nominal", 0]]],
    ["curve.generator", [["domain", "g1"]], "pure", [], [["nominal", 1]]],
    ["curve.generator", [["domain", "g2"]], "pure", [], [["nominal", 2]]],
    ["curve.scale", [["domain", "g1"]], "pure", [["nominal", 1], ["nominal", 0]], [["nominal", 1]]],
    ["curve.scale", [["domain", "g2"]], "pure", [["nominal", 2], ["nominal", 0]], [["nominal", 2]]],
    ["curve.empty", [["domain", "g1"]], "pure", [], [["nominal", 4]]],
    ["curve.append", [["domain", "g1"]], "pure", [["nominal", 4], ["nominal", 1]], [["nominal", 4]]],
    ["poly.coefficients", [["domain", "scalar"]], "pure", [["nominal", 3]], [["nominal", 5]]],
    ["curve.msm", [["domain", "g1"]], "pure", [["nominal", 5], ["nominal", 4]], [["nominal", 1]]],
    ["poly.univariate_evaluate", [["domain", "scalar"]], "pure",
     [["nominal", 3], ["nominal", 0]], [["nominal", 0]]],
    ["poly.divide_opening", [["domain", "scalar"]], "pure",
     [["nominal", 3], ["nominal", 0], ["nominal", 0]], [["nominal", 3]]],
    ["curve.neg", [["domain", "g1"]], "pure", [["nominal", 1]], [["nominal", 1]]],
    ["curve.neg", [["domain", "g2"]], "pure", [["nominal", 2]], [["nominal", 2]]],
    ["curve.add", [["domain", "g1"]], "pure", [["nominal", 1], ["nominal", 1]], [["nominal", 1]]],
    ["curve.add", [["domain", "g2"]], "pure", [["nominal", 2], ["nominal", 2]], [["nominal", 2]]],
    ["pairing.check", [["domain", "scalar"]], "pure",
     [["nominal", 1], ["nominal", 2], ["nominal", 1], ["nominal", 2]], ["bool"]]],
   [["protocol", 0, 3,
     [[["nominal", 3], 1]],
     [[["nominal", 0], 2], [["nominal", 0], 2], ["bool", 2]],
     [],
     [[["sample", 0, 0, 0, []],
       ["at", 0, ["op", 1, []]],
       ["at", 0, ["op", 3, [2, 1]]],
       ["at", 0, ["op", 3, [3, 1]]],
       ["at", 0, ["op", 5, []]],
       ["at", 0, ["op", 6, [5, 2]]],
       ["at", 0, ["op", 6, [6, 3]]],
       ["at", 0, ["op", 6, [7, 4]]],
       ["at", 0, ["op", 2, []]],
       ["at", 0, ["op", 4, [9, 1]]],
       ["exchange", 0, 1, 1, 8],
       ["exchange", 0, 2, 2, 10],
       ["at", 1, ["op", 7, [0]]],
       ["at", 1, ["op", 8, [13, 11]]],
       ["exchange", 1, 2, 3, 14],
       ["draw", 2, [1], 4, 0, []],
       ["at", 1, ["op", 9, [0, 17]]],
       ["at", 1, ["op", 10, [0, 17, 18]]],
       ["at", 1, ["op", 7, [19]]],
       ["at", 1, ["op", 8, [20, 11]]],
       ["exchange", 1, 2, 5, 18],
       ["exchange", 1, 2, 6, 21],
       ["at", 2, ["op", 1, []]],
       ["at", 2, ["op", 2, []]],
       ["at", 2, ["op", 3, [24, 22]]],
       ["at", 2, ["op", 11, [26]]],
       ["at", 2, ["op", 13, [15, 27]]],
       ["at", 2, ["op", 4, [25, 16]]],
       ["at", 2, ["op", 12, [29]]],
       ["at", 2, ["op", 14, [12, 30]]],
       ["at", 2, ["op", 15, [28, 25, 23, 31]]]],
      [16, 22, 32]]]]]],
 [], [], [],
 [["opening"], [["setup", "prover", "verifier"]],
  [["secret", "reference_string", "verification_key", "commitment", "point", "evaluation",
    "proof"]]]]"# fixture "fixtures/core/opening.json"

namespace Zkc.Tests.Core.Opening

-- The definitions below name imported rows and programs, which are not compiled.
noncomputable section

abbrev scalar : Ty := .nominal 0
abbrev first : Ty := .nominal 1
abbrev second : Ty := .nominal 2
abbrev polynomial : Ty := .nominal 3
abbrev points : Ty := .nominal 4
abbrev coefficients : Ty := .nominal 5

/-- The uniform law over the scalar field. -/
abbrev uniform : SamplingRow := .of opening.row.«law.uniform(type field(domain scalar))»

abbrev verifier : Side := Side.ofMask 0b100
abbrev setupAndVerifier : Side := Side.ofMask 0b101
abbrev everyRole : Side := Side.ofMask 0b111

variable (M : Model)

/-! The model's operations, by the catalogue identity of their rows. The two groups
have separate rows of one catalogue operation. -/

def generator₁ : M.Value first :=
  (M.pure (.of opening.row.«curve.generator(domain g1)») .nil).get .here
def generator₂ : M.Value second :=
  (M.pure (.of opening.row.«curve.generator(domain g2)») .nil).get .here
def scale₁ (p : M.Value first) (s : M.Value scalar) : M.Value first :=
  (M.pure (.of opening.row.«curve.scale(domain g1)») (.cons p (.cons s .nil))).get .here
def scale₂ (p : M.Value second) (s : M.Value scalar) : M.Value second :=
  (M.pure (.of opening.row.«curve.scale(domain g2)») (.cons p (.cons s .nil))).get .here
def empty : M.Value points := (M.pure (.of opening.row.«curve.empty(domain g1)») .nil).get .here
def append (list : M.Value points) (p : M.Value first) : M.Value points :=
  (M.pure (.of opening.row.«curve.append(domain g1)») (.cons list (.cons p .nil))).get .here
def coefficientsOf (q : M.Value polynomial) : M.Value coefficients :=
  (M.pure (.of opening.row.«poly.coefficients(domain scalar)») (.cons q .nil)).get .here
def msm (c : M.Value coefficients) (list : M.Value points) : M.Value first :=
  (M.pure (.of opening.row.«curve.msm(domain g1)») (.cons c (.cons list .nil))).get .here
def evaluate (q : M.Value polynomial) (z : M.Value scalar) : M.Value scalar :=
  (M.pure (.of opening.row.«poly.univariate_evaluate(domain scalar)»)
    (.cons q (.cons z .nil))).get .here
def quotient (q : M.Value polynomial) (z y : M.Value scalar) : M.Value polynomial :=
  (M.pure (.of opening.row.«poly.divide_opening(domain scalar)»)
    (.cons q (.cons z (.cons y .nil)))).get .here
def negate₁ (p : M.Value first) : M.Value first :=
  (M.pure (.of opening.row.«curve.neg(domain g1)») (.cons p .nil)).get .here
def negate₂ (p : M.Value second) : M.Value second :=
  (M.pure (.of opening.row.«curve.neg(domain g2)») (.cons p .nil)).get .here
def add₁ (p q : M.Value first) : M.Value first :=
  (M.pure (.of opening.row.«curve.add(domain g1)») (.cons p (.cons q .nil))).get .here
def add₂ (p q : M.Value second) : M.Value second :=
  (M.pure (.of opening.row.«curve.add(domain g2)») (.cons p (.cons q .nil))).get .here
def pairingCheck (a : M.Value first) (b : M.Value second) (c : M.Value first) (d : M.Value second) :
    Bool :=
  (M.pure (.of opening.row.«pairing.check(domain scalar)»)
    (.cons a (.cons b (.cons c (.cons d .nil))))).get .here

/-- The reference string for a secret: the first three powers times the generator. -/
def referenceString (secret : M.Value scalar) : M.Value points :=
  append M (append M (append M (empty M) (generator₁ M)) (scale₁ M (generator₁ M) secret))
    (scale₁ M (scale₁ M (generator₁ M) secret) secret)

/-- The verifier's decision on the key, commitment, point, evaluation and proof. -/
def accepts (key : M.Value second) (commitment : M.Value first) (point evaluation : M.Value scalar)
    (proof : M.Value first) : Bool :=
  pairingCheck M (add₁ M commitment (negate₁ M (scale₁ M (generator₁ M) evaluation))) (generator₂ M)
    proof (add₂ M key (negate₂ M (scale₂ M (generator₂ M) point)))

/-- The verifier alone receives the key, the commitment, the evaluation and the
proof, and draws the point. The operations of the setup and of the prover are
nothing for it. -/
theorem verifier_side :
    opening.opening.meaning M verifier (.cons () .nil) =
      .call (.receive ⟨0, 2⟩ second) fun key =>
      .call (.receive ⟨0, 3⟩ first) fun commitment =>
      .call (.draw ⟨0, 4⟩ uniform .nil) fun point =>
      .call (.receive ⟨0, 5⟩ scalar) fun evaluation =>
      .call (.receive ⟨0, 6⟩ first) fun proof =>
      .done (.cons point (.cons evaluation
        (.cons (accepts M key commitment point evaluation proof) .nil))) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  -- the setup: nothing but the key, which arrives
  refine (sideMeaning_step_done (sample_outside rfl)).trans ?_
  iterate 9 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  refine (sideMeaning_step_done (exchange_outside rfl rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun key => ?_)
  -- the prover's commitment arrives
  iterate 2 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun commitment => ?_)
  -- the point, then the evaluation and the proof
  refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun point => ?_)
  iterate 4 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun evaluation => ?_)
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun proof => ?_)
  -- the check
  iterate 9 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  exact sideMeaning_ret

/-- The setup and the verifier together sample the secret, send the reference string
to the prover, and keep the key exchange internal. -/
theorem setup_verifier_side :
    opening.opening.meaning M setupAndVerifier (.cons () .nil) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun secret =>
      .call (.send ⟨0, 1⟩ points (referenceString M secret)) fun _ =>
      .call (.receive ⟨0, 3⟩ first) fun commitment =>
      .call (.draw ⟨0, 4⟩ uniform .nil) fun point =>
      .call (.receive ⟨0, 5⟩ scalar) fun evaluation =>
      .call (.receive ⟨0, 6⟩ first) fun proof =>
      .done (.cons point (.cons evaluation (.cons
        (accepts M (scale₂ M (generator₂ M) secret) commitment point evaluation proof) .nil))) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  -- the setup samples the secret and computes the reference string and the key
  refine (sideMeaning_step_call (sample_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun secret => ?_)
  iterate 9 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  -- the reference string leaves the side; the key stays inside
  refine (sideMeaning_step_call (exchange_send rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun _ => ?_)
  refine (sideMeaning_step_done (exchange_internal rfl rfl)).trans ?_
  -- the prover commits
  iterate 2 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun commitment => ?_)
  -- the verifier draws the point; the prover opens
  refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun point => ?_)
  iterate 4 refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun evaluation => ?_)
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun proof => ?_)
  -- the verifier checks
  iterate 9 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  exact sideMeaning_ret

/-- Every role: the secret and the point are the only effects. -/
theorem every_role_side (q : M.Value polynomial) :
    opening.opening.meaning M everyRole (.cons q .nil) =
      .call (.sample ⟨0, 0⟩ uniform .nil) fun secret =>
      .call (.draw ⟨0, 4⟩ uniform .nil) fun point =>
      .done (.cons point (.cons (evaluate M q point) (.cons
        (accepts M (scale₂ M (generator₂ M) secret)
          (msm M (coefficientsOf M q) (referenceString M secret)) point (evaluate M q point)
          (msm M (coefficientsOf M (quotient M q point (evaluate M q point)))
            (referenceString M secret))) .nil))) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_call (sample_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun secret => ?_)
  iterate 9 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  iterate 2 refine (sideMeaning_step_done (exchange_internal rfl rfl)).trans ?_
  iterate 2 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_done (exchange_internal rfl rfl)).trans ?_
  refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun point => ?_)
  iterate 4 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  iterate 2 refine (sideMeaning_step_done (exchange_internal rfl rfl)).trans ?_
  iterate 9 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  exact sideMeaning_ret

theorem every_role_randomness (q : M.Value polynomial) :
    OnlyEffects Effect.random (opening.opening.meaning M everyRole (.cons q .nil)) := by
  rw [every_role_side]
  exact ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩

end

end Zkc.Tests.Core.Opening

/-- info: 'Zkc.Tests.Core.Opening.every_role_randomness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Opening.every_role_randomness

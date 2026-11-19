import Zkc.Formal.Written.PrimeFieldCharge
import Zkc.Frontend.Emit.Application
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Root
import Zkc.Tools.Formal.SumcheckCaller
import Zkc.Formal.Written.SumcheckRows

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Zkc.Formal.Written.RoundCharge
open Zkc.Frontend Zkc.Frontend.Written

variable {V : Zkc.Core.Vocabulary} {p : Zkc.Core.Typed V} {owner : Key}
    {state t residual : V.Ty} {prefixSize rounds : Nat} {events : Events t}

/-- Retain the successful source read and the independently checked operand of the bound.
The source lookup and semantic readback use the same definition in the admitted program. -/
structure IssuedCharge (s : Compile.State) (name : String)
    (linked : Linked p owner state t residual prefixSize rounds events) (degree order : Nat) where
  charge : DrawCharge
  written : drawCharge s p owner name = .ok charge
  binding : Matches charge linked degree order

def issueCharge (s : Compile.State) (name : String)
    (linked : Linked p owner state t residual prefixSize rounds events) (degree order : Nat) :
    Except String (IssuedCharge s name linked degree order) :=
  match written : drawCharge s p owner name with
  | .error why => .error why
  | .ok charge =>
    if binding : Matches charge linked degree order then .ok ⟨charge,written,binding⟩
    else .error s!"sites.{name}: source locations disagree or the written bound is too small for this reduction"

open Zkc.Formal.Interactive.Sumcheck Zkc.Formal.Written.SumcheckRows

structure ChargedSumcheck (c : AdmittedRoot) (n : Nat) (name : String) where
  sourceRelation : SourceTableSum
  selectedRelation : tableSumRelation? c = some sourceRelation
  extension : hasSourceExtension c = true
  keys : CallerKeys
  verifier : TableVerifier.Certified (sourceRows c.emission.bindings) (vectorRows c.emission.bindings)
    c.evidence.admitted.program ⟨c.id⟩ keys.reduction keys.evaluator n (sourceEvents c.emission.bindings)
  issued : IssuedCharge c.state name verifier.linked 1 Zkc.Vocabulary.Field.bls12381Fr.order

abbrev ChargedSumcheck.relation {c n name} (cert : ChargedSumcheck c n name) :=
  cert.sourceRelation.declaration

theorem ChargedSumcheck.selected {c n name} (cert : ChargedSumcheck c n name) :
    tableSumClaim? c = some cert.relation := by simp [tableSumClaim?, cert.selectedRelation]

def chargeSumcheck (c : AdmittedRoot) (n : Nat) (name : String) : Except String (ChargedSumcheck c n name) := do
  let some keys := sumcheckCallKeys c.emission ⟨c.id⟩ | throw "missing Sumcheck caller"
  let b := c.emission.bindings
  let rows := sourceRows b
  let some cert := TableVerifier.certify rows (vectorRows b) c.evidence.admitted.program ⟨c.id⟩
    keys.reduction keys.evaluator n (sourceEvents b) rows.evaluationReadback [rows.affineReadback, rows.encodedAffineReadback true false]
    | throw "uncertified Sumcheck verifier"
  match selected : tableSumRelation? c with
  | none => throw "expected the verifier's written sum relation on its public table and claim"
  | some relation =>
    if extension : hasSourceExtension c = true then
      return ⟨relation,selected,extension,keys,cert,← issueCharge c.state name cert.linked 1 Zkc.Vocabulary.Field.bls12381Fr.order⟩
    else throw "the selected reduction requires the extension of the verifier's public table"

section Layer
variable {c : AdmittedRoot} {hdr : ProtocolHeader c.emission.bindings.vocabulary}
    {root : Member c.evidence.admitted.program.headers.protocols hdr} {red site : Key}
    {hidden residual : c.emission.bindings.vocabulary.Ty} {k n : Nat} {args : List Name} {route : List OperationSite.Move}

/-- At a GKR layer, retain the source summand application as well as the closed draw charge.
The caller supplies its expected circuit, inputs, current layer and point as typed operands. -/
structure LayerCharge (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String) where
  caller : hdr.key = ⟨c.id⟩
  relation : c.emission.externalApplicationAt? c.state hdr.key site red [0,1] "p" "Zkc.Circuit.summand" = some summand
  issued : IssuedCharge c.state name call.linked 2 Zkc.Vocabulary.Field.bls12381Fr.order

private def selectLayer (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String) :
    Except String (LayerCharge call summand name) := do
  if caller : hdr.key = ⟨c.id⟩ then
    if relation : c.emission.externalApplicationAt? c.state hdr.key site red [0,1] "p" "Zkc.Circuit.summand" = some summand then
      return ⟨caller,relation,← issueCharge c.state name call.linked 2 Zkc.Vocabulary.Field.bls12381Fr.order⟩
    else throw "the layer call does not select the expected source summand"
  else throw "the layer call does not belong to this source root"

structure ChargedLayer (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String)
    extends LayerCharge call summand name where
  gate : GateMembers gateRow call.linked.entry.definitions call.linked.rounds

def chargeLayer (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String) :
    Except String (ChargedLayer call summand name) := do
  let selected ← selectLayer call summand name
  let some gate := checkGateMembers gateRow call.linked.entry.definitions
    (List.nodup_append.mp call.linked.entry.distinct).1 call.linked.rounds | throw "uncertified gate member at the selected call"
  return ⟨selected,gate⟩

/-- Each named gate primitive is verified against the executable operation at the
corresponding remaining depth of the source-selected reduction. -/
structure ChargedGateFamily (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String) (gateAt : Nat → Emit.PrimitiveName)
    extends LayerCharge call summand name where
  members : call.linked.rounds.AllMembersAt (fun d {_ _ _} ops => GateMember (gateAt d) call.linked.entry.definitions ops)

def chargeGateFamily (call : AtSite c.evidence.admitted.program root red site hidden (sourceRows c.emission.bindings).scalarTy
    residual k n (sourceEvents c.emission.bindings) args route) (summand : Emit.LocalApplication) (name : String) (gateAt : Nat → Emit.PrimitiveName) :
    Except String (ChargedGateFamily call summand name gateAt) := do
  let selected ← selectLayer call summand name
  let some ⟨members⟩ := checkGateFamily gateAt call.linked.entry.definitions
    (List.nodup_append.mp call.linked.entry.distinct).1 call.linked.rounds | throw "uncertified gate member at the selected depth"
  return ⟨selected,members⟩

open Zkc.Formal.Written Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess OracleComp
local notation "rows" => sourceRows c.emission.bindings
local notation "ev" => sourceEvents c.emission.bindings

/-- The selected layer's primitive, member implementations, source summand and ceiling
all belong to the same call. The model gives the interpretation of the selected summand. -/
theorem ChargedLayer.bound {loopKey : Key} {before layers inside width : Nat} {σ : Type}
    {call : AtSite c.evidence.admitted.program root red site hidden (rows).scalarTy residual k n ev args
      (loopRoute before loopKey layers inside)} {summand : Emit.LocalApplication} {name : String}
    (certificate : ChargedLayer call summand name) (M : Model c.emission.bindings.vocabulary)
    [Field ((rows).F M)] [DecidableEq ((rows).F M)] (math : (rows).Arithmetic M)
    (model : Gate.Evaluation rows (.inr gateRow) certificate.gate.bound M)
    (equality : ScalarEquality.Law (rows).scalarTy (ev).equal (ev).equalType M)
    (i : Fin layers) (interpret : Emit.LocalApplication → Claims ((rows).F M))
    (honest : ∀ d : Fin n, (interpret summand).State (d.val+1) → Quadratic ((rows).F M))
    (ends : ∀ d x, (interpret summand).value (d.val+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, (interpret summand).value d.val ((interpret summand).restrict d.val x r) = (honest d x).eval r)
    (size : width+1 = Zkc.Vocabulary.Field.bls12381Fr.order)
    (alphabet : Fin (width+1) → (rows).F M) (distinct : (List.ofFn alphabet).Nodup)
    (advance : Occurrence → (rows).F M → σ → σ) (other : Slots (RSig M) σ)
    (path : List Zkc.Core.Frame) (s : σ) (state : RV M 1 ⟨hidden,[0]⟩) (point : List ((rows).F M)) (claim : (rows).F M)
    (x : (interpret summand).State n) (wrong : claim ≠ (interpret summand).value n x) :
    prEvent (observed (fun vs _ => correctReturn M (interpret summand) x point.length vs) <$> run
      (service (RoundService.withChallenge M ev alphabet advance other))
      (roleOp M 1 (Defs.fnTable M call.callerEntry.definitions) (Defs.rTable M call.callerEntry.definitions)
        site call.linked.application (path ++ [.iteration loopKey i.val]) (publicArgs M state point claim)) s) ≤
      total certificate.issued.charge := by
  exact RoundCharge.gate call certificate.gate.members M math model equality i (interpret summand) honest ends restricted
    alphabet distinct advance other _ (size.symm ▸ certificate.issued.binding) path s state point claim x wrong PolynomialBounds.gates

theorem ChargedGateFamily.bound {loopKey : Key} {before layers inside width : Nat} {σ : Type}
    {call : AtSite c.evidence.admitted.program root red site hidden (rows).scalarTy residual k n ev args
      (loopRoute before loopKey layers inside)} {summand : Emit.LocalApplication} {name : String}
    {gateAt : Nat → Emit.PrimitiveName} (certificate : ChargedGateFamily call summand name gateAt) (M : Model c.emission.bindings.vocabulary)
    [Field ((rows).F M)] [DecidableEq ((rows).F M)] (math : (rows).Arithmetic M)
    (model : ∀ d : Fin n, ∀ sig : c.emission.bindings.vocabulary.row (.inr (gateAt d.val)) = some (Gate.signature rows),
      Gate.Evaluation rows (.inr (gateAt d.val)) sig M)
    (equality : ScalarEquality.Law (rows).scalarTy (ev).equal (ev).equalType M)
    (i : Fin layers) (interpret : Emit.LocalApplication → Claims ((rows).F M))
    (honest : ∀ d : Fin n, (interpret summand).State (d.val+1) → Quadratic ((rows).F M))
    (ends : ∀ d x, (interpret summand).value (d.val+1) x = (honest d x).boundary)
    (restricted : ∀ d x r, (interpret summand).value d.val ((interpret summand).restrict d.val x r) = (honest d x).eval r)
    (size : width+1 = Zkc.Vocabulary.Field.bls12381Fr.order)
    (alphabet : Fin (width+1) → (rows).F M) (distinct : (List.ofFn alphabet).Nodup)
    (advance : Occurrence → (rows).F M → σ → σ) (other : Slots (RSig M) σ)
    (path : List Zkc.Core.Frame) (s : σ) (state : RV M 1 ⟨hidden,[0]⟩) (point : List ((rows).F M)) (claim : (rows).F M)
    (x : (interpret summand).State n) (wrong : claim ≠ (interpret summand).value n x) :
    prEvent (observed (fun vs _ => correctReturn M (interpret summand) x point.length vs) <$> run
      (service (RoundService.withChallenge M ev alphabet advance other))
      (roleOp M 1 (Defs.fnTable M call.callerEntry.definitions) (Defs.rTable M call.callerEntry.definitions)
        site call.linked.application (path ++ [.iteration loopKey i.val]) (publicArgs M state point claim)) s) ≤
      total certificate.issued.charge := by
  apply RoundCharge.gateAtDepth call M equality i (interpret summand) alphabet _ advance other _
    (size.symm ▸ certificate.issued.binding) path s state point claim x wrong
  exact call.linked.rounds.interpretMembersAt _ certificate.members M _ (interpret summand) (List.ofFn alphabet) 2
    (fun d {_ _ _} _ member => Gate.Laws.interpretOn rows member.law M math (model d member.bound)
      (interpret summand) (fun _ : Unit => d.val) (fun _ => honest d) (fun _ => ends d)
      (fun _ => restricted d) _ distinct PolynomialBounds.gates)

end Layer

open Zkc.Formal.Written Zkc.Formal.FiniteService
open scoped Zkc.Formal.Written.RoundCharge

private theorem emptyBindings (b : Emit.Bindings) (plain : b.rows = []) : b = {} := by
  cases b with
  | mk rows _ => cases plain; rfl

/-- Transport both dependent witnesses along the equality of vocabularies. The program in
the result is the same admitted program under the standard interpretation. -/
private def standardReadback {b : Emit.Bindings} {p : Zkc.Core.Typed b.vocabulary}
    {root red eval : Key} {n : Nat} (cert : TableVerifier.Certified (sourceRows b) (vectorRows b) p root red eval n (sourceEvents b))
    {charge : DrawCharge} (binding : Matches charge cert.linked 1 Zkc.Vocabulary.Field.bls12381Fr.order)
    (same : b = {}) :
    (checked : TableVerifier.Certified ArithmeticModel.scalarRows ArithmeticModel.vectors
      (cast (congrArg (fun vocabulary : Emit.Bindings => Zkc.Core.Typed vocabulary.vocabulary) same) p)
      root red eval n ArithmeticModel.events) × PLift (Matches charge checked.linked 1 Zkc.Vocabulary.Field.bls12381Fr.order) := by
  subst b
  exact ⟨cert,⟨binding⟩⟩

def ChargedSumcheck.standardVerifier {c : AdmittedRoot} {n : Nat} {name : String}
    (checked : ChargedSumcheck c n name) (plain : c.emission.bindings.rows = []) :=
  standardReadback checked.verifier checked.issued.binding (emptyBindings _ plain)

abbrev Scalar := ZMod Zkc.Vocabulary.Field.bls12381Fr.order
abbrev scalarModel := ArithmeticModel.model Scalar Scalar

/-- The external probability of accepting a false claim at the root that owns this
certificate, using the source field and an answering service for its uniform challenge. -/
theorem ChargedSumcheck.primeBound {c : AdmittedRoot} {n : Nat} {name : String}
    (checked : ChargedSumcheck c n name) (plain : c.emission.bindings.rows = [])
    {σ : Type} (advance : Occurrence → Scalar → σ → σ) (other : Slots (RSig scalarModel) σ)
    (path : List Zkc.Core.Frame) (s : σ) (x : Cube Scalar n) (claim : Scalar) (wrong : claim ≠ Cube.sum n x) :
    let cert := (checked.standardVerifier plain).1
    let alphabet : Fin (Zkc.Vocabulary.Field.bls12381Fr.order - 1 + 1) → Scalar := ZMod.finEquiv _
    prEvent (observed (fun _ _ => true) <$> Zkc.Formal.ProbabilisticProcess.run
      (service (RoundService.withChallenge scalarModel ArithmeticModel.events alphabet advance other))
      (roleMeaning scalarModel _ cert.root 1 path (TableVerifier.args scalarModel (Cube.flatten n x) claim)) s) ≤
      total checked.issued.charge := by
  let readback := checked.standardVerifier plain
  exact @primeSumcheck (Zkc.Vocabulary.Field.bls12381Fr.order - 1) n
    ⟨scalarOrder_prime⟩ _ _ _ _ readback.1 σ advance other checked.issued.charge readback.2.down path s x claim wrong

/-- A failed equality in the recognized source body gives the false public sum
required by the admitted verifier theorem, in either source operand order. -/
theorem ChargedSumcheck.falseSum {c n name} (checked : ChargedSumcheck c n name)
    {F : Type} [Lean.Grind.Field F] (x : Cube F n) (claim : F)
    (failed : tableMeaning checked.sourceRelation.table checked.sourceRelation.target
      checked.sourceRelation.body (Cube.flatten n x) claim ≠ some True) : claim ≠ Cube.sum n x := by
  rw [checked.sourceRelation.meaning, Cube.sum_flatten] at failed
  intro eq
  exact failed (by simp [eq])

/-- The source-facing probability bound uses the operand order read from the written relation. -/
theorem ChargedSumcheck.primeBoundOfRelation {c : AdmittedRoot} {n : Nat} {name : String}
    (checked : ChargedSumcheck c n name) (plain : c.emission.bindings.rows = [])
    {σ : Type} (advance : Occurrence → Scalar → σ → σ) (other : Slots (RSig scalarModel) σ)
    (path : List Zkc.Core.Frame) (s : σ) (x : Cube Scalar n) (claim : Scalar)
    (failed : tableMeaning checked.sourceRelation.table checked.sourceRelation.target
      checked.sourceRelation.body (Cube.flatten n x) claim ≠ some True) :
    let cert := (checked.standardVerifier plain).1
    let alphabet : Fin (Zkc.Vocabulary.Field.bls12381Fr.order - 1 + 1) → Scalar := ZMod.finEquiv _
    prEvent (observed (fun _ _ => true) <$> Zkc.Formal.ProbabilisticProcess.run
      (service (RoundService.withChallenge scalarModel ArithmeticModel.events alphabet advance other))
      (roleMeaning scalarModel _ cert.root 1 path (TableVerifier.args scalarModel (Cube.flatten n x) claim)) s) ≤
      total checked.issued.charge :=
  checked.primeBound plain advance other path s x claim (checked.falseSum x claim failed)

end Zkc.Tools.Formal

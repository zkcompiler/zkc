module

public import Init.Data.List.Sort.Lemmas
public import Zkc.Source.Structured.ComponentChecking
public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.RetainedClause
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

/-! An admitted pair repacking and terminal check share the request's meaning
with canonical clause reading. Formula and opaque routes use identical helpers.
The claim deliberately leaves the two mixed Boolean pairs in a promise gap. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

noncomputable section
namespace Tests.ComponentMeanings
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations

def digest := "sha256:" ++ String.ofList (List.replicate 64 '0')
abbrev pairTypes : List Ty := [.boolean, .boolean]
def formulaDeclaration : Relation :=
  ⟨"All", .publicDef, "zkc.language.formula/0", "all", "0", pairTypes, [.boolean],
    ["statement", "statement"], some "all", []⟩
def opaqueDeclaration : Relation :=
  { formulaDeclaration with
    kind := "example.boolean-pair/0"
    key := "all"
    revision := "1"
    formula := none
    staticArguments := [.index, .natural "2"] }
def application (direction : ContractDirection) : RelationApplication :=
  ⟨"All", [⟨direction, 0, "V"⟩, ⟨direction, 1, "V"⟩]⟩
def pending : OriginTerm := .nominal .record "PendingPair" []
def ports : List SourcePort := [⟨"pair", pending, ["V"], 0, 2⟩]
def plainInputs : List SourcePort :=
  [⟨"first", .boolean, ["V"], 0, 1⟩, ⟨"second", .boolean, ["V"], 1, 1⟩]
def plainOutput : List SourcePort := [⟨"accepted", .boolean, ["V"], 0, 1⟩]
def original (declaration : Relation) : Snapshot :=
  ⟨digest, "main", [], [declaration], [],
    [.function ⟨"swap", .math, .privateDef, pairTypes, pairTypes, none, [], none,
      .block [] (.ret [1, 0])⟩,
     .function ⟨"all", .math, .privateDef, pairTypes, [.boolean], none, [], none,
      .block [.instruction .booleanAnd [0, 1] [.boolean] [] ""] (.ret [0])⟩,
     .function ⟨"finish", .local, .privateDef, pairTypes, [.boolean], none, [], some (.local "finish" []),
      .block [.instruction .branch [0] [] [
        .region [] [] (.block [] (.yield [])),
        .region [] [] (.block [] (.stop .reject "reject"))] "guard"] (.ret [1])⟩,
     .function ⟨"decide", .protocol, .publicDef, pairTypes, [.boolean],
      some ⟨["V"], [["V"], ["V"]], [["V"]]⟩, [], some (.protocol ⟨"decide", []⟩),
      .block [.instruction (.localCall "finish" "V") [0, 1] [.boolean] [] "finish_call"] (.ret [0])⟩,
     .function ⟨"main", .protocol, .publicDef, pairTypes, [.boolean],
      some ⟨["V"], [["V"], ["V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [0])⟩,
     .function ⟨"repack", .protocol, .publicDef, pairTypes, pairTypes,
      some ⟨["V"], [["V"], ["V"]], [["V"], ["V"]]⟩, [], some (.protocol ⟨"repack", []⟩),
      .block [.instruction (.call "swap") [0, 1] pairTypes [] ""] (.ret [0, 1])⟩],
    [⟨"repack", [⟨.continuation, "next", application .input, some (application .output), none⟩]⟩,
     ⟨"decide", [⟨.target, "truth", application .input, none, some ⟨.output, 0, "V"⟩⟩]⟩,
     ⟨"main", []⟩], blsRows,
    ⟨[⟨pending, "linear", true, [("first", .boolean), ("second", .boolean)]⟩],
      [⟨"repack", ports, ports⟩, ⟨"decide", ports, plainOutput⟩,
       ⟨"main", plainInputs, plainOutput⟩]⟩⟩

abbrev swapHelper : Helper := ⟨"swap", .math, pairTypes, pairTypes⟩
def swapBody : Region dialect pairTypes pairTypes :=
  .ret (.cons (.there .here) (.cons .here .nil))
abbrev allHelper : Helper := ⟨"all", .math, pairTypes, [.boolean]⟩
def allBody : Region dialect pairTypes [.boolean] :=
  .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))
abbrev finishHelper : Helper := ⟨"finish", .local, pairTypes, [.boolean]⟩
def finishBody : Region dialect pairTypes [.boolean] :=
  .letOp (.mark "guard") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil)
    (.cons (.ret .nil) (.cons (.letOp (.mark "reject") .nil .nil (.stop .reject)) .nil))
    (.ret (.cons (.there .here) .nil))
def repackSignature : ProtocolSignature :=
  ⟨"repack", ["V"], pairTypes, pairTypes, [[0], [0]], [[0], [0]]⟩
def repackBody : Region protocolDialect pairTypes pairTypes :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke swapHelper) rfl) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here (.cons (.there .here) .nil)))
def decideSignature : ProtocolSignature :=
  ⟨"decide", ["V"], pairTypes, [.boolean], [[0], [0]], [[0]]⟩
def decideBody : Region protocolDialect pairTypes [.boolean] :=
  .letOp (.mark "finish_call") .nil .nil <|
  .letOp (.localCall finishHelper rfl 0 "finish_call") (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here .nil))
def mainSignature : ProtocolSignature :=
  ⟨"main", ["V"], pairTypes, [.boolean], [[0], [0]], [[0]]⟩
def mainBody : Region protocolDialect pairTypes [.boolean] := .ret (.cons .here .nil)

namespace FormulaUnit
structured_views (original formulaDeclaration)
  helpers [swap := (swapHelper, swapBody), all := (allHelper, allBody), finish := (finishHelper, finishBody)]
  protocols [repack := repack, decide := decide, main := main]
end FormulaUnit
namespace OpaqueUnit
structured_views (original opaqueDeclaration)
  helpers [swap := (swapHelper, swapBody), all := (allHelper, allBody), finish := (finishHelper, finishBody)]
  protocols [repack := repack, decide := decide, main := main]
end OpaqueUnit

def model := ringModel Int Int
def instanceMeaning : OpaqueInstance model.Value :=
  ⟨pairTypes, [.boolean], ["statement", "statement"], fun values =>
    values.get .here = true ∧ values.get (.there .here) = true⟩
def family : OpaqueFamily model.Value :=
  ⟨opaqueDeclaration.opaqueIdentity.family, fun arguments =>
    if arguments = opaqueDeclaration.staticArguments then some instanceMeaning else none⟩
def registry : OpaqueRegistry model.Value := ⟨[family], by decide +kernel⟩
def environment : RelationEnvironmentOn OpaqueUnit.imported model.toCarriers :=
  RegisteredRelations.ofChecked registry (by decide +kernel)
def formulaRelation : RelationBinding (original formulaDeclaration) (application .input) := by bind_contract
def opaqueRelation : RelationBinding (original opaqueDeclaration) (application .input) := by bind_contract
def formula : FormulaBinding FormulaUnit.imported formulaRelation := by bind_contract
def formulaMeaning : RelationMeaning FormulaUnit.imported formulaRelation model.Value registry := .formula formula
def opaqueBinding : OpaqueRegistry.Binding registry opaqueRelation.declaration :=
  (registry.resolve _).get (by decide +kernel)
def opaqueMeaning : RelationMeaning OpaqueUnit.imported opaqueRelation model.Value registry := .opaque opaqueBinding

def claim : ClaimRelation (Bool × Bool) Unit where
  Holds statement _ := statement.1 = true ∧ statement.2 = true
  No statement := statement.1 = false ∧ statement.2 = false
  no_excludes := by rintro _ _ ⟨no, _⟩ ⟨yes, _⟩; exact Bool.false_ne_true (no.symm.trans yes)
def encode (statement : Bool × Bool) (_ : Unit) : Values model.Value pairTypes :=
  .cons statement.1 (.cons statement.2 .nil)
def readback (values : Values model.Value pairTypes) : Option (Bool × Bool) :=
  some (values.get .here, values.get (.there .here))
def swapMap (values : Values model.Value pairTypes) : Values model.Value pairTypes :=
  .cons (values.get (.there .here)) (.cons (values.get .here) .nil)

def wire : ComponentExport.Export :=
  ⟨[], [⟨"decide", .output 0 0, .terminal,
    [.terminal (.localCall "finish" "V") [0] 0 "V" [.input 0 "V", .input 1 "V"]]⟩,
    ⟨"repack", .residual 0, .pure,
    [.pure (.call "swap") [0] 0 "V" [.input 0 "V", .input 1 "V"],
     .pure (.call "swap") [0] 1 "V" [.input 0 "V", .input 1 "V"]]⟩]⟩
theorem sorted_protocols (declaration : Relation) :
    (original declaration).protocolFunctions.mergeSort (fun first second => first.name ≤ second.name) =
      (original declaration).protocolFunctions := by
  apply List.mergeSort_of_pairwise
  change List.Pairwise (fun first second : Function => decide (first.name ≤ second.name) = true)
    (original formulaDeclaration).protocolFunctions
  decide +kernel

theorem derived (declaration : Relation) :
    ComponentRoutes.derive (original declaration) = .ok ⟨wire.seams, [], 12⟩ := by
  simp only [ComponentRoutes.derive]
  rw [sorted_protocols]
  kernel_rfl

def formulaAssociated : ComponentExport.Associated (original formulaDeclaration) wire :=
  ⟨_, derived _, rfl, by unfold ComponentExport.check; rw [derived]; kernel_rfl⟩
def opaqueAssociated : ComponentExport.Associated (original opaqueDeclaration) wire :=
  ⟨_, derived _, rfl, by unfold ComponentExport.check; rw [derived]; kernel_rfl⟩

-- The derived order is decide's terminal followed by repack's pure residual.
def formulaPure : PureSeamBinding (imported := FormulaUnit.imported) formulaAssociated ⟨1, by decide +kernel⟩ :=
  ⟨⟨0, by decide⟩, [0], 0, "V", .call "swap", .math rfl, [.input 0 "V", .input 1 "V"], by simp [wire, SeamRoute.subroutes]⟩
def opaquePure : PureSeamBinding (imported := OpaqueUnit.imported) opaqueAssociated ⟨1, by decide +kernel⟩ :=
  ⟨⟨0, by decide⟩, [0], 0, "V", .call "swap", .math rfl, [.input 0 "V", .input 1 "V"], by simp [wire, SeamRoute.subroutes]⟩
def formulaTerminal : TerminalSeamBinding (imported := FormulaUnit.imported) formulaAssociated ⟨0, by decide +kernel⟩ :=
  ⟨⟨2, by decide⟩, [0], 0, "V", .localCall "finish" "V", .local rfl, [.input 0 "V", .input 1 "V"], .here, rfl,
    rfl, ⟨0, 0, rfl⟩, ⟨_, by simp [wire], .here⟩, by simp [wire, SeamRoute.subroutes]⟩
def opaqueTerminal : TerminalSeamBinding (imported := OpaqueUnit.imported) opaqueAssociated ⟨0, by decide +kernel⟩ :=
  ⟨⟨2, by decide⟩, [0], 0, "V", .localCall "finish" "V", .local rfl, [.input 0 "V", .input 1 "V"], .here, rfl,
    rfl, ⟨0, 0, rfl⟩, ⟨_, by simp [wire], .here⟩, by simp [wire, SeamRoute.subroutes]⟩

theorem formula_realizes : formulaMeaning.RealizesClaim claim rfl encode (fun _ _ => True) := by
  intro statement witness
  cases witness
  rcases statement with ⟨first, second⟩
  have actual : formula.invokeRelationOn model (encode (first, second) ()) =
      .done (.cons (first && second) .nil) := by kernel_rfl
  change (first = true ∧ second = true) ↔ True ∧ formula.invokeRelationOn model _ = _
  rw [actual]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨trivial, rfl⟩
  · rintro ⟨_, completed⟩
    have booleans := congrArg (fun values : Values model.Value [.boolean] => values.get .here)
      (PIR.Process.done.inj completed)
    exact Bool.and_eq_true_iff.mp booleans
theorem opaque_realizes : opaqueMeaning.RealizesClaim claim rfl encode (fun _ _ => True) := by
  intro statement witness
  exact ⟨fun truth => ⟨trivial, truth⟩, fun truth => truth.2⟩

theorem swap_yes (statement : Bool × Bool) : claim.token.Yes statement ↔ claim.token.Yes statement.swap := by
  constructor <;> rintro ⟨witness, first, second⟩ <;> exact ⟨witness, second, first⟩
theorem swap_no : claim.SoundLink claim Prod.swap := fun _ no => ⟨no.2, no.1⟩

theorem formulaPureLaw : PureSeamLaw formulaPure formulaRelation formulaRelation claim claim Prod.swap (fun _ => True)
    swapMap readback readback formulaMeaning formulaMeaning rfl rfl encode encode
    (fun _ _ => True) (fun _ _ => True) where
  sourceRealizes := formula_realizes
  targetRealizes := formula_realizes
  total arguments _ := by cases arguments with | cons first rest => cases rest with | cons second rest => cases rest; rfl
  defined _ _ := ⟨_, rfl⟩
  readback _ _ _ same := by cases same; rfl
  yes := swap_yes
  no := swap_no

theorem opaquePureLaw : PureSeamLaw opaquePure opaqueRelation opaqueRelation claim claim Prod.swap (fun _ => True)
    swapMap readback readback opaqueMeaning opaqueMeaning rfl rfl encode encode
    (fun _ _ => True) (fun _ _ => True) where
  sourceRealizes := opaque_realizes
  targetRealizes := opaque_realizes
  total arguments _ := by cases arguments with | cons first rest => cases rest with | cons second rest => cases rest; rfl
  defined _ _ := ⟨_, rfl⟩
  readback _ _ _ same := by cases same; rfl
  yes := swap_yes
  no := swap_no

/-- A representation may decode only the equal pairs. Both affirmative and
negative statements remain represented; the promise-gap pairs do not decode. -/
abbrev pairDomain (values : Values model.Value pairTypes) : Prop :=
  values.get .here = values.get (.there .here)

def partialReadback (values : Values model.Value pairTypes) : Option (Bool × Bool) :=
  if pairDomain values then readback values else none

theorem partialReadback_of_domain (values : Values model.Value pairTypes) (inside : pairDomain values) :
    partialReadback values = readback values := ite_eq_left inside

theorem scopedPureLaw : PureSeamLaw opaquePure opaqueRelation opaqueRelation claim claim Prod.swap
    pairDomain swapMap partialReadback partialReadback opaqueMeaning opaqueMeaning rfl rfl encode encode
    (fun _ _ => True) (fun _ _ => True) where
  sourceRealizes := opaque_realizes
  targetRealizes := opaque_realizes
  total arguments _ := opaquePureLaw.total arguments trivial
  defined arguments inside := ⟨_, partialReadback_of_domain arguments inside⟩
  readback arguments statement inside same := by
    have next : pairDomain (swapMap arguments) := inside.symm
    rw [partialReadback_of_domain arguments inside] at same
    rw [partialReadback_of_domain (swapMap arguments) next]
    exact opaquePureLaw.readback arguments statement trivial same
  yes := swap_yes
  no := swap_no

example : pairDomain (encode (true, true) ()) := rfl
example : pairDomain (encode (false, false) ()) := rfl
example : partialReadback (encode (true, false) ()) = none := rfl

theorem missing_operational_scope_refused : ¬ pairDomain (encode (true, false) ()) :=
  by decide

theorem scoped_no_transport :
    ReadbackHolds claim.No (partialReadback (swapMap (encode (false, false) ()))) :=
  ⟨(false, false), rfl, scopedPureLaw.no (false, false) ⟨rfl, rfl⟩⟩

/-- The same installed map can be implemented by a sealed Local helper. Its
actual guard rejects inputs outside the representation domain. -/
def guardedSwapBody : Region dialect pairTypes pairTypes :=
  .letOp (.mark "shape") .nil .nil <|
  .letOp (.branch [.boolean] []) (.cons .here (.cons (.there .here) .nil))
    (.cons
      (.letOp (.mark "shape_true") .nil .nil <|
        .letOp (.branch [] []) (.cons .here .nil)
          (.cons (.ret .nil)
            (.cons (.letOp (.mark "shape_reject_true") .nil .nil (.stop .reject)) .nil))
          (.ret .nil))
      (.cons
        (.letOp (.mark "shape_false") .nil .nil <|
          .letOp (.branch [] []) (.cons .here .nil)
            (.cons (.letOp (.mark "shape_reject_false") .nil .nil (.stop .reject))
              (.cons (.ret .nil) .nil))
            (.ret .nil)) .nil))
    (.ret (.cons (.there .here) (.cons .here .nil)))

abbrev guardedSwapHelper : Helper := ⟨"swap", .local, pairTypes, pairTypes⟩

def guardedRepackBody : Region protocolDialect pairTypes pairTypes :=
  .letOp (.mark "swap_call") .nil .nil <|
  .letOp (.localCall guardedSwapHelper rfl 0 "swap_call")
    (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (.cons .here (.cons (.there .here) .nil)))

def guardedOriginal : Snapshot :=
  { original opaqueDeclaration with definitions :=
    (original opaqueDeclaration).definitions.map fun
      | .function helper =>
        if helper.name = "swap" then .function { helper with
          kind := .local, origin := some (.local "swap" []),
          body := .block [
            .instruction .branch [0, 1] [] [
              .region [.boolean] [] (.block [
                .instruction .branch [0] [] [
                  .region [] [] (.block [] (.yield [])),
                  .region [] [] (.block [] (.stop .reject "shape_reject_true"))] "shape_true"] (.yield [])),
              .region [.boolean] [] (.block [
                .instruction .branch [0] [] [
                  .region [] [] (.block [] (.stop .reject "shape_reject_false")),
                  .region [] [] (.block [] (.yield []))] "shape_false"] (.yield []))] "shape"] (.ret [1, 0]) }
        else if helper.name = "repack" then .function { helper with
          body := .block [.instruction (.localCall "swap" "V") [0, 1] pairTypes [] "swap_call"] (.ret [0, 1]) }
        else .function helper
      | other => other }

namespace GuardedUnit
abbrev repackBody := guardedRepackBody
structured_views guardedOriginal
  helpers [swap := (guardedSwapHelper, guardedSwapBody), all := (allHelper, allBody),
    finish := (finishHelper, finishBody)]
  protocols [repack := repack, decide := decide, main := main]
end GuardedUnit

def guardedWire : ComponentExport.Export :=
  { wire with seams := wire.seams.map fun row =>
    if row.caller = "repack" then { row with routes := [
      .pure (.localCall "swap" "V") [0] 0 "V" [.input 0 "V", .input 1 "V"],
      .pure (.localCall "swap" "V") [0] 1 "V" [.input 0 "V", .input 1 "V"]] }
    else row }

theorem guarded_sorted :
    guardedOriginal.protocolFunctions.mergeSort (fun first second => first.name ≤ second.name) =
      guardedOriginal.protocolFunctions := by
  apply List.mergeSort_of_pairwise
  decide +kernel

theorem guarded_derived :
    ComponentRoutes.derive guardedOriginal = .ok ⟨guardedWire.seams, [], 15⟩ := by
  simp only [ComponentRoutes.derive]
  rw [guarded_sorted]
  kernel_rfl

def guardedAssociated : ComponentExport.Associated guardedOriginal guardedWire :=
  ⟨_, guarded_derived, rfl, by unfold ComponentExport.check; rw [guarded_derived]; kernel_rfl⟩
def guardedPure : PureSeamBinding (imported := GuardedUnit.imported) guardedAssociated ⟨1, by decide⟩ :=
  ⟨⟨0, by decide⟩, [0], 0, "V", .localCall "swap" "V", .local rfl,
    [.input 0 "V", .input 1 "V"], by simp [guardedWire, wire, SeamRoute.subroutes]⟩
def guardedRelation : RelationBinding guardedOriginal (application .input) := by bind_contract
def guardedMeaning : RelationMeaning GuardedUnit.imported guardedRelation model.Value registry :=
  .opaque ((registry.resolve _).get (by decide +kernel))

theorem guardedPureLaw : PureSeamLaw guardedPure guardedRelation guardedRelation claim claim Prod.swap
    pairDomain swapMap partialReadback partialReadback guardedMeaning guardedMeaning rfl rfl encode encode
    (fun _ _ => True) (fun _ _ => True) where
  sourceRealizes := opaque_realizes
  targetRealizes := opaque_realizes
  total arguments inside := by
    cases arguments with
    | cons first rest => cases rest with
      | cons second rest =>
        cases rest
        change first = second at inside
        cases inside
        cases first <;> kernel_rfl
  defined := scopedPureLaw.defined
  readback := scopedPureLaw.readback
  yes := swap_yes
  no := swap_no

theorem guarded_helper_stops_outside_scope :
    invoke (closedMeaningsOn model GuardedUnit.imported.program.payload.definitions)
      guardedSwapHelper (encode (true, false) ()) = .halt .reject := by kernel_rfl

theorem formulaTerminalLaw : TerminalSeamLaw formulaTerminal formulaRelation claim (fun _ => True)
    readback formulaMeaning rfl encode (fun _ _ => True) where
  realizes := formula_realizes
  defined _ _ := ⟨_, rfl⟩
  adequate arguments results _ returned accepted := by
    change Values model.Value pairTypes at arguments
    obtain ⟨first, second, rfl⟩ : ∃ first second, arguments = .cons first (.cons second .nil) := by
      cases arguments with | cons first rest => cases rest with | cons second rest => cases rest; exact ⟨_, _, rfl⟩
    cases first with
    | false => cases returned
    | true =>
      change PIR.Process.done (Values.cons second .nil) = .done results at returned
      cases returned
      exact ⟨(true, second), rfl, (), rfl, accepted⟩

theorem opaqueTerminalLaw : TerminalSeamLaw opaqueTerminal opaqueRelation claim (fun _ => True)
    readback opaqueMeaning rfl encode (fun _ _ => True) where
  realizes := opaque_realizes
  defined _ _ := ⟨_, rfl⟩
  adequate arguments results _ returned accepted := by
    change Values model.Value pairTypes at arguments
    obtain ⟨first, second, rfl⟩ : ∃ first second, arguments = .cons first (.cons second .nil) := by
      cases arguments with | cons first rest => cases rest with | cons second rest => cases rest; exact ⟨_, _, rfl⟩
    cases first with
    | false => cases returned
    | true =>
      change PIR.Process.done (Values.cons second .nil) = .done results at returned
      cases returned
      exact ⟨(true, second), rfl, (), rfl, accepted⟩

def formulaOwner : ContractBinding FormulaUnit.imported := ContractBinding.ofName _ "decide"
def opaqueOwner : ContractBinding OpaqueUnit.imported := ContractBinding.ofName _ "decide"
def formulaClause : RetainedClause FormulaUnit.imported formulaOwner (application .input) model.Value registry :=
  ⟨by bind_contract, rfl, formulaMeaning⟩
def opaqueClause : RetainedClause OpaqueUnit.imported opaqueOwner (application .input) model.Value registry :=
  ⟨by bind_contract, rfl, opaqueMeaning⟩
def boundary (statement : Bool × Bool) : BoundaryValuation model.Value pairTypes [.boolean] :=
  ⟨fun _ => .cons (some statement.1) (.cons (some statement.2) .nil), fun _ => .cons none .nil⟩
def assignments {snapshot : Snapshot} {imported : Imported snapshot} (owner : ContractBinding imported) :
    LogicalAssignments model.Value owner ⟨0, []⟩ := ⟨fun _ _ => none, fun _ _ => none⟩

theorem formula_canonical_seam_agree (statement : Bool × Bool) :
    formulaClause.Holds {} (boundary statement) (assignments formulaOwner) ↔
      formulaMeaning.HoldsOn rfl (encode statement ()) :=
  formulaClause.holds_iff_of_read _ _ _ _ rfl

theorem opaque_canonical_seam_agree (statement : Bool × Bool) :
    opaqueClause.Holds {} (boundary statement) (assignments opaqueOwner) ↔
      opaqueMeaning.HoldsOn rfl (encode statement ()) :=
  opaqueClause.holds_iff_of_read _ _ _ _ rfl

theorem opaque_logical_agree (statement : Bool × Bool) :
    opaqueMeaning.HoldsOn rfl (encode statement ()) ↔
      Logical.relationMeaningOn model environment opaqueRelation.index (encode statement ()) :=
  opaqueMeaning.holds_iff_logical environment rfl _

theorem opaque_uniform_logical_agree (statement : Bool × Bool) :
    opaqueMeaning.HoldsOn rfl (encode statement ()) ↔
      Logical.relationMeaning (imported := OpaqueUnit.imported) (F := Int) (G := Int) environment opaqueRelation.index
        (encode statement ()) :=
  opaqueMeaning.holds_iff_uniform_logical environment rfl _

theorem terminal_rejects :
    invoke (closedMeaningsOn model OpaqueUnit.imported.program.payload.definitions)
      (OpaqueUnit.imported.program.payload.definitions.get opaqueTerminal.helperIndex).helper
      (encode (false, true) ()) = .halt .reject := by kernel_rfl

theorem terminal_returns_false :
    invoke (closedMeaningsOn model OpaqueUnit.imported.program.payload.definitions)
      (OpaqueUnit.imported.program.payload.definitions.get opaqueTerminal.helperIndex).helper
      (encode (true, false) ()) = .done (.cons false .nil) := by kernel_rfl

-- Yes agreement cannot turn either mixed pair into a No statement.
theorem promise_gap : ¬ claim.token.Yes (true, false) ∧ ¬ claim.No (true, false) := by
  constructor
  · rintro ⟨_, _, impossible⟩; exact Bool.false_ne_true impossible
  · rintro ⟨impossible, _⟩; exact Bool.noConfusion impossible

theorem sourceNo (statement : Bool × Bool) (no : claim.No statement) :
    ¬ opaqueMeaning.HoldsOn rfl (encode statement ()) :=
  opaquePureLaw.sourceRealizes.rejects_no statement () no trivial

theorem targetNo (statement : Bool × Bool) (no : claim.No statement) :
    ReadbackHolds claim.No (readback (swapMap (encode statement ()))) :=
  ⟨statement.swap, rfl, opaquePureLaw.no statement no⟩

theorem affirmative_outside_domain_refused :
    ¬ opaqueMeaning.RealizesClaim claim rfl encode (fun _ _ => False) := by
  intro law
  exact ((law (true, true) ()).mp ⟨rfl, rfl⟩).1

theorem changed_claim_refused :
    ¬ opaqueMeaning.RealizesClaim (ClaimRelation.exact (fun (_ : Bool × Bool) (_ : Unit) => True))
      rfl encode (fun _ _ => True) := by
  intro law
  have impossible := ((law (false, false) ()).mp trivial).2
  exact Bool.false_ne_true impossible.1

theorem undefined_pure_readback_refused :
    ¬ ∃ _law : PureSeamLaw opaquePure opaqueRelation opaqueRelation claim claim Prod.swap (fun _ => True)
      swapMap (fun _ => none) readback opaqueMeaning opaqueMeaning rfl rfl encode encode
      (fun _ _ => True) (fun _ _ => True), True := by
  rintro ⟨law, _⟩
  obtain ⟨_, impossible⟩ := law.defined (encode (true, true) ()) trivial
  cases impossible

theorem undefined_terminal_readback_refused :
    ¬ ∃ _law : TerminalSeamLaw opaqueTerminal opaqueRelation claim (fun _ => True)
      (fun _ => none) opaqueMeaning rfl encode (fun _ _ => True), True := by
  rintro ⟨law, _⟩
  obtain ⟨_, impossible⟩ := law.defined (encode (true, true) ()) trivial
  cases impossible

theorem changed_runtime_map_refused :
    ¬ ∃ _law : PureSeamLaw opaquePure opaqueRelation opaqueRelation claim claim Prod.swap (fun _ => True)
      id readback readback opaqueMeaning opaqueMeaning rfl rfl encode encode
      (fun _ _ => True) (fun _ _ => True), True := by
  rintro ⟨law, _⟩
  have impossible := law.total (encode (true, false) ()) trivial
  cases impossible

def affirmativeOnly : ClaimRelation (Bool × Bool) Unit where
  Holds := claim.Holds
  No _ := False
  no_excludes _ _ no := no.elim

-- Identical Yes predicates cannot discharge the separately fixed No transport.
theorem changed_no_refused :
    ¬ ∃ _law : PureSeamLaw opaquePure opaqueRelation opaqueRelation claim affirmativeOnly Prod.swap (fun _ => True)
      swapMap readback readback opaqueMeaning opaqueMeaning rfl rfl encode encode
      (fun _ _ => True) (fun _ _ => True), True := by
  rintro ⟨law, _⟩
  exact law.no (false, false) ⟨rfl, rfl⟩

def changedInstance : OpaqueInstance model.Value := { instanceMeaning with holds := fun _ => True }
def changedRegistry : OpaqueRegistry model.Value :=
  ⟨[{ family with instantiate := fun _ => some changedInstance }], by decide +kernel⟩
def changedBinding : OpaqueRegistry.Binding changedRegistry opaqueRelation.declaration :=
  (changedRegistry.resolve _).get (by decide +kernel)

example : True := by
  fail_if_success
    have : RelationMeaning OpaqueUnit.imported opaqueRelation model.Value registry := .opaque changedBinding
  trivial
example : True := by
  fail_if_success
    have : OpaqueRegistry.Binding registry opaqueRelation.declaration :=
      { opaqueBinding with instantiation := changedInstance, selected := rfl }
  trivial

-- All ABI coordinates, purposes and typed static arguments are exact.
example : (registry.resolve { opaqueDeclaration with inputs := [.boolean] }).isNone = true := by decide +kernel
example : (registry.resolve { opaqueDeclaration with outputs := [.index] }).isNone = true := by decide +kernel
example : (registry.resolve { opaqueDeclaration with purposes := ["statement", "witness"] }).isNone = true := by decide +kernel
example : (registry.resolve { opaqueDeclaration with staticArguments := [.natural "2", .index] }).isNone = true := by decide +kernel
example : (registry.resolve { opaqueDeclaration with staticArguments := [.natural "02"] }).isNone = true := by decide +kernel

#print axioms formulaPureLaw
#print axioms opaquePureLaw
#print axioms scopedPureLaw
#print axioms guardedPureLaw
#print axioms guarded_helper_stops_outside_scope
#print axioms formulaTerminalLaw
#print axioms opaqueTerminalLaw
#print axioms formula_canonical_seam_agree
#print axioms opaque_canonical_seam_agree
#print axioms affirmative_outside_domain_refused
#print axioms sourceNo
#print axioms targetNo
#print axioms changed_runtime_map_refused
#print axioms changed_no_refused
#print axioms terminal_rejects
#print axioms opaque_uniform_logical_agree
#print axioms Zkc.Source.Structured.RelationMeaning.unique_meaning
#print axioms Zkc.Source.Structured.RelationMeaning.holds_iff_uniform_logical
end Tests.ComponentMeanings

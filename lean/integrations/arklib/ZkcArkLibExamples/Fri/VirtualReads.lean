module

public import ZkcArkLibExamples.Fri.RetainedFold
public import ZkcExamples.Structured.FriVirtualBody
public import ZkcExamples.Structured.FriPower
public import Zkc.Source.Structured.OracleMathCalls

@[expose] public section

/-! The installed Fold issues exactly two ordered child reads and uses their
actual answers. Its captured Math table supplies every helper, including
word exponentiation. A refusal by either read survives the process equality. -/
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000
namespace ZkcSecurity.ArkLib.Fri.VirtualReads
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceBodies FriSourceViews
variable (model : DomainModel)

abbrev math := checkedUnit.math
abbrev readInterface (domain : DomainModel) := oracleReadInterface domain.toCarriers
abbrev low (position rows : Nat) := bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)
abbrev kind := OracleKind.table (.field extension) none

def captures (source : OracleAnchor) (beta : model.Field extension) (sourceRows rows : Nat)
    (shift generator inverseShift inverseGenerator inverseTwo : model.Field extension) :
    Values model.Value oracle0Signature.inputs.dropLast :=
  .cons source (.cons beta (.cons sourceRows (.cons rows (.cons shift (.cons generator
    (.cons inverseShift (.cons inverseGenerator (.cons inverseTwo .nil))))))))

def arguments (source : OracleAnchor) (beta : model.Field extension) (sourceRows rows : Nat)
    (shift generator inverseShift inverseGenerator inverseTwo : model.Field extension) (position : Nat) :
    Values model.Value oracle0Signature.inputs :=
  (captures model source beta sourceRows rows shift generator inverseShift inverseGenerator inverseTwo).append
    (Values.cons (Value := model.Value) (ty := Ty.index) position .nil)

theorem powerRequires (generator : model.Field extension) (exponent : Nat) :
    (FriPower.powerLaw model).Requires (closedMeaningsOn model math.definitions)
      (.cons generator (.cons exponent .nil)) := by
  constructor
  · intro value
    apply (FriPower.widthLaw model).invoke (helper := helper10Helper) math.definitions math.linked
      (by rw [FriVirtualBody.mathDefinitions]; exact_body helper10Definition) (.cons value .nil)
    intro value offset amount
    exact (FriPower.halfLaw model).invoke (helper := helper9Helper) math.definitions math.linked
      (by rw [FriVirtualBody.mathDefinitions]; exact_body helper9Definition)
      (.cons value (.cons offset (.cons amount .nil))) trivial
  · intro state index lower upper
    cases state with | mk result factor remaining =>
    apply (FriPower.callbackLaw model).invoke (helper := helper8Helper) math.definitions math.linked
      (by rw [FriVirtualBody.mathDefinitions]; exact_body helper8Definition)
      ((WordPower.pack model extension ⟨result, factor, remaining⟩).append
        (.cons index (.cons lower (.cons upper .nil))))
    intro state index
    cases state with | mk result factor remaining =>
    exact (FriPower.stepLaw model).invoke (helper := helper7Helper) math.definitions math.linked
      (by rw [FriVirtualBody.mathDefinitions]; exact_body helper7Definition)
      ((WordPower.pack model extension ⟨result, factor, remaining⟩).append (.cons index .nil)) trivial

abbrev components (domain : DomainModel) := (math.tables domain (readInterface domain)).components

theorem pairCall (position sourceRows : Nat) :
    invoke (components model) helper14Helper (Values.cons position (Values.cons sourceRows Values.nil)).present =
      .done (Values.cons (Value := model.Value) (ty := .index) (low position sourceRows) .nil).present :=
  math.invokeReturned (I := readInterface model) (helper := helper14Helper) (RetainedFold.pairLaw model)
    (by rw [FriVirtualBody.mathDefinitions]; exact_body helper14Definition)
    (.cons position (.cons sourceRows .nil)) trivial (.cons (low position sourceRows) .nil) rfl

theorem powerCall (inverseGenerator : model.Field extension) (position sourceRows : Nat) :
    invoke (components model) helper11Helper (Values.cons (Value := model.Value) (ty := .field extension) inverseGenerator (Values.cons (low position sourceRows) Values.nil)).present =
      .done (Values.cons (Value := model.Value) (ty := .field extension)
        (inverseGenerator ^ low position sourceRows) .nil).present :=
  math.invokeReturned (I := readInterface model) (helper := helper11Helper) (FriPower.powerLaw model)
    (by rw [FriVirtualBody.mathDefinitions]; exact_body helper11Definition)
    (.cons inverseGenerator (.cons (low position sourceRows) .nil)) (powerRequires model _ _)
    (.cons (inverseGenerator ^ low position sourceRows) .nil)
    (WordPower.outcome_power model extension inverseGenerator _ (bitAnd_lt _ _))

theorem foldCall (left right beta inverseTwo inverseX : model.Field extension) :
    invoke (components model) helper15Helper (Values.cons (Value := model.Value) (ty := .field extension) left (.cons right (.cons beta (.cons inverseTwo
      (.cons inverseX .nil))))).present = .done (Values.cons (Value := model.Value) (ty := .field extension)
        ((left + right) * inverseTwo + beta * (left - right) * inverseTwo * inverseX) .nil).present :=
  math.invokeReturned (I := readInterface model)
    (helper := helper15Helper) (RetainedFold.foldLaw model)
    (by rw [FriVirtualBody.mathDefinitions]; exact_body helper15Definition)
    (.cons left (.cons right (.cons beta (.cons inverseTwo (.cons
      inverseX .nil))))) trivial _ rfl

def leftRequest (source : OracleAnchor) (position : Nat) : OracleRead :=
  ⟨kind, source, position, FriVirtualBody.querySites[0]'(by rw [FriVirtualBody.twoSites]; decide), []⟩

def rightRequest (source : OracleAnchor) (position : Nat) : OracleRead :=
  ⟨kind, source, position, FriVirtualBody.querySites[1]'(by rw [FriVirtualBody.twoSites]; decide), []⟩

def twoChildren (source : OracleAnchor) (beta : model.Field extension) (sourceRows : Nat)
    (inverseShift inverseGenerator inverseTwo : model.Field extension) (position : Nat) :
    PIR.Process (readInterface model) (Values (Component model.Value) [.field extension]) :=
      .call (leftRequest source (low position sourceRows)) fun (left : model.Field extension) ↦
      .call (rightRequest source (wrappingAdd (low position sourceRows) (logicalShiftRight sourceRows 1))) fun (right : model.Field extension) ↦
      .done (.cons (some ((left + right) * inverseTwo + beta * (left - right) * inverseTwo *
        (inverseShift * inverseGenerator ^ low position sourceRows))) .nil)

theorem runChildren {S E : Type} (handler : PIR.Handler (readInterface model) S E)
    (source : OracleAnchor) (beta : model.Field extension) (sourceRows : Nat)
    (inverseShift inverseGenerator inverseTwo : model.Field extension) (position : Nat)
    {i j : Nat} (first : low position sourceRows = i)
    (second : wrappingAdd (low position sourceRows) (logicalShiftRight sourceRows 1) = j)
    {initial middle final : S} {left right : model.Field extension} {leftTrace rightTrace : List E}
    (leftRead : handler (leftRequest source i) initial = ⟨.returned left, middle, leftTrace⟩)
    (rightRead : handler (rightRequest source j) middle = ⟨.returned right, final, rightTrace⟩) :
    (twoChildren model source beta sourceRows inverseShift inverseGenerator inverseTwo position).run
        handler initial =
      ⟨.returned (.cons (some ((left + right) * inverseTwo + beta * (left - right) * inverseTwo *
        (inverseShift * inverseGenerator ^ i))) .nil), final, leftTrace ++ rightTrace⟩ := by
  subst j
  subst i
  simp only [twoChildren, PIR.Process.run, leftRead, rightRead, PIR.Execution.follow, List.append_nil]

theorem bodyReads (source : OracleAnchor) (beta : model.Field extension) (sourceRows rows : Nat)
    (shift generator inverseShift inverseGenerator inverseTwo : model.Field extension) (position : Nat)
    (tables : Evaluation.ComponentTablesOn model.toCarriers (readInterface model))
    (pair : invoke tables.components helper14Helper
      (Values.cons (Value := model.Value) (ty := .index) position (.cons sourceRows .nil)).present =
      .done (Values.cons (Value := model.Value) (ty := .index) (low position sourceRows) .nil).present)
    (power : invoke tables.components helper11Helper
      (Values.cons (Value := model.Value) (ty := .field extension) inverseGenerator
        (.cons (low position sourceRows) .nil)).present =
      .done (Values.cons (Value := model.Value) (ty := .field extension)
        (inverseGenerator ^ low position sourceRows) .nil).present)
    (fold : ∀ (left right : model.Field extension), invoke tables.components helper15Helper
      (Values.cons (Value := model.Value) (ty := .field extension) left (.cons right (.cons beta (.cons inverseTwo
        (.cons (inverseShift * inverseGenerator ^ low position sourceRows) .nil))))).present =
      .done (Values.cons (Value := model.Value) (ty := .field extension)
        ((left + right) * inverseTwo + beta * (left - right) * inverseTwo *
          (inverseShift * inverseGenerator ^ low position sourceRows)) .nil).present) :
    oracle0Body.denote (oracleBodyMeaning model tables)
      (arguments model source beta sourceRows rows shift generator inverseShift inverseGenerator inverseTwo position).present.get =
      twoChildren model source beta sourceRows inverseShift inverseGenerator inverseTwo position := by
  unfold twoChildren
  change (invoke tables.components helper14Helper
    (Values.cons position (Values.cons sourceRows Values.nil)).present).bind _ = _
  erw [pair]
  change PIR.Process.call _ _ = PIR.Process.call _ _
  congr 1
  funext left
  change PIR.Process.call _ _ = PIR.Process.call _ _
  congr 1
  funext right
  change (invoke _ helper11Helper _).bind _ = _
  erw [power]
  change (invoke tables.components helper15Helper _).bind _ = _
  erw [fold left right]
  rfl

theorem twoReads (source : OracleAnchor) (beta : model.Field extension) (sourceRows rows : Nat)
    (shift generator inverseShift inverseGenerator inverseTwo : model.Field extension) (position : Nat) :
    FriVirtualBody.installed.denote model
        (arguments model source beta sourceRows rows shift generator inverseShift inverseGenerator inverseTwo position).present =
      twoChildren model source beta sourceRows inverseShift inverseGenerator inverseTwo position :=
  (FriVirtualBody.denote model _).trans (bodyReads model source beta sourceRows rows shift generator
    inverseShift inverseGenerator inverseTwo position _ (pairCall model position sourceRows)
    (powerCall model inverseGenerator position sourceRows)
    (fun left right ↦ foldCall model left right beta inverseTwo _))

end ZkcSecurity.ArkLib.Fri.VirtualReads

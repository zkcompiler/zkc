module

public import ZkcExamples.Structured.FriQueryCall
public import ZkcExamples.Structured.FriValueAssociation
public import Zkc.Source.Structured.OracleReadEffects
public import Zkc.Source.Structured.MarkedPrefix
public import Zkc.Source.Structured.Bindings.Continuation
public import Zkc.Source.Structured.Bindings.RepeatPrefix
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback
public meta import ZkcExamples.Structured.FriSourceBodies

@[expose] public section

/-! The first table read in each installed Check iteration. Its position is
looked up in the bound list at the loop ordinal. Preceding source marks and
the entire continuation are retained. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCheckPositions
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding
open OracleProtocol (concrete)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

open Zkc.Source.Structured.Bindings

checked_callback query := protocol3Body at 0 with_continuation

variable {model : DomainModel}

/-- Select the first receiver query from the admitted callback itself. -/
def initialSite : OracleLocation :=
  (queryBody.erase.operations.findSome? fun op ↦ match op with
    | .oracle (.query _ (some 1)) site => some site
    | _ => none).get (by decide +kernel)

def initialRequest (context : ProtocolContext) (source : OracleAnchor) (position : Nat) :
    (OracleProtocol.Interface model).Op :=
  OracleProtocol.tableQuery model (.field extension) none source position 1 1 context.roles initialSite

/-- Everything else carried into the iteration stays free. The position list
and the initial receiver handle occupy their admitted input roles. -/
structure Captures (model : DomainModel) where
  values : Value model (.vector extension)
  layers : Value model layersSort.type
  folds : Value model layersSort.type
  shift : Value model (.field extension)
  size : Value model .index
  coefficients : Value model (.vector extension)
  associate : Value model .boolean
  first : Value model (.vector extension)
  remaining : Value model .index

def captured (cap : Captures model) (xs : List Nat) (source : OracleAnchor) :
    Values (Value model) querySite.spec.captures :=
  .cons (concrete model initialSort.type source) (.cons cap.layers (.cons cap.folds (.cons cap.shift
    (.cons cap.size (.cons cap.coefficients (.cons (concrete model .indices xs) (.cons cap.associate
      (.cons cap.first (.cons cap.remaining .nil)))))))))

def arguments (cap : Captures model) (xs : List Nat) (ordinal : Nat) (source : OracleAnchor) :
    Values (Value model) (.index :: (querySite.spec.state ++ querySite.spec.captures)) :=
  .cons (concrete model .index ordinal) (.cons cap.values (captured cap xs source))

def iteration (context : ProtocolContext) (cap : Captures model) (xs : List Nat) (ordinal : Nat)
    (source : OracleAnchor) :=
  queryBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
    (arguments cap xs ordinal source).get

def framed (context : ProtocolContext) (captures : Values (Value model) querySite.spec.captures)
    (current : Values (Value model) querySite.spec.state) (ordinal : Nat) :=
  OracleProtocol.enter model (.iteration querySite.site ordinal)
    (queryBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
      (Values.cons (concrete model .index ordinal) (current.append captures)).get)

/-- The source iterates once per ordinal even when two positions coincide. -/
theorem ordered (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (Value model) querySite.context) (count : Nat) (bound : count ≤ querySite.spec.maximum)
    (initial : Values (Value model) querySite.spec.state) (captures : Values (Value model) querySite.spec.captures)
    (selected : Operands.eval env querySite.operands = .cons (concrete model .index count) (initial.append captures)) :
    querySite.iterations ((verifierAlgebra model).meaning (verifierTable model) context 1) env =
      Finite.fold (framed context captures) (List.range count) initial := by
  apply querySite.visibleIterations (verifierAlgebra model) (verifierTable model) context 1 env
    (concrete model .index count) initial captures selected
  · change ([0, 1].map context.roles).contains 1 = true
    simp [receiver]
  · intro out
    match out with
    | .cons _ .nil =>
      change maskValues 1 ([[1]].map (List.map context.roles)) _ = _
      simp [maskValues, receiver, Participant.restrict]
  · exact ProtocolValue.toConcrete_ofConcrete (carriers := model.toCarriers) .index count
  · exact bound

/-- The installed outer loop must complete before the receiver can return
true. The returned vector is precisely its last loop state. -/
theorem returnAfterQueries (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (Value model) querySite.context) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    querySite.region.denote meaning env = (querySite.iterations meaning env).bind fun out ↦
      OracleProtocol.withMarks (querySite.continuationMarks context)
        (.done (.cons (concrete model .boolean true) (.cons (out.get .here) .nil))) := by
  dsimp only
  rw [querySite.denote_region]
  congr 1
  funext out
  match out with
  | .cons values .nil =>
    have restrictStep : ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
        (fun op ↦ .call op .done) (.restrict .boolean [1])
        (.cons (concrete model .boolean true) .nil) .nil (.done (.cons (concrete model .boolean true) .nil)) := by
      apply RegionMeaning.OperationLaw.identity
      change PIR.Process.done (I := OracleProtocol.Interface model)
        (Values.cons (Value := Value model) (ty := .boolean) (Participant.restrict (([1].map context.roles).contains 1) (concrete model .boolean true)) .nil) = _
      rw [show ([1].map context.roles).contains 1 = true by simp [receiver]]
      rfl
    derive_process using (exact restrictStep)

/-- The outer query repeat is on the continuation spine of the installed
Check declaration. An earlier guard or missing operand can still stop it. -/
theorem queryOnSpine : queryOccurrence.onSpine = true := by kernel_rfl

def program (context : ProtocolContext) (env : Environment (Value model) protocol3Signature.inputs) :
    PIR.Process (OracleProtocol.Interface model) (Values (Value model) protocol3Signature.outputs) :=
  let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
  ((queryOccurrence.beforeRepeat queryOnSpine).denote meaning env).bind fun live ↦
    (querySite.iterations meaning live.get).bind fun out ↦
      OracleProtocol.withMarks (querySite.continuationMarks context)
        (.done (.cons (concrete model .boolean true) (.cons (out.get .here) .nil)))

theorem body (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (env : Environment (Value model) protocol3Signature.inputs) :
    protocol3Body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) env =
      program context env := by
  refine (queryOccurrence.denote_prefix ((verifierAlgebra model).meaning (verifierTable model) context 1)
    queryOnSpine env).trans ?_
  unfold program
  congr 1
  funext live
  exact returnAfterQueries context receiver live.get

/-- Source execution of Check, including all input/return masks, its complete
admission prefix, and every iteration. Acceptance is reachable only after
the outer repeat returns its actual accumulated vector. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (args : Values (Value model) protocol3Signature.inputs) :
    invokeProtocol (verifierTable model) protocol3Signature context 1 args =
      (program context (maskValues 1 (context.mapScopes protocol3Signature.inputScopes) args).get).bind fun out ↦
        .done (maskValues 1 (context.mapScopes protocol3Signature.outputScopes) out) :=
  (verifierAlgebra model).invokePresented unit.protocolsLinked protocol3Definition protocol3_member
    context 1 args _ (body context receiver _)

theorem lookup (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs)
    (ordinal : Fin xs.length) :
    OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil)) =
        .done (.cons (concrete model .index xs[ordinal.val]) .nil) := by
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper30Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) xs
      (.cons (ty := .index) ordinal.val .nil)).present) = _
  rw [OracleProtocol.owned_present,
    (FriBoundedPositions.lookupLaw model).invokeOn (helper := helper30Helper)
      unit.definitions unit.linked (by exact_body helper30Definition)
      (.cons xs (.cons ordinal.val .nil)) ⟨admitted, ordinal.isLt⟩]
  simp [FriBoundedPositions.lookupLaw,
    primitiveOutcome, PIR.Process.bind]
  rfl

/-- An associated checker compares by ordinal even when sampled positions
repeat. A wrong value stops before any later query or append. -/
def rejectsMismatch (cap : Captures model) (i : Nat)
    {context : ProtocolContext} {source : OracleAnchor} {position : Nat}
    (next : (OracleProtocol.Interface model).Reply (initialRequest context source position) →
      PIR.Process (OracleProtocol.Interface model) (Values (Value model) querySite.spec.state)) : Prop :=
  ∀ (first : List (model.Field extension)) (value : model.Field extension),
    cap.associate = concrete model .boolean true → cap.first = concrete model (.vector extension) first →
    first.length < indexLimit → ∀ inside : i < first.length, value ≠ first[i] →
      OracleProtocol.StopsAfterMarks .reject (next (.cons (concrete model (.field extension) value) .nil))

/-- All other captured values may be arbitrary. Only the initial handle and
the checked position vector determine the first table request. -/
theorem firstRead (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (xs : List Nat) (admitted : FriBoundedPositions.Admitted xs)
    (ordinal : Fin xs.length) (source : OracleAnchor)
    (cap : Captures model) :
    OracleProtocol.AtMarkedCall (initialRequest context source xs[ordinal.val])
      (rejectsMismatch (context := context) (source := source) (position := xs[ordinal.val]) cap ordinal.val)
      (iteration context cap xs ordinal.val source) := by
  unfold iteration
  apply OracleProtocol.AtMarkedCall.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [3, 1]
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper30Helper
      (.cons (concrete model .indices xs) (.cons (concrete model .index ordinal.val) .nil))
    rw [receiver, lookup xs admitted ordinal]
  apply OracleProtocol.AtMarkedCall.mark
  apply OracleProtocol.AtMarkedCall.found
  intro first value enabled vector size inside mismatch
  apply OracleProtocol.StopsAfterMarks.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [2, 1]
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper31Helper
      (.cons cap.associate (.cons cap.first (.cons (concrete model .index ordinal.val)
        (.cons (concrete model (.field extension) value) .nil))))
    rw [receiver, enabled, vector, FriValueAssociation.installed true first ordinal.val value (fun _ ↦ ⟨size, inside⟩)]
    simp only [List.getElem?_eq_getElem inside, Option.any_some, mismatch, decide_false, ↓reduceIte]
  apply OracleProtocol.StopsAfterMarks.mark
  simp only [PIR.Process.bind]
  rw [Region.denote]
  conv =>
    enter [2, 1]
    change ((Participant.guard (services := services) (Value := model.Value) 1 (context.roles 1)
      ((concrete model .boolean false).bind ProtocolValue.toConcrete)).interpret
        (OracleProtocol.actions model)).bind _
    rw [receiver]
    simp [OracleProtocol.concrete, ProtocolValue.toConcrete_ofConcrete, Participant.guard,
      PIR.Process.interpret, PIR.Process.bind]
  exact OracleProtocol.StopsAfterMarks.now .reject

end ZkcExamples.Structured.FriCheckPositions

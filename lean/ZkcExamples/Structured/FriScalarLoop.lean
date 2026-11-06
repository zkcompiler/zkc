module

public import ZkcExamples.Structured.FriIndexCollections
public import Zkc.Source.Structured.Bindings.Selection
public import Zkc.Source.Structured.OracleQueryDerivation
public import Zkc.Source.Structured.OracleLoopPresentation

@[expose] public section

/-! The scalar verifier's actual counted loop. The state consists of positions
below 32. Each raw reply is checked before delivery, and the installed append
helper receives that same position. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriScalarLoop
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews
open OracleProtocol (concrete)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions ServiceOp.contract

abbrev contract := "random.koala-bear.ext8-binomial3/0"
def context := lowDegreeContext.enter "label_71756572696573" [0, 1]
def site (name : String) := qualifyProtocolSite context.applicationPrefix name

def loop := (Bindings.checkedRepeat 0 protocol1Body (by decide +kernel)).repeatSite

abbrev Positions := List (Fin 32)

def marks (model : DomainModel) : List String → PIR.Process (OracleProtocol.Interface model) Unit
  | [] => .done ()
  | name :: names => .call (.mark name (site name)) fun _ ↦ marks model names

def draw (model : DomainModel) (service : Nat) : PIR.Process (OracleProtocol.Interface model) (Fin 32) :=
  (marks model ["", "s13"]).bind fun _ ↦
    OracleProtocol.finiteIndex model (site "s13") contract service 32

def deliver (model : DomainModel) (i : Fin 32) : PIR.Process (OracleProtocol.Interface model) Unit := do
  marks model ["s15_0"]
  PIR.Process.call (.ordinary (.send (ty := .index) (site "s15_0") 0 i.val)) fun _ ↦ .done ()
  marks model ["", "", "s19", "s21", ""]

def step (model : DomainModel) (service : Nat) (xs : Positions) :
    PIR.Process (OracleProtocol.Interface model) Positions := do
  let i ← draw model service
  deliver model i
  return xs ++ [i]

def packed (model : DomainModel) (xs : Positions) :
    Values (Component (ProtocolValue model.toCarriers)) [.indices] :=
  .cons (concrete model .indices (xs.map Fin.val)) .nil

private theorem appendStep (model : DomainModel) (xs : Positions) (short : xs.length < 8)
    (i : Fin 32) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper23Helper rfl 1 "s21")
      (.cons (concrete model .indices (xs.map Fin.val)) (.cons (concrete model .index i.val) .nil)) .nil
      (.done (packed model (xs ++ [i]))) := by
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper23Helper
    (.cons (concrete model .indices (xs.map Fin.val)) (.cons (concrete model .index i.val) .nil)) = _
  have bound : 32 < indexLimit := by decide
  have all : (xs.map Fin.val).all (· < indexLimit) = true := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, decide_eq_true_eq]
    rintro n j _ rfl
    exact j.isLt.trans bound
  have size : (xs.map Fin.val).length + 1 < indexLimit := by simp only [List.length_map]; omega
  simpa only [packed, List.map_append, List.map_cons, List.map_nil, concrete] using
    FriIndexCollections.append model 1 (xs.map Fin.val) i.val all size (i.isLt.trans bound)

set_option maxHeartbeats 1200000 in
/-- Equality of effect trees at the actual nested call. A physical handler may
refuse any mark, delivery or query, including after earlier successful draws. -/
theorem callback (model : DomainModel) (xs : Positions) (index service : Nat)
    (short : xs.length < 8) :
    loop.body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
      (Values.cons (concrete model .index index) (.cons (concrete model .indices (xs.map Fin.val))
        (.cons (concrete model (.service contract) service) .nil))).get =
      (step model service xs).bind fun ys ↦ .done (packed model ys) := by
  trans ?generated
  · derive_process using
      (first
       | exact OracleProtocol.scalarQuery model (context := context) (owner := 1) (by decide) service 32
       | apply OracleProtocol.sendConcrete model (context := context) (owner := 1) (by decide)
       | apply appendStep model xs short)
  · simp only [step, draw, deliver, marks, bind, pure, PIR.Process.bind_assoc, PIR.Process.bind]
    rfl

theorem stepLength (model : DomainModel) (xs : Positions) (service : Nat) :
    PIR.Yields (fun ys ↦ ys.length = xs.length + 1) (step model service xs) := by
  have all {A : Type} (p : PIR.Process (OracleProtocol.Interface model) A) :
      PIR.Yields (fun _ ↦ True) p := by
    induction p with
    | done => trivial
    | halt => trivial
    | call _ _ ih => exact ih
  unfold step
  repeat' first | apply (all _).bind; intro _ _
  change (xs ++ [_]).length = xs.length + 1
  simp

def positions (model : DomainModel) (service : Nat) : PIR.Process (OracleProtocol.Interface model) Positions :=
  Finite.fold (fun xs index ↦ (OracleProtocol.iterationObservations model).within loop.site index
    (step model service xs)) (List.range' 0 8) []

/-- Apply the shared counted invariant to the callback selected in the admitted body. -/
theorem eightDraws (model : DomainModel) (service : Nat) :
    (verifierAlgebra model).repeatProcess loop.spec context 1 loop.site (concrete model .index 8)
      (packed model []) (.cons (concrete model (.service contract) service) .nil)
      (fun args ↦ loop.body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) args.get) =
      (positions model service).bind fun ys ↦ .done (packed model ys) := by
  apply ProtocolLoopPresentation.present (verifierAlgebra model) loop.spec context 1 loop.site
    (OracleProtocol.iterationObservations model)
    (OracleProtocol.iteration_eq model 1 _ _ context loop.site)
    (by decide) (.cons (concrete model (.service contract) service) .nil) _
    (fun _ xs ↦ packed model xs) (fun index xs ↦ xs.length = index)
    (fun _ _ ↦ rfl) (fun xs _ ↦ step model service xs) 8
  · intro index xs inside length
    exact callback model xs index service (by omega)
  · intro index xs _ length
    exact (stepLength model xs service).mono (fun ys size ↦ size.trans (congrArg (· + 1) length))
  · change (some (ProtocolValue.ofConcrete .index 8)).bind ProtocolValue.toConcrete = some 8
    exact ProtocolValue.toConcrete_ofConcrete (carriers := model.toCarriers) .index 8
  · decide
  · rfl
  · rfl

private theorem repeatStep (model : DomainModel) (service : Nat) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
      (fun op ↦ .call op .done) (.repeat loop.spec loop.site)
      (.cons (concrete model .index 8) (.cons (concrete model .indices [])
        (.cons (concrete model (.service contract) service) .nil)))
      (.cons (fun args ↦ loop.body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
        args.get) .nil) ((positions model service).bind fun ys ↦ .done (packed model ys)) := by
  apply RegionMeaning.OperationLaw.identity
  exact eightDraws model service

def program (model : DomainModel) (service : Nat) : PIR.Process (OracleProtocol.Interface model) Positions :=
  (marks model ["", "", "s2", "", "", "s5", "s6", "s8", "", loop.site]).bind fun _ ↦ positions model service

set_option maxHeartbeats 1200000 in
/-- The full scalar component, including the two count guards and empty calls. -/
theorem body (model : DomainModel) (service : Nat) :
    protocol1Body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
      (Values.cons (concrete model .index 8) (.cons (concrete model (.service contract) service) .nil)).get =
      (program model service).bind fun ys ↦ .done (packed model ys) := by
  trans ?generated
  · derive_process using
      (first
       | exact OracleProtocol.equalIndex model 8
       | apply OracleProtocol.guardTrue model
       | apply RegionMeaning.OperationLaw.identity; exact FriIndexCollections.empty model 1)
      summarizing (exact repeatStep model service)
  · simp only [program, marks, PIR.Process.bind]
    rfl

#print axioms body

end ZkcExamples.Structured.FriScalarLoop

import Zkc.Core.Facts.Body.RoleChecking
import Zkc.Tests.Core.Shapes

namespace Zkc.Core.BodyAnalysis.HolderTransfer
open Shapes

private abbrev P := protocolDialect plain Shapes.none
private abbrev Body (outs : List (LTy plain)) := Term P (Ctx.positional []) outs
private def catalog := (FunctionContracts.check ([] : List (FnHeader plain))).toOption.get (by decide)
private def header {outs} (p : Body outs) : ProtocolHeader plain := ⟨⟨10⟩, 4, [], outs, shapeOf p⟩

private def narrow (τ : plain.Ty) : ProtocolOp plain Shapes.none [⟨τ,[0,1]⟩] [⟨τ,[0]⟩] :=
  .narrow [0] (by decide)

/-- Role 1 is an unrelated holder. Role 2 is both an old holder and a receiver.
Role 3 first acquires the value, and role 4 observes neither side. -/
private def send (τ : plain.Ty) (kind := FlowKind.message) :
    ProtocolOp plain Shapes.none [⟨τ,[0,1,2]⟩] [⟨τ,[0,1,2,3]⟩] :=
  .flow kind 0 [2,3] (by decide) (by decide)

private def countAfter {before after : Holders} (nonempty : after ≠ [])
    (op : ProtocolOp plain Shapes.none [nat before] [nat after]) : Body [] :=
  .op ⟨1⟩ (.compute before (.literal .nat [4] rfl) [] rfl (fun _ h => nomatch h))
    .nil (.cons 0 .nil) <|
  .op ⟨2⟩ op (.cons (var 0) .nil) (.cons 1 .nil) <|
  .loop (carried := []) (each := []) ⟨3⟩ after (.value (var 1) ⟨rfl, fun _ h => h, nonempty⟩)
    (fun _ h => nomatch h) .nil (.cons 2 .nil) (.ret .nil) .nil (.ret .nil)

private def bounds (p : Body []) (r : Role) :=
  (RoleContracts.checkRole catalog r (header p) (inputs := .nil) (project r p)).toOption

private def fourAt (r : Role) : Option (List (Place × Nat)) :=
  some [(⟨⟨10⟩, [], some ⟨3⟩, some r⟩, 4)]

theorem narrowBound : bounds (countAfter (by decide) (narrow .nat)) 0 = fourAt 0 := by decide +kernel

private def sentCount := countAfter (by decide) (send .nat)

theorem sendBounds : [0,1,2,3].map (bounds sentCount) =
    [fourAt 0, fourAt 1, some [], some []] := by decide +kernel

private def truthAfter {before after : Holders} (b : Bool)
    (op : ProtocolOp plain Shapes.none [⟨.bool,before⟩] [⟨.bool,after⟩]) : Body [⟨.bool,after⟩] :=
  .op ⟨1⟩ (.compute before (.literal .bool [b.toNat] (by cases b <;> rfl)) [] rfl
    (fun _ h => nomatch h)) .nil (.cons 0 .nil) <|
  .op ⟨2⟩ op (.cons (var 0) .nil) (.cons 1 .nil) <|
  .ret (.cons (var 1) .nil)

/-- Decide an actual guarantee on the returned Boolean port. -/
private def decision {holders} (p : Body [⟨.bool,holders⟩]) (r : Role) : Option (Unit ⊕ Verdict) :=
  match RoleContracts.checkRole catalog r (header p) (inputs := .nil) (project r p)
      ⟨[], [⟨.arg 0, none⟩]⟩ with
  | .ok [] => some (.inl ())
  | .error (.refused [⟨_, .guarantee, 0, _, v, _⟩]) => some (.inr v)
  | _ => Option.none

theorem narrowTruth : [true,false].map (fun b => decision (truthAfter b (narrow .bool)) 0) =
    [some (.inl ()), some (.inr .knownFalse)] := by decide +kernel

theorem sendTruth : [0,1,2,3].map (decision (truthAfter false (send .bool))) =
    [some (.inr .knownFalse), some (.inr .knownFalse), some (.inr .unknown), some (.inr .unknown)] := by
  decide +kernel

example : [0,2].map (decision (truthAfter true (send .bool))) =
    [some (.inl ()), some (.inr .unknown)] := by decide +kernel

private def walked {outs} (p : Body outs) (r : Role) :=
  analyse (RoleContracts.config catalog r (header p).key []) [] ⟨[], []⟩ .nil (project r p)

private def returnedTruth {hs} (p : Body [⟨.bool,hs⟩]) (r : Role) : Option Bool := do
  let exit := walked p r
  let id ← exit.returned[0]?
  (RoleContracts.config catalog r (header p).key []).domain.truth .nobody exit.state.values.table exit.known id

example : returnedTruth (truthAfter true (send .bool)) 4 = Option.none := by decide +kernel
example : returnedTruth (truthAfter true (narrow .bool)) 1 = Option.none := by decide +kernel

/-- Check the typed event, key, operand and result leaf in the very walk that learns the truth. -/
private def event (r : Role) : Option (Key × RoleCode plain × List Ident × Nat × List Ident) :=
  match (walked (truthAfter true (send .bool)) r).skel with
  | .step key (.effect op args lo) (.ret ids) => some (key, roleCode op, args, lo, ids)
  | _ => Option.none

example : event 0 = some (⟨2⟩, .give .message [2,3], [.val 0], 0, [.leaf 0]) := by decide +kernel
example : event 2 = some (⟨2⟩, .get .bool [0,1,2] .message 0 [2,3], [], 0, [.leaf 0]) := by
  decide +kernel

/-- The projected receiver can return either permitted Boolean reply, even though role 2
computed the literal false before receiving. -/
theorem receiveReply (b : Bool) :
    let sem := roleSem plainModel 2 noFns noPrograms
    ((project 2 (truthAfter false (send .bool))).denote sem [] Env.empty).CanReturn
      (Permitted plainModel) (.cons (hide plainModel 2 ⟨.bool,[0,1,2,3]⟩ b) .nil) := by
  exact .call _ b trivial (.done _)

-- A shared keep also retains a result slot with its own located operation.
example :
    let exit := walked (truthAfter true (narrow .bool)) 0
    (exit.returned, exit.state.values.table.formOf (.val 1)) =
      ([.val 1], some (.app (.keep [0]) [.val 0], 0)) := by decide +kernel

private def differences (r : Role) (other : ProtocolOp plain Shapes.none
    [⟨.bool,[0,1,2]⟩] [⟨.bool,[0,1,2,3]⟩]) :=
  let source := truthAfter true (send .bool)
  let candidate := truthAfter true other
  match RoleContracts.compareRoles catalog r (header source) (inputs := .nil) (otherInputs := .nil)
      (project r source) (project r candidate) with
  | .error (.body [] diff) => some diff
  | _ => Option.none

example : differences 0 (send .bool .opening) = some [⟨(header (truthAfter true (send .bool))).key, [], some ⟨2⟩, some 0⟩] := by decide +kernel

-- The receiver's written effect omits getter order. Typed comparison still distinguishes it.
example : differences 2 (.flow .message 0 [3,2] (by decide) (by decide)) =
    some [⟨(header (truthAfter true (send .bool))).key, [], some ⟨2⟩, some 2⟩] := by decide +kernel

end Zkc.Core.BodyAnalysis.HolderTransfer

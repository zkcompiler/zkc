module

public import Zkc.Source.Structure

@[expose] public section

/-! Step equations for the existing Region interpreter. Reifying the environment
as an ordered value tuple permits operation proofs to share a continuation;
these laws introduce no additional evaluator or operation semantics. -/
namespace Zkc.Source

/-- Share the existing denotation at each step while retaining a flat value tuple. -/
theorem Environment.prepend_values_get {T : Type} {V : T → Type} {Γ Δ : List T}
    (before : Values V Γ) (added : Values V Δ) :
    @Eq (Environment V (Δ ++ Γ)) (Environment.prepend before.get added)
      (added.append before).get := by
  induction added with
  | nil => rfl
  | cons value rest ih =>
    funext ty ref
    cases ref with
    | here => rfl
    | there ref => exact congrFun (congrFun ih _) ref

/-- A general operation keeps all of its actions and binds its result tuple to
its literal continuation. This also covers operations with multiple actions. -/
theorem Region.denote_letOp_values {dialect : Dialect} {interface : PIR.Signature}
    (meaning : RegionMeaning dialect interface) {Γ out : List dialect.Ty}
    (op : dialect.Op) (arguments : Operands Γ (dialect.arguments op))
    (bodies : Regions dialect (dialect.regions op))
    (next : Region dialect (dialect.results op ++ Γ) out)
    (before : Values meaning.Value Γ) :
    (Region.letOp op arguments bodies next).denote meaning before.get =
      (meaning.operation op (arguments.eval before.get) (bodies.denote meaning)).bind
        fun added => next.denote meaning (added.append before).get := by
  change (meaning.operation op (arguments.eval before.get) (bodies.denote meaning)).bind _ = _
  apply congrArg (PIR.Proc.bind _)
  funext added
  exact congrArg (next.denote meaning) (Environment.prepend_values_get before added)

/-- A returning operation extends the value tuple before its literal continuation. -/
theorem Region.denote_letOp_done {d : Dialect} {I : PIR.Signature} (m : RegionMeaning d I) {Γ out : List d.Ty}
    (op : d.Op) (args : Operands Γ (d.arguments op))
    (bodies : Regions d (d.regions op)) (next : Region d (d.results op ++ Γ) out)
    (before : Values m.Value Γ) (added : Values m.Value (d.results op))
    (operation : m.operation op (args.eval before.get) (bodies.denote m) = .done added) :
    (Region.letOp op args bodies next).denote m before.get =
      next.denote m (added.append before).get := by
  rw [Region.denote_letOp_values, operation]
  rfl

/-- A stopped operation does not enter the literal continuation. -/
theorem Region.denote_letOp_halt {d : Dialect} {I : PIR.Signature} (m : RegionMeaning d I) {Γ out : List d.Ty}
    (op : d.Op) (args : Operands Γ (d.arguments op))
    (bodies : Regions d (d.regions op)) (next : Region d (d.results op ++ Γ) out)
    (before : Values m.Value Γ) (reason : PIR.Stop)
    (operation : m.operation op (args.eval before.get) (bodies.denote m) = .halt reason) :
    (Region.letOp op args bodies next).denote m before.get = .halt reason := by
  rw [Region.denote_letOp_values, operation]
  rfl

/-- An action preserves every reply continuation of the existing Region denotation. -/
theorem Region.denote_letOp_call {d : Dialect} {I : PIR.Signature} (m : RegionMeaning d I) {Γ out : List d.Ty}
    (op : d.Op) (args : Operands Γ (d.arguments op))
    (bodies : Regions d (d.regions op)) (next : Region d (d.results op ++ Γ) out)
    (before : Values m.Value Γ) (action : I.Op)
    (added : I.Reply action → Values m.Value (d.results op))
    (result : I.Reply action → PIR.Proc I (Values m.Value out))
    (operation : m.operation op (args.eval before.get) (bodies.denote m) =
      .call action (fun reply => .done (added reply)))
    (continuation : ∀ reply, next.denote m ((added reply).append before).get = result reply) :
    (Region.letOp op args bodies next).denote m before.get = .call action result := by
  rw [Region.denote_letOp_values, operation]
  apply congrArg (PIR.Proc.call action)
  funext reply
  exact continuation reply

end Zkc.Source

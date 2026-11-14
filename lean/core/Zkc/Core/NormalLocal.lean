module

public import Zkc.Core.Normal
public import Zkc.Core.ThreadPlain

public section

/-! The normal form of local code.

What the local dialect gives the pass of `Zkc.Core.Normal`.

- **Shared operations.** An operation the core owns, a literal that is no `bool`, a pure or
  restricted row and a call of a function. Each returns or stops and performs nothing, and
  reads no nested region; a call is so because a function performs no effect. A `bool`
  literal is not shared: the check of facts reads the form "a region that is one `bool`
  literal and its return" in the regions of an `if` (`a and b`, `a or b`), and a shared
  literal would leave a region that is a return alone.
- **Rebuilt operations.** `if`, `match` and `loop` capture every value in scope: the captures
  of the operation become the whole context, and each region is typed over its own inputs
  (the payload of an alternative; the iteration number and the carried values) and that
  context. Every other operation is unchanged.

`localNormalizer_sound`: these choices are sound for the meaning of local code over a table
of functions that perform no effect.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

deriving instance DecidableEq for Builtin

namespace LocalOp

/-- When two local operations are one shared operation: the same operation of the core, the
same literal, the same row, or a call of the same function. -/
@[expose] def same : SameOp (LocalDialect operations functions deployed)
  | .builtin first, .builtin second =>
      if equal : first = second then some ⟨by rw [equal]⟩ else none
  | .literal (.bool _), _ => none
  | .literal first, .literal second =>
      if equal : first = second then some ⟨by rw [equal]⟩ else none
  | .op (inputs := firstInputs) (outputs := firstOutputs) (kind := firstKind) first _,
      .op (inputs := secondInputs) (outputs := secondOutputs) (kind := secondKind) second _ =>
      if equal : firstInputs = secondInputs ∧ firstOutputs = secondOutputs ∧
          firstKind = secondKind ∧ first.index = second.index then
        some ⟨by
          obtain ⟨rfl, rfl, rfl, index⟩ := equal
          cases Var.ext index
          rfl⟩
      else none
  | .call (header := firstHeader) first _, .call (header := secondHeader) second _ =>
      if equal : firstHeader = secondHeader ∧ first.index = second.index then
        some ⟨by
          obtain ⟨rfl, index⟩ := equal
          cases Var.ext index
          rfl⟩
      else none
  | _, _ => none

/-- The plan of the regions of a `match` that captures every value of `Δ`: the region of an
alternative takes its payload and then the context. -/
@[expose] def armsPlan {Δ captures : List Ty} (outputs : List Ty) (captured : Operands Δ captures)
    (table : List (Entry (LocalDialect operations functions deployed) Δ)) :
    (alternatives : List Ty) →
      Plan (LocalDialect operations functions deployed)
        (alternatives.map fun payload => (payload :: captures, outputs))
        (alternatives.map fun payload => (payload :: Δ, outputs))
  | [] => .nil
  | payload :: rest =>
      .cons (Renaming.inward captured [payload] (Mapping.start (Δ := ([] : List Ty)) 0 rfl))
        (Entry.inwardAll (dialect := LocalDialect operations functions deployed) [payload]
              (base := []) table) (armsPlan outputs captured table rest)

/-- A local operation rebuilt at a context: `if`, `match` and `loop` capture every value of
the context; every other operation is itself. -/
@[expose] def reopen {Δ : List Ty} :
    (op : LocalOp operations functions deployed) → Operands Δ op.arguments →
      List (Entry (LocalDialect operations functions deployed) Δ) →
        Reopened (LocalDialect operations functions deployed) Δ op
  | .conditional _ outputs, arguments, table =>
      { regions := [(Δ, outputs), (Δ, outputs)]
        plan :=
          .cons (Renaming.inward arguments.tail [] (Mapping.start (Δ := ([] : List Ty)) 0 rfl))
            (Entry.inwardAll (dialect := LocalDialect operations functions deployed) []
              (base := []) table)
            (.cons (Renaming.inward arguments.tail [] (Mapping.start (Δ := ([] : List Ty)) 0 rfl))
              (Entry.inwardAll (dialect := LocalDialect operations functions deployed) []
              (base := []) table) .nil)
        build := fun bodies rest =>
          .letOp (.conditional Δ outputs) (.cons (arguments.get .here) (Operands.every Δ)) bodies
            rest }
  | .match declaration alternatives _ outputs, arguments, table =>
      { regions := alternatives.map fun payload => (payload :: Δ, outputs)
        plan := armsPlan outputs arguments.tail table alternatives
        build := fun bodies rest =>
          .letOp (.match declaration alternatives Δ outputs)
            (.cons (arguments.get .here) (Operands.every Δ)) bodies rest }
  | .loop (.static count) carried collected _, arguments, table =>
      { regions := [(.nat :: (carried ++ Δ), collected ++ carried)]
        plan :=
          .cons
            (Renaming.inward (arguments.split carried).2 (Ty.nat :: carried)
              (Mapping.start (Δ := ([] : List Ty)) 0 rfl))
            (Entry.inwardAll (dialect := LocalDialect operations functions deployed) (Ty.nat :: carried)
              (base := []) table) .nil
        build := fun bodies rest =>
          .letOp (.loop (.static count) carried collected Δ)
            ((arguments.split carried).1.append (Operands.every Δ)) bodies rest }
  | .loop (.runtime maximum) carried collected _, arguments, table =>
      { regions := [(.nat :: (carried ++ Δ), collected ++ carried)]
        plan :=
          .cons
            (Renaming.inward (arguments.tail.split carried).2 (Ty.nat :: carried)
              (Mapping.start (Δ := ([] : List Ty)) 0 rfl))
            (Entry.inwardAll (dialect := LocalDialect operations functions deployed) (Ty.nat :: carried)
              (base := []) table) .nil
        build := fun bodies rest =>
          .letOp (.loop (.runtime maximum) carried collected Δ)
            (.cons (arguments.get .here)
              ((arguments.tail.split carried).1.append (Operands.every Δ))) bodies rest }
  | .op row applies, arguments, _ =>
      { regions := [], plan := .nil, build := fun _ rest => .letOp (.op row applies) arguments .nil rest }
  | .call callee permitted, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.call callee permitted) arguments .nil rest }
  | .guard reason, arguments, _ =>
      { regions := [], plan := .nil, build := fun _ rest => .letOp (.guard reason) arguments .nil rest }
  | .literal value, arguments, _ =>
      { regions := [], plan := .nil, build := fun _ rest => .letOp (.literal value) arguments .nil rest }
  | .builtin operation, arguments, _ =>
      { regions := [], plan := .nil
        build := fun _ rest => .letOp (.builtin operation) arguments .nil rest }

end LocalOp

section Sound

variable {model : Model} {table : FunctionTable model functions}

/-- A shared local operation is deterministic, over functions that perform no effect. -/
theorem LocalOp.same_deterministic (quiet : QuietTable table) :
    ∀ (op : LocalOp operations functions deployed), (LocalOp.same op op).isSome = true →
      Deterministic (localMeaning model table) op
  | .builtin operation, _ =>
      { ends := fun arguments _ => by
          show (∃ values, definedProcess model (operation.eval arguments) = .done values) ∨
            (∃ reason, definedProcess model (operation.eval arguments) = .halt reason)
          cases operation.eval arguments with
          | some values => exact .inl ⟨values, rfl⟩
          | none => exact .inr ⟨.undefined, rfl⟩
        closed := fun _ _ _ => rfl }
  | .literal _, _ => { ends := fun _ _ => .inl ⟨_, rfl⟩, closed := fun _ _ _ => rfl }
  | .op (kind := kind) row applies, _ =>
      { ends := fun arguments _ => by
          show (∃ values, rowProcess model (.of row) kind applies arguments = .done values) ∨
            (∃ reason, rowProcess model (.of row) kind applies arguments = .halt reason)
          cases kind with
          | pure => exact .inl ⟨_, rfl⟩
          | restricted domain =>
              show (∃ values, definedProcess model (model.restricted (.of row) arguments) =
                  .done values) ∨
                (∃ reason, definedProcess model (model.restricted (.of row) arguments) =
                  .halt reason)
              cases model.restricted (.of row) arguments with
              | some values => exact .inl ⟨values, rfl⟩
              | none => exact .inr ⟨.undefined, rfl⟩
          | sampling => exact absurd applies Bool.false_ne_true
        closed := fun _ _ _ => rfl }
  | .call callee _, _ =>
      { ends := fun arguments _ => by
          show (∃ values, table.get callee arguments = .done values) ∨
            (∃ reason, table.get callee arguments = .halt reason)
          have silent := quiet callee arguments
          cases process : table.get callee arguments with
          | done values => exact .inl ⟨values, rfl⟩
          | halt reason => exact .inr ⟨reason, rfl⟩
          | call _ _ =>
              rw [process] at silent
              cases silent
        closed := fun _ _ _ => rfl }
  | .conditional .., shared => by cases shared
  | .match .., shared => by cases shared
  | .loop .., shared => by cases shared
  | .guard _, shared => by cases shared

/-- The regions of a `match` that captures every value of a context do what the old ones do
on the values of their captures. -/
theorem LocalOp.matchProcess_inward {Δ captures outputs : List Ty} (captured : Operands Δ captures)
    {entries : List (Entry (LocalDialect operations functions deployed) Δ)}
    {image : Environment model.Value Δ} (known : TableHolds (localMeaning model table) entries image) :
    ∀ (alternatives : List Ty)
      (old : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (new : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: Δ, outputs))),
      Plan.Agrees (localMeaning model table) (LocalOp.armsPlan outputs captured entries alternatives)
        old new →
      ∀ (value : Ty.Variant model.Carrier alternatives),
        matchProcess model Δ outputs alternatives new value (Operands.eval image (Operands.every Δ)) =
          matchProcess model captures outputs alternatives old value (Operands.eval image captured)
  | [], _, _, _, value => nomatch value
  | _ :: _, .cons _ _, .cons _ _, agrees, .inl payload =>
      Plan.agrees_inward (localMeaning model table) captured known _ _ agrees.1 (.cons payload .nil)
  | _ :: rest, .cons _ old, .cons _ new, agrees, .inr later =>
      LocalOp.matchProcess_inward captured known rest old new agrees.2 later

/-- A rebuilt local operation whose regions agree with the old ones is the operation. -/
theorem LocalOp.reopen_denote {Δ : List Ty} :
    ∀ (op : LocalOp operations functions deployed) (arguments : Operands Δ op.arguments)
      (entries : List (Entry (LocalDialect operations functions deployed) Δ))
      (image : Environment model.Value Δ),
      TableHolds (localMeaning model table) entries image →
      ∀ (old : Values (RegionFunction model.Value (Effects model)) op.regions)
        (bodies : Regions (LocalDialect operations functions deployed)
          (LocalOp.reopen op arguments entries).regions),
        Plan.Agrees (localMeaning model table) (LocalOp.reopen op arguments entries).plan old
          (bodies.denote (localMeaning model table)) →
        ∀ {out : List Ty}
          (rest : Region (LocalDialect operations functions deployed) (bindAll Δ op.results) out),
          ((LocalOp.reopen op arguments entries).build bodies rest).denote
              (localMeaning model table) image =
            (localOperation model table op (Operands.eval image arguments) old).bind fun values =>
              rest.denote (localMeaning model table) (Environment.bindAll image values)
  | .conditional captures outputs, .cons condition captured, entries, image, known,
      .cons onTrue (.cons onFalse .nil), .cons first (.cons second .nil), agrees, _, rest => by
      have true_ := Plan.agrees_inward (own := []) (localMeaning model table) captured known onTrue
        (fun values => first.denote (localMeaning model table) (Environment.ofValues values))
        agrees.1 .nil
      have false_ := Plan.agrees_inward (own := []) (localMeaning model table) captured known onFalse
        (fun values => second.denote (localMeaning model table) (Environment.ofValues values))
        agrees.2.1 .nil
      show (cond (image condition)
          (first.denote (localMeaning model table)
            (Environment.ofValues (Operands.eval image (Operands.every Δ))))
          (second.denote (localMeaning model table)
            (Environment.ofValues (Operands.eval image (Operands.every Δ))))).bind _ =
        (cond (image condition) (onTrue (Operands.eval image captured))
          (onFalse (Operands.eval image captured))).bind _
      rw [show first.denote (localMeaning model table)
            (Environment.ofValues (Operands.eval image (Operands.every Δ))) =
          onTrue (Operands.eval image captured) from true_,
        show second.denote (localMeaning model table)
            (Environment.ofValues (Operands.eval image (Operands.every Δ))) =
          onFalse (Operands.eval image captured) from false_]
  | .match declaration alternatives captures outputs, .cons value captured, entries, image, known,
      old, bodies, agrees, _, rest => by
      show (matchProcess model Δ outputs alternatives (bodies.denote (localMeaning model table))
          (image value) (Operands.eval image (Operands.every Δ))).bind _ =
        (matchProcess model captures outputs alternatives old (image value)
          (Operands.eval image captured)).bind _
      rw [LocalOp.matchProcess_inward captured known alternatives old _ agrees (image value)]
  | .loop (.static count) carried collected captures, arguments, entries, image, known,
      .cons body .nil, .cons region .nil, agrees, _, rest => by
      have step : loopStep model carried collected Δ
            (((Regions.cons region Regions.nil).denote (localMeaning model table)).get .here)
            (Operands.eval image (Operands.every Δ)) =
          loopStep model carried collected captures body
            (Operands.eval image (arguments.split carried).2) := by
        funext iteration state
        exact Plan.agrees_inward (localMeaning model table) (arguments.split carried).2 known _ _
          agrees.1 (Values.cons (ty := Ty.nat) iteration state)
      have left : (Operands.eval image
            ((arguments.split carried).1.append (Operands.every Δ))).split carried =
          (Operands.eval image (arguments.split carried).1,
            Operands.eval image (Operands.every Δ)) := by
        rw [Operands.eval_append, Values.split_append]
      have right := Operands.eval_split image carried arguments
      show (staticLoopProcess model count carried collected Δ _
          ((Operands.eval image ((arguments.split carried).1.append (Operands.every Δ))).split
            carried).1
          ((Operands.eval image ((arguments.split carried).1.append (Operands.every Δ))).split
            carried).2).bind _ =
        (staticLoopProcess model count carried collected captures body
          ((Operands.eval image arguments).split carried).1
          ((Operands.eval image arguments).split carried).2).bind _
      rw [left, right]
      unfold staticLoopProcess
      rw [step]
  | .loop (.runtime maximum) carried collected captures, .cons count arguments, entries, image,
      known, .cons body .nil, .cons region .nil, agrees, _, rest => by
      have step : loopStep model carried collected Δ
            (((Regions.cons region Regions.nil).denote (localMeaning model table)).get .here)
            (Operands.eval image (Operands.every Δ)) =
          loopStep model carried collected captures body
            (Operands.eval image (arguments.split carried).2) := by
        funext iteration state
        exact Plan.agrees_inward (localMeaning model table) (arguments.split carried).2 known _ _
          agrees.1 (Values.cons (ty := Ty.nat) iteration state)
      have left : (Operands.eval image
            ((arguments.split carried).1.append (Operands.every Δ))).split carried =
          (Operands.eval image (arguments.split carried).1,
            Operands.eval image (Operands.every Δ)) := by
        rw [Operands.eval_append, Values.split_append]
      have right := Operands.eval_split image carried arguments
      show (loopProcess model maximum carried collected Δ _ (image count)
          ((Operands.eval image ((arguments.split carried).1.append (Operands.every Δ))).split
            carried).1
          ((Operands.eval image ((arguments.split carried).1.append (Operands.every Δ))).split
            carried).2).bind _ =
        (loopProcess model maximum carried collected captures body (image count)
          ((Operands.eval image arguments).split carried).1
          ((Operands.eval image arguments).split carried).2).bind _
      rw [left, right]
      unfold loopProcess
      rw [step]
  | .op _ _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .call _ _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .guard _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .literal _, _, _, _, _, _, .nil, _, _, _ => rfl
  | .builtin _, _, _, _, _, _, .nil, _, _, _ => rfl

end Sound

/-- What the local dialect gives the normal form. -/
@[expose] def localNormalizer : Normalizer (LocalDialect operations functions deployed) :=
  ⟨LocalOp.same, LocalOp.reopen⟩

/-- The choices of the local dialect are sound for the meaning of local code, over functions
that perform no effect. -/
theorem localNormalizer_sound {model : Model} {table : FunctionTable model functions}
    (quiet : QuietTable table) :
    (localNormalizer (operations := operations) (deployed := deployed)).Sound
      (localMeaning model table) :=
  ⟨LocalOp.same_deterministic quiet, fun op arguments entries image known old bodies agrees _ rest =>
    LocalOp.reopen_denote op arguments entries image known old bodies agrees rest⟩

end Zkc.Core

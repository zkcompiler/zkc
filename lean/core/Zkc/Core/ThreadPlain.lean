module

public import Zkc.Core.ThreadMeaning
public import Zkc.Core.ExpandMeaning

public section

/-! What a threading step leaves alone.

Three facts that the structural theorem of threading uses for the parts of a program that
a step does not rewrite.

- **Local code performs no effect.** A process without an effect is `Quiet`. When every
  function of a table is quiet, so is every local operation and every local region
  (`localOperation_quiet`), and the table of the functions of a program is
  (`Functions.table_quiet`). A handler therefore passes local work as it is.
- **A handler passes a process** (`Passes`) when interpreting the process from a state
  is the process itself, with the state returned unchanged. A quiet process is passed by
  every handler, and passing is kept by sequencing.
- **A region that a step copies has the meaning it had** (`plainRegion_meaning`), for
  every side: the copy names the callees' images with their own headers, which have the
  callees' meanings. With identities that survive the step, the two processes are equal;
  no site is renumbered.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace PIR

variable {I : Signature} {A B S : Type}

/-- A process that performs no effect: it returns or stops. -/
@[expose] def Process.Quiet : Process I A → Prop
  | .done _ => True
  | .halt _ => True
  | .call _ _ => False

theorem Process.Quiet.bind {source : Process I A} {next : A → Process I B}
    (quiet : source.Quiet) (quietNext : ∀ value, (next value).Quiet) : (source.bind next).Quiet := by
  cases source with
  | done value => exact quietNext value
  | halt why => trivial
  | call op tail => cases quiet


/-- A handler passes a process: interpreted from a state, it is the process itself and
the state is unchanged. -/
@[expose] def Passes (handler : StatefulInterpretation I I S) (source : Process I A) : Prop :=
  ∀ state : S, source.interpretWith handler state = source.bind fun value => .done (value, state)

/-- Every handler passes a process without an effect. -/
theorem Process.Quiet.passes (handler : StatefulInterpretation I I S) {source : Process I A}
    (quiet : source.Quiet) : Passes handler source := by
  intro state
  cases source with
  | done value => rfl
  | halt why => rfl
  | call op tail => cases quiet

theorem Passes.done (handler : StatefulInterpretation I I S) (value : A) :
    Passes handler (.done value : Process I A) := fun _ => rfl

theorem Passes.halt (handler : StatefulInterpretation I I S) (why : Stop) :
    Passes handler (.halt why : Process I A) := fun _ => rfl

/-- A passed process followed by passed processes is passed. -/
theorem Passes.bind {handler : StatefulInterpretation I I S} {source : Process I A}
    {next : A → Process I B} (passes : Passes handler source)
    (passesNext : ∀ value, Passes handler (next value)) : Passes handler (source.bind next) := by
  intro state
  rw [Process.interpretWith_bind, passes state, Process.bind_assoc, Process.bind_assoc]
  congr 1
  funext value
  exact passesNext value state


end PIR

namespace Zkc.Core

/-- A handler passes the iterations of a step that it passes. -/
theorem iterations_passes {I : PIR.Signature} {S State Produced : Type} {Collected : Nat → Type}
    {handler : PIR.StatefulInterpretation I I S}
    {step : Nat → State → PIR.Process I Produced} {carry : Produced → State}
    {push : (done : Nat) → Produced → Collected done → Collected (done + 1)}
    (passes : ∀ iteration state, PIR.Passes handler (step iteration state)) :
    ∀ (remaining done : Nat) (state : State) (earlier : Collected done),
      PIR.Passes handler (iterations step carry push remaining done state earlier)
  | 0, _, state, earlier => PIR.Passes.done handler (state, earlier)
  | remaining + 1, done, state, _ =>
      (passes done state).bind fun _ => iterations_passes passes remaining (done + 1) _ _

open Zkc.Source

/-! ## Local code performs no effect -/

section Quiet

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- Every function of the table performs no effect. -/
@[expose] def QuietTable (table : FunctionTable model functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header)
    (arguments : Values model.Value header.inputs), (table.get callee arguments).Quiet

/-- Every region function of a list performs no effect. -/
@[expose] def QuietRegions : {signatures : List (List Ty × List Ty)} →
    Values (RegionFunction model.Value (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: _, .cons body rest => (∀ values, (body values).Quiet) ∧ QuietRegions rest

theorem partialProcess_quiet {A : Type} (result : Except Reason A) :
    (partialProcess model result).Quiet := by
  cases result <;> trivial

theorem definedProcess_quiet {A : Type} (result : Option A) :
    (definedProcess model result).Quiet := by
  cases result <;> trivial

theorem rowProcess_quiet (row : OperationRow) :
    ∀ (kind : OperationKind)
      (applies : OperationSignature.applies ⟨row.inputs, row.outputs, kind⟩ = true)
      (arguments : Values model.Value row.inputs),
      (rowProcess model row kind applies arguments).Quiet
  | .pure, _, _ => trivial
  | .restricted _, _, _ => definedProcess_quiet _
  | .sampling, applies, _ => absurd applies Bool.false_ne_true

/-- A `match` over quiet regions performs no effect. -/
theorem matchProcess_quiet {captures outputs : List Ty} :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction model.Value (Effects model))
        (alternatives.map fun payload => (payload :: captures, outputs)))
      (value : Ty.Variant model.Carrier alternatives) (captured : Values model.Value captures),
      QuietRegions regions →
        (matchProcess model captures outputs alternatives regions value captured).Quiet
  | [], _, value, _, _ => nomatch value
  | _ :: _, .cons _ _, .inl _, _, quietRegions => quietRegions.1 _
  | _ :: rest, .cons _ tail, .inr later, captured, quietRegions =>
      matchProcess_quiet rest tail later captured quietRegions.2

/-- The iterations of a loop whose step performs no effect perform none. -/
theorem loopIterations_quiet {carried collected : List Ty}
    {step : Nat → Values model.Value carried →
      PIR.Process (Effects model) (Values model.Value (collected ++ carried))}
    (quiet : ∀ iteration state, (step iteration state).Quiet) :
    ∀ (remaining done : Nat) (state : Values model.Value carried)
      (earlier : Values model.Value (collectedSequences (some done) collected)),
      (loopIterations model carried collected step remaining done state earlier).Quiet
  | 0, _, _, _ => trivial
  | remaining + 1, done, state, earlier =>
      PIR.Process.Quiet.bind (quiet done state) fun _ =>
        loopIterations_quiet quiet remaining (done + 1) _ _

/-- A local operation over quiet functions and quiet regions performs no effect. -/
theorem localOperation_quiet {table : FunctionTable model functions} (quiet : QuietTable table) :
    ∀ (op : LocalOp operations functions deployed) (arguments : Values model.Value op.arguments)
      (regions : Values (RegionFunction model.Value (Effects model)) op.regions),
      QuietRegions regions → (localOperation model table op arguments regions).Quiet
  | .op (kind := kind) row applies, arguments, _, _ => by
      show (rowProcess model (.of row) kind applies arguments).Quiet
      exact rowProcess_quiet (model := model) (OperationRow.of row) kind applies arguments
  | .call callee _, arguments, _, _ => quiet callee arguments
  | .conditional .., arguments, .cons onTrue (.cons onFalse .nil), quietRegions => by
      show PIR.Process.Quiet (cond (arguments.get .here) (onTrue arguments.tail)
        (onFalse arguments.tail))
      cases arguments.get .here
      · exact quietRegions.2.1 _
      · exact quietRegions.1 _
  | .match _ alternatives captures outputs, arguments, regions, quietRegions =>
      matchProcess_quiet alternatives regions (arguments.get .here) arguments.tail quietRegions
  | .loop (.static count) carried collected captures, arguments, .cons body .nil,
      quietRegions => by
      show (staticLoopProcess model count carried collected captures body _ _).Quiet
      exact PIR.Process.Quiet.bind
        (loopIterations_quiet (fun _ _ => quietRegions.1 _) _ _ _ _) fun _ => trivial
  | .loop (.runtime maximum) carried collected captures, arguments, .cons body .nil,
      quietRegions => by
      show (loopProcess model maximum carried collected captures body _ _ _).Quiet
      unfold loopProcess
      cases withinMaximum (arguments.get .here) maximum
      · trivial
      · exact PIR.Process.Quiet.bind
          (loopIterations_quiet (fun _ _ => quietRegions.1 _) _ _ _ _) fun _ => trivial
  | .guard reason, arguments, _, _ => by
      have either : ∀ condition : Bool, PIR.Process.Quiet
          (cond condition (PIR.Process.done (Values.nil : Values model.Value []))
            (PIR.Process.halt reason.stop : PIR.Process (Effects model) _)) := by
        intro condition
        cases condition <;> trivial
      exact either _
  | .literal value, _, _, _ => trivial
  | .builtin operation, arguments, _, _ => definedProcess_quiet _

mutual
  /-- A local region over quiet functions performs no effect. -/
  theorem localRegion_quiet {table : FunctionTable model functions} (quiet : QuietTable table)
      {Γ out : List Ty} :
      ∀ (region : Region (LocalDialect operations functions deployed) Γ out)
        (env : Environment model.Value Γ), (region.denote (localMeaning model table) env).Quiet
    | .ret _, _ => trivial
    | .stop _, _ => trivial
    | .letOp op arguments bodies next, env =>
        PIR.Process.Quiet.bind
          (localOperation_quiet quiet op _ _ (localRegions_quiet quiet bodies))
          fun values => localRegion_quiet quiet next _
    | .bind body next, env =>
        PIR.Process.Quiet.bind (localRegion_quiet quiet body env)
          fun values => localRegion_quiet quiet next _

  theorem localRegions_quiet {table : FunctionTable model functions} (quiet : QuietTable table)
      {signatures : List (List Ty × List Ty)} :
      ∀ (regions : Regions (LocalDialect operations functions deployed) signatures),
        QuietRegions (regions.denote (localMeaning model table))
    | .nil => trivial
    | .cons body tail =>
        ⟨fun values => localRegion_quiet quiet body _, localRegions_quiet quiet tail⟩
end

/-- The functions of a program perform no effect. -/
theorem Functions.table_quiet {typeTable : TypeTable} :
    ∀ {functions : List FunctionHeader} (program : Functions typeTable operations functions),
      QuietTable (program.table model)
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc earlier definition wellFormed => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          (Values.get ((Functions.snoc earlier definition wellFormed).table model) callee
            arguments).Quiet)
        (fun arguments => localRegion_quiet (Functions.table_quiet earlier) definition.body _)
        (fun callee => Functions.table_quiet earlier callee) callee
  | _, .opaque earlier other named => by
      intro callee
      exact Var.cases
        (motive := fun header callee => ∀ arguments : Values model.Value header.inputs,
          (Values.get ((Functions.opaque earlier other named).table model) callee arguments).Quiet)
        (fun arguments => partialProcess_quiet _)
        (fun callee => Functions.table_quiet earlier callee) callee

/-- A role's step over a computation without an effect performs no effect. -/
theorem performStep_quiet {inputs outputs : List Ty}
    {run : Values model.Value inputs → PIR.Process (Effects model) (Values model.Value outputs)}
    (quiet : ∀ values, (run values).Quiet) :
    ∀ (present : Bool) (held : Values (fun type => Held (model.Value type) present) inputs),
      (performStep model run present held).Quiet
  | true, held => quiet held
  | false, _ => trivial

variable {protocols : List ProtocolHeader}

/-- The local work of a role performs no effect for any side. -/
theorem at_quiet {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    (label : Nat → Site) (table : ProtocolTable model protocols) (side : Side) (role : Nat)
    (op : LocalOp operations functions deployed)
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (arguments : Values (SideValue model side) (Located.atRole role op.arguments)) :
    (labelledOperation model label functionTable table side (.at role op bodies) arguments
      .nil).Quiet := by
  exact PIR.Process.Quiet.bind
    (performStep_quiet (fun values => localOperation_quiet quiet op values _
      (localRegions_quiet quiet bodies)) (side role) _) fun _ => trivial

end Quiet

/-! ## A copied region -/

section Plain

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {newTable : ProtocolTable model new} {table : CalleeTable t.header old new}
  {label : Nat → Site} {side : Side}

/-- The image of a callee with the callee's own header has the callee's meaning. -/
@[expose] def PlainCallees (table : CalleeTable t.header old new) (oldTable : ProtocolTable model old)
    (newTable : ProtocolTable model new) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var old header) (image : Var new header),
    table.find callee none = some image → newTable.get image = oldTable.get callee

/-- The environments of a closed region's inputs agree across the renaming of the inputs
to themselves. -/
theorem Renaming.identity_agrees {Ty : Type} {Value : Ty → Type} (inputs : List Ty)
    (values : Values Value inputs) :
    (Renaming.identity inputs).Agrees (Environment.ofValues values) (Environment.ofValues values) :=
  Renaming.Agrees.keepAll (rename := Mapping.start (Δ := ([] : List Ty)) 0 rfl)
    (old := Environment.empty) (new := Environment.empty) (fun reference => reference.elimNil)
    values

mutual
  /-- A copied region is the region: over the images of the callees, in environments that
  agree across the renaming, it has the same process for every side. -/
  theorem plainRegion_meaning (callees : PlainCallees table oldTable newTable)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        {Δ : List Located} (rename : Renaming Γ Δ)
        (copy : Region (ProtocolDialect operations functions new deployed) Δ out),
        plainRegion t table region rename = .ok copy →
        ∀ (env : Environment (SideValue model side) Γ) (env' : Environment (SideValue model side) Δ),
          rename.Agrees env env' →
          copy.denote (labelledMeaning model label functionTable newTable side) env' =
            region.denote (labelledMeaning model label functionTable oldTable side) env
    | .ret values, _, rename, copy, plain, env, env', agrees => by
        simp only [plainRegion, Except.ok.injEq] at plain
        subst plain
        exact congrArg PIR.Process.done (agrees.operands values)
    | .stop reason, _, rename, copy, plain, env, env', agrees => by
        simp only [plainRegion, Except.ok.injEq] at plain
        subst plain
        rfl
    | .bind (mid := mid) body rest, _, rename, copy, plain, env, env', agrees => by
        unfold plainRegion at plain
        split at plain
        · rename_i body' rest' plainBody plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          exact bind_congr (plainRegion_meaning callees body rename body' plainBody env env' agrees)
            fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
              (agrees.keepAll values)
        · cases plain
        · cases plain
    | .letOp (.at role op bodies) arguments nested rest, _, rename, copy, plain, env, env',
        agrees => by
        cases nested
        unfold plainRegion at plain
        split at plain
        · rename_i rest' plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side (.at role op bodies)
              (Operands.eval env' (rename.operands arguments)) .nil = _
          rw [agrees.operands]
          rfl
        · cases plain
    | .letOp (.exchange sender receiver site type) arguments nested rest, _, rename, copy, plain,
        env, env', agrees => by
        cases nested
        unfold plainRegion at plain
        split at plain
        · rename_i rest' plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side
              (.exchange sender receiver site type)
              (Operands.eval env' (rename.operands arguments)) .nil = _
          rw [agrees.operands]
          rfl
        · cases plain
    | .letOp (.draw owner receivers site law populated) arguments nested rest, _, rename, copy, plain, env,
        env', agrees => by
        cases nested
        unfold plainRegion at plain
        split at plain
        · rename_i rest' plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side
              (.draw owner receivers site law populated)
              (Operands.eval env' (rename.operands arguments)) .nil = _
          rw [agrees.operands]
          rfl
        · cases plain
    | .letOp (.sample owner site law populated) arguments nested rest, _, rename, copy, plain, env, env',
        agrees => by
        cases nested
        unfold plainRegion at plain
        split at plain
        · rename_i rest' plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side (.sample owner site law populated)
              (Operands.eval env' (rename.operands arguments)) .nil = _
          rw [agrees.operands]
          rfl
        · cases plain
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, _, rename,
        copy, plain, env, env', agrees => by
        unfold plainRegion at plain
        split at plain
        · rename_i bodies' rest' plainBodies plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side
              (.repeat participants count carried collected captures covered)
              (Operands.eval env' (rename.operands arguments))
              (bodies'.denote (labelledMeaning model label functionTable newTable side)) = _
          rw [agrees.operands, plainRegions_meaning callees bodies bodies' plainBodies]
          rfl
        · cases plain
        · cases plain
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _, rename,
        copy, plain, env, env', agrees => by
        unfold plainRegion at plain
        split at plain
        · rename_i bodies' rest' plainBodies plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show labelledOperation model label functionTable newTable side
              (.choose participants tag captures outputs covered)
              (Operands.eval env' (rename.operands arguments))
              (bodies'.denote (labelledMeaning model label functionTable newTable side)) = _
          rw [agrees.operands, plainRegions_meaning callees bodies bodies' plainBodies]
          rfl
        · cases plain
        · cases plain
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, _,
        rename, copy, plain, env, env', agrees => by
        cases nested
        unfold plainRegion at plain
        split at plain
        · rename_i image rest' found plainRest
          simp only [Except.ok.injEq] at plain
          subst plain
          refine bind_congr ?_ fun values => plainRegion_meaning callees rest _ rest' plainRest _ _
            (agrees.keepAll values)
          show ((newTable.get image) (label site).below (Side.preimage roleMap side)
              (unmapValues (F := SideValue model side) (Located.rename roleMap) header.inputs
                (Operands.eval env' (rename.operands arguments)))).bind _ = _
          rw [agrees.operands, callees callee image found]
          rfl
        · cases plain
        · cases plain

  /-- Copied closed regions are the regions. -/
  theorem plainRegions_meaning (callees : PlainCallees table oldTable newTable)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (copies : Regions (ProtocolDialect operations functions new deployed) signatures),
        plainRegions t table regions = .ok copies →
          copies.denote (labelledMeaning model label functionTable newTable side) =
            regions.denote (labelledMeaning model label functionTable oldTable side)
    | .nil, copies, plain => by
        simp only [plainRegions, Except.ok.injEq] at plain
        subst plain
        rfl
    | .cons (inputs := inputs) body tail, copies, plain => by
        unfold plainRegions at plain
        split at plain
        · rename_i body' tail' plainBody plainTail
          simp only [Except.ok.injEq] at plain
          subst plain
          exact cons_congr
            (funext fun values => plainRegion_meaning callees body _ body' plainBody _ _
              (Renaming.identity_agrees inputs values))
            (plainRegions_meaning callees tail tail' plainTail)
        · cases plain
        · cases plain
end

end Plain

end Zkc.Core

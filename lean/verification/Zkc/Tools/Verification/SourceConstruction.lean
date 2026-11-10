module

public import Zkc.Verification.Construction.Source
public import Zkc.Tools.IR.StructuredSource.Bindings
public import Zkc.Tools.Protocol.Construction
public meta import Zkc.IR.Source.Structured.UnitViews

/-! Source selection installs structural WP rules in the ordinary specification database.
The rules are indexed by the actual admitted unit and signature. A companion proves the named
body specification once; call arguments, table framing and lexical placement stay automatic. -/

public meta section
open Lean Elab Command
open PIR Zkc.Source Zkc.Source.Structured Std.WP
attribute [construction_simp] Zkc.Source.Values.get_append Zkc.Source.Values.split
  Zkc.Source.Values.split_append id_eq

attribute [construction_simp] maskValues ProtocolContext.mapScopes Participant.restrict

namespace Zkc.Tools.Verification

elab "bind_source_helper " name:ident " from " imported:term " named " symbol:str : command =>
    UnitViews.synchronously do
  elabCommand (← `(source_helper $name from $imported named $symbol))
  if (← get).messages.hasErrors then throwError "source helper binding failed"
  let signature := mkIdent (name.getId ++ `signature)
  let body := mkIdent (name.getId ++ `body)
  let member := mkIdent (name.getId ++ `member)
  let closed := mkIdent (name.getId ++ `closed)
  let component := mkIdent (name.getId ++ `components)
  UnitViews.emit { command := "source installation" } (← `(
    @[spec] theorem $closed (model : DomainModel) {I : Signature} {Pred EPred : Type}
        [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
        (observations : SiteObservations I) (arguments : Values model.Value ($signature).inputs)
        (post : Values model.Value ($signature).outputs → Pred) (stopped : EPred) :
        ⦃wp (($body).denote (Evaluation.meaningOn model observations
          (($imported).program.payload.definitions.foldl
            (Evaluation.extendMeaningsOn model observations) [])) arguments.get) post stopped⦄
          invoke (($imported).program.payload.definitions.foldl
            (Evaluation.extendMeaningsOn model observations) []) $signature arguments
          ⦃post; stopped⦄ :=
      Zkc.Verification.Construction.helper model observations ($imported).program.payload
        $name $member arguments post stopped))
  UnitViews.emit { command := "source installation" } (← `(
    @[spec] theorem $component (model : DomainModel) {I : Signature} {Pred EPred : Type}
        [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
        (observations : SiteObservations I)
        (arguments : Values (Component model.Value) ($signature).inputs)
        (post : Values (Component model.Value) ($signature).outputs → Pred) (stopped : EPred) :
        ⦃wp ((RoleFamily.sequence arguments).elim
          (($body).component
            (Evaluation.meaningOn model observations
              (($imported).program.payload.definitions.foldl
                (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).closed)
            (Evaluation.componentOperationOn model observations
              (($imported).program.payload.definitions.foldl
                (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩))
            arguments.get)
          (fun values => (invoke (($imported).program.payload.definitions.foldl
            (Evaluation.extendMeaningsOn model observations) []) $signature values).bind
              (fun results => .done results.present))) post stopped⦄
          invoke (($imported).program.payload.definitions.foldl
            (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).components
            $signature arguments ⦃post; stopped⦄ := by
      exact Zkc.Verification.Construction.component model observations ($imported).program.payload
        $name $member arguments post stopped))

elab "bind_source_protocol " name:ident " from " imported:term " named " symbol:str : command =>
    UnitViews.synchronously do
  elabCommand (← `(source_protocol $name from $imported named $symbol))
  if (← get).messages.hasErrors then throwError "source protocol binding failed"
  let signature := mkIdent (name.getId ++ `signature)
  let body := mkIdent (name.getId ++ `body)
  let member := mkIdent (name.getId ++ `member)
  let installed := mkIdent (name.getId ++ `installed)
  UnitViews.emit { command := "source installation" } (← `(
    @[spec] theorem $installed (model : DomainModel) {I : Signature} {Pred EPred : Type}
        [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
        (observations : SiteObservations I)
        (actions : OperationInterpretation (participantInterfaceOn model.toCarriers) I)
        (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
        (iterations : IterationObservations I) (context : ProtocolContext) (self : Nat)
        (arguments : Values (Component model.Value) ($signature).inputs)
        (post : Values (Component model.Value) ($signature).outputs → Pred) (stopped : EPred) :
        ⦃wp (($body).denote
          (participantMeaningWithOn model observations actions helpers self
            (($imported).program.payload.protocols.foldl (fun table definition =>
              extendProtocolTableOn model observations actions helpers table definition iterations) [])
            context iterations)
          (maskValues self (context.mapScopes ($name).inputScopes) arguments).get)
          (fun values => post (maskValues self (context.mapScopes ($name).outputScopes) values))
          stopped⦄
          invokeProtocol (($imported).program.payload.protocols.foldl (fun table definition =>
            extendProtocolTableOn model observations actions helpers table definition iterations) [])
            $signature context self arguments ⦃post; stopped⦄ :=
      Zkc.Verification.Construction.protocol model observations ($imported).program.payload
        actions helpers iterations $name $member context self arguments post stopped))

end Zkc.Tools.Verification

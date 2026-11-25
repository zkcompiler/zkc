module

public import Zkc.Frontend.Written.Package

public section
set_option autoImplicit false

namespace Zkc.Frontend
open Core

private def clauseText {Raw : Type} (op : Raw → String) (clause : BodyAnalysis.ContractClause Raw) :=
  Written.exprWith op clause.assertion ++
    (clause.staticBound.map (fun bound => s!" with bound {Written.exprWith op bound}")).getD ""

private def detailText {T Raw : Type} (ty : T → String) (op : Raw → String) : Detail T Raw → String
  | .name n => s!"name {n}"
  | .types expected found => s!"expected {Subject.Print.list (expected.map ty)}, found {Subject.Print.list (found.map ty)}"
  | .type t => ty t
  | .number expected found => s!"expected {expected}, found {found}"
  | .operation written => op written
  | .callee key found => s!"callee {key.number} has {found} preceding definitions"
  | .given ts => s!"given {Subject.Print.list (ts.map ty)}"
  | .key k => s!"key {k.number}"
  | .stops header body => s!"stops in header {header}, in body {body}"
  | .uses n found | .around n found => s!"{found} uses of name {n}"
  | .unjustified written q known =>
    s!"{op written} requires {Written.requirementWith op q}, known ranges {reprStr known}"
  | .unestablished q known => s!"unproved {Written.requirementWith op q}, known ranges {reprStr known}"
  | .requirement q => Written.requirementWith op q
  | .contractAssertion c => clauseText op c
  | .unjustifiedAssertion written c => s!"{op written} requires {clauseText op c}"
  | .annotationSite site => Written.annotationSite site
  | .premise site i => s!"premise {i} at {Written.annotationSite site}"
  | .invariant site i preservation =>
    s!"invariant {i} at {Written.annotationSite site}, preservation {preservation}"
  | .nothing => ""

private def roleText {b : Zkc.Vocabulary.Project.Bindings} : RoleRaw b.vocabulary → String
  | .compute roles op => s!"compute {roles}: {Written.localRaw (b := b) op}"
  | .absent items => s!"absent {Written.located (b := b) items}"
  | .effect part result =>
    let action := match part with
      | .give kind peers => s!"give {Written.flowKind kind} to {peers}"
      | .get kind peer => s!"get {Written.flowKind kind} from {peer}"
      | .own kind peers => s!"own {Written.givenKind (b := b) kind} with {peers}"
      | .hear kind peer => s!"hear {Written.givenKind (b := b) kind} from {peer}"
    s!"{action}, result {Written.located (b := b) [result]}"
  | .keep holders => s!"keep {holders}"
  | .apply key roles => s!"apply {key.number} at {roles}"

/-- Render the original refusals at the point where a client asks for diagnostic text. -/
def SourcePackage.describeRefusals (p : SourcePackage)
    (errors : List (AdmissionRefusal p.bindings.vocabulary)) : String :=
  let describe {T Raw : Type} (stage : String) (ty : T → String) (op : Raw → String)
      (r : Core.Refusal T Raw) :=
    let detail := detailText ty op r.detail
    let place := s!"{stage}: {reprStr r.rule} at {reprStr r.place}"
    if detail.isEmpty then place else s!"{place}: {detail}"
  let located := fun t => Written.located (b := p.bindings) [t]
  "; ".intercalate <| errors.map fun
    | .definition (.fn r) => describe "function" Subject.Print.linkedTy (Written.localRaw (b := p.bindings)) r
    | .definition (.protocol r) => describe "protocol" located (Written.protocolRaw (b := p.bindings)) r
    | .projection r => describe "projection" located (roleText (b := p.bindings)) r
    | .association r => describe "association" Subject.Print.linkedTy (Written.localRaw (b := p.bindings)) r

end Zkc.Frontend

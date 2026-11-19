module

public import Zkc.Core.Program.DefinitionChecks
public import Zkc.Core.Admission.Admit
public import Zkc.Frontend.Emit.Reports
public import Zkc.Frontend.Written.LeanTerms

@[expose] public section
set_option autoImplicit false

/-!
An admitted package as a Lean module.

The module states the package twice. The program by names is written from what the frontend
gave to admission (`stored`). The typed program is written from what admission returned
(`installed`): every definition against the headers of those before it, with each proof argument
as a decision that Lean makes again. The kernel then checks, one definition at a time, that the
erasure of the typed definition is the definition by names (`erased<key>`), so that the program
of any admission of `stored` is `installed` (`readback`).

The traversal follows the constructors of the Core program: every definition, instruction and
operation has a case, and no case reads a source identifier or the shape of a protocol.

Every computation that the module needs is a decision of the kernel (`by decide +kernel`): that a
context has a name at a type, that the vocabulary has a row at a signature, who holds a value.
Each type that a decision reads is written out, so that no decision waits for Lean to infer one.
Lean's unifier is asked only to compare written values. When the unifier was asked to find each
variable in its context, the root of the GKR example, whose vocabulary has project primitives,
took between a quarter of a second and a second for each variable and did not end within twenty
times Lean's default limit; with the kernel's decisions the same module is checked in seconds.

A module that holds a printed package imports the modules of `packageImports`.
-/

namespace Zkc.Frontend.Written
open Core

/-! ## Small values -/

def namesTerm (xs : List Nat) : String := consList (xs.map toString)

/-- A variable by name. The kernel decides that the context has the name at the type that the
place of the variable asks for. Unification is not asked to find it: it would evaluate the
context again at every use, outside the kernel. -/
def varTerm (x : Nat) : String := s!"⟨{x}, by decide +kernel⟩"

def varsTerm (xs : List Nat) : String := consList (xs.map varTerm)

def reason : Reason → String
  | .reject => ".reject"
  | .abort => ".abort"
  | .exhausted => ".exhausted"
  | .refused => ".refused"

def flowKind : FlowKind → String
  | .message => ".message"
  | .rows => ".rows"
  | .opening => ".opening"

def member {α : Type} {items : List α} {a : α} : Member items a → String
  | .head => ".head"
  | .tail x => s!"(.tail {member x})"

def primitiveName (name : Emit.PrimitiveName) : String :=
  s!"(Zkc.Frontend.Emit.PrimitiveName.mk {reprStr name.name} ({reprStr name.arguments}))"

/-- A row of a linked vocabulary: a standard one, or a primitive that the project binds. -/
def linkedRowKey : Sum Zkc.Vocabulary.RowKey Emit.PrimitiveName → String
  | .inl k => s!"(.inl ({reprStr k}))"
  | .inr name => s!"(.inr {primitiveName name})"

section
variable {b : Emit.Bindings}

def rowKey (k : b.vocabulary.RowKey) : String := linkedRowKey k

def givenKind : GivenKind b.vocabulary → String
  | .coin law => s!"(.coin {lawKey law})"
  | .request service => s!"(.request {key service})"

def locatedTy (a : LTy b.vocabulary) : String := s!"⟨{ty a.ty}, {numbers a.holders}⟩"

def located (ts : List (LTy b.vocabulary)) : String := list (ts.map locatedTy)

def tyList (ts : List b.vocabulary.Ty) : String := list (ts.map ty)

/-! ## The program by names -/

def localRaw : LocalRaw b.vocabulary → String
  | .row k => s!"(.row {rowKey k})"
  | .owned name ts args => s!"(.owned ({reprStr name}) {tyList ts} {numbers args})"
  | .literal t data => s!"(.literal {ty t} {numbers data})"
  | .call callee => s!"(.call {key callee})"

def eventClass : EventClass b.vocabulary → String
  | .flow kind giver getters => s!"(.flow {flowKind kind} {giver} {numbers getters})"
  | .given kind owner hearers => s!"(.given {givenKind kind} {owner} {numbers hearers})"

def protocolRaw : ProtocolRaw b.vocabulary → String
  | .compute roles o => s!"(.compute {numbers roles} {localRaw o})"
  | .event cls t => s!"(.event {eventClass cls} {ty t})"
  | .narrow roles => s!"(.narrow {numbers roles})"
  | .apply callee roles => s!"(.apply {key callee} {numbers roles})"

end

def repeatTimes : Repeat → String
  | .fixed n => s!"(.fixed {n})"
  | .count name => s!"(.count {name})"

mutual
  /-- A region by names, for any operations and performers. -/
  partial def storedRegion {Op Who : Type} (op : Op → String) (who : Who → String) :
      Region Op Who → String
    | .mk ins steps outs =>
        let body := steps.map fun step => "\n    " ++ storedStep op who step
        s!"(.mk {numbers ins} [{",".intercalate body}] {numbers outs})"
  partial def storedStep {Op Who : Type} (op : Op → String) (who : Who → String) :
      Instruction Op Who → String
    | .op k out o vs => s!".op {key k} {numbers out} {op o} {numbers vs}"
    | .guard k w x why => s!".guard {key k} {who w} {x} {reason why}"
    | .choose k w x outs yes no =>
        s!".choose {key k} {who w} {x} {numbers outs} {storedRegion op who yes} {storedRegion op who no}"
    | .cases k w x outs arms =>
        s!".cases {key k} {who w} {x} {numbers outs} {list (arms.map (storedRegion op who))}"
    | .loop k w times carried outs body =>
        s!".loop {key k} {who w} {repeatTimes times} {numbers carried} {numbers outs} {storedRegion op who body}"
    | .block k number outs body =>
        s!".block {key k} {number} {numbers outs} {storedRegion op who body}"
    | .attempt k w outs body => s!".attempt {key k} {who w} {numbers outs} {storedRegion op who body}"
end

/-! ## Summaries and annotations of a function -/

section
variable {b : Emit.Bindings}

mutual
  def expr : BodyAnalysis.Expr (LocalRaw b.vocabulary) → String
    | .arg position => s!"(.arg {position})"
    | .apply written operands result => s!"(.apply {localRaw written} {exprs operands} {result})"
  def exprs : BodyAnalysis.Exprs (LocalRaw b.vocabulary) → String
    | .nil => ".nil"
    | .cons first others => s!"(.cons {expr first} {exprs others})"
end

def operand : Operand Empty → String
  | .arg position => s!"(.arg {position})"
  | .apply written _ => nomatch written

def requirement : Requirement Empty → String
  | .le x y => s!"(.le {operand x} {operand y})"
  | .lt x y => s!"(.lt {operand x} {operand y})"
  | .atLeast x n => s!"(.atLeast {operand x} {n})"
  | .below x n => s!"(.below {operand x} {n})"
  | .exactly x n => s!"(.exactly {operand x} {n})"
  | .difference x y n => s!"(.difference {operand x} {operand y} {n})"
  | .holds x => s!"(.holds {operand x})"
  | .bounded x => s!"(.bounded {operand x})"

def headerClause : HeaderClause b.vocabulary → String
  | .positional q => s!"(.positional {requirement q})"
  | .assertion c => s!"(.assertion ⟨{expr c.assertion}, {option expr c.staticBound}⟩)"

def headerSummary (s : HeaderSummary b.vocabulary) : String :=
  s!"⟨{list (s.requires.map headerClause)}, {list (s.ensures.map headerClause)}⟩"

def staticRegion : BodyAnalysis.StaticRegion → String
  | .root => ".root"
  | .body parent ordinal k => s!"(.body {staticRegion parent} {ordinal} {key k})"
  | .otherwise parent ordinal k => s!"(.otherwise {staticRegion parent} {ordinal} {key k})"
  | .arm parent ordinal => s!"(.arm {staticRegion parent} {ordinal})"
  | .block parent ordinal k number => s!"(.block {staticRegion parent} {ordinal} {key k} {number})"

def staticCursor (c : BodyAnalysis.StaticCursor) : String :=
  s!"⟨{staticRegion c.enclosing}, {c.ordinal}⟩"

def annotationSite : BodyAnalysis.AnnotationSite → String
  | .instruction c k => s!"(.instruction {staticCursor c} {key k})"
  | .block c k number => s!"(.block {staticCursor c} {key k} {number})"

def annotation : BodyAnalysis.Annotation (LocalRaw b.vocabulary) → String
  | .invariant uses assertions => s!"(.invariant {numbers uses} {list (assertions.map expr)})"
  | .step lemma names => s!"(.step {lemma} {numbers names})"
  | .fact uses assertion => s!"(.fact {numbers uses} {expr assertion})"

def annotations (notes : BodyAnalysis.Annotations (LocalRaw b.vocabulary)) : String :=
  list (notes.map fun (site, note) => s!"({annotationSite site}, {annotation note})")

/-- A definition by names, from what the frontend gave to admission. -/
def storedDefinition : Definition b.vocabulary → String
  | .fn k ins outs stop kernel summary body notes =>
      s!".fn {key k} {tyList ins} {tyList outs} {stop} {option key kernel} {headerSummary summary}\n  " ++
        s!"{storedRegion localRaw (fun _ => "()") body}\n  {annotations notes}"
  | .protocol k roles ins outs body =>
      s!".protocol {key k} {roles} {located ins} {located outs}\n  " ++
        storedRegion protocolRaw numbers body

/-! ## Typed operations -/

/-- An operation that the core owns, by its constructor. The vocabulary is written at each: the
type of an owned operation depends on its arguments, so Lean reads them before it knows the
vocabulary from the place of the operation. -/
def ownedOp {ins outs : List b.vocabulary.Ty} : OwnedOp b.vocabulary ins outs → String
  | .natAdd => "(OwnedOp.natAdd (V := V))"
  | .natSub => "(OwnedOp.natSub (V := V))"
  | .natMul => "(OwnedOp.natMul (V := V))"
  | .natDiv => "(OwnedOp.natDiv (V := V))"
  | .natRem => "(OwnedOp.natRem (V := V))"
  | .natPow => "(OwnedOp.natPow (V := V))"
  | .natEqual => "(OwnedOp.natEqual (V := V))"
  | .natLess => "(OwnedOp.natLess (V := V))"
  | .boolAnd => "(OwnedOp.boolAnd (V := V))"
  | .boolOr => "(OwnedOp.boolOr (V := V))"
  | .boolNot => "(OwnedOp.boolNot (V := V))"
  | .boolEqual => "(OwnedOp.boolEqual (V := V))"
  | .seqLength item size _ => s!"(OwnedOp.seqLength (V := V) {ty item} {option toString size} (by decide +kernel))"
  | .seqAt item size _ => s!"(OwnedOp.seqAt (V := V) {ty item} {option toString size} (by decide +kernel))"
  | .seqSlice item size result _ =>
      s!"(OwnedOp.seqSlice (V := V) {ty item} {option toString size} {option toString result} (by decide +kernel))"
  | .seqConcat item first second =>
      s!"(OwnedOp.seqConcat (V := V) {ty item} {option toString first} {option toString second})"
  | .seqFill item count _ => s!"(OwnedOp.seqFill (V := V) {ty item} {count} (by decide +kernel))"
  | .seqSized item size _ => s!"(OwnedOp.seqSized (V := V) {ty item} {size} (by decide +kernel))"
  | .natBelow bound => s!"(OwnedOp.natBelow (V := V) {bound})"
  | .seqUnsized item size => s!"(OwnedOp.seqUnsized (V := V) {ty item} {size})"
  | .finToNat bound => s!"(OwnedOp.finToNat (V := V) {bound})"
  | .finWiden bound wider _ => s!"(OwnedOp.finWiden (V := V) {bound} {wider} (by decide +kernel))"
  | .makeSeq item count => s!"(OwnedOp.makeSeq (V := V) {ty item} {count})"
  | .makeTuple items => s!"(OwnedOp.makeTuple (V := V) {tys items})"
  | .makeRecord k linear fields => s!"(OwnedOp.makeRecord (V := V) {key k} {linear} {tys fields})"
  | .getTuple items position _ => s!"(OwnedOp.getTuple (V := V) {tys items} {member position} (by decide +kernel))"
  | .getRecord k fields position _ =>
      s!"(OwnedOp.getRecord (V := V) {key k} {tys fields} {member position} (by decide +kernel))"
  | .takeSeq item count => s!"(OwnedOp.takeSeq (V := V) {ty item} {count})"
  | .takeTuple items => s!"(OwnedOp.takeTuple (V := V) {tys items})"
  | .takeRecord k linear fields => s!"(OwnedOp.takeRecord (V := V) {key k} {linear} {tys fields})"
  | .variant k alternatives position => s!"(OwnedOp.variant (V := V) {key k} {tys alternatives} {member position})"

/-- A local operation against the functions that `fnsName` names. A called function is the
header of its key, at its position among them. The signature of a row is written out and the
kernel decides that the vocabulary has it: the types of what a row returns are then written types,
and nothing after the row looks its signature up again. -/
def localOp {fns : List (FnHeader b.vocabulary)} {ins outs : List b.vocabulary.Ty}
    (fnsName : String) : LocalOp b.vocabulary fns ins outs → String
  | .row k signature _ =>
      let kind := match signature.kind with
        | .pure => ".pure"
        | .restricted domain => s!"(.restricted {rowKey domain})"
      s!"(LocalOp.row (V := V) (fns := {fnsName}) {rowKey k} " ++
        s!"⟨{tyList signature.ins}, {tyList signature.outs}, {kind}⟩ (by decide +kernel))"
  | .owned o => s!"(LocalOp.owned (V := V) (fns := {fnsName}) {ownedOp o})"
  | .literal t data _ =>
      s!"(LocalOp.literal (V := V) (fns := {fnsName}) {ty t} {numbers data} (by decide +kernel))"
  | .call (hdr := hdr) callee =>
      s!"(LocalOp.call (V := V) (fns := {fnsName}) (hdr := header{hdr.key.number}) {member callee})"

/-- An operation of a protocol against the headers that `headersName` names. -/
def protocolOp {hs : Headers b.vocabulary} {ins outs : List (LTy b.vocabulary)}
    (headersName : String) : ProtocolOp b.vocabulary hs ins outs → String
  | .compute who o operands _ _ =>
      s!"(ProtocolOp.compute (V := V) (hs := {headersName}) {numbers who} " ++
        s!"{localOp (headersName ++ ".fns") o} {located operands} rfl (by decide +kernel))"
  | .flow (τ := τ) (H := holders) kind giver getters _ _ =>
      s!"(ProtocolOp.flow (V := V) (hs := {headersName}) (τ := {ty τ}) (H := {numbers holders}) " ++
        s!"{flowKind kind} {giver} {numbers getters} (by decide +kernel) (by decide +kernel))"
  | .given kind owner hearers operands τ _ _ _ =>
      let typed := match kind with
        | .coin _ => "⟨_, rfl, rfl, rfl⟩"
        | .request _ => "rfl"
      s!"(ProtocolOp.given (V := V) (hs := {headersName}) {givenKind kind} {owner} {numbers hearers} " ++
        s!"{located operands} {ty τ} {typed} (by decide +kernel) (by decide +kernel))"
  | .narrow (τ := τ) (H := holders) who _ =>
      s!"(ProtocolOp.narrow (V := V) (hs := {headersName}) (τ := {ty τ}) (H := {numbers holders}) " ++
        s!"{numbers who} (by decide +kernel))"
  | .apply (hdr := hdr) callee roles _ _ operands _ =>
      s!"(ProtocolOp.apply (V := V) (hs := {headersName}) (hdr := header{hdr.key.number}) " ++
        s!"{member callee} {numbers roles} (by decide +kernel) rfl {located operands} " ++
        "(Fits.of_decision (by decide +kernel)))"

/-! ## Typed bodies -/

mutual
  /-- The body of a function, by the constructors of the term. -/
  partial def typedFn {fns : List (FnHeader b.vocabulary)} (fnsName : String) :
      {Γ : Ctx b.vocabulary.Ty} → {outs : List b.vocabulary.Ty} →
        Term (localDialect b.vocabulary fns) Γ outs → String
    | _, _, .ret vs => s!".ret {varsTerm vs.names}"
    | _, _, .step k (.op o args) ns rest =>
        s!".op {key k} {localOp fnsName o} {varsTerm args.names} {namesTerm ns.toList} <|\n" ++
          typedFn fnsName rest
    | _, _, .step k (.guard _ c _ why) _ rest =>
        s!".guard (t := .bool) {key k} () {varTerm c.name} rfl {reason why} <|\n" ++
          typedFn fnsName rest
    | _, _, .step k (.choose (mid := mid) _ c _ _ yes no) ns rest =>
        s!".choose (mid := {tyList mid}) (t := .bool) {key k} () {varTerm c.name} rfl " ++
          "(fun _ _ => trivial)\n" ++
          s!"({typedFn fnsName yes})\n({typedFn fnsName no})\n{namesTerm ns.toList} <|\n" ++
          typedFn fnsName rest
    | _, _, .step k (.cases (mid := mid) (t := t) (payloads := payloads) _ x _ _ arms) ns rest =>
        s!".cases (mid := {tyList mid}) (t := {ty t}) (payloads := {tyList payloads}) {key k} () " ++
          s!"{varTerm x.name} ⟨_, _, rfl, rfl⟩ (fun _ _ => trivial)\n{typedFnArms fnsName arms}\n" ++
          s!"{namesTerm ns.toList} <|\n" ++ typedFn fnsName rest
    | _, _, .step k (.loop (carried := carried) (each := each) _ times _ initial inputs body) ns rest =>
        let count := match times with
          | .fixed n => s!"(.fixed {n})"
          | .value v _ => s!"(.value (t := .nat) {varTerm v.name} rfl)"
        s!".loop (carried := {tyList carried}) (each := {tyList each}) {key k} () {count} " ++
          s!"(fun _ _ => trivial) {varsTerm initial.names} {namesTerm inputs.toList}\n" ++
          s!"({typedFn fnsName body})\n{namesTerm ns.toList} <|\n" ++ typedFn fnsName rest
    | _, _, .step k (.block (mid := mid) number body) ns rest =>
        s!".block (mid := {tyList mid}) {key k} {number}\n({typedFn fnsName body})\n" ++
          s!"{namesTerm ns.toList} <|\n" ++ typedFn fnsName rest
    | _, _, .step _ (.attempt _ owns _ _) _ _ => nomatch owns
  partial def typedFnArms {fns : List (FnHeader b.vocabulary)} (fnsName : String) :
      {Γ : Ctx b.vocabulary.Ty} → {mid payloads : List b.vocabulary.Ty} →
        Arms (localDialect b.vocabulary fns) Γ mid payloads → String
    | _, _, _, .nil => ".nil"
    | _, _, _, .cons inputs arm rest =>
        s!"(.cons {namesTerm inputs.toList} ({typedFn fnsName arm})\n{typedFnArms fnsName rest})"
end

/-- The decisions of a condition of the protocol dialect: the type, then who holds the value,
then that somebody performs. -/
def held := "⟨rfl, by decide +kernel, by decide +kernel⟩"

mutual
  /-- The body of a protocol, by the constructors of the term. -/
  partial def typedProtocol {hs : Headers b.vocabulary} (headersName : String) :
      {Γ : Ctx (LTy b.vocabulary)} → {outs : List (LTy b.vocabulary)} →
        Term (protocolDialect b.vocabulary hs) Γ outs → String
    | _, _, .ret vs => s!".ret {varsTerm vs.names}"
    | _, _, .step k (.op o args) ns rest =>
        s!".op {key k} {protocolOp headersName o} {varsTerm args.names} {namesTerm ns.toList} <|\n" ++
          typedProtocol headersName rest
    | _, _, .step k (.guard (t := t) who c _ why) _ rest =>
        s!".guard (t := {locatedTy t}) {key k} {numbers who} {varTerm c.name} {held} {reason why} <|\n" ++
          typedProtocol headersName rest
    | _, _, .step k (.choose (mid := mid) (t := t) who c _ _ yes no) ns rest =>
        s!".choose (mid := {located mid}) (t := {locatedTy t}) {key k} {numbers who} {varTerm c.name} " ++
          s!"{held} (by decide +kernel)\n" ++
          s!"({typedProtocol headersName yes})\n({typedProtocol headersName no})\n" ++
          s!"{namesTerm ns.toList} <|\n" ++ typedProtocol headersName rest
    | _, _, .step k (.cases (mid := mid) (t := t) (payloads := payloads) who x _ _ arms) ns rest =>
        s!".cases (mid := {located mid}) (t := {locatedTy t}) (payloads := {located payloads}) {key k} " ++
          s!"{numbers who} {varTerm x.name} ⟨_, _, rfl, rfl, by decide +kernel, by decide +kernel⟩ " ++
          "(by decide +kernel)\n" ++
          s!"{typedProtocolArms headersName arms}\n{namesTerm ns.toList} <|\n" ++
          typedProtocol headersName rest
    | _, _, .step k (.loop (carried := carried) (each := each) who times _ initial inputs body) ns rest =>
        let count := match times with
          | .fixed n => s!"(.fixed {n})"
          | .value (t := t) v _ => s!"(.value (t := {locatedTy t}) {varTerm v.name} {held})"
        s!".loop (carried := {located carried}) (each := {located each}) {key k} {numbers who} {count} " ++
          s!"(by decide +kernel) {varsTerm initial.names} {namesTerm inputs.toList}\n" ++
          s!"({typedProtocol headersName body})\n{namesTerm ns.toList} <|\n" ++
          typedProtocol headersName rest
    | _, _, .step k (.block (mid := mid) number body) ns rest =>
        s!".block (mid := {located mid}) {key k} {number}\n({typedProtocol headersName body})\n" ++
          s!"{namesTerm ns.toList} <|\n" ++ typedProtocol headersName rest
    | _, _, .step k (.attempt (mid := mid) who _ inputs body) ns rest =>
        s!".attempt (mid := {located mid}) {key k} {numbers who} ⟨_, rfl⟩ {namesTerm inputs.toList}\n" ++
          s!"({typedProtocol headersName body})\n{namesTerm ns.toList} <|\n" ++
          typedProtocol headersName rest
  partial def typedProtocolArms {hs : Headers b.vocabulary} (headersName : String) :
      {Γ : Ctx (LTy b.vocabulary)} → {mid payloads : List (LTy b.vocabulary)} →
        Arms (protocolDialect b.vocabulary hs) Γ mid payloads → String
    | _, _, _, .nil => ".nil"
    | _, _, _, .cons inputs arm rest =>
        s!"(.cons {namesTerm inputs.toList} ({typedProtocol headersName arm})\n" ++
          s!"{typedProtocolArms headersName rest})"
end

/-! ## Definitions -/

/-- A term over several lines, each further in than the declaration that it belongs to: Lean
reads an argument only when it starts to the right of where its command starts. -/
def indented (term : String) : String := "  " ++ term.replace "\n" "\n  "

/-- The suffix of the names of what is stated before any definition. -/
def baseSuffix := "Base"

/-- The typed definitions in order. Each is stated against the headers of those before it,
named by the key of the latest; the result is the lines and the key of the last definition. -/
def typedDefinitions : {hs : Headers b.vocabulary} → Defs b.vocabulary hs → List String × String
  | _, .nil => ([
      "noncomputable section",
      "abbrev headersBase : Headers V := ⟨[], []⟩",
      "def defsBase : Defs V headersBase := .nil",
      "def storedThroughBase : List (Definition V) := []",
      "theorem erasedBase : defsBase.erase = storedThroughBase := rfl"], baseSuffix)
  | _, .fn hdr inputs body _ rest notes =>
      let (before, p) := typedDefinitions rest
      let k := toString hdr.key.number
      (before ++ [
        s!"abbrev header{k} : FnHeader V :=\n  ⟨{key hdr.key}, {tyList hdr.ins}, {tyList hdr.outs}, " ++
          s!"{hdr.canStop}, {option key hdr.kernel}, {headerSummary hdr.summary}⟩",
        s!"abbrev names{k} : Names header{k}.ins := {namesTerm inputs.toList}",
        s!"noncomputable def body{k} : Fn V headers{p}.fns header{k} names{k} :=\n" ++
          indented (typedFn s!"headers{p}.fns" body),
        s!"theorem conditions{k} : FnConditions body{k} := FnConditions.of_checks (by decide +kernel)",
        s!"abbrev headers{k} : Headers V := ⟨header{k} :: headers{p}.fns, headers{p}.protocols⟩",
        s!"def defs{k} : Defs V headers{k} :=\n  .fn header{k} names{k} body{k} conditions{k} defs{p} " ++
          annotations notes,
        s!"def storedThrough{k} : List (Definition V) := storedThrough{p} ++ [stored{k}]",
        s!"theorem erased{k} : defs{k}.erase = storedThrough{k} :=\n" ++
          s!"  Defs.erase_fn erased{p} (by decide +kernel)"], k)
  | _, .protocol hdr inputs body _ rest =>
      let (before, p) := typedDefinitions rest
      let k := toString hdr.key.number
      (before ++ [
        s!"abbrev ports{k} : List (LTy V) := {located hdr.ins}",
        s!"abbrev results{k} : List (LTy V) := {located hdr.outs}",
        s!"abbrev names{k} : Names ports{k} := {namesTerm inputs.toList}",
        s!"noncomputable def body{k} : Term (protocolDialect V headers{p}) (Ctx.empty.extend names{k}) " ++
          s!"results{k} :=\n" ++
          indented (typedProtocol s!"headers{p}" body),
        s!"abbrev header{k} : ProtocolHeader V := ⟨{key hdr.key}, {hdr.roles}, ports{k}, results{k}, " ++
          s!"shapeOf body{k}⟩",
        s!"theorem conditions{k} : ProtocolConditions header{k} body{k} :=\n" ++
          "  ProtocolConditions.of_checks rfl (by decide +kernel)",
        s!"abbrev headers{k} : Headers V := ⟨headers{p}.fns, header{k} :: headers{p}.protocols⟩",
        s!"def defs{k} : Defs V headers{k} := .protocol header{k} names{k} body{k} conditions{k} defs{p}",
        s!"def storedThrough{k} : List (Definition V) := storedThrough{p} ++ [stored{k}]",
        s!"theorem erased{k} : defs{k}.erase = storedThrough{k} :=\n" ++
          s!"  Defs.erase_protocol erased{p} (by decide +kernel)"], k)

end

/-! ## The module -/

def staticArgument : Core.Static → String
  | .nat n => s!"(.nat {n})"
  | .key k => s!"(.key {key k})"

def associationTerm (a : Core.Association) : String :=
  let families := a.families.map fun f =>
    s!"⟨{key f.generic}, {list (f.arguments.map staticArgument)}, {key f.definition}⟩"
  let relations := a.relations.map fun r =>
    s!"⟨{key r.relation}, {keys r.binders}, {keys r.statement}, {keys r.witness}⟩"
  let interpretations := a.interpretations.map fun (handle, chosen) => s!"({key handle}, {key chosen})"
  s!"⟨{list families}, {list relations}, {list interpretations}, {keys a.claims}, {keys a.specifications}⟩"

def vocabularyTerm (b : Emit.Bindings) : String :=
  let rows := b.rows.map fun (name, signature) =>
    let inputs := list (signature.inputs.map linkedTy)
    let outputs := list (signature.outputs.map linkedTy)
    s!"({primitiveName name}, ⟨{inputs}, {outputs}⟩)"
  s!"(Zkc.Frontend.Emit.Bindings.mk {list rows} (by decide +kernel)).vocabulary"

/-- The modules that the declarations of a printed package use. -/
def packageImports : List String :=
  ["Zkc.Core.Admission.Theorems", "Zkc.Core.Program.DefinitionChecks", "Zkc.Frontend.Emit.Bindings"]

/-- The declarations of a printed package and what a reader of them needs to refer to its
definitions. -/
structure PrintedPackage where
  /-- The declarations, for a namespace that the caller opens. -/
  text : String
  /-- The key of each definition in order, and whether it is a protocol. The root of a
  package is its last definition. What is stated of the definition with key `k` is named with
  that number: `stored<k>`, `header<k>`, `names<k>`, `body<k>`, `conditions<k>`, and for a
  protocol `ports<k>` and `results<k>`. -/
  definitions : List (Key × Bool)

/-- An admitted package as Lean declarations: the vocabulary (`V`), the program by names
(`stored`) with its association, the typed program one definition at a time with the kernel's
check of each erasure (`installed`, `erasure`), that the program of any admission of the program
by names is the typed program (`readback`), and that there is such an admission
(`admitted_exists`): the kernel runs admission on the program by names, so the hypothesis of
`readback` is met. -/
def package (p : SourcePackage) (ev : p.Admission) : ExportM PrintedPackage := do
  let named := p.named.definitions
  let typedKeys := ev.admitted.program.defs.erase.map (·.key)
  unless named.map (·.key) == typedKeys do
    throw "WK-CORE: the admitted program does not have the definitions of the stored program in order"
  let storedLines := named.map fun d =>
    s!"def stored{d.key.number} : Definition V :=\n  {storedDefinition (b := p.bindings) d}"
  let storedProgram := [
    s!"def stored : NamedProgram V := ⟨{list (named.map fun d => s!"stored{d.key.number}")}⟩",
    s!"def association : Association := {associationTerm p.association}"]
  let (typedLines, last) := typedDefinitions (b := p.bindings) ev.admitted.program.defs
  let closing := [
    s!"def installed : Typed V := ⟨headers{last}, defs{last}, by decide +kernel⟩",
    s!"theorem erasure : stored = erase installed := congrArg NamedProgram.mk erased{last}.symm",
    "theorem readback {a : Admitted V} (h : admit stored association = .ok a) :",
    "    a.program = installed := admitted_eq_of_readback h erasure",
    "end"]
  let admitted := [
    "theorem admitted_exists : ∃ a, admit stored association = .ok a := by",
    "  have ok : (admit stored association).isOk = true := by decide +kernel",
    "  cases eq : admit stored association with",
    "  | ok a => exact ⟨a, rfl⟩",
    "  | error e => rw [eq] at ok; contradiction"]
  let vocabulary := s!"abbrev V : Zkc.Core.Vocabulary := {vocabularyTerm p.bindings}"
  let text := "\n".intercalate <|
    vocabulary :: storedLines ++ storedProgram ++ typedLines ++ closing ++ admitted ++ [""]
  let definitions := named.map fun
    | .fn k .. => (k, false)
    | .protocol k .. => (k, true)
  return ⟨text, definitions⟩

end Zkc.Frontend.Written

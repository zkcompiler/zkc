module

public import Zkc.Core.Admission.Theorems
public import Zkc.Frontend.Emit.Reports
public import Zkc.Frontend.Written.LeanTerms

@[expose] public section
set_option autoImplicit false

/-!
A package as a Lean module.

The frontend writes one thing: the program by names that it gives to admission (`stored`), with
its vocabulary and its association. The typed program is not written. For each definition, in
order, the module asks the kernel to elaborate it against the headers of the definitions before
it (`kernel_ok … := elaborateDefinition …`), and names what the kernel returns: the
elaborated definition, its header, the names of its inputs and its body. From the equations
of these steps, the program of any admission of `stored` is the program that the module names
(`readback`), and the kernel runs that admission once (`admitted_exists`).

So the typed program in a module is the one that Core's elaborator gives, computed by the
kernel, and no constructor of a typed term is written here. A program that does not elaborate
is refused by the kernel command of its first definition that does not.

What this leaves unchecked inside the module: that `stored` is the program the frontend meant.
A wrong print that still elaborates gives a module about another program. The check of printed
packages compares `stored` with the frontend's program by value, and sends a fixture with
every constructor of the stored form through `storedDefinition`.

A module that holds a printed package imports the modules of `packageImports`. They are built
before Lean reads the module; the printer itself has no use for the kernel command and does not
import it.
-/

namespace Zkc.Frontend.Written
open Core

/-! ## Small values -/

def namesTerm (xs : List Nat) : String := consList (xs.map toString)

def reason : Reason → String
  | .reject => ".reject"
  | .abort => ".abort"
  | .exhausted => ".exhausted"
  | .refused => ".refused"

def flowKind : FlowKind → String
  | .message => ".message"
  | .rows => ".rows"
  | .opening => ".opening"

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

def located (ts : List (LTy b.vocabulary)) : String :=
  list (ts.map fun a => s!"⟨{ty a.ty}, {numbers a.holders}⟩")

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
  ["Zkc.Core.Admission.Theorems", "Zkc.Kernel", "Zkc.Frontend.Emit.Bindings"]

/-- The declarations of a printed package and what a reader of them needs to refer to its
definitions. -/
structure PrintedPackage where
  /-- The declarations, for a namespace that the caller opens. -/
  text : String
  /-- The key of each definition in order, and whether it is a protocol. The root of a
  package is its last definition. What is stated of the definition with key `k` is named with
  that number: `stored<k>`, `elaborated<k>`, `header<k>`, `names<k>`, `body<k>`, and
  `program<k>` for the program through it. -/
  definitions : List (Key × Bool)

/-- The suffix of the names of what is stated before any definition. -/
def baseSuffix := "Base"

/-- A package as Lean declarations: the vocabulary (`V`), the program by names (`stored`) with
its association, each definition elaborated by the kernel against the program before it, the
program that results (`installed`), that the program of any admission of the program by names
is that program (`readback`), and that there is such an admission (`admitted_exists`). -/
def package (p : SourcePackage) : PrintedPackage :=
  let named := p.named.definitions
  let suffix (d : Definition p.bindings.vocabulary) := toString d.key.number
  let storedLines := named.map fun d =>
    s!"def stored{suffix d} : Definition V :=\n  {storedDefinition (b := p.bindings) d}"
  let storedProgram := [
    s!"def stored : NamedProgram V := ⟨{list (named.map fun d => s!"stored{suffix d}")}⟩",
    s!"def association : Association := {associationTerm p.association}"]
  -- each definition against the program before it; the suffix of that program is carried along
  let (steps, last) := named.foldl (init := (([] : List String), baseSuffix)) fun (lines, before) d =>
    let k := suffix d
    (lines ++ [
      s!"kernel_ok elaborated{k} with header{k} names{k} body{k} : " ++
        s!"Elaborated V program{before}.headers :=\n  elaborateDefinition program{before}.headers stored{k}",
      s!"def program{k} : Typed V := program{before}.add elaborated{k}"], k)
  let chain := named.foldr (fun d rest => s!".cons elaborated{suffix d}.eq ({rest})") ".nil _"
  let typed := ["noncomputable section", s!"def program{baseSuffix} : Typed V := Typed.empty"] ++ steps ++ [
    s!"def installed : Typed V := program{last}",
    "theorem elaborated : ElaboratedFrom Typed.empty stored.definitions installed :=",
    s!"  {chain}",
    "theorem readback {a : Admitted V} (h : admit stored association = .ok a) :",
    "    a.program = installed := admitted_eq_of_elaborated h elaborated",
    "end"]
  let admitted := [
    "theorem admitted_exists : ∃ a, admit stored association = .ok a := by",
    "  have ok : (admit stored association).isOk = true := by decide +kernel",
    "  cases eq : admit stored association with",
    "  | ok a => exact ⟨a, rfl⟩",
    "  | error e => rw [eq] at ok; contradiction"]
  let vocabulary := s!"abbrev V : Zkc.Core.Vocabulary := {vocabularyTerm p.bindings}"
  let text := "\n".intercalate <|
    vocabulary :: storedLines ++ storedProgram ++ typed ++ admitted ++ [""]
  let definitions := named.map fun
    | .fn k .. => (k, false)
    | .protocol k .. => (k, true)
  ⟨text, definitions⟩

end Zkc.Frontend.Written

module

public import Zkc.Core.Functions
public import Zkc.Core.Admission.Check
public import Zkc.Core.Facts.Facts
public import Zkc.Core.Program.EraseProgram
public import Zkc.Core.Value.TransformSound

@[expose] public section

/-!
The statements, as propositions over the types of the core.

Each is a theorem to be proved. None is proved here: this file checks that every statement can
be said with the types that cross between the parts. Every statement is about what a function
of `Functions` returns, or about a definition; none has a field of a record of functions as a
premise or as its subject. Each says what kind of thing it preserves: execution and state (a
process or a run is the same), a view (what one reader sees is the same), validity (no value
or stop outside what is allowed), or progress (a run goes on or ends as said).

That every role program is a projection of its protocol is not a statement: it is the
theorem `Zkc.Core.projection` (`Projection/Theorem.lean`). For a program of functions, the
round trip in both directions is the theorems `Zkc.Core.elaborateFunctions_erase` and
`Zkc.Core.erase_elab` (`Admission/Elaboration.lean`).
-/

namespace Zkc.Core

namespace Statements

variable {V : Vocabulary} (c : Functions V)

/-! ## The program by names -/

/-- Execution and state: elaborating the erased form of a typed program gives the
program. -/
def roundTrip : Prop :=
  ∀ p : Typed V, c.elaborate (erase p) = .ok p

/-- Execution and state: a program that elaboration gives erases to the program by names that
was elaborated. -/
def eraseOfElaborated : Prop :=
  ∀ named p, c.elaborate named = .ok p → erase p = named

/-- Execution and state: an admitted program is the elaboration of what was given, and its
association is the resolution in it of the association given. -/
def admitsWhatWasGiven : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    c.elaborate named = .ok a.program ∧ resolve a.program assoc = .ok a.association

/-- A view: what `admit` accepts as a program, `check` accepts one definition at a time, and
the headers that it gives, which are what an application sees of each definition, are the
program's. -/
def checkAgrees : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    checkAll c.check ⟨[], []⟩ named.definitions = .ok a.program.headers

/-! ## Admission -/

/-- Validity: a function of an admitted program never stops `undefined`, on any valid
inputs. -/
def functionsSafe : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Member a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins), ins.All M.Valid →
      (fnMeaning M a.program f ins).Stops (· ≠ .undefined)

/-- Validity: a function returns valid values. -/
def functionsKeepValidity : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Member a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins) (outs : HList M.Val hdr.outs), ins.All M.Valid →
      fnMeaning M a.program f ins = .done outs → outs.All M.Valid

/-- A view: a function that its header says cannot stop does not stop. -/
def headersSayWhoStops : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Member a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins), ins.All M.Valid → hdr.canStop = false →
      (fnMeaning M a.program f ins).Stops fun _ => False

/-- Execution and state: two functions that the decision of the value form finds the same mean
the same. For two bodies of functions over the same headers and of the same types, each with
distinct addresses and accepted by the check of facts, of which the second follows the skeleton
of the first (`same`): against callees with distinct keys that never stop `undefined` on valid
inputs, keep validity, and stop only `undefined` where their headers say that they cannot stop,
on every valid input the two processes mean the same, for any replies permitted. -/
def functionsSame : Prop :=
  ∀ (fns : List (FnHeader V)) {types outs : List V.Ty} (inputs inputs' : Names types)
    (body : Term (localDialect V fns) (Ctx.empty.extend inputs) outs)
    (body' : Term (localDialect V fns) (Ctx.empty.extend inputs') outs)
    (definition definition' : Key) (bounds bounds' : List (Place × Nat)),
    Term.Distinct body → Term.Distinct body' →
    checkFacts (localFactRules V fns) definition none inputs body = .ok bounds →
    checkFacts (localFactRules V fns) definition' none inputs' body' = .ok bounds' →
    same (localValueRules V fns) (localSkelRules V fns) inputs inputs' body body' = true →
    ∀ (M : Model V) (table : FnTable M fns), (fns.map (·.key)).Nodup → FnTable.Safe table →
      FnTable.KeepsValidity table →
      (∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
        (table hdr callee args).Stops (· = .undefined)) →
      ∀ ins : HList M.Val types, ins.All M.Valid → ∀ permitted : ∀ op, NoSig.Reply op → Prop,
        Process.SameWhen permitted
          (body.denote (localSem M fns table) [] (Env.empty.extend inputs ins))
          (body'.denote (localSem M fns table) [] (Env.empty.extend inputs' ins))

/-- Execution and state: a transformation of a function that the step accepts relates functions
with the same meaning. When `transform` accepts a source and a target, both elaborated and
accepted by the check of facts and the target following the skeleton of the source: against
callees with distinct keys that never stop `undefined` on valid inputs, keep validity, and stop
only `undefined` where their headers say that they cannot stop, the two return the same on every
valid input (`AcceptedFn.SameAs`). -/
def transformSound : Prop :=
  ∀ (fns : List (FnHeader V)) (hdr : FnHeader V) (source target : Region (LocalRaw V) Unit)
    (step : Transformed V fns hdr), transform fns hdr source target = .ok step →
      step.source.SameAs step.target

/-- Execution and state: a program whose functions were replaced by functions that the decision
accepts means what the first means. For two programs over the same headers with distinct keys,
both accepted by the check of facts, whose functions follow one by one (`Defs.follows`): every
function of the second has, on valid inputs, the meaning of the function of the first with its
header, the callers of a replaced function included. -/
def transformedProgramSame : Prop :=
  ∀ (hs : Headers V) (defs defs' : Defs V hs), (hs.fns.map (·.key)).Nodup →
    ∀ (bounds bounds' : List (Place × Nat)), Defs.Accepted defs bounds →
      Defs.Accepted defs' bounds' → Defs.follows defs defs' = true →
      ∀ (M : Model V) (hdr : FnHeader V) (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins),
        ins.All M.Valid → Defs.fnTable M defs' hdr f ins = Defs.fnTable M defs hdr f ins

/-- Validity: an open role program is safe: on valid inputs and every permitted reply it
never stops `undefined`, whatever its peers do. -/
def rolesSafe : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : ProtocolHeader V) (p : Member a.program.headers.protocols hdr)
      (r : Role) (path : List Frame) (ins : HList (RV M r) hdr.ins), ins.All (RV.Valid M r) →
      (roleMeaning M a.program p r path ins).StopsWhen (Permitted M) (· ≠ .undefined)

/-- Validity: no loop of an admitted program runs more often than the bound that its
annotation gives it. -/
def annotationHolds : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a → ∀ M : Model V, Respects M a.annotation a.program

/-! ## Runs of every typed program -/

/-- The network of the projections of a protocol, each on its part of one input. -/
def projections (p : Typed V) (M : Model V) {hdr : ProtocolHeader V}
    (x : Member p.headers.protocols hdr) (path : List Frame) (ins : HList (LVal M) hdr.ins) :
    Net M (fun _ => Stop) (fun r => HList (RV M r) hdr.outs) × Pending M :=
  ((fun r => roleMeaning M p x r path (hideAll M r ins)), Pending.empty M)

/-- Execution and state: a run of a protocol is reached by the network of its projections
on parts of one input:
where it returns, every role has returned its part and nothing is pending; where it stops, the
roles that stop have stopped with its reason; and what was sent in the execution is exactly
what the run sent, in its order. -/
def realized : Prop :=
  ∀ (p : Typed V) (M : Model V) (hdr : ProtocolHeader V) (x : Member p.headers.protocols hdr)
    (path : List Frame) (ins : HList (LVal M) hdr.ins) (source : Source M)
    (events : List (Event M)) (e : GEnd _),
    GRun M source (protocolMeaning M p x path ins) events e →
    ∃ record net pending,
      Reach M source (projections p M x path ins) record (net, pending) ∧
      Happened.sent M record = Event.sent M events ∧
      Ended M (fun r out mine => mine = hideAll M r out.1) net e ∧
      (∀ out, e = .returned out → pending = Pending.empty M)

/-- Execution and progress: the order of the steps does not matter. Where a run of the
protocol returns, every
execution of the network of its projections that can go no further has every role returned
with its part and nothing pending; where the run stops, in every such execution the roles
that stop have stopped with its reason, and every other role has returned, stopped, waits
for a message that will not come, or starves for what the world does not give. -/
def anyOrder : Prop :=
  ∀ (p : Typed V) (M : Model V) (hdr : ProtocolHeader V) (x : Member p.headers.protocols hdr)
    (path : List Frame) (ins : HList (LVal M) hdr.ins) (source : Source M) (e : GEnd _),
    GExec M source (protocolMeaning M p x path ins) e →
    ∀ record net pending,
      Reach M source (projections p M x path ins) record (net, pending) →
      Quiescent M source (net, pending) →
      Ended M (fun r out mine => mine = hideAll M r out.1) net e ∧
      (∀ out, e = .returned out → pending = Pending.empty M) ∧
      (∀ r, (∃ b, net r = .done b) ∨ (∃ why, net r = .halt why) ∨
        (∃ at_, Waits M (net, pending) r at_) ∨ ∃ at_, Starves M source (net, pending) r at_)

/-- Execution and state: an execution is replayed from its record: the record determines
where it ends. -/
def replayed : Prop :=
  ∀ (M : Model V) (source source' : Source M) (H B : Role → Type)
    (c c' c'' : Net M H B × Pending M) (record : List (Happened M)),
    Reach M source c record c' → Reach M source' c record c'' → c' = c''

/-- Validity: on valid inputs and against a world that gives what its laws allow, a run that
returns gives valid results and a valid record. -/
def recordsAreValid : Prop :=
  ∀ (p : Typed V) (M : Model V) (hdr : ProtocolHeader V) (x : Member p.headers.protocols hdr)
    (path : List Frame) (ins : HList (LVal M) hdr.ins) (source : Source M) out,
    ins.All (fun a v => M.Valid a.ty v) → Lawful M source (protocolMeaning M p x path ins) →
    GExec M source (protocolMeaning M p x path ins) (.returned out) →
    out.1.All (fun a v => M.Valid a.ty v) ∧ Fields.Valid M hdr.record out.2

/-- Execution and progress: the scheduler's run is an execution of the network of the
projections, with the record
it reports; a role that it reports returned, stopped or blocked is so in the state reached,
and when it does not report the limit for any role, no role can move. A budget counts steps
of the network: when some execution of `n` steps reaches a state where no role can move, the
scheduler with a budget of at least `n` reports the limit for no role. -/
def schedulerRuns : Prop :=
  ∀ (p : Typed V) (M : Model V) (hdr : ProtocolHeader V) (x : Member p.headers.protocols hdr)
    (ins : HList (LVal M) hdr.ins) (source : Source M),
    (∀ limit, ∃ net pending,
      Reach M source (projections p M x [] ins)
        (c.schedule p M hdr x (fun r => hideAll M r ins) source limit).1 (net, pending) ∧
      (∀ r, match (c.schedule p M hdr x (fun r => hideAll M r ins) source limit).2 r with
        | .ended (.returned (outs, _)) => net r = .done outs
        | .ended (.stopped why) => net r = .halt why
        | .ended (.blocked at_) => Waits M (net, pending) r at_
        | .limit => True
        | .failed _ => False) ∧
      ((∀ r, (c.schedule p M hdr x (fun r => hideAll M r ins) source limit).2 r ≠ .limit) →
        Quiescent M source (net, pending))) ∧
    (∀ record net pending,
      Reach M source (projections p M x [] ins) record (net, pending) →
      Quiescent M source (net, pending) →
      ∀ limit, record.length ≤ limit →
        ∀ r, (c.schedule p M hdr x (fun r => hideAll M r ins) source limit).2 r ≠ .limit)

/-! ## Deployment -/

/-- Execution and state: deployment admits nothing again: a deployed scheme holds the
program and the declaration that it was given, and its entry is the declaration's. -/
def deployKeeps : Prop :=
  ∀ (a : Admitted V) declaration (d : Deployed V), c.deploy a declaration = .ok d →
    d.admitted = a ∧ d.declaration = declaration ∧ d.entry.key = declaration.entry

/-- A view: a deployed scheme that is not interactive has a prover and a verifier, which the
shape says. -/
def deployFindsRoles : Prop :=
  ∀ (a : Admitted V) declaration (d : Deployed V), c.deploy a declaration = .ok d →
    declaration.interactive = false → ∃ prover verifier, d.roles = some (prover, verifier)

/-- A view: the prover's handlers take nothing from outside the run, and what they give is
what the verifier's take. -/
def deployMatches : Prop :=
  ∀ (a : Admitted V) declaration (d : Deployed V), c.deploy a declaration = .ok d →
    ∀ prover verifier, d.roles = some (prover, verifier) →
      Stack.Takes (d.stack prover) = [] ∧ Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier)

/-- Validity: a deployed role of an admitted program never stops `undefined`: its run, on
valid inputs, valid values taken and every permitted reply. -/
def deployedSafe : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ declaration (d : Deployed V), c.deploy a declaration = .ok d →
      ∀ (M : Model V) (r : Role) (ins : HList (RV M r) d.entry.ins)
        (taken : HList M.Val (Stack.Takes (d.stack r))),
        ins.All (RV.Valid M r) → taken.All M.Valid →
        (d.run M r ins taken).StopsWhen (Permitted M) (· ≠ .undefined)

/-- Progress: the compiler's completeness. On valid inputs, if every run of the entry's
protocol against
a world that gives what its laws allow returns, then against every such world that answers
the protocol: the prover's run alone returns, with what its handlers give; the verifier's run
alone on that returns; and some run of the protocol returns with both roles' results their
parts of its results, against a world that gives what the laws allow and what this one gives
at every occurrence that is not a coin that some role hears. -/
def complete : Prop :=
  ∀ named assoc (a : Admitted V), c.admit named assoc = .ok a →
    ∀ declaration (d : Deployed V), c.deploy a declaration = .ok d →
      ∀ (prover verifier : Role), d.roles = some (prover, verifier) →
      ∀ (first : Stack.Takes (d.stack prover) = [])
        (matched : Stack.Gives (d.stack prover) = Stack.Takes (d.stack verifier))
        (M : Model V) (ins : HList (LVal M) d.entry.ins),
        ins.All (fun a v => M.Valid a.ty v) →
        (∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) → ∀ e,
          GExec M source (protocolMeaning M d.admitted.program d.callee [] ins) e →
          ∃ out, e = .returned out) →
        ∀ source, Lawful M source (protocolMeaning M d.admitted.program d.callee [] ins) →
          Fed M source (protocolMeaning M d.admitted.program d.callee [] ins) →
          ∃ outP gives recordP outV givesV recordV,
            Alone M source prover
              (d.run M prover (hideAll M prover ins)
                (cast (congrArg (HList M.Val) first.symm) .nil))
              recordP (.returned (outP, gives)) ∧
            Alone M source verifier
              (d.run M verifier (hideAll M verifier ins)
                (cast (congrArg (HList M.Val) matched) gives))
              recordV (.returned (outV, givesV)) ∧
            ∃ source' out,
              Lawful M source' (protocolMeaning M d.admitted.program d.callee [] ins) ∧
              (∀ at_ τ, at_.site ∉ d.entry.shape.heardCoins → source' at_ τ = source at_ τ) ∧
              GExec M source' (protocolMeaning M d.admitted.program d.callee [] ins)
                (.returned out) ∧
              outP = hideAll M prover out.1 ∧ outV = hideAll M verifier out.1

/-- Execution and state: the retry of a deployed scheme has a scope: the attempt that it
retries is an attempt of the entry's shape, and every guard with `abort` is inside an
attempt. -/
def deployScoped : Prop :=
  ∀ (a : Admitted V) declaration (d : Deployed V), c.deploy a declaration = .ok d → d.Scoped

/-- Execution and state: what the clauses of a deployed scheme do keeps the occurrences of the
entry's events: an event that a clause makes, other than performing again the event that it
answers, has a key that is no key of the entry's events. -/
def deployFresh : Prop :=
  ∀ (a : Admitted V) declaration (d : Deployed V), c.deploy a declaration = .ok d → d.Fresh

/-- A view: the identity of a deployed scheme reads its declaration and the erased
definitions that its entry and its declaration reach, and nothing else: not the association,
not the annotation, not another definition. -/
def identityReads : Prop :=
  ∀ d d' : Deployed V, d.declaration = d'.declaration →
    (erase d.admitted.program).definitions.filter (fun definition => decide (definition.key ∈ d.closure)) =
      (erase d'.admitted.program).definitions.filter
        (fun definition => decide (definition.key ∈ d'.closure)) →
    c.identity d = c.identity d'

/-! ## Runs of the executor -/

/-- Execution and progress: the executor's run is a run of the role alone: where it reports
a return, a stop or a
blocked role with a record, the role's run ends so with that record; where it reports the
limit, its record is a legal prefix of the role's run alone; it never reports a defect of its
own; and every run of the role alone is reported for some limit. -/
def executorRuns : Prop :=
  ∀ (d : Deployed V) (M : Model V) (r : Role) (ins : HList (RV M r) d.entry.ins)
    (taken : HList M.Val (Stack.Takes (d.stack r))) (source : Source M),
    (∀ limit, match c.execute d M r ins taken source limit with
      | (.ended ending, record) => Alone M source r (d.run M r ins taken) record ending
      | (.limit, record) => AlonePrefix M source r (d.run M r ins taken) record
      | (.failed _, _) => False) ∧
    (∀ record ending, Alone M source r (d.run M r ins taken) record ending →
      ∃ limit, c.execute d M r ins taken source limit = (.ended ending, record))

/-! ## Formats -/

/-- A view: the canonical format of every type has the two laws, for a model whose nominal
carriers have lawful codecs: what is written reads back as it was. -/
def formats : Prop :=
  ∀ (M : Model V) (codecs : Codecs M) (τ : V.Ty), (c.format M codecs τ).Lawful

end Statements

end Zkc.Core

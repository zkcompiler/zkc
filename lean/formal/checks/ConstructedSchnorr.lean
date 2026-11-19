module

meta import Zkc.Frontend.Syntax.Parser
meta import Zkc.Tools.Formal.ConstructedVerifier
meta import Zkc.Formal.Written.FiniteModel
import Zkc.Frontend.Syntax.Parser
import Zkc.Tools.Formal.ConstructedVerifier
import Zkc.Formal.Written.FiniteModel

open Zkc Zkc.Core Zkc.Frontend Zkc.Frontend.Constructed
open Zkc.Tools.Formal.ConstructedVerifier
open Zkc.Formal.Written.FiniteModel (model)

namespace ConstructedSchnorrCheck

variable {src : Assembly} {request : ExecutionRequest}

/-- Two distinct fixed-width test words. The reader checks the entire prefix. -/
def twoWords (width : Nat) (word : Bool → List Nat)
    (size : ∀ b, (word b).length = width) (distinct : word false ≠ word true)
    (valid : ∀ b n, n ∈ word b → n < 256) : Encoding Bool width where
  write := word
  read data :=
    if data.take width = word false then some (false, data.drop width)
    else if data.take width = word true then some (true, data.drop width) else none
  size := size
  bytesValid := valid
  lawful := by
    constructor
    · intro b rest
      cases b <;> simp [List.take_left' (size _), List.drop_left' (size _), Ne.symm distinct]
    · intro data b rest h
      change data = word b ++ rest
      dsimp at h
      split at h
      · rename_i matchesWord
        cases h
        rw [← matchesWord, List.take_append_drop]
      · split at h
        · rename_i matchesWord
          cases h
          rw [← matchesWord, List.take_append_drop]
        · contradiction

def pointWord : Bool → List Nat
  | false => 192 :: List.replicate 47 0
  | true => [151,241,211,167,49,151,215,148,38,149,99,140,79,169,172,15,
      195,104,140,79,151,116,185,5,161,78,58,63,23,27,172,88,
      108,85,232,63,249,122,26,239,251,58,240,10,219,34,198,187]

def scalarWord (b : Bool) := b.toNat :: List.replicate 31 0

def encoding : Interpretation model where
  group := twoWords 48 pointWord (by decide) (by decide) (by
    intro b n h
    have bounded : ∀ x ∈ pointWord b, decide (x < 256) = true := by cases b <;> decide
    exact of_decide_eq_true (bounded n h))
  field := twoWords 32 scalarWord (by decide) (by decide) (by
    intro b n h
    simp [scalarWord] at h
    rcases h with e | e <;> subst n <;> cases b <;> decide)
  fromResidue n := n.val % 2 == 1

def digest : Vector UInt8 32 := Vector.replicate 32 42

def ports (v : Verifier src request) (base publicPoint : Bool) :
    Except String (HList (RV model v.verifier) v.deployment.entry.ins) := do
  let hdr := v.deployment.entry
  let [a,b,w] := hdr.ins.map LTy.holders | throw "expected three input ports"
  if h : hdr.ins = [⟨point,a⟩,⟨point,b⟩,⟨scalar,w⟩] then
    let xs : HList (LVal model) [⟨point,a⟩,⟨point,b⟩,⟨scalar,w⟩] :=
      .cons base (.cons publicPoint (.cons false .nil))
    return cast (congrArg (HList (RV model v.verifier)) h.symm) (hideAll model v.verifier xs)
  throw "unexpected verifier ports"

/-- Independent schedule for the authored two-role instance. The words all fit one byte. -/
def words (ns : List Nat) := ns.flatMap fun n => n :: List.replicate 7 0

def expected : Query :=
  ⟨[(0,ascii "dom-sep",ascii "suite.merlin3.bls12-381.fr64be/0",()),
    (0,ascii "identity",List.replicate 32 42,()),
    (0,words [0,0],pointWord true,()), (0,words [0,1],pointWord true,()),
    (0,words [1,0,1,0,1],pointWord false,())], words [1,0,2,0,1]⟩

def units (byte : UInt8) : Units := Vector.ofFn fun i => if i.val = 63 then byte else 0

inductive Seen where
  | commitment (at_ : Occurrence) | squeeze (q : Query) (reply : Units) | response (at_ : Occurrence)
  deriving DecidableEq

abbrev History := List Seen

def policy {m : Type → Type} [Monad m] (response : Option Bool) : Policy model History m where
  commitment site seen := pure (some false, seen ++ [.commitment site])
  observe q reply seen := seen ++ [.squeeze q reply]
  response site seen := pure (response, seen ++ [.response site])

inductive Result where | accepted (log : Constructed.Log) | stopped (why : Stop) | unavailable
  deriving DecidableEq, Repr

def executeWith {m : Type → Type} [Monad m] {A : Type}
    (draw : Query → m Units) (pol : Policy model History m)
    (p : Process (signature model) Stop (A × Constructed.Log)) (state : Cache × History) :
    m (Result × Cache × History) := do
  match p with
  | .done (_,log) => return (.accepted log,state)
  | .halt why => return (.stopped why,state)
  | .call op k =>
    let (reply,s) ← serve pol draw op state
    match reply with
    | some value => executeWith draw pol (k value) s
    | none => return (.unavailable,s)

abbrev execute {A : Type} := @executeWith Id _ A

/-- Use the existing Merlin implementation for the query emitted by the running layer. -/
def merlin (q : Query) : IO Units := do
  let frames := q.history.toArray.map fun (op,name,data,_) =>
    Lean.Json.arr #[Lean.toJson op, Lean.toJson name, Lean.toJson data]
  let json := Lean.Json.arr #[.arr frames, Lean.toJson q.label]
  let result ← IO.Process.output {cmd := "python3", args := #["-B","checks/constructed_merlin.py",json.compress]}
  unless result.exitCode == 0 do throw (IO.userError result.stderr)
  let some ns := (result.stdout.trimAscii.toString.splitOn " ").mapM String.toNat?
    | throw (IO.userError "malformed Merlin output")
  unless ns.all (· < 256) do throw (IO.userError "invalid Merlin byte")
  let data := (ns.map Nat.toUInt8).toArray
  if h : data.size = 64 then return ⟨data,h⟩
  throw (IO.userError "wrong Merlin output size")

/-- Generated independently by replay_derived_schnorr.prove for G, G, nonce 0,
witness 1 and the test identity. The decoded scalar is odd after reduction. -/
def referenceReply : Units := ⟨#[145,71,115,90,193,131,192,191,93,207,36,194,212,98,131,231,
  38,225,126,161,60,169,174,168,20,162,250,44,11,65,94,67,17,84,28,49,236,111,228,175,
  123,109,47,121,23,8,119,115,235,111,85,15,27,117,11,205,2,156,166,203,170,255,232,210],rfl⟩

def source (p : System.FilePath) (edit : String → String) : IO SourceInput := do
  let s := edit (← IO.FS.readFile p)
  return ⟨p.toString,Syntax.parse p.toString s.toUTF8⟩

def assembly (editScheme editProtocol : String → String := id) : IO Assembly := do
  assemble #[← source "../../examples/schnorr_example.zkc" editScheme] fun path => do
    for dir in ["../../libraries","../../examples","../../examples/support"] do
      let p := (dir : System.FilePath) / ("/".intercalate path.toList ++ ".zkc")
      if ← p.pathExists then return some (← source p (if path.toList == ["schnorr"] then editProtocol else id))
    return none

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"failed: {name}")

def need {α : Type} (x : Except String α) : IO α := IO.ofExcept x

def refuses {α : Type} (code : String) : Except String α → Bool
  | .error why => why.contains code
  | .ok _ => false

def rejected : Result → Bool
  | .stopped (.declared .reject _) => true
  | _ => false

def process (v : Verifier src request) (base pk : Bool := true) (d : Vector UInt8 32 := digest) := do
  let ins ← ports v base pk
  v.run encoding (fun _ => some d) ins

def draw (q : Query) := if q = expected then units 1 else units 0

def schedule (q : Query) (reply : Units) (response : Bool) : Constructed.Log :=
  q.history ++ [(1,q.label,reply.toList.map UInt8.toNat,()),
    (0,words [1,0,3,0,1],scalarWord response,())]

/-- Same clause type and get as the selected handler, returning its unmodified state. -/
def dropClause {hs : Headers V} (s : Sites) (p r : Role) : Clause V hs r transcript where
  site := ⟨⟨[],s.commitment⟩,.get .message p,[],[point]⟩
  code := .op s.commitment (.get point [] .message p [r] (by simp)) .nil (.cons 1 .nil)
    (.ret (.cons ⟨1,rfl⟩ (.cons ⟨0,rfl⟩ .nil)))

def weakened (v : Verifier src request) (r : Role) : Layer V v.deployment.admitted.program.headers r v.deployment.entry.ins :=
  { verifierLayer v.sites v.prover r point scalar uniformScalar _ with
    clauses := [dropClause v.sites v.prover r, challengeClause v.sites v.prover uniformScalar scalar,
      receiveClause v.sites v.prover v.sites.response scalar .absorbScalar] }

/-- Send a scalar payload to the point member, using a well-typed Core request. -/
def misbound (v : Verifier src request) (r : Role) : Layer V v.deployment.admitted.program.headers r v.deployment.entry.ins :=
  { verifierLayer v.sites v.prover r point scalar uniformScalar _ with
    clauses := [receiveClause v.sites v.prover v.sites.commitment point .absorbPoint,
      challengeClause v.sites v.prover uniformScalar scalar,
      receiveClause v.sites v.prover v.sites.response scalar .absorbPoint] }

/-- Run a replacement layer on the very same admitted program and service. -/
def replaced (v : Verifier src request) (layer : (r : Role) →
    Layer V v.deployment.admitted.program.headers r v.deployment.entry.ins)
    (takes : (layer v.verifier).takes = [transcript])
    (gives : (layer v.verifier).gives = [transcript]) (start : Constructed.Log) :
    Except String (Process (signature model) Stop (HList (RV model v.verifier) v.deployment.entry.outs × Constructed.Log)) := do
  let inputs ← ports v true true
  let d : Deployed V := {v.deployment with stack := fun r => [layer r]}
  have ht : Stack.Takes (d.stack v.verifier) = [transcript] := by
    change (layer v.verifier).takes ++ [] = _; simp [takes]
  have hg : Stack.Gives (d.stack v.verifier) = [transcript] := by
    change (layer v.verifier).gives ++ [] = _; simp [gives]
  let p := d.run model v.verifier inputs (cast (congrArg (HList model.Val) ht.symm) (.cons start .nil))
  return (Constructed.interpret (A := HList (RV model v.verifier) d.entry.outs × HList model.Val (Stack.Gives (d.stack v.verifier))) v encoding p).map fun (outs,states) =>
    (outs,(cast (congrArg (HList model.Val) hg) states).single)

-- The issued entry is the entire selection from this request, including its admitted root.
example {name : String} (execution : GoalExecution src name) (selected : SourceEntry (.goal name))
    (resolved : resolveEntry src (.goal name) = .ok selected) :
    execution.verifier.entry.toSourceEntry = selected :=
  Except.ok.inj (execution.verifier.entry.issued.symm.trans resolved)

example {other : Assembly} {name another : String} (issued : GoalExecution src name)
    (_foreign : GoalExecution other name) (_differentName : GoalExecution src another)
    (_scheme : Verifier src (.scheme name)) (_state : Compile.State) (_entry : SchemeEntry) :
    GoalExecution src name := by
  fail_if_success have := construct _state _entry
  fail_if_success have := resolveEntry _state _entry
  fail_if_success exact ⟨_foreign.verifier⟩
  fail_if_success exact ⟨_differentName.verifier⟩
  fail_if_success exact ⟨_scheme⟩
  exact ⟨issued.verifier⟩

open Zkc.Formal.ProbabilisticProcess

inductive ExpectedOutcome where
  | returned | rejected | unavailable
  deriving DecidableEq, Repr

def ExpectedOutcome.matches {A : Type} : ExpectedOutcome → Zkc.Formal.ProbabilisticProcess.Outcome Stop A → Bool
  | .returned, .returned _ | .rejected, .halted (.declared .reject _)
  | .unavailable, .unavailable => true
  | _, _ => false

/-- Check the actual deterministic ProbComp result and return a proof of the public probability. -/
def exactAcceptance (v : Verifier src request)
    (inputs : HList (RV model v.verifier) v.deployment.entry.ins)
    (reply : Option Bool) (fresh : Query → Units) (cache : Cache) (want : ExpectedOutcome) :
    Except String (PLift (acceptance v encoding (fun _ => some digest) inputs (policy reply)
      (fun q => pure (fresh q)) (cache, []) = .ok (if want = .returned then 1 else 0))) := do
  match started : v.run encoding (fun _ => some digest) inputs with
  | .error why => throw why
  | .ok p =>
    match sampled : run (serve (policy reply) (fun q => pure (fresh q))) p (cache, []) with
    | .queryBind _ _ => throw "expected a deterministic service"
    | .pure (outcome, state) =>
      if observed : want.matches outcome then
        return ⟨by
          unfold acceptance
          rw [started]
          simp only [Except.map]
          rw [sampled, ← OracleComp.pure_def, map_pure]
          cases outcome <;> cases want <;> simp_all [ExpectedOutcome.matches]⟩
      else throw s!"expected {repr want} from the public experiment"

/-- Only a successful proof of the requested probability passes this executable check. -/
def checkAcceptance (v : Verifier src request) (reply : Option Bool) (fresh : Query → Units)
    (cache : Cache) (want : ExpectedOutcome) : IO Unit := do
  let inputs ← need (ports v true true)
  let _ ← need (exactAcceptance v inputs reply fresh cache want)

def runChecks : IO Unit := do
  let a ← assembly
  let v ← need (selectScheme a "Proof")
  let selectedGoal ← need (selectGoalExecution a "derived_view")
  let fromGoal := selectedGoal.verifier
  check "constructed goal selects Proof" (fromGoal.entry.scheme.declaration == v.entry.scheme.declaration)
  check "written and default serialized stages" (refuses "FS-STAGE" (selectGoalExecution a "fork") &&
    refuses "FS-STAGE" (selectGoalExecution a "knowledge"))
  check "signature directives" (refuses "FS-SCHEME" (selectScheme a "Signature"))
  check "source labels and physical keys" (v.labels == ⟨1,2,3⟩ &&
    [v.sites.commitment.number,v.sites.challenge.number,v.sites.response.number] == [2,3,6])
  let inputs ← need (ports v true true)
  check "identity is required" (refuses "FS-IDENTITY" (v.run encoding (fun _ => none) inputs))
  checkAcceptance fromGoal (some true) draw [] .returned
  checkAcceptance fromGoal (some false) draw [] .rejected
  checkAcceptance fromGoal none draw [] .unavailable
  checkAcceptance fromGoal (some true) (fun _ => units 0) [] .rejected
  checkAcceptance fromGoal (some true) (fun _ => units 0) [(expected, units 1)] .returned
  let p ← need (process fromGoal)
  let (result,cache,seen) := execute draw (policy (some true)) p ([],[])
  check "source verifier, final absorption and cache miss"
    (result == .accepted (schedule expected (units 1) true) && cache == [(expected,units 1)])
  check "adversary observation order" (seen == [.commitment ⟨[],v.sites.commitment⟩,
    .squeeze expected (units 1), .response ⟨[],v.sites.response⟩])
  let (real,merlinCache,_) ← executeWith merlin (policy (some true)) p ([],[])
  check "reference Merlin replies to the live query"
    (real == .accepted (schedule expected referenceReply true) && merlinCache == [(expected,referenceReply)])
  let (again,cache',_) := execute (fun _ => units 0) (policy (some true)) p (cache,[])
  check "cache hit survives a changed miss law" (again == result && cache' == cache)
  let (wrong,_,_) := execute draw (policy (some false)) p ([],[])
  check "response with wrong challenge" (rejected wrong)
  let (zero,_,_) := execute (fun _ => units 0) (policy (some false)) p ([],[])
  check "fresh zero challenge changes accepted response" (zero == .accepted (schedule expected (units 0) false))
  let order := Zkc.Vocabulary.Field.bls12381Fr.order
  let modulus : Units := Vector.ofFn fun i => ((order / 256^(63-i.val)) % 256).toUInt8
  let (reduced,_,_) := execute (fun _ => modulus) (policy (some false)) p ([],[])
  check "64-byte big-endian modulus reduces to zero in the live guard"
    (reduced == .accepted (schedule expected modulus false))
  check "unavailable response" ((execute draw (policy none) p ([],[])).1 == .unavailable)
  let shifted ← need (process v true true (Vector.replicate 32 43))
  let (badDigest,shiftedCache,_) := execute draw (policy (some true)) shifted (cache,[])
  check "identity separates cached queries" (rejected badDigest && shiftedCache.length == 2)
  let changedStatement ← need (process v true false)
  let (statementResult,statementCache,_) := execute draw (policy (some false)) changedStatement (cache,[])
  let changedQuery := {expected with history := expected.history.set 3 (0,words [0,1],pointWord false,())}
  check "held public input changes its encoded value and the lookup"
    (statementResult == .accepted (schedule changedQuery (units 0) false) &&
      statementCache == (changedQuery,units 0) :: cache)
  let canonical := fun r => verifierLayer (hs := v.deployment.admitted.program.headers)
    v.sites v.prover r point scalar uniformScalar v.deployment.entry.ins
  let start := expected.history.take 4
  let [domain, ident, base, pk] := start | throw (IO.userError "bad test schedule")
  for (name, modified) in [("reordered statement",[domain,ident,pk,base]),
      ("wrong domain",[(0,ascii "dom-sep",ascii "other",()),ident,base,pk])] do
    let modifiedProgram ← need (replaced v canonical rfl rfl modified)
    let (out,c,_) := execute draw (policy (some true)) modifiedProgram (cache,[])
    check name (rejected out && c.length == 2 && c.head?.any (fun kv => kv.1.history.take 4 == modified))
  let wrongDecl := {v.entry.declaration with construction := .catalogue "suite.poseidon2-duplex.koala-bear/0"}
  check "declaration correspondence rejects another binding"
    ((declaredHandlers wrongDecl v.deployment.entry (v.entry.firstUnused v.found)).isNone)
  check "same-typed handler fails the declaration readback"
    (decide (readLayer (weakened v v.verifier) ≠ declaredCode v.sites v.prover v.verifier point scalar uniformScalar))
  let misboundProgram ← need (replaced v (misbound v) rfl rfl start)
  check "wrong member after the squeeze fails at dispatch"
    ((execute draw (policy (some true)) misboundProgram (cache,[])).1 == .stopped .undefined)
  let weakenedProgram ← need (replaced v (weakened v) rfl rfl start)
  let (out,c,_) := execute draw (policy (some true)) weakenedProgram (cache,[])
  check "dropped commitment changes verifier outcome"
    (rejected out && c.head?.any (fun kv => kv.1 == {expected with history := start}))
  let changed ← assembly
    (fun s => (s.replace "scheme Proof =" "scheme Other =").replace "Proof," "Other,")
    (fun s => s.replace "base * response == commitment" "base * response != commitment")
  let alternate ← need (selectScheme changed "Other")
  let alternateGoal ← need (selectGoalExecution changed "derived_view")
  let opposite := alternateGoal.verifier
  check "named schemes and goals select Proof and Other"
    (v.entry.scheme.name == "Proof" && alternate.entry.scheme.name == "Other" &&
      opposite.entry.scheme.name == "Other" && fromGoal.entry.scheme.name == "Proof")
  let (goalId, _) ← need (Written.selectDeclaration fromGoal.entry.root.state .goal "derived_view" "FS-GOAL")
  let (otherGoalId, _) ← need (Written.selectDeclaration opposite.entry.root.state .goal "derived_view" "FS-GOAL")
  check "local goal, scheme and admitted protocol IDs collide"
    (goalId == otherGoalId && v.entry.scheme.declaration == alternate.entry.scheme.declaration &&
      fromGoal.entry.scheme.declaration == opposite.entry.scheme.declaration &&
      fromGoal.entry.root.id == opposite.entry.root.id)
  let changedProcess ← need (process opposite)
  let (changedOutcome, changedCache, changedHistory) := execute draw (policy (some true)) changedProcess ([], [])
  check "opposite source guard rejects after the identical service exchanges"
    (rejected changedOutcome && changedCache == cache && changedHistory == seen)
  checkAcceptance v (some true) draw [] .returned
  checkAcceptance alternate (some true) draw [] .rejected
  checkAcceptance opposite (some true) draw [] .rejected
  let reversed ← assembly id (fun s => s.replace "roles(P, V)" "roles(V, P)")
  let swapped ← need (selectScheme reversed "Proof")
  check "SC3 follows the authored roles" (swapped.prover == 1 && swapped.verifier == 0)
  let swappedRun ← need (process swapped)
  let (swappedResult,swappedCache,_) := execute (fun _ => units 1) (policy (some true)) swappedRun ([],[])
  let swappedQuery : Query := ⟨expected.history.set 4 (0,words [1,0,1,1,0],pointWord false,()),
    words [1,0,2,1,0]⟩
  let swappedLog := swappedQuery.history ++ [(1,swappedQuery.label,(units 1).toList.map UInt8.toNat,()),
    (0,words [1,0,3,1,0],scalarWord true,())]
  check "role remapping reaches the byte labels and verifier"
    (swappedCache == [(swappedQuery,units 1)] && swappedResult == .accepted swappedLog)
  let alternateSuite ← assembly (fun s => s.replace "Merlin3Bls12381" "Poseidon2KoalaBear") id
  check "different catalogue suite with the same interface" (refuses "FS-SUITE" (selectScheme alternateSuite "Proof") &&
    refuses "FS-SUITE" (selectGoalExecution alternateSuite "derived_view"))
  let other ← assembly (fun s => s.replace "derived(Merlin3Bls12381)" "interactive") id
  check "wrong scheme binding" (refuses "FS-SUITE" (selectScheme other "Proof"))
  IO.println "Constructed Schnorr source selection, transcript, handler, cache and exact acceptance checks passed."

end ConstructedSchnorrCheck

#print axioms Zkc.Frontend.Constructed.Verifier.handler_correspondence
#eval ConstructedSchnorrCheck.runChecks

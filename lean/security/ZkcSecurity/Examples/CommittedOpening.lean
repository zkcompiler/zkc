module

public import ZkcSecurity.FiatShamir.ProviderSimulation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

@[expose] public section

/-! A committed table, one challenge and an authenticated opening.

This module states the joint security experiment of the smallest protocol that
combines commitment metadata, transcript binding, a challenge and an
authenticated opening; its bound is proved in
`ZkcSecurity.Examples.CommittedOpeningBound` (`intendedBound`). The
authenticated configuration `c = (σ, k, w)` fixes the scheme identity `σ`
(which also fixes how a row is read, `accepts σ row`), the depth `k` of a
binary Merkle tree of `2 ^ k` rows and the row width `w`; a root binds neither
the height nor the scheme, so the configuration is bound explicitly.

1. Binding: the transcript starts with the binding event of the context and `c`.
2. The producer sends a root, which is absorbed.
3. The validator requests one index below `2 ^ k`. Its transcript key `K` is the
   binding, the root and the request.
4. The producer sends the opening (a row and a path) after this last request; it
   is either absorbed or omitted as a terminal message.
5. The validator authenticates the opening through hash-effect calls (one leaf
   hash and `k` node hashes), rejects unless it authenticates, and accepts
   exactly when `accepts σ row`.

`verifier` is this validator as a process over `signature`, whose operations are
the two receives, the request and the calls of the two hash families. One
interpreter, `interpret`, reads the process under any oracle for the joint
namespace `Query` (transcript keys, leaf hashes, node hashes), in any monad:

- **Concrete.** Deterministic hash functions and a challenge function, in `Id`.
  The honest proof is accepted exactly when its opened row is accepted
  (`concrete_honest`), and absorbing or omitting the terminal opening gives the
  same outcome for every challenge and hash function (`concrete_absorption`).
- **Random oracle.** Every family is lazily sampled in one oracle
  `OracleSpec.ofFn Range`. Evaluated against a total answer table this is the
  concrete reading (`evalWithAnswerFn_interpret`), so the honest experiment for a
  table whose rows are all accepted accepts with probability one
  (`oracle_honest`).
- **Ideal.** The carriers of the hash families are the committed tables:
  hashing builds the tree of rows (`Carrier`, `idealHash`). Under this reading
  an authenticated row is the committed row at its index (`ideal_authenticated`).

**The joint experiment.** An adversary is any oracle computation on the joint
namespace producing proof messages, with at most `q_T` transcript calls and
`q_M` Merkle calls on every path (`Budgets`). The validator's `k + 1` Merkle
calls and its transcript call run in the same oracle and appear in the same
record (`loggedRun`).

**The extraction checkpoint convention.** Extraction for a transcript key `K`
runs once, immediately before the first fresh query of `K` in the joint record
(its first query, from the empty cache), from the record so far, whichever party
issues that query, and is reused whenever `K` is queried again. The extracted table `T*[c, K]` is indexed by the
configuration and the key, not by the root (`frozen`):

- the record before the first query of `K` does not change when the record is
  extended (`frozen_append`), so repetitions and later calls reuse it;
- it does not change when the answer at `K` is resampled, in every
  deterministic run (`frozen_update`), so it is fixed before that answer;
- one root under two configurations gives two keys and two checkpoints
  (`verifierKey_configuration`).

Re-extraction at a repetition is admissible only as a separately specified and
charged checkpoint; extraction from the terminal record is not frozen (a
counterexample is in `TestsSecurity`).

**The event and the intended bound.** `Far` holds of an extracted table when no
table was extracted or when at least `δ · 2 ^ k` of its rows are not accepted.
The extractor must therefore be total: it returns a table for every record,
with arbitrary rows where the record determines none. An extractor that returns
no table when a row is missing makes `IntendedBound` false: a prover whose tree
has honest accepted rows at half the indices and no row elsewhere is accepted
with probability one half while `Far` holds.
`IntendedBound` states, as a proposition and not a theorem,
`Pr[Accept ∧ Far(T*[c, K])] ≤ (q_T + 1) · κ · (1 - δ) + ε_ext + ε_ns`: the
history-oracle term, the extraction and drift term over at most `q_T + 1`
checkpoints, and the namespace term. Its proof, through the commitment bridge,
is `ZkcSecurity.Examples.CommittedOpeningBound.intendedBound`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CommittedOpening
open OracleComp OracleSpec ZkcSecurity.FiatShamir

/-! ### Tables, hash calls and climbs -/

/-- A perfect binary tree of depth `d` holding a table of `2 ^ d` rows. Row `i`
is reached by the bits of `i`, most significant first. -/
inductive PTree (α : Type) : ℕ → Type where
  | leaf (value : α) : PTree α 0
  | node {depth : ℕ} (left right : PTree α depth) : PTree α (depth + 1)

/-- The row at an index. -/
def PTree.get {α : Type} : {d : ℕ} → PTree α d → ℕ → α
  | _, .leaf value, _ => value
  | _, @PTree.node _ depth left right, index =>
      if index < 2 ^ depth then left.get index else right.get (index - 2 ^ depth)

/-- A call of the commitment scheme's hash families: the leaf hash of a row or
the two-to-one node hash. -/
inductive HashCall (Row Digest : Type) where
  | leaf (row : Row)
  | node (left right : Digest)
  deriving DecidableEq

variable {Row Digest : Type}

/-- One step of a climb: at an even index the current digest is the left
child. -/
def parent (index : ℕ) (current sibling : Digest) : HashCall Row Digest :=
  if index % 2 = 0 then .node current sibling else .node sibling current

section Pure
variable (hash : HashCall Row Digest → Digest)

/-- The root of a table. -/
def root : {d : ℕ} → PTree Row d → Digest
  | _, .leaf row => hash (.leaf row)
  | _, .node left right => hash (.node (root left) (root right))

/-- The authentication path of a row, from the leaf level up. -/
def path : {d : ℕ} → PTree Row d → ℕ → List Digest
  | _, .leaf _, _ => []
  | _, @PTree.node _ depth left right, index =>
      if index < 2 ^ depth then path left index ++ [root hash right]
      else path right (index - 2 ^ depth) ++ [root hash left]

/-- Climb from a digest along a path; the bits of the index, least significant
first, choose the side at each level. -/
def climb : ℕ → List Digest → Digest → Digest
  | _, [], current => current
  | index, sibling :: rest, current => climb (index / 2) rest (hash (parent index current sibling))

theorem path_length : ∀ {d : ℕ} (table : PTree Row d) (index : ℕ), (path hash table index).length = d
  | _, .leaf _, _ => rfl
  | _, @PTree.node _ depth left right, index => by
      unfold path
      split
      · simp [path_length left index]
      · simp [path_length right (index - 2 ^ depth)]

theorem climb_append (index : ℕ) :
    ∀ (siblings : List Digest) (sibling current : Digest),
      climb hash index (siblings ++ [sibling]) current =
        hash (parent (index / 2 ^ siblings.length) (climb hash index siblings current) sibling)
  | [], sibling, current => by simp [climb]
  | first :: rest, sibling, current => by
      simp only [List.cons_append, climb, List.length_cons]
      rw [climb_append (index / 2) rest sibling, Nat.div_div_eq_div_mul, pow_succ', mul_comm]

/-- A climb reads only as many low bits of the index as the path has levels. -/
theorem climb_mod (index : ℕ) :
    ∀ (siblings : List Digest) (current : Digest),
      climb hash index siblings current = climb hash (index % 2 ^ siblings.length) siblings current
  | [], current => rfl
  | sibling :: rest, current => by
      simp only [climb, List.length_cons]
      have low : index % 2 ^ (rest.length + 1) % 2 = index % 2 := by
        rw [pow_succ, Nat.mod_mul_left_mod]
      have high : index % 2 ^ (rest.length + 1) / 2 % 2 ^ rest.length =
          index / 2 % 2 ^ rest.length := by
        rw [pow_succ, Nat.mod_mul_left_div_self, Nat.mod_mod]
      rw [climb_mod (index / 2) rest, climb_mod (index % 2 ^ (rest.length + 1) / 2) rest, high]
      unfold parent
      rw [low]

/-- Completeness of authentication: climbing the path of a row from its leaf
digest yields the root. -/
theorem climb_path : ∀ {d : ℕ} (table : PTree Row d) (index : ℕ), index < 2 ^ d →
    climb hash index (path hash table index) (hash (.leaf (table.get index))) = root hash table
  | _, .leaf _, _, _ => rfl
  | _, @PTree.node _ depth left right, index, below => by
      unfold path PTree.get
      split
      · rename_i inLeft
        rw [climb_append, path_length, climb_mod, path_length, Nat.mod_eq_of_lt inLeft,
          climb_path left index inLeft, Nat.div_eq_of_lt inLeft]
        rfl
      · rename_i inRight
        have upper : index - 2 ^ depth < 2 ^ depth := by rw [pow_succ] at below; omega
        have bit : index / 2 ^ depth = 1 := by
          rw [Nat.div_eq_iff (Nat.two_pow_pos depth)]
          constructor <;> rw [pow_succ] at below <;> omega
        have low : index % 2 ^ depth = index - 2 ^ depth := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt upper]
        rw [climb_append, path_length, climb_mod, path_length, low,
          climb_path right (index - 2 ^ depth) upper, bit]
        rfl

end Pure

/-! ### The ideal reading of authentication -/

/-- The ideal carriers of the hash families: the committed rows themselves, as
a tree. -/
inductive Carrier (Row : Type) where
  | leaf (row : Row)
  | node (left right : Carrier Row)
  deriving DecidableEq

/-- The ideal reading's hash families build the tree of committed rows. -/
def idealHash : HashCall Row (Carrier Row) → Carrier Row
  | .leaf row => .leaf row
  | .node left right => .node left right

/-- In the ideal reading, an authenticated row is the committed row at its
index: climbing a path of the table's depth from a row's leaf to the committed
tree places the row at the index. -/
theorem ideal_authenticated : ∀ {d : ℕ} (table : PTree Row d) (index : ℕ) (row : Row)
    (siblings : List (Carrier Row)), index < 2 ^ d → siblings.length = d →
      climb idealHash index siblings (.leaf row) = root idealHash table → row = table.get index
  | _, .leaf value, _, row, siblings, _, length, reached => by
      rw [List.length_eq_zero_iff.mp length] at reached
      exact Carrier.leaf.inj reached
  | _, @PTree.node _ depth left right, index, row, siblings, below, length, reached => by
      obtain ⟨lower, sibling, rfl⟩ : ∃ lower sibling, siblings = lower ++ [sibling] := by
        rcases List.eq_nil_or_concat siblings with empty | ⟨lower, sibling, concat⟩
        · simp [empty] at length
        · exact ⟨lower, sibling, concat.trans List.concat_eq_append⟩
      have lowerLength : lower.length = depth := by simpa using length
      rw [climb_append, climb_mod, lowerLength] at reached
      unfold PTree.get
      split
      · rename_i inLeft
        rw [Nat.div_eq_of_lt inLeft, Nat.mod_eq_of_lt inLeft] at reached
        simp only [parent, Nat.zero_mod, ↓reduceIte, idealHash, root, Carrier.node.injEq] at reached
        exact ideal_authenticated left index row lower inLeft lowerLength reached.1
      · rename_i inRight
        have upper : index - 2 ^ depth < 2 ^ depth := by rw [pow_succ] at below; omega
        have bit : index / 2 ^ depth = 1 := by
          rw [Nat.div_eq_iff (Nat.two_pow_pos depth)]
          constructor <;> rw [pow_succ] at below <;> omega
        have low : index % 2 ^ depth = index - 2 ^ depth := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt upper]
        rw [bit, low] at reached
        simp only [parent, Nat.one_mod, one_ne_zero, ↓reduceIte, idealHash, root,
          Carrier.node.injEq] at reached
        exact ideal_authenticated right (index - 2 ^ depth) row lower upper lowerLength reached.2

/-! ### The validator process -/

/-- The validator's operations: receive the root, request an index below
`2 ^ depth`, receive the opening, and call a hash family. -/
inductive Op (Row Digest : Type) where
  | root
  | position (depth : ℕ)
  | opening
  | hash (call : HashCall Row Digest)

abbrev signature (Row Digest : Type) : PIR.Signature where
  Op := Op Row Digest
  Reply
    | .root => Digest
    | .position depth => Fin (2 ^ depth)
    | .opening => Row × List Digest
    | .hash _ => Digest

/-- Processes compose associatively. -/
theorem bind_assoc {I : PIR.Signature} {A B C : Type} :
    ∀ (process : PIR.Process I A) (first : A → PIR.Process I B) (second : B → PIR.Process I C),
      (process.bind first).bind second = process.bind fun value => (first value).bind second
  | .done _, _, _ => rfl
  | .halt _, _, _ => rfl
  | .call operation next, first, second => by
      simp only [PIR.Process.bind]
      congr
      funext reply
      exact bind_assoc (next reply) first second

/-- The climb as a process of hash-effect calls. -/
def climbProcess : ℕ → List Digest → Digest → PIR.Process (signature Row Digest) Digest
  | _, [], current => .done current
  | index, sibling :: rest, current =>
      .call (.hash (parent index current sibling)) fun up => climbProcess (index / 2) rest up

/-- The authenticated configuration: scheme identity, tree depth and row width
(in coordinates). -/
structure Configuration (Scheme : Type) where
  scheme : Scheme
  depth : ℕ
  width : ℕ
  deriving DecidableEq

variable {Scheme Coordinate : Type}

/-- Authentication of an opening at the configuration's expected shape: the row
has the configured width and the path the configured depth, and climbing from
the row's leaf hash reaches the root. The shape comes from the configuration,
never from the opening. -/
def authenticate [DecidableEq Digest] (configuration : Configuration Scheme) (rootValue : Digest)
    (index : ℕ) (row : List Coordinate) (siblings : List Digest) :
    PIR.Process (signature (List Coordinate) Digest) Bool :=
  if row.length = configuration.width ∧ siblings.length = configuration.depth then
    .call (.hash (.leaf row)) fun leafDigest =>
      (climbProcess index siblings leafDigest).bind fun top => .done (decide (top = rootValue))
  else .done false

/-- The validator: receive the root, request the index, receive the opening,
reject unless it authenticates, and accept exactly when the scheme accepts the
row. -/
def verifier [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (configuration : Configuration Scheme) : PIR.Process (signature (List Coordinate) Digest) Bool :=
  .call .root fun rootValue =>
    .call (.position configuration.depth) fun index =>
      .call .opening fun opened =>
        (authenticate configuration rootValue index.val opened.1 opened.2).bind fun ok =>
          if ok then .done (accepts configuration.scheme opened.1) else .halt .reject

/-! ### The joint namespace and one interpreter -/

/-- Proof messages. -/
inductive Message (Row Digest : Type) where
  | root (value : Digest)
  | opening (row : Row) (siblings : List Digest)
  deriving DecidableEq

/-- Absorbed transcript events. -/
inductive Event (Context Scheme Row Digest : Type) where
  | binding (context : Context) (configuration : Configuration Scheme)
  | root (value : Digest)
  | position (depth : ℕ)
  | opening (row : Row) (siblings : List Digest)
  deriving DecidableEq

variable {Context : Type}

/-- The depth of the request that ends a transcript key; zero for other keys. -/
def depthOf : List (Event Context Scheme Row Digest) → ℕ := fun key =>
  match key.getLast? with
  | some (.position depth) => depth
  | _ => 0

/-- The transcript oracle's answer at a key: an index below `2 ^ depth` for the
key's final request. -/
abbrev Answer (key : List (Event Context Scheme Row Digest)) := Fin (2 ^ depthOf key)

theorem depthOf_request (history : List (Event Context Scheme Row Digest)) (depth : ℕ) :
    depthOf (history ++ [.position depth]) = depth := by
  simp [depthOf]

/-- A query of the joint namespace: a transcript key or a hash call. -/
inductive Query (Context Scheme Row Digest : Type) where
  | transcript (key : List (Event Context Scheme Row Digest))
  | hash (call : HashCall Row Digest)
  deriving DecidableEq

/-- Answers in the joint namespace. -/
@[reducible] def Range : Query Context Scheme Row Digest → Type
  | .transcript key => Answer key
  | .hash _ => Digest

instance [SampleableType Digest] :
    ∀ query : Query Context Scheme Row Digest, SampleableType (Range query)
  | .transcript key => inferInstanceAs (SampleableType (Fin (2 ^ depthOf key)))
  | .hash _ => inferInstanceAs (SampleableType Digest)

/-- The joint oracle: the typed history oracle and the two hash families. -/
abbrev spec (Context Scheme Row Digest : Type) := OracleSpec.ofFn (Range (Context := Context)
  (Scheme := Scheme) (Row := Row) (Digest := Digest))

/-- The index a request decodes from its raw answer; exact when the answer is
below `2 ^ depth`, as the transcript oracle's answers at the request's key are
(`decodeIndex_answer`). -/
def decodeIndex (depth : ℕ) {bound : ℕ} (raw : Fin bound) : Fin (2 ^ depth) :=
  ⟨raw.val % 2 ^ depth, Nat.mod_lt _ (Nat.two_pow_pos depth)⟩

theorem decodeIndex_answer (history : List (Event Context Scheme Row Digest)) (depth : ℕ)
    (raw : Answer (history ++ [.position depth])) :
    (decodeIndex depth raw).val = raw.val := by
  have below : raw.val < 2 ^ depth :=
    calc raw.val < 2 ^ depthOf (history ++ [.position depth]) := raw.isLt
      _ = 2 ^ depth := by rw [depthOf_request]
  exact Nat.mod_eq_of_lt below

/-- Read a process of `signature` under an oracle for the joint namespace:
receives read proof messages (the root is absorbed; the opening is absorbed
only when `absorbOpening`), the request asks the transcript oracle at the
absorbed history followed by its occurrence, and hash calls pass through to
the oracle. Returns the outcome and the unread proof. -/
def interpret {m : Type → Type} [Monad m] {A : Type}
    (oracle : (query : Query Context Scheme Row Digest) → m (Range query)) (absorbOpening : Bool) :
    PIR.Process (signature Row Digest) A → List (Event Context Scheme Row Digest) →
      List (Message Row Digest) → m (PIR.Outcome A × List (Message Row Digest))
  | .done value, _, proof => pure (.returned value, proof)
  | .halt stop, _, proof => pure (.stopped stop, proof)
  | .call .root next, history, proof =>
      match proof with
      | .root value :: rest =>
          interpret oracle absorbOpening (next value) (history ++ [.root value]) rest
      | _ => pure (.stopped .refused, proof)
  | .call (.position depth) next, history, proof => do
      let raw ← oracle (.transcript (history ++ [.position depth]))
      interpret oracle absorbOpening (next (decodeIndex depth raw)) (history ++ [.position depth])
        proof
  | .call .opening next, history, proof =>
      match proof with
      | .opening row siblings :: rest =>
          interpret oracle absorbOpening (next (row, siblings))
            (if absorbOpening then history ++ [.opening row siblings] else history) rest
      | _ => pure (.stopped .refused, proof)
  | .call (.hash call) next, history, proof => do
      let digest ← oracle (.hash call)
      interpret oracle absorbOpening (next digest) history proof

/-- Binding in `Id` applies the continuation. -/
theorem id_bind_eq {α β : Type} (value : Id α) (next : α → Id β) : value >>= next = next value :=
  rfl

/-- The hash families of an oracle in `Id`. -/
def hashOf (oracle : (query : Query Context Scheme Row Digest) → Range query) :
    HashCall Row Digest → Digest :=
  fun call => oracle (.hash call)

/-- A climb process followed by a continuation is the climb's digest followed
by the continuation, in a deterministic reading. -/
theorem interpret_climb {A : Type} (oracle : (query : Query Context Scheme Row Digest) → Range query)
    (absorbOpening : Bool) (next : Digest → PIR.Process (signature Row Digest) A)
    (history : List (Event Context Scheme Row Digest)) (proof : List (Message Row Digest)) :
    ∀ (index : ℕ) (siblings : List Digest) (current : Digest),
      interpret (m := Id) oracle absorbOpening ((climbProcess index siblings current).bind next)
          history proof =
        interpret (m := Id) oracle absorbOpening (next (climb (hashOf oracle) index siblings current))
          history proof
  | _, [], _ => rfl
  | index, sibling :: rest, current => by
      simp only [climbProcess, PIR.Process.bind, interpret, climb]
      exact interpret_climb oracle absorbOpening next history proof (index / 2) rest _

/-- Authentication followed by a continuation is the continuation at the
authentication's decision, in a deterministic reading. -/
theorem interpret_authenticate [DecidableEq Digest] {A Bound : Type}
    (oracle : (query : Query Context Bound (List Coordinate) Digest) → Range query)
    (absorbOpening : Bool) (configuration : Configuration Scheme) (rootValue : Digest) (index : ℕ)
    (row : List Coordinate) (siblings : List Digest)
    (next : Bool → PIR.Process (signature (List Coordinate) Digest) A)
    (history : List (Event Context Bound (List Coordinate) Digest))
    (proof : List (Message (List Coordinate) Digest)) :
    interpret (m := Id) oracle absorbOpening
        ((authenticate configuration rootValue index row siblings).bind next) history proof =
      interpret (m := Id) oracle absorbOpening
        (next (decide (row.length = configuration.width ∧ siblings.length = configuration.depth ∧
          climb (hashOf oracle) index siblings (hashOf oracle (.leaf row)) = rootValue)))
        history proof := by
  unfold authenticate
  split
  · rename_i shape
    simp only [PIR.Process.bind, interpret]
    change interpret (m := Id) oracle absorbOpening
      (((climbProcess index siblings (hashOf oracle (.leaf row))).bind fun top =>
        .done (decide (top = rootValue))).bind next) history proof = _
    rw [bind_assoc, interpret_climb]
    simp only [PIR.Process.bind, shape, true_and]
  · rename_i shape
    have refused : ¬ (row.length = configuration.width ∧ siblings.length = configuration.depth ∧
        climb (hashOf oracle) index siblings (hashOf oracle (.leaf row)) = rootValue) :=
      fun held => shape ⟨held.1, held.2.1⟩
    simp only [PIR.Process.bind, refused, decide_false]

/-- The validator's outcome in a deterministic reading from any absorbed history,
whose binding events may record any metadata `Bound`, on a proof that starts
with a root and an opening: the decision of authentication at the index the
transcript answers after the history, the root and the request, then the
scheme's acceptance of the row. -/
theorem interpret_verifier_from [DecidableEq Digest] {Bound : Type}
    (oracle : (query : Query Context Bound (List Coordinate) Digest) → Range query)
    (absorbOpening : Bool) (accepts : Scheme → List Coordinate → Bool)
    (configuration : Configuration Scheme) (history : List (Event Context Bound (List Coordinate) Digest))
    (rootValue : Digest) (row : List Coordinate) (siblings : List Digest)
    (rest : List (Message (List Coordinate) Digest)) :
    interpret (m := Id) oracle absorbOpening (verifier accepts configuration) history
        (.root rootValue :: .opening row siblings :: rest) =
      ((if row.length = configuration.width ∧ siblings.length = configuration.depth ∧
          climb (hashOf oracle)
              (decodeIndex configuration.depth (oracle (.transcript
                (history ++ [.root rootValue] ++ [.position configuration.depth])))).val
              siblings (hashOf oracle (.leaf row)) = rootValue
        then .returned (accepts configuration.scheme row) else .stopped .reject), rest) := by
  simp only [verifier, interpret, id_bind_eq]
  rw [interpret_authenticate]
  split
  · rename_i held
    rw [ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true held))]
    rfl
  · rename_i refused
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun held => refused (decide_eq_true held))]
    rfl

/-- The validator's outcome in a deterministic reading, on a proof that starts
with a root and an opening: the decision of authentication at the index the
transcript answers at the validator's key, then the scheme's acceptance of the
row. -/
theorem interpret_verifier [DecidableEq Digest]
    (oracle : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (absorbOpening : Bool) (accepts : Scheme → List Coordinate → Bool)
    (configuration : Configuration Scheme) (context : Context) (rootValue : Digest)
    (row : List Coordinate) (siblings : List Digest) (rest : List (Message (List Coordinate) Digest)) :
    interpret (m := Id) oracle absorbOpening (verifier accepts configuration)
        [.binding context configuration] (.root rootValue :: .opening row siblings :: rest) =
      ((if row.length = configuration.width ∧ siblings.length = configuration.depth ∧
          climb (hashOf oracle)
              (decodeIndex configuration.depth (oracle (.transcript
                [.binding context configuration, .root rootValue, .position configuration.depth]))).val
              siblings (hashOf oracle (.leaf row)) = rootValue
        then .returned (accepts configuration.scheme row) else .stopped .reject), rest) :=
  interpret_verifier_from oracle absorbOpening accepts configuration [.binding context configuration]
    rootValue row siblings rest

/-! ### The three readings -/

/-- The concrete reading's oracle: deterministic hash functions and a challenge
function on transcript keys. -/
def concreteOracle (challenge : (key : List (Event Context Scheme Row Digest)) → Answer key)
    (hash : HashCall Row Digest → Digest) : (query : Query Context Scheme Row Digest) → Range query
  | .transcript key => challenge key
  | .hash call => hash call

/-- The random-oracle reading: every query goes to the joint lazily sampled
oracle. -/
def oracleReading {A : Type} (absorbOpening : Bool) (process : PIR.Process (signature Row Digest) A)
    (history : List (Event Context Scheme Row Digest)) (proof : List (Message Row Digest)) :
    OracleComp (spec Context Scheme Row Digest) (PIR.Outcome A × List (Message Row Digest)) :=
  interpret (fun query => liftM ((spec Context Scheme Row Digest).query query)) absorbOpening
    process history proof

/-- Evaluated against a total answer table, the random-oracle reading is the
concrete reading with that table. -/
theorem evalWithAnswerFn_interpret {A : Type}
    (table : QueryImpl (spec Context Scheme Row Digest) Id) (absorbOpening : Bool) :
    ∀ (process : PIR.Process (signature Row Digest) A)
      (history : List (Event Context Scheme Row Digest)) (proof : List (Message Row Digest)),
      evalWithAnswerFn table (oracleReading absorbOpening process history proof) =
        interpret (m := Id) (fun query => table query) absorbOpening process history proof := by
  intro process
  induction process with
  | done value => intro history proof; rfl
  | halt stop => intro history proof; rfl
  | call operation next ih =>
      intro history proof
      cases operation with
      | root =>
          cases proof with
          | nil => rfl
          | cons message rest =>
              cases message with
              | root value => exact ih value _ _
              | opening row siblings => rfl
      | position depth =>
          simp only [oracleReading, interpret, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
          exact ih _ _ _
      | opening =>
          cases proof with
          | nil => rfl
          | cons message rest =>
              cases message with
              | root value => rfl
              | opening row siblings => exact ih (row, siblings) _ _
      | hash call =>
          simp only [oracleReading, interpret, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
          exact ih _ _ _

/-! ### Honest runs -/

/-- The initial history: the binding of the context and the configuration. -/
def initial (context : Context) (configuration : Configuration Scheme) :
    List (Event Context Scheme Row Digest) :=
  [.binding context configuration]

/-- The validator's transcript key for a root: the binding, the root and the
request. -/
def verifierKey (context : Context) (configuration : Configuration Scheme) (rootValue : Digest) :
    List (Event Context Scheme Row Digest) :=
  initial context configuration ++ [.root rootValue, .position configuration.depth]

/-- One root under two configurations gives two validator keys, hence two
checkpoints. -/
theorem verifierKey_configuration (context : Context) (rootValue : Digest)
    {first second : Configuration Scheme} (different : first ≠ second) :
    verifierKey (Row := Row) context first rootValue ≠ verifierKey context second rootValue := by
  intro same
  simp only [verifierKey, initial, List.cons_append, List.nil_append, List.cons.injEq,
    Event.binding.injEq, true_and] at same
  exact different same.1

/-- The honest index in the concrete reading: the challenge at the validator's
key for the table's root. -/
def honestIndex (challenge : (key : List (Event Context Scheme (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (context : Context)
    (configuration : Configuration Scheme) (table : PTree (List Coordinate) configuration.depth) :
    Fin (2 ^ configuration.depth) :=
  decodeIndex configuration.depth (challenge (verifierKey context configuration (root hash table)))

/-- The honest proof in the concrete reading: the root of the committed table,
then the opening at the honest index. -/
def honestProof (challenge : (key : List (Event Context Scheme (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (context : Context)
    (configuration : Configuration Scheme) (table : PTree (List Coordinate) configuration.depth) :
    List (Message (List Coordinate) Digest) :=
  let index := honestIndex challenge hash context configuration table
  [.root (root hash table), .opening (table.get index.val) (path hash table index.val)]

/-- In the concrete reading, for every challenge function and hash functions,
the honest proof of a table whose rows have the configured width is read
completely and accepted exactly when its opened row is accepted, whether the
opening is absorbed or omitted. -/
theorem concrete_honest [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (challenge : (key : List (Event Context Scheme (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (absorbOpening : Bool) (context : Context)
    (configuration : Configuration Scheme) (table : PTree (List Coordinate) configuration.depth)
    (widths : ∀ index, (table.get index).length = configuration.width) :
    interpret (m := Id) (concreteOracle challenge hash) absorbOpening (verifier accepts configuration)
        (initial context configuration) (honestProof challenge hash context configuration table) =
      (.returned (accepts configuration.scheme
        (table.get (honestIndex challenge hash context configuration table).val)), []) := by
  have held : (table.get (honestIndex challenge hash context configuration table).val).length =
        configuration.width ∧
      (path hash table (honestIndex challenge hash context configuration table).val).length =
        configuration.depth ∧
      climb hash (honestIndex challenge hash context configuration table).val
          (path hash table (honestIndex challenge hash context configuration table).val)
          (hash (.leaf (table.get (honestIndex challenge hash context configuration table).val))) =
        root hash table :=
    ⟨widths _, path_length hash table _, climb_path hash table _ (Fin.isLt _)⟩
  exact (interpret_verifier (concreteOracle challenge hash) absorbOpening accepts configuration
    context (root hash table) _ _ []).trans
    (congrArg (fun outcome => (outcome, ([] : List (Message (List Coordinate) Digest))))
      (ite_eq_left_of_eq_true _ _ (eq_true (by exact held))))

/-- The terminal opening: absorbing it or omitting it gives the same outcome in
the concrete reading, for every challenge and hash function and every proof,
because no request follows it. -/
theorem concrete_absorption [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (challenge : (key : List (Event Context Scheme (List Coordinate) Digest)) → Answer key)
    (hash : HashCall (List Coordinate) Digest → Digest) (context : Context)
    (configuration : Configuration Scheme) (proof : List (Message (List Coordinate) Digest)) :
    interpret (m := Id) (concreteOracle challenge hash) true (verifier accepts configuration)
        (initial context configuration) proof =
      interpret (m := Id) (concreteOracle challenge hash) false (verifier accepts configuration)
        (initial context configuration) proof := by
  cases proof with
  | nil => rfl
  | cons first rest =>
      cases first with
      | opening row siblings => rfl
      | root rootValue =>
          cases rest with
          | nil => rfl
          | cons second tail =>
              cases second with
              | root value => rfl
              | opening row siblings =>
                  exact (interpret_verifier _ true accepts configuration context rootValue row
                    siblings tail).trans
                    (interpret_verifier _ false accepts configuration context rootValue row
                      siblings tail).symm

/-- The ideal reading's honest run: with the committed tree as the carrier of
every digest, the honest proof is accepted exactly when its opened row is. -/
theorem ideal_honest [DecidableEq Coordinate] (accepts : Scheme → List Coordinate → Bool)
    (challenge : (key : List (Event Context Scheme (List Coordinate) (Carrier (List Coordinate)))) →
      Answer key)
    (absorbOpening : Bool) (context : Context) (configuration : Configuration Scheme)
    (table : PTree (List Coordinate) configuration.depth)
    (widths : ∀ index, (table.get index).length = configuration.width) :
    interpret (m := Id) (concreteOracle challenge idealHash) absorbOpening
        (verifier accepts configuration) (initial context configuration)
        (honestProof challenge idealHash context configuration table) =
      (.returned (accepts configuration.scheme
        (table.get (honestIndex challenge idealHash context configuration table).val)), []) :=
  concrete_honest accepts challenge idealHash absorbOpening context configuration table widths

/-! ### The random-oracle experiment -/

/-- An event that holds of the deterministic evaluation against every total
answer table holds with probability one in the lazily sampled oracle. -/
theorem prEvent_randomOracle_eq_one {ι α : Type} [DecidableEq ι] {oracleSpec : OracleSpec ι}
    [∀ query, SampleableType (oracleSpec.Range query)] (computation : OracleComp oracleSpec α)
    (event : α → Prop)
    (holds : ∀ table : QueryImpl oracleSpec Id, event (evalWithAnswerFn table computation)) :
    Pr{let result ← (simulateQ randomOracle computation).run' ∅}[event result] = 1 := by
  refine OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun result member => ?_
  rw [StateT.run'_eq, support_map] at member
  obtain ⟨⟨value, cache⟩, reached, rfl⟩ := member
  obtain ⟨table, _, evaluated⟩ :=
    (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support computation ∅ value).mpr
      ⟨cache, reached⟩
  rw [← evaluated]
  exact holds table

/-- One call of a hash family in the joint oracle. -/
def hashQuery (call : HashCall Row Digest) : OracleComp (spec Context Scheme Row Digest) Digest :=
  liftM ((spec Context Scheme Row Digest).query (.hash call))

theorem evalWithAnswerFn_hashQuery (table : QueryImpl (spec Context Scheme Row Digest) Id)
    (call : HashCall Row Digest) :
    evalWithAnswerFn table (hashQuery call) = hashOf (fun query => table query) call :=
  evalWithAnswerFn_liftM_query table _

/-- The honest table's root, computed by hash queries. -/
def rootQueries : {d : ℕ} → PTree Row d → OracleComp (spec Context Scheme Row Digest) Digest
  | _, .leaf row => hashQuery (.leaf row)
  | _, .node left right => do
      let leftDigest ← rootQueries left
      let rightDigest ← rootQueries right
      hashQuery (.node leftDigest rightDigest)

/-- An authentication path, computed by hash queries. -/
def pathQueries :
    {d : ℕ} → PTree Row d → ℕ → OracleComp (spec Context Scheme Row Digest) (List Digest)
  | _, .leaf _, _ => pure []
  | _, @PTree.node _ depth left right, index =>
      if index < 2 ^ depth then do
        let below ← pathQueries left index
        let sibling ← rootQueries right
        pure (below ++ [sibling])
      else do
        let below ← pathQueries right (index - 2 ^ depth)
        let sibling ← rootQueries left
        pure (below ++ [sibling])

theorem evalWithAnswerFn_rootQueries (table : QueryImpl (spec Context Scheme Row Digest) Id) :
    ∀ {d : ℕ} (committed : PTree Row d),
      evalWithAnswerFn table (rootQueries (Context := Context) (Scheme := Scheme) committed) =
        root (hashOf fun query => table query) committed
  | _, .leaf row => evalWithAnswerFn_hashQuery table _
  | _, .node left right => by
      simp only [rootQueries, evalWithAnswerFn_bind, evalWithAnswerFn_rootQueries table left,
        evalWithAnswerFn_rootQueries table right, evalWithAnswerFn_hashQuery]
      rfl

theorem evalWithAnswerFn_pathQueries (table : QueryImpl (spec Context Scheme Row Digest) Id) :
    ∀ {d : ℕ} (committed : PTree Row d) (index : ℕ),
      evalWithAnswerFn table (pathQueries (Context := Context) (Scheme := Scheme) committed index) =
        path (hashOf fun query => table query) committed index
  | _, .leaf _, _ => rfl
  | _, @PTree.node _ depth left right, index => by
      unfold pathQueries path
      split
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pathQueries table left,
          evalWithAnswerFn_rootQueries, evalWithAnswerFn_pure]
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pathQueries table right,
          evalWithAnswerFn_rootQueries, evalWithAnswerFn_pure]

/-- The honest prover with oracle access: commit, ask the validator's key, then
compute the opening. -/
def honestProver (context : Context) (configuration : Configuration Scheme)
    (table : PTree (List Coordinate) configuration.depth) :
    OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest)) := do
  let rootValue ← rootQueries table
  let raw ← liftM ((spec Context Scheme (List Coordinate) Digest).query
    (.transcript (verifierKey context configuration rootValue)))
  let index := decodeIndex configuration.depth raw
  let siblings ← pathQueries table index.val
  pure [.root rootValue, .opening (table.get index.val) siblings]

/-- The joint experiment: the prover runs with access to every family, then the
validator runs in the same oracle. -/
def experiment [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (absorbOpening : Bool) (context : Context) (configuration : Configuration Scheme)
    (prover : OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest))) :
    OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest) ×
        (PIR.Outcome Bool × List (Message (List Coordinate) Digest))) :=
  prover >>= fun proof => (proof, ·) <$>
    oracleReading absorbOpening (verifier accepts configuration) (initial context configuration) proof

/-- In the random-oracle reading, the honest experiment for a table whose rows
all have the configured width and are all accepted accepts with probability
one. -/
theorem oracle_honest [DecidableEq Digest] [SampleableType Digest] [DecidableEq Context]
    [DecidableEq Scheme] [DecidableEq Coordinate] (accepts : Scheme → List Coordinate → Bool)
    (absorbOpening : Bool) (context : Context) (configuration : Configuration Scheme)
    (table : PTree (List Coordinate) configuration.depth)
    (widths : ∀ index, (table.get index).length = configuration.width)
    (accepted : ∀ index, accepts configuration.scheme (table.get index) = true) :
    Pr{let result ← (simulateQ randomOracle
        (experiment (Digest := Digest) accepts absorbOpening context configuration
          (honestProver context configuration table))).run' ∅}[
      result.2.1 = PIR.Outcome.returned true] = 1 := by
  refine prEvent_randomOracle_eq_one _ _ fun answers => ?_
  simp only [experiment, honestProver, evalWithAnswerFn_bind, evalWithAnswerFn_map,
    evalWithAnswerFn_liftM_query, evalWithAnswerFn_pathQueries, evalWithAnswerFn_pure,
    evalWithAnswerFn_interpret]
  rw [evalWithAnswerFn_rootQueries]
  refine (congrArg Prod.fst (interpret_verifier (fun query => answers query) absorbOpening accepts
    configuration context _ _ _ [])).trans ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    exact ⟨widths _, path_length _ _ _, climb_path _ _ _ (Fin.isLt _)⟩)), accepted]

/-! ### Records and the checkpoint convention -/

/-- The joint query record of a computation: every call, by the adversary or the
validator, in call order. -/
abbrev Record (Context Scheme Row Digest : Type) := QueryLog (spec Context Scheme Row Digest)

/-- Run a computation in the lazily sampled joint oracle from an empty cache,
keeping its record. -/
def loggedRun [SampleableType Digest] [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Row]
    [DecidableEq Digest] {α : Type} (computation : OracleComp (spec Context Scheme Row Digest) α) :
    ProbComp (α × Record Context Scheme Row Digest) :=
  (simulateQ randomOracle.withLogging computation).run.run' ∅

section Checkpoints
variable [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Row] [DecidableEq Digest]

/-- The record before the first query of the transcript key `key`: before its
first fresh query, since the joint experiment starts from an empty cache. -/
def beforeFirst (key : List (Event Context Scheme Row Digest))
    (record : Record Context Scheme Row Digest) : Record Context Scheme Row Digest :=
  record.takeWhile fun entry => decide (entry.1 ≠ .transcript key)

/-- An extractor reads a table of rows for a configuration and a checkpoint key
from a query record. `Far` counts a missing table as far, so the intended bound
needs an extractor that returns a table for every record (a total extractor). -/
abbrev Extractor (Context Scheme Coordinate Digest : Type) :=
  (configuration : Configuration Scheme) → List (Event Context Scheme (List Coordinate) Digest) →
    Record Context Scheme (List Coordinate) Digest →
      Option (Fin (2 ^ configuration.depth) → List Coordinate)

theorem beforeFirst_append (key : List (Event Context Scheme Row Digest))
    (record more : Record Context Scheme Row Digest)
    (queried : ∃ entry ∈ record, entry.1 = .transcript key) :
    beforeFirst key (record ++ more) = beforeFirst key record := by
  obtain ⟨entry, member, same⟩ := queried
  unfold beforeFirst
  induction record with
  | nil => simp at member
  | cons first rest ih =>
      by_cases hit : first.1 = .transcript key
      · rw [List.cons_append, List.takeWhile_cons_of_neg (by simp [hit]),
          List.takeWhile_cons_of_neg (by simp [hit])]
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact absurd same hit
        · rw [List.cons_append, List.takeWhile_cons_of_pos (by simp [hit]),
            List.takeWhile_cons_of_pos (by simp [hit]), ih inRest]

/-- The record before a key's first query does not depend on the answer at the
key: in every deterministic run, resampling that answer leaves it unchanged. -/
theorem beforeFirst_update (key : List (Event Context Scheme Row Digest)) {α : Type} :
    ∀ (computation : OracleComp (spec Context Scheme Row Digest) α)
      (answers : (query : Query Context Scheme Row Digest) → Range query)
      (answer : Range (Query.transcript (Row := Row) (Digest := Digest) key)),
      beforeFirst key (tableQueryLog computation (Function.update answers (.transcript key) answer)) =
        beforeFirst key (tableQueryLog computation answers) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro answers answer; simp
  | query_bind query next ih =>
      intro answers answer
      rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
      by_cases hit : query = .transcript key
      · subst hit
        unfold beforeFirst
        rw [List.takeWhile_cons_of_neg (by simp), List.takeWhile_cons_of_neg (by simp)]
      · have unchanged : Function.update answers (.transcript key) answer query = answers query :=
          Function.update_of_ne hit _ _
        unfold beforeFirst
        rw [List.takeWhile_cons_of_pos (by simp [hit]), List.takeWhile_cons_of_pos (by simp [hit]),
          unchanged]
        exact congrArg _ (ih (answers query) answers answer)

/-- An extraction respects the checkpoint convention at `key` when it reads only
the record before the key's first query. -/
def FrozenAt {β : Type} (key : List (Event Context Scheme Row Digest))
    (extract : Record Context Scheme Row Digest → β) : Prop :=
  ∀ first second, beforeFirst key first = beforeFirst key second → extract first = extract second

/-- Reading the record before the first query respects the convention. -/
theorem frozenAt_beforeFirst {β : Type} (key : List (Event Context Scheme Row Digest))
    (extract : Record Context Scheme Row Digest → β) :
    FrozenAt key fun record => extract (beforeFirst key record) :=
  fun _ _ same => congrArg extract same

end Checkpoints

/-- The frozen extraction `T*[c, K]`: extraction for the configuration and the
checkpoint key from the record before the key's first query. -/
def frozen [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest]
    (extract : Extractor Context Scheme Coordinate Digest) (configuration : Configuration Scheme)
    (key : List (Event Context Scheme (List Coordinate) Digest))
    (record : Record Context Scheme (List Coordinate) Digest) :
    Option (Fin (2 ^ configuration.depth) → List Coordinate) :=
  extract configuration key (beforeFirst key record)

section Frozen
variable [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate] [DecidableEq Digest]

/-- Reuse: once the key has been queried, later calls, including repetitions of
the key, do not move its frozen extraction. -/
theorem frozen_append (extract : Extractor Context Scheme Coordinate Digest)
    (configuration : Configuration Scheme)
    (key : List (Event Context Scheme (List Coordinate) Digest))
    (record more : Record Context Scheme (List Coordinate) Digest)
    (queried : ∃ entry ∈ record, entry.1 = .transcript key) :
    frozen extract configuration key (record ++ more) = frozen extract configuration key record := by
  rw [frozen, frozen, beforeFirst_append key record more queried]

/-- The frozen extraction is fixed before the answer at its key is sampled. -/
theorem frozen_update (extract : Extractor Context Scheme Coordinate Digest)
    (configuration : Configuration Scheme)
    (key : List (Event Context Scheme (List Coordinate) Digest)) {α : Type}
    (computation : OracleComp (spec Context Scheme (List Coordinate) Digest) α)
    (answers : (query : Query Context Scheme (List Coordinate) Digest) → Range query)
    (answer : Range (Query.transcript (Row := List Coordinate) (Digest := Digest) key)) :
    frozen extract configuration key
        (tableQueryLog computation (Function.update answers (.transcript key) answer)) =
      frozen extract configuration key (tableQueryLog computation answers) := by
  rw [frozen, frozen, beforeFirst_update]

end Frozen

/-! ### Budgets, the event and the intended bound -/

/-- The two budgeted families: transcript keys and Merkle hash calls. -/
inductive Family where
  | transcript
  | merkle
  deriving DecidableEq

/-- The family of a joint query. -/
def familyOf : Query Context Scheme Row Digest → Family
  | .transcript _ => .transcript
  | .hash _ => .merkle

/-- At most `transcriptCalls` transcript calls and `merkleCalls` Merkle calls on
every path. -/
def Budgets {α : Type} (adversary : OracleComp (spec Context Scheme Row Digest) α)
    (transcriptCalls merkleCalls : ℕ) : Prop :=
  Provider.FamilyQueryBound familyOf adversary fun
    | .transcript => transcriptCalls
    | .merkle => merkleCalls

/-- The false statement: no table was extracted, or at least `δ · 2 ^ k` rows of
the extracted table are not accepted. -/
def Far (accepts : Scheme → List Coordinate → Bool) (configuration : Configuration Scheme)
    (fraction : ENNReal) : Option (Fin (2 ^ configuration.depth) → List Coordinate) → Prop
  | none => True
  | some table => fraction * 2 ^ configuration.depth ≤
      ((Finset.univ.filter fun index => accepts configuration.scheme (table index) = false).card :
        ENNReal)

/-- The validator's checkpoint key for a proof: the key of its request after the
proof's root, or none when the proof does not start with a root. -/
def proofKey (context : Context) (configuration : Configuration Scheme) :
    List (Message Row Digest) → Option (List (Event Context Scheme Row Digest))
  | .root rootValue :: _ => some (verifierKey context configuration rootValue)
  | _ => none

/-- The joint security experiment's event: the validator accepts, and the
frozen extraction at its checkpoint key is far. -/
def AcceptsFar [DecidableEq Context] [DecidableEq Scheme] [DecidableEq Coordinate]
    [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (extract : Extractor Context Scheme Coordinate Digest) (context : Context)
    (configuration : Configuration Scheme) (fraction : ENNReal)
    (result : (List (Message (List Coordinate) Digest) ×
        (PIR.Outcome Bool × List (Message (List Coordinate) Digest))) ×
      Record Context Scheme (List Coordinate) Digest) : Prop :=
  result.1.2.1 = .returned true ∧
    ∃ key, proofKey context configuration result.1.1 = some key ∧
      Far accepts configuration fraction (frozen extract configuration key result.2)

/-- The intended bound of the joint experiment, a proposition: every adversary
within the budgets makes the validator accept while the frozen extraction at its
key is far with probability at most the history-oracle term, the extraction and
drift term and the namespace term. -/
def IntendedBound [SampleableType Digest] [DecidableEq Context] [DecidableEq Scheme]
    [DecidableEq Coordinate] [DecidableEq Digest] (accepts : Scheme → List Coordinate → Bool)
    (absorbOpening : Bool) (extract : Extractor Context Scheme Coordinate Digest) (context : Context)
    (configuration : Configuration Scheme) (fraction factor extraction namespaceTerm : ENNReal)
    (transcriptCalls merkleCalls : ℕ) : Prop :=
  ∀ adversary : OracleComp (spec Context Scheme (List Coordinate) Digest)
      (List (Message (List Coordinate) Digest)),
    Budgets adversary transcriptCalls merkleCalls →
      Pr{let result ← loggedRun (experiment accepts absorbOpening context configuration adversary)}[
        AcceptsFar accepts extract context configuration fraction result] ≤
        (transcriptCalls + 1) * factor * (1 - fraction) + extraction + namespaceTerm

end ZkcSecurity.Examples.CommittedOpening
